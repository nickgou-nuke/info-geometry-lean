#!/usr/bin/env python3
"""Assume-and-Recurse Poset DAG Generator.

Builds an in-memory dependency DAG of theorem subgoals, identifies leaf
subgoals (in-degree 0 in unresolved dependencies) dispatchable to concurrent
REPL workers, generates Lean 4 top-level glue verification stubs with explicit
local declarations, and tracks DAG state progression upon subgoal closure.
"""

from __future__ import annotations

import argparse
import enum
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Set, Tuple


# ---------------------------------------------------------------------------
# Enums and Data Models
# ---------------------------------------------------------------------------

class NodeStatus(str, enum.Enum):
    """Lifecycle status of a subgoal in the poset DAG."""
    BLOCKED = "blocked"          # Has unresolved dependencies (in-degree > 0)
    READY = "ready"              # 0 unresolved dependencies, ready for worker dispatch
    IN_PROGRESS = "in_progress"  # Dispatched to a worker REPL
    CLOSED = "closed"            # Proven and kernel-admitted
    FAILED = "failed"            # Failed / counterexample / elaboration error


def sanitize_lean_ident(raw: str) -> str:
    """Sanitize arbitrary string into a valid Lean 4 identifier."""
    cleaned = re.sub(r"[^a-zA-Z0-9_']", "_", raw)
    if cleaned and cleaned[0].isdigit():
        cleaned = "subgoal_" + cleaned
    return cleaned or "subgoal"


@dataclass
class SubgoalNode:
    """A subgoal node within the poset dependency DAG."""
    id: str
    statement: str
    name: str = ""
    dependencies: list[str] = field(default_factory=list)
    dependents: list[str] = field(default_factory=list)
    tactics: list[str] = field(default_factory=list)
    status: NodeStatus = NodeStatus.BLOCKED
    proof: Optional[str] = None
    worker_id: Optional[str] = None
    dispatched_at: Optional[str] = None
    closed_at: Optional[str] = None
    metadata: dict[str, Any] = field(default_factory=dict)

    def __post_init__(self) -> None:
        if not self.name:
            self.name = sanitize_lean_ident(self.id)
        if isinstance(self.status, str):
            self.status = NodeStatus(self.status)

    def to_dict(self) -> dict[str, Any]:
        return {
            "id": self.id,
            "name": self.name,
            "statement": self.statement,
            "dependencies": list(self.dependencies),
            "dependents": list(self.dependents),
            "tactics": list(self.tactics),
            "status": self.status.value,
            "proof": self.proof,
            "worker_id": self.worker_id,
            "dispatched_at": self.dispatched_at,
            "closed_at": self.closed_at,
            "metadata": dict(self.metadata),
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> SubgoalNode:
        return cls(
            id=str(data["id"]),
            name=str(data.get("name") or sanitize_lean_ident(str(data["id"]))),
            statement=str(data.get("statement") or data.get("claim") or data.get("formal_target") or ""),
            dependencies=list(data.get("dependencies") or []),
            dependents=list(data.get("dependents") or []),
            tactics=list(data.get("tactics") or data.get("candidate_tactics") or []),
            status=NodeStatus(data.get("status", NodeStatus.BLOCKED.value)),
            proof=data.get("proof"),
            worker_id=data.get("worker_id"),
            dispatched_at=data.get("dispatched_at"),
            closed_at=data.get("closed_at"),
            metadata=dict(data.get("metadata") or {}),
        )


# ---------------------------------------------------------------------------
# Poset Dependency DAG
# ---------------------------------------------------------------------------

class PosetDAG:
    """Directed Acyclic Graph of subgoals forming a partial order."""

    def __init__(
        self,
        target_name: str = "main_theorem",
        target_statement: str = "",
        hypotheses: str = "",
        open_namespaces: Optional[list[str]] = None,
        glue_tactics: Optional[list[str]] = None,
    ) -> None:
        self.target_name = sanitize_lean_ident(target_name)
        self.target_statement = target_statement
        self.hypotheses = hypotheses.strip()
        self.open_namespaces = open_namespaces or []
        self.glue_tactics = glue_tactics or []
        self.nodes: dict[str, SubgoalNode] = {}
        # Tracks unresolved dependency IDs for each node
        self.unresolved_deps: dict[str, set[str]] = {}

    def add_node(
        self,
        node_id: str,
        statement: str,
        name: Optional[str] = None,
        dependencies: Optional[Iterable[str]] = None,
        tactics: Optional[list[str]] = None,
        metadata: Optional[dict[str, Any]] = None,
    ) -> SubgoalNode:
        """Add a subgoal node to the DAG."""
        if node_id in self.nodes:
            raise ValueError(f"Subgoal node with id {node_id!r} already exists in DAG")

        deps = list(dict.fromkeys(dependencies or []))
        node = SubgoalNode(
            id=node_id,
            name=name or sanitize_lean_ident(node_id),
            statement=statement,
            dependencies=deps,
            tactics=tactics or [],
            status=NodeStatus.BLOCKED,
            metadata=metadata or {},
        )
        self.nodes[node_id] = node
        self.unresolved_deps[node_id] = set(deps)

        # Update dependents for existing nodes
        for dep in deps:
            if dep in self.nodes:
                if node_id not in self.nodes[dep].dependents:
                    self.nodes[dep].dependents.append(node_id)

        # Update dependents if other nodes were added that depend on this one
        for existing_id, existing_node in self.nodes.items():
            if existing_id != node_id and node_id in existing_node.dependencies:
                if existing_id not in node.dependents:
                    node.dependents.append(existing_id)

        # Initial status check: if in-degree in unresolved dependencies is 0, mark READY
        if len(self.unresolved_deps[node_id]) == 0:
            node.status = NodeStatus.READY

        return node

    def build_from_spec(self, spec: dict[str, Any]) -> None:
        """Populate DAG from a structured specification dictionary."""
        self.target_name = sanitize_lean_ident(str(spec.get("name") or spec.get("target_name") or "main_theorem"))
        self.target_statement = str(
            spec.get("statement") or spec.get("target_statement") or spec.get("target") or spec.get("formal_target") or ""
        )
        hyps = spec.get("hypotheses", "")
        if isinstance(hyps, list):
            self.hypotheses = " ".join(str(h) for h in hyps)
        else:
            self.hypotheses = str(hyps).strip()
        self.open_namespaces = list(spec.get("open_namespaces") or spec.get("namespaces") or [])
        self.glue_tactics = list(spec.get("glue_tactics") or spec.get("tactics") or [])

        lemmas = spec.get("lemmas") or spec.get("subgoals") or spec.get("intermediate_lemmas") or []
        for item in lemmas:
            node_id = str(item.get("id") or item.get("name") or f"subgoal_{len(self.nodes) + 1}")
            stmt = str(item.get("statement") or item.get("claim") or item.get("formal_target") or "")
            name = str(item.get("name") or sanitize_lean_ident(node_id))
            deps = list(item.get("dependencies") or item.get("deps") or [])
            tacts = list(item.get("tactics") or item.get("candidate_tactics") or [])
            meta = dict(item.get("metadata") or {})
            self.add_node(
                node_id=node_id,
                statement=stmt,
                name=name,
                dependencies=deps,
                tactics=tacts,
                metadata=meta,
            )

        self.validate()

    def validate(self) -> list[str]:
        """Validate DAG acyclicity and return topological order of node IDs.

        Raises:
            ValueError: If a dependency cycle is detected or an unknown dependency is referenced.
        """
        # Check that all referenced dependencies exist
        for node_id, node in self.nodes.items():
            for dep in node.dependencies:
                if dep not in self.nodes:
                    raise ValueError(f"Node {node_id!r} depends on unknown subgoal {dep!r}")

        # Kahn's algorithm for topological sort and cycle detection
        in_degree = {nid: len(node.dependencies) for nid, node in self.nodes.items()}
        zero_in = [nid for nid, deg in in_degree.items() if deg == 0]
        topo_order: list[str] = []

        while zero_in:
            curr = zero_in.pop(0)
            topo_order.append(curr)
            for dep_node in self.nodes[curr].dependents:
                in_degree[dep_node] -= 1
                if in_degree[dep_node] == 0:
                    zero_in.append(dep_node)

        if len(topo_order) != len(self.nodes):
            unresolved = [nid for nid, deg in in_degree.items() if deg > 0]
            raise ValueError(f"Cycle detected in dependency DAG involving nodes: {unresolved}")

        return topo_order

    def get_leaf_subgoals(self) -> list[SubgoalNode]:
        """Return all nodes with in-degree 0 in unresolved dependencies that are not closed."""
        leaves: list[SubgoalNode] = []
        for nid, node in self.nodes.items():
            if node.status != NodeStatus.CLOSED:
                if len(self.unresolved_deps.get(nid, set())) == 0:
                    leaves.append(node)
        return leaves

    def get_dispatchable_subgoals(self) -> list[SubgoalNode]:
        """Return leaf subgoals currently in READY status for REPL worker dispatch."""
        return [node for node in self.get_leaf_subgoals() if node.status == NodeStatus.READY]

    def dispatch_subgoal(self, node_id: str, worker_id: Optional[str] = None) -> SubgoalNode:
        """Mark a ready subgoal as dispatched / IN_PROGRESS."""
        if node_id not in self.nodes:
            raise KeyError(f"Subgoal {node_id!r} does not exist in DAG")
        node = self.nodes[node_id]
        if node.status not in (NodeStatus.READY, NodeStatus.BLOCKED):
            raise ValueError(f"Cannot dispatch subgoal {node_id!r} in state {node.status.value}")
        if len(self.unresolved_deps.get(node_id, set())) > 0:
            raise ValueError(f"Cannot dispatch subgoal {node_id!r}: unresolved dependencies {sorted(self.unresolved_deps[node_id])}")

        node.status = NodeStatus.IN_PROGRESS
        node.worker_id = worker_id or "default_worker"
        node.dispatched_at = datetime.now(timezone.utc).isoformat()
        return node

    def close_subgoal(
        self,
        node_id: str,
        proof: Optional[str] = None,
        tactics: Optional[list[str]] = None,
    ) -> list[SubgoalNode]:
        """Mark a subgoal as CLOSED and unblock newly enabled parent nodes.

        Returns:
            list[SubgoalNode]: Newly promoted nodes transitioning to READY.
        """
        if node_id not in self.nodes:
            raise KeyError(f"Subgoal {node_id!r} does not exist in DAG")
        node = self.nodes[node_id]
        node.status = NodeStatus.CLOSED
        node.proof = proof or ("; ".join(tactics) if tactics else node.proof or "sorry")
        if tactics:
            node.tactics = list(tactics)
        node.closed_at = datetime.now(timezone.utc).isoformat()

        # Update unresolved dependencies for dependent nodes
        newly_promoted: list[SubgoalNode] = []
        for dep_id in node.dependents:
            dep_node = self.nodes[dep_id]
            if dep_id in self.unresolved_deps:
                self.unresolved_deps[dep_id].discard(node_id)
                # If all dependencies are satisfied and node was BLOCKED
                if len(self.unresolved_deps[dep_id]) == 0:
                    if dep_node.status == NodeStatus.BLOCKED:
                        dep_node.status = NodeStatus.READY
                        newly_promoted.append(dep_node)

        return newly_promoted

    def fail_subgoal(self, node_id: str, reason: Optional[str] = None) -> SubgoalNode:
        """Mark a subgoal as FAILED."""
        if node_id not in self.nodes:
            raise KeyError(f"Subgoal {node_id!r} does not exist in DAG")
        node = self.nodes[node_id]
        node.status = NodeStatus.FAILED
        if reason:
            node.metadata["failure_reason"] = reason
        return node

    def is_complete(self) -> bool:
        """Check if all nodes in the DAG have reached CLOSED status."""
        return bool(self.nodes) and all(n.status == NodeStatus.CLOSED for n in self.nodes.values())

    def generate_glue_verification_stub(
        self,
        theorem_name: Optional[str] = None,
        hypotheses: Optional[str] = None,
        target_statement: Optional[str] = None,
        open_namespaces: Optional[list[str]] = None,
    ) -> str:
        """Generate top-level Lean 4 glue verification stub with explicit local declarations.

        In the Assume-and-Recurse paradigm:
        Each sub-lemma is introduced as an explicit local declaration (`have ... : ... := by sorry`),
        allowing Lean's kernel and elaborator to typecheck the top-level glue proof that
        assembles these intermediate lemmas into the main theorem.
        """
        th_name = sanitize_lean_ident(theorem_name or self.target_name)
        hyps = hypotheses if hypotheses is not None else self.hypotheses
        target_stmt = target_statement or self.target_statement
        namespaces = open_namespaces if open_namespaces is not None else self.open_namespaces

        # Sort nodes topologically for clean sequential declaration
        topo_order = self.validate()

        lines: list[str] = []
        lines.append("/-!")
        lines.append("  Assume-and-Recurse Top-Level Glue Verification Stub")
        lines.append(f"  Target Theorem: {th_name}")
        lines.append("   intermediate sub-lemmas are represented as explicit local declarations")
        lines.append("  to enable formal kernel typechecking of the reduction/glue step.")
        lines.append("-/")
        lines.append("")

        if namespaces:
            for ns in namespaces:
                lines.append(f"open {ns}")
            lines.append("")

        decl_head = f"theorem {th_name}"
        if hyps:
            decl_head += f" {hyps}"
        if target_stmt:
            decl_head += f" : {target_stmt}"
        decl_head += " := by"
        lines.append(decl_head)

        # 1. Local declarations for intermediate sub-lemmas
        lines.append("  -- Local Sub-Lemma Declarations (Assumed for Glue Verification)")
        for nid in topo_order:
            node = self.nodes[nid]
            ident = node.name
            stmt = node.statement.strip()
            if not stmt:
                continue
            
            # If the node has a verified proof, we can embed it; otherwise stub with sorry
            if node.status == NodeStatus.CLOSED and node.proof and node.proof != "sorry":
                lines.append(f"  have {ident} : {stmt} := by")
                lines.append(f"    {node.proof}")
            else:
                lines.append(f"  have {ident} : {stmt} := by sorry")

        # 2. Glue proof section
        lines.append("")
        lines.append("  -- Top-Level Glue Proof (stitches assumed sub-lemmas into target)")
        if self.glue_tactics:
            for tactic in self.glue_tactics:
                lines.append(f"  {tactic}")
        else:
            lines.append("  sorry")

        return "\n".join(lines) + "\n"

    def to_dict(self) -> dict[str, Any]:
        """Serialize DAG state to dictionary."""
        return {
            "target_name": self.target_name,
            "target_statement": self.target_statement,
            "hypotheses": self.hypotheses,
            "open_namespaces": list(self.open_namespaces),
            "glue_tactics": list(self.glue_tactics),
            "nodes": {nid: node.to_dict() for nid, node in self.nodes.items()},
            "unresolved_deps": {nid: sorted(deps) for nid, deps in self.unresolved_deps.items()},
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> PosetDAG:
        """Deserialize DAG from dictionary."""
        dag = cls(
            target_name=data.get("target_name", "main_theorem"),
            target_statement=data.get("target_statement", ""),
            hypotheses=data.get("hypotheses", ""),
            open_namespaces=list(data.get("open_namespaces") or []),
            glue_tactics=list(data.get("glue_tactics") or []),
        )
        nodes_dict = data.get("nodes", {})
        for nid, ndata in nodes_dict.items():
            node = SubgoalNode.from_dict(ndata)
            dag.nodes[node.id] = node
        unres = data.get("unresolved_deps", {})
        dag.unresolved_deps = {nid: set(deps) for nid, deps in unres.items()}
        return dag


# ---------------------------------------------------------------------------
# Self-Tests (Hermetic Dry-Run)
# ---------------------------------------------------------------------------

def run_hermetic_dry_run() -> None:
    """Execute hermetic self-tests on the poset DAG generator."""
    print("=" * 70)
    print("🚀 [DRY-RUN] Executing Poset DAG Generator Verification Suite")
    print("=" * 70)

    # 1. Construct Mock Specification
    mock_spec: dict[str, Any] = {
        "target_name": "fisher_metric_pos_def",
        "hypotheses": "(M : Type) [StatManifold M] (p : M)",
        "target_statement": "PosDef (fisher_metric p)",
        "open_namespaces": ["InformationGeometry", "MeasureTheory"],
        "glue_tactics": [
            "intro v hv",
            "have h1 := lemma_score_variance_pos p v hv",
            "exact lemma_pos_def_from_variance p v h1",
        ],
        "lemmas": [
            {
                "id": "lemma_score_integrable",
                "name": "lemma_score_integrable",
                "statement": "Integrable (score_function p)",
                "dependencies": [],
                "tactics": ["exact score_integrable_of_regular p"],
            },
            {
                "id": "lemma_score_variance_pos",
                "name": "lemma_score_variance_pos",
                "statement": "∀ (v : TangentSpace M p), v ≠ 0 → Variance (score_function p v) > 0",
                "dependencies": ["lemma_score_integrable"],
                "tactics": ["intro v hv", "apply variance_pos_of_identifiability"],
            },
            {
                "id": "lemma_metric_eq_variance",
                "name": "lemma_metric_eq_variance",
                "statement": "fisher_metric p v v = Variance (score_function p v)",
                "dependencies": ["lemma_score_integrable"],
                "tactics": ["exact fisher_metric_def p v"],
            },
            {
                "id": "lemma_pos_def_from_variance",
                "name": "lemma_pos_def_from_variance",
                "statement": "(∀ v ≠ 0, Variance (score_function p v) > 0) → PosDef (fisher_metric p)",
                "dependencies": ["lemma_score_variance_pos", "lemma_metric_eq_variance"],
                "tactics": ["intro hvar", "apply pos_def_intro", "exact hvar"],
            },
        ],
    }

    # 2. Build DAG
    dag = PosetDAG()
    dag.build_from_spec(mock_spec)
    print("✓ Poset DAG successfully constructed from specification.")

    # 3. Validate Topology and Ordering
    topo = dag.validate()
    print(f"✓ Topological order verified ({len(topo)} nodes): {topo}")
    assert topo[0] == "lemma_score_integrable", "Root leaf must be first in topological sort"

    # 4. Cycle Detection Test
    cyclic_dag = PosetDAG()
    cyclic_dag.add_node("A", "True", dependencies=["B"])
    cyclic_dag.add_node("B", "True", dependencies=["A"])
    cycle_detected = False
    try:
        cyclic_dag.validate()
    except ValueError as e:
        cycle_detected = True
        print(f"✓ Cycle detection verified: caught '{e}'")
    assert cycle_detected, "Cycle detection must raise ValueError on cyclic dependencies"

    # 5. Identify Leaf Subgoals (in-degree 0 in unresolved dependencies)
    leaves = dag.get_leaf_subgoals()
    print(f"✓ Initial leaf subgoals (in-degree 0): {[l.id for l in leaves]}")
    assert len(leaves) == 1, f"Expected 1 leaf initially, got {len(leaves)}"
    assert leaves[0].id == "lemma_score_integrable"

    # 6. Verify Dispatchable Subgoals
    dispatchable = dag.get_dispatchable_subgoals()
    assert len(dispatchable) == 1
    assert dispatchable[0].status == NodeStatus.READY

    # 7. Dispatch Leaf Subgoal
    dispatched = dag.dispatch_subgoal("lemma_score_integrable", worker_id="repl_worker_alpha")
    assert dispatched.status == NodeStatus.IN_PROGRESS
    assert dispatched.worker_id == "repl_worker_alpha"
    print(f"✓ Subgoal '{dispatched.id}' dispatched to worker '{dispatched.worker_id}'.")

    # 8. Generate Glue Verification Stub
    glue_code = dag.generate_glue_verification_stub()
    print("\n--- Generated Lean 4 Glue Verification Stub ---")
    print(glue_code.strip())
    print("------------------------------------------------\n")
    assert "theorem fisher_metric_pos_def" in glue_code
    assert "have lemma_score_integrable :" in glue_code
    assert "have lemma_pos_def_from_variance :" in glue_code
    assert "intro v hv" in glue_code
    print("✓ Lean 4 glue verification stub conforms to explicit local declaration standard.")

    # 9. Close Leaf Subgoal and Observe Parent Promotion
    newly_ready = dag.close_subgoal("lemma_score_integrable", proof="exact score_integrable_of_regular p")
    print(f"✓ Closed 'lemma_score_integrable'. Newly promoted READY nodes: {[n.id for n in newly_ready]}")
    # Dependent nodes are lemma_score_variance_pos and lemma_metric_eq_variance.
    # Both had only lemma_score_integrable as dependency, so both should be unblocked and promoted!
    promoted_ids = {n.id for n in newly_ready}
    assert promoted_ids == {"lemma_score_variance_pos", "lemma_metric_eq_variance"}, (
        f"Unexpected promoted nodes: {promoted_ids}"
    )

    # 10. Check Diamond Join (lemma_pos_def_from_variance should still be BLOCKED)
    pos_def_node = dag.nodes["lemma_pos_def_from_variance"]
    assert pos_def_node.status == NodeStatus.BLOCKED, "Parent node must remain BLOCKED while dependencies remain"
    assert dag.unresolved_deps["lemma_pos_def_from_variance"] == {
        "lemma_score_variance_pos", "lemma_metric_eq_variance"
    }

    # 11. Close One Branch of the Diamond
    dag.dispatch_subgoal("lemma_score_variance_pos", worker_id="repl_worker_beta")
    newly_after_one = dag.close_subgoal("lemma_score_variance_pos", proof="apply variance_pos_of_identifiability")
    assert len(newly_after_one) == 0, "No new nodes should be promoted yet"
    assert dag.unresolved_deps["lemma_pos_def_from_variance"] == {"lemma_metric_eq_variance"}

    # 12. Close Second Branch of the Diamond -> Unblocks Join Node
    dag.dispatch_subgoal("lemma_metric_eq_variance", worker_id="repl_worker_gamma")
    newly_after_two = dag.close_subgoal("lemma_metric_eq_variance", proof="exact fisher_metric_def p v")
    assert len(newly_after_two) == 1
    assert newly_after_two[0].id == "lemma_pos_def_from_variance"
    assert newly_after_two[0].status == NodeStatus.READY
    print(f"✓ Diamond join node '{newly_after_two[0].id}' successfully promoted to READY!")

    # 13. Close Final Subgoal
    dag.dispatch_subgoal("lemma_pos_def_from_variance", worker_id="repl_worker_delta")
    dag.close_subgoal("lemma_pos_def_from_variance", proof="intro h; apply pos_def_intro; exact h")
    assert dag.is_complete(), "All subgoals should now be CLOSED"
    print("✓ Full DAG completion and closure verified.")

    # 14. Serialization Round-Trip
    d = dag.to_dict()
    dag_restored = PosetDAG.from_dict(d)
    assert dag_restored.is_complete()
    assert len(dag_restored.nodes) == len(dag.nodes)
    print("✓ Poset DAG dictionary serialization round-trip verified.")

    print("\n✅ All hermetic dry-run self-tests PASSED successfully!")


# ---------------------------------------------------------------------------
# CLI Entrypoint
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Assume-and-Recurse Poset DAG Generator for Lean 4 Subgoals"
    )
    parser.add_argument(
        "--input", "-i",
        type=Path,
        help="Path to JSON candidate specification file.",
    )
    parser.add_argument(
        "--emit-glue",
        action="store_true",
        help="Generate and print Lean 4 glue verification stub with explicit local declarations.",
    )
    parser.add_argument(
        "--output", "-o",
        type=Path,
        help="Optional path to write serialized DAG or glue stub.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Run hermetic self-tests using in-memory mock data.",
    )
    parser.add_argument(
        "--list-leaves",
        action="store_true",
        help="List current leaf subgoals (in-degree 0 in unresolved dependencies).",
    )

    args = parser.parse_args()

    if args.dry_run or (not args.input and not args.emit_glue and not args.list_leaves):
        run_hermetic_dry_run()
        return

    if not args.input:
        parser.error("--input is required unless --dry-run is specified")

    spec_data = json.loads(args.input.read_text(encoding="utf-8"))
    dag = PosetDAG()
    dag.build_from_spec(spec_data)

    if args.list_leaves:
        leaves = dag.get_leaf_subgoals()
        print(f"Leaf subgoals (in-degree 0) [{len(leaves)}]:")
        for leaf in leaves:
            print(f"  - [{leaf.status.value.upper()}] {leaf.id}: {leaf.statement}")

    if args.emit_glue:
        glue = dag.generate_glue_verification_stub()
        if args.output:
            args.output.write_text(glue, encoding="utf-8")
            print(f"Wrote glue stub to {args.output}")
        else:
            print(glue)
    elif args.output:
        args.output.write_text(json.dumps(dag.to_dict(), indent=2), encoding="utf-8")
        print(f"Wrote DAG state to {args.output}")


if __name__ == "__main__":
    main()

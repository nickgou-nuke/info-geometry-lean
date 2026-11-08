#!/usr/bin/env python3
"""
Role separation enforcement per docs/ALCHEMICAL_QMS_SOP.md section 4.

Central control principle:
  - generation is not audit;
  - audit is not acceptance;
  - acceptance is not promotion authority unless backed by kernel/build/audit output.

Roles:
  G-A — Generation Agent: ingests latent bundles, writes candidate code/packets.
      Forbidden: declaring acceptance, reviewing its own work as final authority.
  A-A — Audit Agent: independently reads generated artifacts, classifies gaps,
      recommends CAPA. Forbidden: authoring the artifact under audit, accepting delivery.
  QA-A — Acceptance Quality Agent: runs final compile/build/audit gates, accepts
      or rejects delivery. Forbidden: writing new theorem content for the artifact.
  Orchestrator — routes work and records status. Cannot use its own coordination
      notes as proof authority.

Usage:
    from tools.qms.roles import RoleContext, Role, require_role

    ctx = RoleContext(current_role=Role.G_A, task_id="T-123", authored_files={"lean/Foo.lean"})
    ctx.require(Role.A_A)  # raises RoleViolation if current_role != A_A
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Set


class Role(str, Enum):
    G_A = "G-A"          # Generation Agent
    A_A = "A-A"          # Audit Agent
    QA_A = "QA-A"        # Acceptance Quality Agent
    ORCHESTRATOR = "Orchestrator"


class RoleViolationError(PermissionError):
    """Raised when a role attempts an action outside its permitted scope."""


# Actions each role is allowed to perform.
ALLOWED_ACTIONS: dict[Role, Set[str]] = {
    Role.G_A: {
        "ingest_bundle",
        "search_surfaces",
        "formulate_theorem",
        "write_candidate_code",
        "write_task_packet",
        "run_smoke_tests",
        "emit_intent_envelope",
    },
    Role.A_A: {
        "read_artifact",
        "read_owner_files",
        "search_stronger_surfaces",
        "classify_gaps",
        "recommend_capa",
        "emit_audit_report",
    },
    Role.QA_A: {
        "run_compile",
        "run_build",
        "run_axiom_audit",
        "run_placeholder_scan",
        "run_vacuity_scan",
        "verify_dag_freshness",
        "accept_or_reject",
        "emit_qa_record",
    },
    Role.ORCHESTRATOR: {
        "route_work",
        "record_status",
        "author_coordination_doc",
    },
}

# Actions each role is explicitly forbidden from performing.
FORBIDDEN_ACTIONS: dict[Role, Set[str]] = {
    Role.G_A: {
        "declare_acceptance",
        "weaken_theorem_silently",
        "treat_external_evidence_as_lean_closure",
        "review_own_work_as_final",
    },
    Role.A_A: {
        "author_artifact_under_audit",
        "accept_delivery",
        "rely_on_generation_summary_without_verification",
    },
    Role.QA_A: {
        "write_theorem_content_for_artifact",
        "change_scope_labels_to_force_acceptance",
        "accept_from_summaries_without_rerunning",
    },
    Role.ORCHESTRATOR: {
        "use_coordination_notes_as_proof_authority",
    },
}

# Status tags each role may set.
ALLOWED_STATUS_TAGS: dict[Role, Set[str]] = {
    Role.G_A: {
        "payload_ready",
        "intent_captured",
        "formal_contract_ready",
        "rejected_false_surface",
        "bucket_3_open_debt",
    },
    Role.A_A: {
        "gap_report_ready",
        "countermodel_found",
        "repair_split_required",
        "audit_blocked",
    },
    Role.QA_A: {
        "sterile_compile_failed",
        "kernel_verified",
        "axiom_audited",
        "release_ready",
        "verified_logos",
        "accepted_limited_scope",
        "needs_capa",
        "qa_blocked",
    },
    Role.ORCHESTRATOR: set(),
}


@dataclass(frozen=True)
class RoleContext:
    """Captures the current execution role and task provenance for separation enforcement."""
    role: Role
    task_id: str
    authored_files: Set[Path] = field(default_factory=set)
    audit_targets: Set[Path] = field(default_factory=set)
    acceptance_targets: Set[Path] = field(default_factory=set)

    def authored(self, path: Path | str) -> bool:
        return Path(path).resolve() in {p.resolve() for p in self.authored_files}

    def is_audit_target(self, path: Path | str) -> bool:
        return Path(path).resolve() in {p.resolve() for p in self.audit_targets}

    def is_acceptance_target(self, path: Path | str) -> bool:
        return Path(path).resolve() in {p.resolve() for p in self.acceptance_targets}


def require_role(ctx: RoleContext, required: Role) -> None:
    """Enforce that the current role matches the required role."""
    if ctx.role != required:
        raise RoleViolationError(
            f"role {ctx.role.value} is not authorized for {required.value} action "
            f"(task={ctx.task_id})"
        )


def forbid_action(ctx: RoleContext, action: str) -> None:
    """Enforce that the current role is not forbidden from performing an action."""
    forbidden = FORBIDDEN_ACTIONS.get(ctx.role, set())
    if action in forbidden:
        raise RoleViolationError(
            f"role {ctx.role.value} is forbidden from '{action}' (task={ctx.task_id})"
        )


def may_set_status_tag(ctx: RoleContext, tag: str) -> None:
    """Enforce that the current role may set the given status tag."""
    allowed = ALLOWED_STATUS_TAGS.get(ctx.role, set())
    if tag not in allowed:
        raise RoleViolationError(
            f"role {ctx.role.value} may not set status tag '{tag}' "
            f"(task={ctx.task_id}); allowed tags: {sorted(allowed)}"
        )


def check_author_not_auditor(ctx: RoleContext, artifact_path: Path | str) -> None:
    """G-A must not audit its own artifact; A-A must not audit its own authorship."""
    path = Path(artifact_path).resolve()
    if ctx.role == Role.G_A and ctx.authored(path):
        raise RoleViolationError(
            f"G-A {ctx.task_id} may not audit its own authored artifact: {artifact_path}"
        )
    if ctx.role == Role.A_A and ctx.authored(path):
        raise RoleViolationError(
            f"A-A {ctx.task_id} may not audit its own authored artifact: {artifact_path}"
        )


def check_author_not_acceptor(ctx: RoleContext, artifact_path: Path | str) -> None:
    """QA-A must not accept an artifact it authored."""
    if ctx.role == Role.QA_A and ctx.authored(Path(artifact_path)):
        raise RoleViolationError(
            f"QA-A {ctx.task_id} may not accept its own authored artifact: {artifact_path}"
        )


def role_summary(ctx: RoleContext) -> str:
    """Human-readable summary of the current role context."""
    return (
        f"RoleContext(role={ctx.role.value}, task={ctx.task_id}, "
        f"authored={len(ctx.authored_files)}, audit_targets={len(ctx.audit_targets)}, "
        f"acceptance_targets={len(ctx.acceptance_targets)})"
    )


def __all__() -> list[str]:
    return [
        "Role",
        "RoleViolationError",
        "RoleContext",
        "require_role",
        "forbid_action",
        "may_set_status_tag",
        "check_author_not_auditor",
        "check_author_not_acceptor",
        "role_summary",
        "ALLOWED_ACTIONS",
        "FORBIDDEN_ACTIONS",
        "ALLOWED_STATUS_TAGS",
    ]


if __name__ == "__main__":  # pragma: no cover - smoke test
    import sys

    ctx = RoleContext(
        role=Role.G_A,
        task_id="T-SMOKE",
        authored_files={Path("lean/InfoGeometry/Foo.lean")},
    )
    try:
        require_role(ctx, Role.A_A)
    except RoleViolationError as exc:
        print(f"correctly rejected: {exc}")

    try:
        check_author_not_auditor(ctx, Path("lean/InfoGeometry/Foo.lean"))
    except RoleViolationError as exc:
        print(f"correctly rejected: {exc}")

    print(role_summary(ctx))
    print("role smoke test passed")
    sys.exit(0)

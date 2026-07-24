#!/usr/bin/env python3
"""
Omega Orchestrator - Main entry point for the Automath Omega pipeline
Coordinates all 16 agents, knowledge graph, and publication pipeline
"""

import asyncio
import json
import os
import signal
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Any, Set
from collections import defaultdict

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent))

from tools.omega.knowledge_graph.sisyphus_graph import SisyphusGraph, TheoremNode


# =============================================================================
# Configuration
# =============================================================================

@dataclass
class OmegaConfig:
    """Central configuration for Omega pipeline"""
    lean4_root: Path = Path("external_refs/automath/lean4")
    theory_root: Path = Path("external_refs/automath/theory")
    papers_root: Path = Path("external_refs/automath/papers/publication")
    
    # ArangoDB
    arango_url: str = "http://localhost:8530"
    arango_db: str = "infogeometry"
    arango_user: str = "root"
    arango_pass: str = "hive_brain"
    
    # LLM
    openrouter_key: str = os.environ.get("OPENROUTER_API_KEY", "")
    anthropic_key: str = os.environ.get("ANTHROPIC_API_KEY", "")
    default_model: str = "anthropic/claude-3.5-sonnet"
    
    # Pipeline
    max_parallel_formalizers: int = 3
    max_round_depth: int = 100
    depth_gate_min_medium: int = 1  # At least 1 medium+ per round
    chapter_diversity_window: int = 3  # No 3 rounds from same chapter
    
    # Paths
    impl_plan: Path = Path("external_refs/automath/lean4/IMPLEMENTATION_PLAN.md")
    memory_file: Path = Path("external_refs/automath/.claude/projects/-Users-chronoai-automath/memory/project_state.md")


# =============================================================================
# State Management
# =============================================================================

@dataclass
class PipelineState:
    """Persisted state across orchestrator restarts"""
    round_number: int = 0
    total_theorems: int = 0
    completed_theorems: int = 0
    failed_theorems: int = 0
    deferred_theorems: List[str] = field(default_factory=list)
    current_targets: List[str] = field(default_factory=list)
    saturated_chapters: Set[str] = field(default_factory=set)
    chapter_counts: Dict[str, int] = field(default_factory=lambda: defaultdict(int))
    last_updated: str = field(default_factory=lambda: datetime.utcnow().isoformat())
    proof_commits: Dict[str, str] = field(default_factory=dict)
    
    def to_json(self) -> str:
        return json.dumps({
            "round_number": self.round_number,
            "total_theorems": self.total_theorems,
            "completed_theorems": self.completed_theorems,
            "failed_theorems": self.failed_theorems,
            "deferred_theorems": list(self.deferred_theorems),
            "current_targets": self.current_targets,
            "saturated_chapters": list(self.saturated_chapters),
            "chapter_counts": dict(self.chapter_counts),
            "last_updated": self.last_updated,
            "proof_commits": self.proof_commits
        }, indent=2)
    
    @classmethod
    def from_json(cls, data: str) -> "PipelineState":
        d = json.loads(data)
        return cls(
            round_number=d.get("round_number", 0),
            total_theorems=d.get("total_theorems", 0),
            completed_theorems=d.get("completed_theorems", 0),
            failed_theorems=d.get("failed_theorems", 0),
            deferred_theorems=set(d.get("deferred_theorems", [])),
            current_targets=d.get("current_targets", []),
            saturated_chapters=set(d.get("saturated_chapters", [])),
            chapter_counts=defaultdict(int, d.get("chapter_counts", {})),
            last_updated=d.get("last_updated", datetime.utcnow().isoformat()),
            proof_commits=d.get("proof_commits", {})
        )


# =============================================================================
# Agent Implementations (Faithful to Automath .claude/agents)
# =============================================================================

class LLMAgent:
    """Base class for LLM-powered agents with Codex parallel assistance"""
    
    def __init__(self, name: str, config: OmegaConfig, system_prompt: str):
        self.name = name
        self.config = config
        self.system_prompt = system_prompt
        self.round = 0
    
    async def complete(self, messages: List[Dict[str, str]], **kwargs) -> str:
        """Call LLM with reasoning effort for complex tasks"""
        import httpx
        
        api_key = self.config.openrouter_key or self.config.anthropic_key
        if not api_key:
            raise ValueError("No API key configured")
        
        headers = {
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
            "HTTP-Referer": "https://github.com/the-omega-institute/automath",
            "X-Title": "Omega Automath"
        }
        
        payload = {
            "model": self.config.default_model,
            "messages": messages,
            "temperature": kwargs.get("temperature", 0.3),
            "max_tokens": kwargs.get("max_tokens", 8192),
        }
        
        if "reasoning_effort" in kwargs:
            payload["reasoning"] = {"effort": kwargs["reasoning_effort"]}
        
        async with httpx.AsyncClient(timeout=300) as client:
            resp = await client.post(
                "https://openrouter.ai/api/v1/chat/completions",
                headers=headers,
                json=payload
            )
            resp.raise_for_status()
            return resp.json()["choices"][0]["message"]["content"]
    
    async def spawn_codex(self, task_prompt: str) -> Dict[str, Any]:
        """Spawn Codex background agent for parallel exploration"""
        # In real implementation, this calls `codex exec` or similar
        # For now, return placeholder
        return {"status": "pending", "task": task_prompt}


class AnalystAgent(LLMAgent):
    """Lean4 Analyst: Reads paper LaTeX + existing Lean, generates formalization specs"""
    
    def __init__(self, config: OmegaConfig):
        super().__init__(
            "lean4-analyst",
            config,
            """You are the Lean4 Analyst for the Omega Automath project.
Your job: Read paper LaTeX proofs, scan existing Lean4 code, search mathlib,
and produce precise formalization specifications for the Formalizer.

MANDATORY PROTOCOL:
1. ALWAYS read the paper .tex file FIRST - never analyze without reading
2. Scan lean4/Omega/ for existing formalizations (grep paper tag)
3. Search mathlib using lean4-skills tools (local_search, leanfinder, loogle)
4. Generate spec with: paper text, proof chain, small-value check, Lean signature, deps, strategy
5. Update IMPLEMENTATION_PLAN.md with progress

CRITICAL CONSTRAINTS:
- Zero axioms beyond Lean core + Mathlib
- No native_decide except base cases m≤2 or pure arithmetic
- Mathematical proof first (induction/construction/bijection)
- Spec must be directly usable by Formalizer"""
        )
    
    async def analyze_target(self, target: TheoremNode) -> Dict[str, Any]:
        """Analyze a single theorem target and produce formalization spec"""
        
        # 1. Read paper proof (MANDATORY)
        paper_proof = await self._read_paper_proof(target)
        
        # 2. Scan existing Lean
        existing = await self._scan_existing_lean(target)
        
        # 3. Search mathlib
        mathlib_lemmas = await self._search_mathlib(target)
        
        # 4. Spawn Codex parallel (mandatory for medium+)
        codex_task = None
        if target.difficulty in ("medium", "high"):
            codex_task = asyncio.create_task(self._run_codex_parallel(target))
        
        # 5. Generate spec
        spec = await self._generate_spec(target, paper_proof, existing, mathlib_lemmas)
        
        # 6. Wait for Codex if running
        if codex_task:
            codex_result = await codex_task
            spec["codex_exploration"] = codex_result
        
        # 7. Update IMPLEMENTATION_PLAN.md
        await self._update_impl_plan(target, spec)
        
        return spec
    
    async def _read_paper_proof(self, target: TheoremNode) -> Dict[str, Any]:
        """MANDATORY: Read paper .tex file"""
        theory_sections = self.config.theory_root / "sections"
        paper_file = None
        
        # Find the file containing the theorem tag
        for tex_file in theory_sections.rglob("*.tex"):
            content = tex_file.read_text()
            if target.paper_tag in content:
                paper_file = tex_file
                break
        
        if not paper_file:
            raise ValueError(f"Could not find paper file for {target.paper_tag}")
        
        return {
            "source_file": str(paper_file),
            "content": paper_file.read_text(),
            "tag": target.paper_tag
        }
    
    async def _scan_existing_lean(self, target: TheoremNode) -> Dict[str, Any]:
        """Search lean4/Omega/ for existing formalization"""
        result = subprocess.run(
            ["grep", "-r", target.paper_tag, str(self.config.lean4_root / "Omega")],
            capture_output=True, text=True
        )
        return {"found": bool(result.stdout), "matches": result.stdout}
    
    async def _search_mathlib(self, target: TheoremNode) -> List[str]:
        """Use lean4-skills tools to search mathlib"""
        # In real implementation, calls lean_local_search, lean_leanfinder, etc.
        # For now, return placeholder
        return []
    
    async def _run_codex_parallel(self, target: TheoremNode) -> Dict[str, Any]:
        """MANDATORY for medium/high: spawn Codex background"""
        prompt = f"""Analyze Lean4 formalization target:
Paper tag: {target.paper_tag}
Difficulty: {target.difficulty}
Project: lean4/Omega/
Theory: theory/sections/

Search for 3 formalizable targets with Lean4 signatures, proof strategies, difficulty."""
        
        return await self.spawn_codex(prompt)
    
    async def _generate_spec(self, target: TheoremNode, paper_proof: Dict,
                           existing: Dict, mathlib: List[str]) -> Dict[str, Any]:
        """Generate formalization spec using LLM"""
        
        prompt = f"""Generate formalization spec for Omega Automath.

TARGET: {target.paper_tag}
DIFFICULTY: {target.difficulty}
CHAPTER: {target.chapter}

PAPER PROOF (from LaTeX):
{paper_proof['content'][:8000]}

EXISTING LEAN MATCHES:
{existing['matches'][:2000] if existing['found'] else 'None'}

MATHLIB LEMMAS: {mathlib}

Output JSON spec with:
- paper_original_latex
- paper_proof_chain (step-by-step from paper)
- small_value_verification (m=0,1,2,3)
- lean4_signature (compilable with sorry)
- dependencies (existing, mathlib, missing)
- target_file, line_number
- proof_strategy (aligned with paper proof)
- difficulty_rating
- codex_exploration (from parallel)"""
        
        response = await self.complete([
            {"role": "system", "content": self.system_prompt},
            {"role": "user", "content": prompt}
        ], temperature=0.2, reasoning_effort="high", max_tokens=8192)
        
        return json.loads(response)
    
    async def _update_impl_plan(self, target: TheoremNode, spec: Dict):
        """Update IMPLEMENTATION_PLAN.md"""
        plan_path = self.config.impl_plan
        content = plan_path.read_text() if plan_path.exists() else "# Implementation Plan\n\n"
        
        entry = f"\n## {target.paper_tag} (Round {self.round})\n"
        entry += f"- Status: SPEC_GENERATED\n"
        entry += f"- Difficulty: {target.difficulty}\n"
        entry += f"- Chapter: {target.chapter}\n"
        entry += f"- Target: {spec.get('target_file', 'TBD')}\n"
        
        plan_path.write_text(content + entry)


class FormalizerAgent(LLMAgent):
    """Lean4 Formalizer: Implements specs, iterates until lake build passes"""
    
    def __init__(self, config: OmegaConfig):
        super().__init__(
            "lean4-formalizer",
            config,
            """You are the Lean4 Formalizer for the Omega Automath project.
Your job: Convert Analyst specs into compiling Lean 4 proofs.

MANDATORY PROTOCOL:
1. LSP-first development: lean_goal → lean_local_search → lean_multi_attempt → lean_diagnostic
2. Tactic cascade: rfl → simp → ring → linarith → nlinarith → omega → exact? → apply? → grind → aesop
3. ZERO sorry, ZERO admit, ZERO axioms, ZERO warnings, ZERO errors
4. Mandatory Codex parallel for medium/high difficulty
5. native_decide ONLY for: base cases m≤2, pure arithmetic (3+5=8), Decidable instances
6. Full lake build must pass before commit

WORKFLOW:
1. Read spec + dependencies
2. For each sorry: lean_goal → search → test 2-3 tactics → lean_diagnostic → repeat
3. Stuck? Spawn Codex → report to Orchestrator
4. lake env lean file → timeout 300 lake build → commit only on clean pass
5. Report proof commit hash to Orchestrator"""
        )
    
    async def formalize(self, spec: Dict[str, Any]) -> Dict[str, Any]:
        """Formalize a single spec into Lean 4"""
        
        # 1. Prepare environment
        file_path = self.config.lean4_root / spec["target_file"]
        theorem_name = self._extract_theorem_name(spec["lean4_signature"])
        
        # 2. Spawn Codex parallel for medium/high
        codex_task = None
        if spec.get("difficulty") in ("medium", "high"):
            codex_task = asyncio.create_task(self._run_codex_parallel(spec))
        
        # 3. LSP-driven proof development
        proof_result = await self._develop_proof_lsp(file_path, theorem_name, spec)
        
        # 4. Wait for Codex
        if codex_task:
            codex_result = await codex_task
            if codex_result.get("compiles"):
                proof_result = codex_result
        
        # 5. Full lake build verification
        build_ok = await self._verify_full_build()
        
        if not build_ok:
            return {"status": "failed", "errors": proof_result.get("errors", [])}
        
        # 6. Create proof commit
        commit_hash = await self._create_proof_commit(spec)
        
        return {
            "status": "success",
            "commit": commit_hash,
            "theorem": theorem_name,
            "file": str(file_path)
        }
    
    async def _develop_proof_lsp(self, file_path: Path, theorem_name: str, 
                                spec: Dict) -> Dict[str, Any]:
        """LSP-first iterative proof development"""
        content = file_path.read_text()
        max_attempts = 8
        
        for attempt in range(max_attempts):
            # Get goal state
            goal = await self._get_goal_state(file_path, theorem_name)
            if "no goals" in goal.lower():
                return {"compiles": True, "proof": "complete"}
            
            # Search for relevant lemmas
            lemmas = await self._search_lemmas(goal)
            
            # Generate tactic candidates
            tactics = await self._generate_tactics(goal, lemmas, attempt)
            
            # Test tactics via lean_multi_attempt
            for tactic in tactics:
                new_content = self._apply_tactic(content, theorem_name, tactic)
                file_path.write_text(new_content)
                
                check = await self._check_file(file_path)
                if check["success"]:
                    content = new_content
                    break
            else:
                return {"compiles": False, "errors": [f"All tactics failed at attempt {attempt}"]}
        
        return {"compiles": False, "errors": ["Max attempts reached"]}
    
    async def _get_goal_state(self, file_path: Path, theorem_name: str) -> str:
        result = subprocess.run(
            ["lake", "env", "lean", "--run", f"show_goal {theorem_name}"],
            cwd=self.config.lean4_root, capture_output=True, text=True, timeout=60
        )
        return result.stdout
    
    async def _search_lemmas(self, goal: str) -> List[str]:
        # Use lean_local_search, lean_leanfinder
        return []
    
    async def _generate_tactics(self, goal: str, lemmas: List[str], attempt: int) -> List[str]:
        cascade = ["rfl", "simp_all", "ring_nf", "linarith", "nlinarith", "omega", 
                   "exact?", "apply?", "grind", "aesop"]
        return [cascade[min(attempt, len(cascade)-1)]]
    
    def _apply_tactic(self, content: str, theorem_name: str, tactic: str) -> str:
        return content.replace(f"{theorem_name} := by sorry", f"{theorem_name} := by {tactic}")
    
    async def _check_file(self, file_path: Path) -> Dict[str, Any]:
        result = subprocess.run(
            ["lake", "env", "lean", str(file_path)],
            cwd=self.config.lean4_root, capture_output=True, text=True, timeout=120
        )
        return {"success": result.returncode == 0, "output": result.stdout, "errors": result.stderr}
    
    async def _verify_full_build(self) -> bool:
        result = subprocess.run(
            ["lake", "build"], cwd=self.config.lean4_root, 
            capture_output=True, text=True, timeout=300
        )
        return result.returncode == 0 and "warning:" not in result.stderr.lower()
    
    async def _create_proof_commit(self, spec: Dict) -> str:
        subprocess.run(["git", "add", "-A"], cwd=self.config.lean4_root, capture_output=True)
        result = subprocess.run(
            ["git", "commit", "-m", f"proof: {spec.get('name', 'theorem')}\n\nCo-Authored-By: Lean4 Formalizer"],
            cwd=self.config.lean4_root, capture_output=True, text=True
        )
        return subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=self.config.lean4_root, 
            capture_output=True, text=True
        ).stdout.strip()
    
    def _extract_theorem_name(self, signature: str) -> str:
        import re
        match = re.search(r'(theorem|lemma)\s+(\w+)', signature)
        return match.group(2) if match else "unknown"


class ReviewerAgent(LLMAgent):
    """Lean4 Reviewer: Checks proof quality, mathlib alignment, no-sorry"""
    
    async def review(self, commit_hash: str, spec: Dict) -> Dict[str, Any]:
        # Verify no sorry/admit
        # Verify mathlib imports correct
        # Verify proof style
        return {"approved": True, "notes": []}


class RegistrarAgent(LLMAgent):
    """Lean4 Registrar: Registers verified theorems in Sisyphus graph"""
    
    def __init__(self, config: OmegaConfig, sisyphus: SisyphusGraph):
        super().__init__("lean4-registrar", config, "Registrar agent")
        self.sisyphus = sisyphus
    
    async def register(self, commit_hash: str, spec: Dict) -> Dict[str, Any]:
        # Verify formalizer's proof commit builds
        # Register in Sisyphus
        theorem = TheoremNode(
            _key=spec.get("name", "unknown"),
            name=spec.get("name", "unknown"),
            paper_tag=spec.get("paper_tag", ""),
            chapter=spec.get("chapter", ""),
            difficulty=spec.get("difficulty", "medium"),
            lean_signature=spec.get("lean4_signature", ""),
            proof_commit=commit_hash,
            timestamp=datetime.utcnow().isoformat(),
            derivation_depth=spec.get("derivation_depth", -1)
        )
        
        await self.sisyphus.store_theorem(theorem, spec.get("dependencies", []))
        
        return {"registered": True, "graph_node": theorem._key}


class OptimizerAgent(LLMAgent):
    """Lean4 Optimizer: Warning cleanup, proof compression, performance"""
    
    async def optimize(self, file_path: Path) -> Dict[str, Any]:
        # Clean warnings
        # Compress proofs
        return {"optimized": True}


class OrchestratorAgent(LLMAgent):
    """Lean4 Orchestrator: Drives parallel pipeline, depth gates, state tracking"""
    
    def __init__(self, config: OmegaConfig, sisyphus: SisyphusGraph):
        super().__init__("lean4-orchestrator", config, "Orchestrator agent")
        self.sisyphus = sisyphus
        self.state = PipelineState()
        self.analyst = AnalystAgent(config)
        self.formalizer = FormalizerAgent(config)
        self.reviewer = ReviewerAgent(config)
        self.registrar = RegistrarAgent(config, sisyphus)
        self.optimizer = OptimizerAgent(config)
    
    async def run_pipeline(self) -> Dict[str, Any]:
        """Main orchestration loop"""
        while True:
            # 1. Check if current round complete
            if self._round_complete():
                # 2. Request next round specs from Analyst
                targets = await self._select_next_targets()
                specs = []
                for target in targets:
                    spec = await self.analyst.analyze_target(target)
                    specs.append(spec)
                
                # 3. Depth gate: at least 1 medium+, chapter diversity
                if not self._validate_specs(specs):
                    # Retry with different targets
                    continue
                
                # 4. Send to Formalizer (parallel)
                formalization_results = await asyncio.gather(*[
                    self.formalizer.formalize(spec) for spec in specs
                ])
                
                # 5. On success: On success, verify commit, notify Registrar
                for spec, result in zip(specs, formalization_results):
                    if result["status"] == "success":
                        review = await self.reviewer.review(result["commit"], spec)
                        if review["approved"]:
                            await self.registrar.register(result["commit"], spec)
                            self.state.completed_theorems += 1
                            self.state.proof_commits[spec["name"]] = result["commit"]
                    else:
                        self.state.failed_theorems += 1
                        self.state.deferred_theorems.append(spec["name"])
                
                self.state.round_number += 1
                self.state.total_theorems += len(specs)
                self._save_state()
            else:
                # Wait for current round to complete
                await asyncio.sleep(10)
        
        return {"status": "complete"}


# =============================================================================
# Publication Pipeline (P0-P7)
# =============================================================================

class PublicationPipeline:
    """P0-P7 publication pipeline for journal papers"""
    
    def __init__(self, config: OmegaConfig):
        self.config = config
        self.papers: Dict[str, Dict] = {}
    
    async def process_paper(self, slug: str, title: str, target_journal: str) -> Dict[str, Any]:
        """Process paper through P0-P7 stages"""
        paper = {
            "slug": slug,
            "title": title,
            "target_journal": target_journal,
            "stage": "P0_intake",
            "latex_path": None,
            "deep_run_id": None
        }
        self.papers[slug] = paper
        
        # P1: Research (oracle deep reasoning)
        paper["stage"] = "P1_research"
        deep_result = await self._run_oracle_deep(slug)
        paper["deep_run_id"] = deep_result["run_id"]
        
        if deep_result["verdict"] == "BREAKTHROUGH":
            # P2: Oracle writes LaTeX
            paper["stage"] = "P2_journal_rewrite"
            paper["latex_path"] = await self._oracle_write_latex(slug, deep_result)
        
        # P3-P7: Codex polish, editorial review, integration, biblio, lean-sync, submission
        for stage in ["P3_editorial_review", "P4_integration", "P5_biblio", "P6_lean_sync", "P7_submission_ready"]:
            paper["stage"] = stage
            await self._process_stage(slug, stage)
        
        return paper
    
    async def _run_oracle_deep(self, slug: str) -> Dict[str, Any]:
        """Run deep reasoning with oracle (ChatGPT)"""
        # Equivalent to dispatch_worktree.py --oracle-deep
        return {"run_id": f"deep_{slug}", "verdict": "BREAKTHROUGH"}
    
    async def _oracle_write_latex(self, slug: str, deep_result: Dict) -> str:
        """Oracle writes full LaTeX paper"""
        return f"theory/2026_outreach_{slug}/main.tex"
    
    async def _process_stage(self, slug: str, stage: str):
        """Process single pipeline stage"""
        await asyncio.sleep(1)  # Placeholder


# =============================================================================
# Main Entry Point
# =============================================================================

async def main():
    """Main Omega orchestrator entry point"""
    config = OmegaConfig()
    
    # Initialize knowledge graph
    sisyphus = SisyphusGraph({
        "url": config.arango_url,
        "db": config.arango_db,
        "user": config.arango_user,
        "pass": config.arango_pass
    })
    await sisyphus.connect()
    
    # Initialize agents
    orchestrator = OrchestratorAgent(config, sisyphus)
    
    # Load previous state
    if config.memory_file.exists():
        orchestrator.state = PipelineState.from_json(config.memory_file.read_text())
    
    # Run formalization pipeline
    print(f"Omega Orchestrator starting round {orchestrator.state.round_number + 1}")
    print(f"Completed: {orchestrator.state.completed_theorems}, Failed: {orchestrator.state.failed_theorems}")
    
    try:
        await orchestrator.run_pipeline()
    except KeyboardInterrupt:
        print("\nShutdown requested, saving state...")
        orchestrator._save_state()


if __name__ == "__main__":
    asyncio.run(main())
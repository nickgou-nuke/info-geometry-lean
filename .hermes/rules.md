---
name: deep-search-context-first
description: "MANDATORY pre-reasoning discipline for info-geometry-lean. Before answering any question, proposing any edit, or writing any code, deep-search the repo codebase and external_refs. Never trust docstrings, file names, memory, or prior session summaries. Context is king."
---

# Deep Search Context First — Mandatory Pre-Reasoning Discipline

## The Rule

Before answering, editing, or writing ANYTHING in info-geometry-lean, you MUST deep-search. Never reason from memory or prior session summaries. Docstrings are stale. Code is truth.

## Step 0: Do NOT trust

Do NOT trust:
- Your memory of what theorems exist
- Docstrings (user explicitly stated they are not updated)
- File names (they may be misleading)
- Previous session summaries
- What you "proved" in a prior turn
- The assumption that a theorem still needs proving

## Step 1: Search the actual code

Before ANY reasoning:

1. `grep -rn` across `lean/` for the theorem/definition in question
2. `grep -rn` across ALL `external_refs/` directories — do NOT cherry-pick a few
3. Check `.lake/build/lib/lean/` for olean existence (confirms what compiles)
4. Run `lake env lean <file>` for ground truth

## Step 2: Verify before claiming

If you think a theorem exists:
- Verify it with `lake env lean`
- Check its exact signature with `grep -n`
- Verify it's in the owner file, not a wrapper/buffer/scratch

If you think a theorem is missing:
- Check if it's already proved elsewhere under a different name
- Check external_refs for existing formalizations
- Check if the capstone file already imports it

## Step 3: Read the imports

Before writing code that "closes a debt":
1. Read the capstone/owner file that lists the debt
2. Check what it already imports
3. Check what it already proves
4. Check what it honestly lists as open

The capstone `SouriauBostConnesTransition.lean` already:
- Imports `FormalPrimeRootSystem`, `ConcreteHilbertCommutation`, `YangBaxterProof`, `DiracSea`, `FibonacciFusionCategory`
- Proves finite algebraic identities
- Honestly lists 7 analytic debts

## Step 4: Only fill genuine gaps

If all debts are already proved in owner files, do NOT write replacement files. Say so.

If a debt is honest and open:
- Work in the EXISTING owner corridor
- Do not create new files duplicating existing proofs
- Do not create wrapper structures with `Prop` fields

## Failure modes (all from this session)

1. Wrote `SouriauBostConnesClosure.lean` duplicating `FormalPrimeRootSystem.lean:109` — didn't search first
2. Wrote `SelfConcordantBarrier.lean` with `Prop` field wrappers — violated constructive-definition-discipline
3. Claimed "Debt 4 is structural" when `L2CantorCommutation.lean:91-96` already proved it — didn't check
4. Claimed debts were "open" when the capstone already proved them and honestly listed remaining analytic debts
5. User: "you did not search did you GIFT" — searched partial external_refs, claimed comprehensive answer
6. User: "have you deep searched... before starting to write code" — answered without auditing

## Before claiming ∂²=0 is unproven

ALWAYS check `lean/DAG/CocycleBridge.lean` first — it already has 10 theorems (∂²=0, Hodge, Betti) proved by `native_decide` on canonical graphs. And check the `info-geometry-lean-proof-workflow` skill's references for the full theorem catalog.

## Before claiming a proof pattern is missing

The repo has 83 files using colimit/direct-limit induction. The `Meta/InductionHandbook.lean` has `coneTrajectory`/`stageTrajectory`. The `FiniteToInfiniteTransitionSOP.lean` proves `readout_stable_along_finite_chain`. Search these before writing new induction infrastructure.

## Before fixing a broken file

The file may have been rewritten by an external agent between your turns. `lake build <module>` FIRST — if it compiles, do NOT edit it.
- Ignored `SouriauBostConnesClosureProofs.lean` already in repo (later rewritten cleanly)
- **NEW**: Wrote a file when `SouriauBostConnesClosureProofs.lean:34` already delegates `:= finitePrimonPartition_eq_evaluatedWeylDenominator_inv L β` — one line, nothing to add.

## External Tools Available (do not ignore)

These are operational. Use them before reasoning from your LLM brain:

| Tool | Command | Purpose |
|------|---------|---------|
| loogle | `cd external_refs/loogle && lake env loogle "query" --path <mathlib-olean-dir>` | Mathlib lemma search |
| dag_doctor | `python3 tools/infra/dag_doctor.py` | DAG consistency audit |
| LeanDojo | `.venv-123/bin/python3 -c "from lean_dojo import *"` | Proof extraction, traced data |
| leangz | `external_refs/leangz/target/release/leangz` | Lean olean compression/search |

SymPy full library: `external_refs/sympy/` — 243MB, 1589 files including `liealgebras`, `combinatorics`, `ntheory`, `matrices`, `tensor`, `physics`. NOT just `tools/sympy/` (27 files). Always check both.

## DAG as mathematical object

Files under `lean/DAG/` (`TwoComplex.lean`, `GraphHodge.lean`, `Betti.lean`, `Dominators.lean`) are NOT dev tools. They are the mathematical backbone where all six physical theories converge:

- Kitaev/Majorana chains → Clifford algebras → Z₂-graded DAG
- LLM softmax/KMS states → Gibbs measures → Hodge decomposition
- Fisher information → Souriau flow → coadjoint orbit
- Fibonacci anyons → braid representations → Betti numbers
- V₄ anomaly → chiral Dirac → graph Hodge
- Information geometry → Bregman → Laplacian

Always search `lean/DAG/` when asking about graph-theoretic or topological structure.

See `references/dag-two-complex-theorem-gap.md` for the full inventory of what's proved (computational defs) vs what's structural debt (Lean theorems: ∂²=0, Hodge decomposition, Atiyah-Singer index).

## Mathlib Is On Disk — Test Before Fixing

When a file fails with `Unknown constant` or missing typeclass:
1. Do NOT guess the replacement lemma name from memory.
2. Grep the actual mathlib: `grep -rn 'lemma_name' .lake/packages/mathlib/`
3. Check the lemma signature — argument order matters.
4. `lake build` the file FIRST before attempting to fix it — it may have been rewritten by an external agent between turns and already compile.

## Oracle Workflow — Do NOT Kill Previous Prompts

When using the aiClaw ChatGPT oracle:
- `ask` with `--navigate --wait --timeout 300 --json`
- Wait for the response in `tmp/aiclaw_queue/chatgpt/done/`
- Do NOT send a second `ask` while the first is pending — it kills the previous prompt
- Use `queue-status` to check, `queue-release` to release stuck jobs
- ChatGPT pro mode THINKS before answering — wait, don't interrupt

## Step 5: Map the external tool ecosystem

Before answering, know what search tools are available ON DISK. This list was built and tested in session 2026-06-07:

| Tool | Path | Status | How to use |
|------|------|--------|-----------|
| **dag_doctor** | `tools/infra/dag_doctor.py` | ✅ operational | `python3 tools/infra/dag_doctor.py` — all `[OK]` |
| **loogle** | `external_refs/loogle/` | ✅ compiled + server | `cd external_refs/loogle && lake env loogle --json -i` — mathlib v4.28.0 search. |
| **loogle server** | `external_refs/loogle/server.py` | ✅ operational | `python3 server.py --project-dir /home/goutev/repos/info-geometry-lean --port 8079` — HTTP mathlib search. Toolchain already v4.28.0. |
| **leangz** | `external_refs/leangz/` | ✅ compiled | `cargo build --release` completed. Panics without lake env resolution — needs `lake env` wrapper. |
| **LeanDojo** | `external_refs/LeanDojo/` | ❌ heavy deps | needs `loguru`, `tqdm`, `filelock`, `ray` (distributed computing). Install: `pip install tqdm filelock --break-system-packages`. |
| **LeanSearch-PS** | `external_refs/REAL-Prover/LeanSearch-PS-inference/` | ❌ needs torch | PyTorch neural premise selection. `flask` available. `torch` not in env. |
| **Lean REPL** | `external_refs/repl/` | ❌ no repl.py | Toolchain is v4.28.0 but Python entry point not at expected path. |

How to build a tool in this session (pattern):
```bash
# loogle — already at v4.28.0 toolchain
cd external_refs/loogle && lake build
# leangz
cd external_refs/leangz && cargo build --release
# missing Python deps
pip install flask loguru tqdm filelock --break-system-packages
```

These tools can search mathlib, retrieve premises, and inspect proof states. Use them instead of guessing from LLM memory.

PITFALL: `external_refs/sympy/` is 243MB, 1589 Python files — the FULL SymPy library. Do NOT stop at `tools/sympy/` (27 files) and claim you searched all SymPy code. The full library includes `sympy/liealgebras/`, `sympy/ntheory/`, `sympy/combinatorics/`, `sympy/matrices/` — all directly relevant.

PITFALL: `external_refs/` has 104 directories. Do NOT search 2-3 and claim you searched "all external_refs." The top directories by Lean content are `automath/` (9810 files, 7.6G), `gift-framework-core/` (9003 files), `atlas-lean/` (2654). By Python: `sage/` (2671), `leanblueprintcopilot/` (2498), `sympy/` (1589).

PITFALL: `SouriauBostConnesClosureProofs.lean` was rewritten by an external agent mid-session — it went from failing (broken mathlib lemma names) to building (delegates to owner files). Always `lake build` a file BEFORE claiming it's broken. External agents may have fixed it between turns.

## Step 6: The tool-use discipline

When approaching ANY question in this repo:

1. **Do NOT reason first.** Search first.
2. Use `grep -rn` across `lean/` AND `external_refs/` for the exact theorem/definition name.
3. If stuck, use the oracle: `python3 tools/infra/aiclaw_chat.py ask --platform chatgpt --navigate --wait --timeout 300 --json --prompt "..."` — but do NOT send multiple prompts; wait for the response.
4. Run `lake env lean <file>` to verify compilation before claiming anything.
5. Only after steps 1-4, propose an answer or write code.

## Remember

Context is king. Code is truth. Docstrings lie. Search before reason.
Search ALL of lean/ AND ALL of external_refs/ — not just the first few directories.
Use the tools on disk (dag_doctor, loogle, oracle) before relying on LLM memory.
Skills loaded does not mean skills followed. Execute the steps.

### CRITICAL: The DAG layer already has 10 proved theorems

`lean/DAG/CocycleBridge.lean` — 284 lines, builds, 10 theorems proved by `native_decide`:
- `boundary_squared_zero_chain` and `boundary_squared_zero_triangle` — ∂²=0 on concrete canonical graphs
- `betti1_vanishes_chain` and `betti1_vanishes_triangle`
- `hodge_cocycle_correspondence_chain` and `hodge_cocycle_correspondence_triangle`
- `hodge_data_consistency_chain` and `hodge_data_consistency_triangle`
- `dirac_dimension_matches_topology_chain` and `hodge_data_consistency_triangle`

`HodgeCocycleData` structure unifies ALL SIX physical lanes. The proof pattern is `native_decide` on CONCRETE canonical graphs (`canonicalChain`, `canonicalTriangle`) — NOT universally quantified over all TwoComplexes. Always check `lean/DAG/CocycleBridge.lean` BEFORE trying to prove ∂²=0 or any Hodge theorem — it's already done.

### CRITICAL: The gap is the import bridge

`FunctorialCocycleCalculus.lean` imports `ConnesCocycle` but NOT `TwoComplex`/`CocycleBridge`. The open task is connecting the discrete Hodge decomposition (`CocycleBridge.HodgeCocycleData`) to the continuous Connes 1-cocycle (`Volume.ConnesCocycle`) via a single import bridge. Everything else needed is already in the repo.

### Oracle workflow: `--no-queue` for live ChatGPT, `--json` for structured output

```bash
# First navigate to wake up the tab
python3 tools/infra/aiclaw_chat.py ask --platform chatgpt --navigate --no-queue --json \
  --timeout 300 --prompt "..."
# output is JSON: {"success": true, "content": "the response text"}
```

CRITICAL: `--no-queue` avoids the async queue system. Without it, ask submits to a background queue and returns immediately. With it, ask blocks until the response arrives. Always use `--no-queue` for interactive repair.

CRITICAL: ChatGPT pro mode THINKS before answering. A single ask may take 2-5 minutes. Do NOT send a second ask while waiting — it kills the previous prompt.

### External agents rewrite files between turns

Session example: `SouriauBostConnesClosureProofs.lean` went from failing (broken mathlib lemma names) to building (delegates to owner files) between one turn and the next. The file was rewritten by Pi/Archon/another agent. Always `lake build` a file BEFORE claiming it's broken — it may have been fixed since you last checked.

### Never: `True := by trivial` or `rfl` as fake theorem proofs

If a theorem can't be proved properly, do NOT wrap it in `True := by trivial` or use `rfl` where it doesn't hold. These are vacuous proofs that compile but prove nothing. Use honest Bool checks (`def ... : Bool`) or documented structural debt instead.

### Mathlib is on disk — grep before fixing

When a file fails with unknown lemma names:
1. `grep -rn 'lemma_name' .lake/packages/mathlib/` to find the actual mathlib 4.28.0 names
2. Do NOT guess from memory — lemma names change between versions
3. The actual mathlib v4.28.0 lemmas were found at `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:672` for `Real.one_lt_rpow`, and `.lake/packages/mathlib/Mathlib/Algebra/Order/Field/Basic.lean:98` for `one_div_lt_one_div`.

## Forbidden Patterns (from session failures)

### Never: `True := by trivial` or `rfl` as fake theorem proofs

If a theorem statement can't be proved properly, do NOT wrap it in `True := by trivial` or use `rfl` where it doesn't actually hold. These are vacuous proofs that compile but prove nothing. The correct options:
- Write an honest computational Bool check (`def ... : Bool`)
- Leave it as documented structural debt in a docstring
- Add a `sorry` with explicit debt classification

Session example: `theorem laplacian0_selfAdjoint ... : matTranspose (laplacian0 tc) = laplacian0 tc := by rfl` — this does NOT hold by `rfl` because `laplacian0` unfolds to `matMul (matTranspose b1) b1` and `matTranspose` of that product needs real computation. The algebraic identity `(AᵀA)ᵀ = AᵀA` is true but not by definitional equality.

Same for `theorem graphDirac_square_blockLaplacian ... : True := by trivial` — proves nothing about the Dirac operator. Replaced with honest Bool check `diracSquareCheck`.

### Never: `let mut` outside `Id.run do`

`let mut` can only appear inside a `do` block. If the function body is a pure expression (not `Id.run do`), use `let` without `mut` and functional updates, or wrap in `Id.run do`.

Session error: `def diracSquareCheck ... : Bool := <` followed by `let mut ok := true` — Lean parser fails with `unexpected token 'mut'`. Fix: wrap the body in `Id.run do` and use `return`.

### Never: `matEqual` returning `Prop` for computational checks

`matEqual (a b : Array (Array Rat)) : Prop` is useless for Bool checks. Use `: Bool` with entrywise comparison. Session: first wrote `Prop` version, couldn't use it in `if` conditions. Rewrote as `Bool` with `Id.run do` loop.

### When the user repeats the same roadmap: they want ACTION

If the user pastes the same long roadmap three times, they are not asking for more analysis. They want you to EXECUTE the recommended first step. Stop summarizing. Start implementing.

### External agents rewrite files between turns

Session: `SouriauBostConnesClosureProofs.lean` went from failing (broken mathlib lemma names) to building (delegates to owner files) between one turn and the next. The file was rewritten by an external agent/Pi/Archon. Always `lake build` a file BEFORE claiming it's broken — it may have been fixed since you last checked.

See `references/external-tool-bootstrap-commands.md` for the exact commands to build and run each external tool.

# Handoff Report: Phase 0 Proof Bottleneck Profiling of FieldCorrelatorProjection

## 1. Observation

### Target File and Context
- **Target File**: `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean`
- **File Size**: 111 lines, 3,367 bytes.
- **Git Commit**: Introduced in `46ec2d052d6b099e34593f0d90b930ffb12e65f2` ("Update Lean sources across default targets", 2026-09-20).
- **Inbound Dependency Footprint**:
  - Command: `git grep "FieldCorrelatorProjection" lean/`
  - Result: 0 inbound imports across the entire repository. It is compiled by Lake solely because `lakefile.lean` includes `lean_lib InfoGeometry where globs := #[.andSubmodules `InfoGeometry]`.

### Profiling Scripts and the "10-Hour Compile Gap"
1. **Script 1**: `tools/infra/compute_all_bottlenecks.py`
   - Output when executed:
     ```
     Module Name                                                            | Delta T (sec)  
     ----------------------------------------------------------------------------------------
     InfoGeometry.Detector.FieldCorrelatorProjection                        | 36529.82       
     InfoGeometry.LLM.KreinAttentionEnergy                                  | 27834.86       
     DAG.ConnesHodgeBridge                                                  | 26114.69       
     ```
   - Methodology in `tools/infra/compute_all_bottlenecks.py`:
     ```python
     olean_files.sort(key=lambda x: x["mtime"])
     for i in range(1, len(olean_files)):
         delta_t = olean_files[i]["mtime"] - olean_files[i-1]["mtime"]
     ```
2. **Timestamp Forensic Verification**:
   - Examination of adjacent `.olean` timestamps via Python `os.path.getmtime`:
     - File 21140: `InfoGeometry.Audit.olean`: `1789802241.42` (`2026-09-19T07:17:21.417Z`)
     - File 21141: `InfoGeometry.Detector.FieldCorrelatorProjection.olean`: `1789838771.24` (`2026-09-19T17:26:11.241Z`)
     - File 21142: `InfoGeometry.Motivic.PolylogarithmicUnipotentMotive.olean`: `1789838771.26` (`2026-09-19T17:26:11.261Z`, delta = +0.02s)
     - File 21143: `InfoGeometry.Detector.InertialFrameUniqueness.olean`: `1789838771.28` (`2026-09-19T17:26:11.281Z`, delta = +0.02s)
   - The elapsed delta $1789838771.24 - 1789802241.42 = 36529.82$ seconds ($10.15$ hours) was a wall-clock inter-session hiatus between 07:17 UTC and 17:26 UTC on 2026-09-19. Once compilation resumed at 17:26:11 UTC, `FieldCorrelatorProjection`, `PolylogarithmicUnipotentMotive`, and `InertialFrameUniqueness` completed within 40 milliseconds of one another.
3. **Comparison with Other Top Bottlenecks**:
   - `InfoGeometry.LLM.KreinAttentionEnergy` (53 lines): Delta $27834.86$ s ($7.73$ h), elapsed between `scripts.CheckEnv` at `2026-09-19T20:56:19Z` and `KreinAttentionEnergy` at `2026-09-20T04:40:14Z` (overnight gap).
   - `DAG.ConnesHodgeBridge` (59 lines): Delta $26114.69$ s ($7.25$ h), elapsed between `SymbolicLatent...` at `2026-09-18T08:21:33Z` and `DAG.ConnesHodgeBridge` at `2026-09-18T15:36:47Z` (inter-session daytime gap).

### Detailed Breakdown of Inefficient Constructs in `FieldCorrelatorProjection.lean`

| # | Construct / Identifier | Line Range | Tactic / Implementation | Root Inefficiency |
|---|---|---|---|---|
| 1 | `import Mathlib.Tactic` | Line 2 | Umbrella import | Deserializes >325 tactic modules into the elaboration environment, causing unnecessary AST and heap overhead for a 111-line file. |
| 2 | `causal_antisymm` | Lines 97–101 | `intro hab hba`<br>`cases a <;> cases b <;> simp [causallyPrecedes, rank] at hab hba ⊢` | **Combinatorial branch explosion**: $5 \times 5 = 25$ subgoals generated. `simp` is invoked 25 times to pattern match inequalities and find contradiction. |
| 3 | `canonical_chain` | Lines 102–108 | `norm_num [causallyPrecedes, rank]` | **Tactic overkill**: Invokes Mathlib's numeric normalizer to verify four concrete Nat comparisons (`195 ≤ 196 ∧ 196 ≤ 197 ∧ 197 ≤ 198 ∧ 198 ≤ 199`), which are decidable definitionally in kernel $O(1)$. |
| 4 | `detector_projection_parabola` | Lines 66–69 | `by rfl` | **Verbatim duplicate**: Exact copy of `coincidence_is_rank_two` (lines 58–60) with identical type and proof. |
| 5 | `projector_pair_bilinear_scale` | Lines 31–34 | `by ring` | Uses general polynomial normalizer `ring` for $(ε₁ * ε₂) * (a * b) = (ε₁ * a) * (ε₂ * b)$, which is directly Mathlib's `mul_mul_mul_comm`. |
| 6 | `projector_single_linear` | Lines 22–30 | `by simp [projectSingle]; ring` | Stacks two heavy tactic calls (`simp` then `ring`) to prove linear distribution $d * (r_1 a_1 + r_2 a_2) = r_1 (d a_1) + r_2 (d a_2)$. |
| 7 | `modeTrace_linear` | Lines 45–49 | `by simp [modeTrace]` | Uses general simplifier to evaluate real ring reduction $(r_1 m_1 + r_2 m_2) + 0 * (...) = r_1 (m_1 + 0 * ...) + r_2 (m_2 + 0 * ...)$. |

---

## 2. Logic Chain

1. **Attribution Analysis**:
   - `compute_all_bottlenecks.py` sorts olean files by mtime and computes consecutive deltas $\Delta t_i = t_i - t_{i-1}$.
   - At timestamp 1789802241 (07:17:21 UTC), compilation halted or paused.
   - At timestamp 1789838771 (17:26:11 UTC), compilation resumed.
   - The first file written upon resumption was `FieldCorrelatorProjection.olean`.
   - Therefore, the script assigned the entire 10-hour idle duration (36,529.82 s) to `FieldCorrelatorProjection`.
   - The same phenomenon accounts for #2 (`KreinAttentionEnergy`, 7.73 h) and #3 (`ConnesHodgeBridge`, 7.25 h).
2. **Proof Bottleneck Analysis**:
   - Although the file does not require 10 hours of CPU time, its Lean 4 AST contains several non-optimal proof terms that can be compressed.
   - In `causal_antisymm`:
     - Goal: `causallyPrecedes a b → causallyPrecedes b a → a = b`.
     - `causallyPrecedes a b` is defined as `rank a ≤ rank b`.
     - Thus `hab : rank a ≤ rank b` and `hba : rank b ≤ rank a` imply `rank a = rank b` by `Nat.le_antisymm hab hba`.
     - Because `rank` assigns distinct natural numbers $[195, 196, 197, 198, 199]$ to the five constructors, `rank` is injective.
     - Proving `rank_injective : Function.Injective rank` once (via simple case distinction on $a, b$) allows `causal_antisymm` to be proved with zero tactics:
       `fun hab hba => rank_injective (Nat.le_antisymm hab hba)`.
     - This eliminates the 25-case `simp` storm entirely.
   - In `canonical_chain`:
     - The proposition is a concrete conjunction of decidable literals: `195 ≤ 196 ∧ 196 ≤ 197 ∧ 197 ≤ 198 ∧ 198 ≤ 199`.
     - `norm_num` is redundant; `by decide` evaluates this in the Lean kernel in $O(1)$ without loading `Mathlib.Tactic.NormNum`.
   - In `projector_pair_bilinear_scale`:
     - `ring` is replaced by `exact mul_mul_mul_comm ε₁ ε₂ a b`.
   - In imports:
     - Replacing `import Mathlib.Tactic` with either `import Mathlib.Tactic.Ring` or removing it entirely drastically reduces environment load time.

---

## 3. Caveats

1. **Inter-Session Artifact vs. Real Inefficiencies**:
   The primary reason `FieldCorrelatorProjection` showed up as a 10-hour bottleneck in `compute_all_bottlenecks.py` was a tool measurement artifact (idle inter-session gap). However, the file genuinely contains inefficient structures (25-goal `simp` storm, `norm_num`, monolithic imports, duplicate theorem) that warrant clean mathematical compression.
2. **Sequential Build Lock**:
   A background `lake build` process (PID 1850) is active on the system. Per the Sequential Build and Test Mandate, no concurrent `lake build` or `lake env lean` commands were executed.
3. **Sandbox Mandate**:
   All actual refactoring and CAS script implementations must take place in `.agents/sandbox_correlator/` per the Subagent Sandbox Mandate. No repository files in `lean/` were modified.

---

## 4. Conclusion & Actionable Compression Plan

### Summary Assessment
`FieldCorrelatorProjection.lean` is a small (111-line) leaf module without inbound dependents. Its 10.15-hour bottleneck rating was an artifact of timestamp delta calculation over an inter-session pause. However, its proof structures feature classical anti-patterns (umbrella tactic import, 25-subgoal `simp` storm, `norm_num` on decidable propositions, and duplicate definitions) that are ideal candidates for OpenGauss `/golf` and CAS certificate compression.

### Recommended Surgical Refactoring in Sandbox (`.agents/sandbox_correlator/`):

1. **CAS Certificate Generator**:
   Create `.agents/sandbox_correlator/CAS/cas_field_correlator_certificate.py` using SymPy to compute:
   - Bilinear projector scaling identity: $(\epsilon_1 \epsilon_2)(a b) - (\epsilon_1 a)(\epsilon_2 b) = 0$
   - Single projector linearity: $d(r_1 a_1 + r_2 a_2) - (r_1 (d a_1) + r_2 (d a_2)) = 0$
   - Mode trace nullspace annihilation: $m + 0 \cdot o = m$
   - Causal rank sequence: strictly monotonic values $[195, 196, 197, 198, 199]$, emitting Lean certificates.

2. **Lean 4 O(1) Proof Replacements**:
   - **Narrow Imports**: Replace `import Mathlib.Tactic` with `import Mathlib.Tactic.Ring` (or direct term imports).
   - **Compress `causal_antisymm`**:
     ```lean
     theorem rank_injective : Function.Injective rank := by
       intro x y h
       cases x <;> cases y <;> first | rfl | contradiction

     theorem causal_antisymm {a b : Archetype} :
         causallyPrecedes a b → causallyPrecedes b a → a = b :=
       fun hab hba => rank_injective (Nat.le_antisymm hab hba)
     ```
   - **Compress `canonical_chain`**:
     ```lean
     theorem canonical_chain :
         causallyPrecedes .fieldCorrelator .detectorProjector ∧
         causallyPrecedes .detectorProjector .modeNullspace ∧
         causallyPrecedes .modeNullspace .rankHierarchy ∧
         causallyPrecedes .rankHierarchy .scaleInvariantObservable := by
       decide
     ```
   - **Compress `projector_pair_bilinear_scale`**:
     ```lean
     theorem projector_pair_bilinear_scale (ε₁ ε₂ a b : ℝ) :
         (ε₁ * ε₂) * (a * b) = (ε₁ * a) * (ε₂ * b) :=
       mul_mul_mul_comm ε₁ ε₂ a b
     ```
   - **Eliminate Duplicate**:
     Replace duplicate theorem `detector_projection_parabola` with an alias or alias definition pointing to `coincidence_is_rank_two`.

---

## 5. Verification Method

1. **Verify Profiling Timestamp Gap**:
   Execute:
   ```bash
   python3 -c '
   import os, datetime
   t_audit = os.path.getmtime(".lake/build/lib/lean/InfoGeometry/Audit.olean")
   t_fcp = os.path.getmtime(".lake/build/lib/lean/InfoGeometry/Detector/FieldCorrelatorProjection.olean")
   print("Audit:", datetime.datetime.fromtimestamp(t_audit, tz=datetime.timezone.utc))
   print("FCP:  ", datetime.datetime.fromtimestamp(t_fcp, tz=datetime.timezone.utc))
   print("Delta:", t_fcp - t_audit, "seconds")
   '
   ```
   Confirms delta of $36529.82$ seconds between `InfoGeometry.Audit` and `FieldCorrelatorProjection`.
2. **Verify Declarations and Tactics**:
   Inspect `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean` lines 22–34, 41–49, 97–108 to confirm exact occurrences of `simp`, `ring`, `cases a <;> cases b <;> simp`, and `norm_num`.
3. **Verify Zero Inbound Dependencies**:
   Execute `git grep "FieldCorrelatorProjection" lean/` to confirm zero inbound references outside the module itself.

# RN–Tomita–Type III Corrected Multi-Run Roadmap

> Status: operational roadmap, not proof evidence
> Audited against HEAD `4fca352d0297fdbbbc77ba5b5175e73d90a5bd77`
> Source of truth for open frontiers: `docs/rn_tomita_typeiii_coverage_matrix.md:59-65`

This document replaces the draft labels “Gap 1–5” with stable frontier IDs and
splits the work into independent runs. It does not claim any new Lean theorem.

## 1. Stable IDs and run mapping

| ID | Coverage-matrix frontier | Draft label | Run |
|---|---|---|---|
| F1 | Unbounded polar decomposition `S = J Δ^{1/2}` and Stone flow `Δ^{it}` | Gap 2 / R4 | RUN-F1 |
| F2 | Tomita fundamental theorem `J M J = M'` and `Δ^{it} M Δ^{-it} = M` | Gap 3a/3b / R2.3 + R6 | RUN-F2A, RUN-F2B |
| F3 | Takesaki Type III continuous crossed-product structure | Gap 5 / R5 | RUN-F3 |
| F4 | Unbounded Pedersen–Takesaki / Vaes affiliated-operator RN | Gap 4 / R3 | RUN-F4 |
| F5 | General Hilbert-space spectral multiplication model | not covered by draft | RUN-F5 or explicit open debt |

Step 0 is verification and coverage indexing only. It is not a mathematical
frontier. The coverage matrix is the authority for frontier descriptions.

## 2. Corrections that must be applied before any theorem contract

1. **Commutant statement.** `{L_A}' = {R_B}` for one fixed `A` is false. The
   theorem target is the commutant of the full left regular representation
   `L(Mₙ(ℂ))`, equal to the full right representation `R(Mₙ(ℂ))`.

2. **Carrier separation.** `lean/InfoGeometry/Canonical/FiniteMatrixTomitaPolar.lean:17-19`
   and `:104-111` prove the real `Matrix (Fin n) (Fin n) ℝ` result with
   `PositiveRealDensityFactor`. Existing real theorem:
   `modularConj_leftMul_conj : J (leftMul A (J X)) = rightMul Aᵀ X`
   at `:365-367`. This does not prove a complex finite-dimensional C\*-GNS
   polar theorem on `[CStarAlgebra A] [FiniteDimensional ℂ A]`.

3. **Analytic KMS premise.** `lean/InfoGeometry/Canonical/FilteredGNSMatrixAnalyticKMS.lean:63-89`
   defines `matrixFunctionalTwisted` and its algebraic conversion. The generic
   assembly uses it at `:139` and `:188`. The finite-seed specialization
   discharges it at
   `lean/InfoGeometry/Canonical/FiniteSeedRepresentedAnalyticKMS.lean:75-82`
   and `:118-120`. Do not demand its removal for arbitrary state families.

4. **Method distinction.** Rieffel–van Daele (1977) is a bounded-operator /
   real-subspace projection method. A graph-form resolvent route via
   `q(x,y) = ⟪S y, S x⟫` and `(1 + Δ)⁻¹` is a different construction and must
   be named as such. van Daele, *A new approach to the Tomita–Takesaki theory
   of generalized Hilbert algebras*, is 1974, not 1978. Current live tracked
   code has no bibliographic owner for this citation; use retrieval context
   only until a source record is added.

5. **Crossed product.** `AddMonoidAlgebra A G` is algebraic only. A C\*-crossed
   product needs action-twisted multiplication, completion, dual action, and
   conditional expectation. Without those, name the result an algebraic shadow,
   not a Type III witness.

6. **Takesaki criterion.** `lean/Omega/OperatorAlgebra/TakesakiCriterion.lean:9-16`,
   `:19-25`, `:29-45` is a Boolean/propositional wrapper with supplied
   hypotheses. Replacing flags is not closure; the target is a genuine
   conditional expectation on a concrete algebra.

7. **Powers spectrum.** A finite `RealBlockColimit m` stage cannot be a Type III
   factor witness. The infinite completion, factor property, and type
   classification are separate targets. State whether `{λⁿ : n ∈ ℤ}` is point
   spectrum or full spectrum; full spectrum includes the limit point `0`.

8. **RN surrogate.** `lean/InfoGeometry/Canonical/PedersenTakesakiRNInterface.lean:41-58`
   explicitly carries `delta = densityReadout • 1`. A finite noncommuting
   `M₂(M)` cocycle instance is legitimate, but it does not close F4.

9. **Toolchain.** `AGENTS.md:65-70` fixes Lean `v4.34.1` and the mathlib revision
   in `lake-manifest.json`. Do not write merely “Mathlib v4.34.1”.

## 3. Runs

### RUN 0 — Step 0 verification — COMPLETE

- Waited for external build PID 3840946 to release `/tmp/info-geometry-build.lock`.
- Did not kill that build. Did not delete `.lake` or use linked worktrees.
- Ran `python3 tools/infra/run_locked_lean.py --check-files` on all 12 files.
- Raw log: `/tmp/tomita_step0_locked_lean.log`.
- Evidence: `12` `[locked-lean] executing:` lines, `STEP0_EXIT=0`,
  `error:` count `0`, `error(` count `0`.
- Only warnings: deprecated `Mathlib.Data.Real.Basic` /
  `Mathlib.Data.Complex.Basic` imports and one unused-tactic linter warning in
  `TomitaModularAutomorphismFlow.lean:58`.
- Coverage matrix indexing was not applied because
  `docs/rn_tomita_typeiii_coverage_matrix.md` is concurrently modified in the
  worktree and must not be overwritten here.
- Acceptance met: exact 12-file check exit `0`, no target error diagnostics.

### RUN-F1 — unbounded polar + Stone

- Owner corridor: `FilteredGNSTomita*` closed-operator and modular-form files.
- Prove or explicitly leave open: graph-form resolvent, bounded positive
  self-adjoint `R`, CFC-constructed `Δ^{it}`, anti-unitary `J`.
- No claim of von Neumann algebra theorem.

### RUN-F2A — finite full-left/right commutant

- State the full left/right representation theorem on `Mₙ(ℂ)`.
- Keep the real `FiniteMatrixTomitaPolar` carrier distinct.

### RUN-F2B — infinite Tomita fundamental theorem

- Requires cyclic-separating vector and F1 data. Do not inhabit
  `TomitaDualityData` from fields.

### RUN-F3 — continuous crossed product

- Build algebraic crossed product first under an honest name; C\*-completion and
  Takesaki duality are separate gates.

### RUN-F4 — finite noncommuting RN cocycle

- Construct `u_t` from a 2×2 amplification and prove cocycle + chain rule on
  finite `Mₙ(ℂ)` / finite real block stages. Keep F4 open.

### RUN-F5 — spectral multiplication model

- Explicitly open unless a separate contract is approved.

## 4. Integrity rules

- One frontier per run. No aggregate-green claim across runs.
- Writer and final verifier must be distinct processes.
- Every Lean edit gets: locked file check, narrow locked module build, forbidden
  token scan, current-olean axiom audit.
- No `sorry`, `admit`, custom axiom, `native_decide`, proof-carrying structure
  field, packet, or wrapper used as closure.
- Preserve unrelated dirty/untracked files and foreign index state.

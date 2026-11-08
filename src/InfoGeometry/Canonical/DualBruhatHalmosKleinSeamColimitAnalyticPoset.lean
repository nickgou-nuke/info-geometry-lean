/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import InfoGeometry.Canonical.KleinBottleV4SeamSumDifferenceWalshHadamardPoset
import InfoGeometry.Canonical.FirstQuantizedAmariOperatorGeometryPoset
import InfoGeometry.Canonical.ParaKahlerSuperGrassmannianBruhatPushPullDikinPoset
import InfoGeometry.Canonical.AmariBerezinianModularColimitAnalyticClosurePoset

/-!
# Dual Bruhat Super-Grassmannian Idempotents, Halmos Two-Projector Cubic Complementarity, Fourfold Klein Bottle `V₄` Walsh–Hadamard Isolation, Telescopic & Norm-Convergent Push–Pull Series, and Inductive Colimit Closure (`𝔘₁ ≺ 𝔘₂ ≺ 𝔘₃ ≺ 𝔘₄ ≺ 𝔘₅ ≺ 𝔘₆ ≺ 𝔘₇`)

===============================================================================
  EPISTEMIC COMPILATION & CANONICAL FORMALIZATION
  Dual Bruhat Orderings (`bruhatDressedProjector` vs. `bruhatDressedDualProjector`) ·
  Halmos Two-Projector Identity (`(P̂ + P̂_dual - 1)² + (P̂_dual - P̂)² = (1 + V³) + (-V³) = 1`) ·
  Klein Bottle `V₄` Walsh–Hadamard Sector Isolation ·
  Telescopic & Norm-Convergent Analytic Push–Pull / Hua–Bergman–Dikin Series ·
  Inductive Categorical Colimit Continuum Lift
===============================================================================

This module bridges the Para-Kähler Super-Grassmannian (`𝔓₁ ≺ … ≺ 𝔓₇`), the Klein Bottle
`V₄` Seam (`𝔅₁ ≺ … ≺ 𝔅₇`), and the Inductive Colimit / Norm-Convergent Analytic Closure
(`𝔛₁ ≺ … ≺ 𝔛₈`) through a 7-stage causal poset (`𝔘₁ ≺ 𝔘₂ ≺ 𝔘₃ ≺ 𝔘₄ ≺ 𝔘₅ ≺ 𝔘₆ ≺ 𝔘₇`):

1. **Stage `𝔘₁` (`stage_U1_dual_bruhat_idempotents_and_cubic_ordering_holonomy`)**:
   - Reuses `bruhatDressedProjector P A C` (`P̂`) and `bruhatDressedDualProjector P A C` (`P̂_dual`)
     from `ParaKahlerSuperGrassmannianBruhatPushPullDikinPoset` and proves:
     * **Opposite Unipotent Two-Chart Group Action on `P`**:
       `P̂ = ℰ_+(-A) (ℰ_-(C) P ℰ_-(-C)) ℰ_+(A) = P + Φ - Σ - V N_+`,
       `P̂_dual = ℰ_-(C) (ℰ_+(-A) P ℰ_+(A)) ℰ_-(-C) = P + Φ - Σ - V N_-`,
     * **Exact Idempotency & Complementary Projectors**:
       `P̂² = P̂`, `P̂_dual² = P̂_dual`, `(1 - P̂_dual)² = 1 - P̂_dual`, `P̂_dual * (1 - P̂_dual) = 0`,
     * **Bruhat Ordering Holonomy Defect (`bruhatOrderingHolonomy P A C := P̂_dual - P̂`)**:
       `bruhatOrderingHolonomy P A C = V * J = Σ * Φ`,
     * **Centered Bruhat Sum (`bruhatCenteredSum P A C := P̂ + P̂_dual - 1`)**:
       `bruhatCenteredSum P A C = (S_P - 2 • Σ) + ((2 : ℤ) • Φ - V * Φ)`.

2. **Stage `𝔘₂` (`stage_U2_halmos_two_projector_cubic_complementarity_and_commutator`)**:
   - Proves that the even part `S_P - 2 • Σ` and the odd part `(2 : ℤ) • Φ - V * Φ` of the centered
     Bruhat sum `bruhatCenteredSum P A C = P̂ + P̂_dual - 1` anticommute, with squares:
     * `(S_P - 2 • Σ)² = (1 - 2 • V)² = 1 - 4 • V + 4 • V²`,
     * `((2 : ℤ) • Φ - V * Φ)² = 4 • V - 4 • V² + V³`.
   - The linear (`±4 • V`) and quadratic (`∓4 • V²`) terms cancel identically, yielding the
     **Halmos Two-Projector Cubic Complementarity Identity**:
     * `(P̂ + P̂_dual - 1)² = 1 + V³`,
     * `(P̂_dual - P̂)² = (V * J)² = -V³`,
     * `(P̂ + P̂_dual - 1)² + (P̂_dual - P̂)² = 1`,
     together with the exact commutator `[P̂, P̂_dual] = (1 - 2 • V) * V * Φ - ((2 : ℤ) • 1 - V) * V * Σ`.

3. **Stage `𝔘₃` (`stage_U3_klein_bottle_v4_walsh_hadamard_isolation_of_dual_bruhat_pair`)**:
   - Proves that the four Walsh–Hadamard projectors (`walshHadamardPP`, `walshHadamardPM`,
     `walshHadamardMP`, `walshHadamardMM`) of the Klein Bottle `V₄ = ℤ₂ × ℤ₂` seam group
     isolate the canonical invariants of the Dual Bruhat Super-Grassmannian Pair into the
     four mutually orthogonal character sectors:
     * `χ_{++} = (+1, +1)` (`walshHadamardPP`): houses the Halmos central squares `1 + V³` and `-V³`,
     * `χ_{+-} = (+1, -1)` (`walshHadamardPM`): isolates the even part `S_P - 2 • Σ` of `P̂ + P̂_dual - 1`,
     * `χ_{-+} = (-1, +1)` (`walshHadamardMP`): isolates the odd part `(2 : ℤ) • Φ - V * Φ` of `P̂ + P̂_dual - 1`,
     * `χ_{--} = (-1, -1)` (`walshHadamardMM`): isolates the Bruhat ordering holonomy defect
       `P̂_dual - P̂ = V * J = Σ * Φ`.

4. **Stage `𝔘₄` (`stage_U4_finite_horizon_telescopic_push_pull_partial_sums`)**:
   - Proves for every truncation horizon `N, M : ℕ` in any associative ring `B` that the
     truncated geometric series `geomPartialSum X N := ∑ k ∈ Finset.range N, X ^ k` satisfies:
     * `geomPartialSum Q_+ N * N_+ = N_+ * geomPartialSum Q_- N = geomPartialSum V N * N_+ = N_+ * geomPartialSum V N`,
     * `geomPartialSum Q_- N * N_- = N_- * geomPartialSum Q_+ N = geomPartialSum V N * N_- = N_- * geomPartialSum V N`,
     * `(1 - Q_+) * geomPartialSum Q_+ N * N_+ = (1 - V ^ N) * N_+`,
     * `geomPartialSum Q_+ N * dN_+ * geomPartialSum Q_- M = geomPartialSum V N * dN_+ * geomPartialSum V M`.

5. **Stage `𝔘₅` (`stage_U5_norm_convergent_analytic_push_pull_and_hua_bergman_dikin_metric`)**:
   - In any complete normed algebra `[NormedRing B] [CompleteSpace B]` with `‖V‖ < 1`:
     * Proves norm-summability and term-by-term equality of the infinite Push–Pull series
       `∑' n : ℕ, Q_+ ^ n * N_+ = ∑' n : ℕ, N_+ * Q_- ^ n = ∑' n : ℕ, V ^ n * N_+ = Ring.inverse (1 - V) * N_+`,
     * Proves exact left inversion `(1 - Q_+) * (∑' n : ℕ, Q_+ ^ n * N_+) = (1 - V) * (∑' n : ℕ, V ^ n * N_+) = N_+`,
     * Proves that the analytic Legendre–Schur differential `analyticLegendreSchurDiff P A C dA`
       satisfies two-sided Bergman–Krein inversion `(1 - V) * analyticLegendreSchurDiff P A C dA * (1 - V) = dN_+`.

6. **Stage `𝔘₆` (`stage_U6_inductive_colimit_continuum_and_chiral_supertrace_recovery`)**:
   - Lifts the Dual Bruhat Idempotents `P̂, P̂_dual`, the Halmos Two-Projector Identity, and the
     Push–Pull partial sums across any directed system of operator rings `(G : ι → Type*)`
     into `A_inf`, and proves that under any cyclic trace `tr : B →+ K`,
     `tr (P̂_dual - P̂) = tr (V * J) = 0` and `tr (P̂ - P) = 0` (`trace-first blindness`),
     while the chiral supertrace `chiralSupertrace tr P (P̂ - P) = -tr V` and
     `chiralSupertrace tr P (P̂_dual - P) = -tr V` recover the exact negative Para-Kähler metric trace.

7. **Stage `𝔘₇` (`dual_bruhat_halmos_klein_seam_colimit_analytic_master_poset`)**:
   - Unifies `𝔘₁ ≺ … ≺ 𝔘₇` with `ParaKahlerSuperGrassmannianStage` (`𝔓₁ ≺ … ≺ 𝔓₇`),
     `KleinBottleSeamConnectionStage` (`𝔅₁ ≺ … ≺ 𝔅₇`), and
     `AmariBerezinianColimitAnalyticStage` (`𝔛₁ ≺ … ≺ 𝔛₈`).

## i. Overview

Unifies the primal and dual Bruhat Super-Grassmannian idempotents, Halmos two-projector cubic
complementarity, fourfold Klein Bottle `V₄` Walsh–Hadamard sector isolation, telescopic and
norm-convergent Push–Pull series, and inductive colimit closure across `𝔘₁ ≺ … ≺ 𝔘₇`.

## ii. Key results

- `stage_U1_dual_bruhat_idempotents_and_cubic_ordering_holonomy`
- `stage_U2_halmos_two_projector_cubic_complementarity_and_commutator`
- `stage_U3_klein_bottle_v4_walsh_hadamard_isolation_of_dual_bruhat_pair`
- `stage_U4_finite_horizon_telescopic_push_pull_partial_sums`
- `stage_U5_norm_convergent_analytic_push_pull_and_hua_bergman_dikin_metric`
- `stage_U6_inductive_colimit_continuum_and_chiral_supertrace_recovery`
- `dual_bruhat_halmos_klein_seam_colimit_analytic_master_poset`

## iii. Table of contents

- Section 1: The 7-Stage Dual Bruhat Halmos–Klein–Colimit–Analytic Poset (`𝔘₁ ≺ … ≺ 𝔘₇`)
- Sections 2–8: Stages `𝔘₁` through `𝔘₇`

## iv. References

- P. R. Halmos, *Two subspaces* (1969).
- L. K. Hua, *Harmonic Analysis of Functions of Several Complex Variables in the Classical Domains* (1963).

#### BUCKET 1: CLOSED FINITE THEOREMS
- `DualBruhatHalmosColimitAnalyticStage.causalEdge_acyclic`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `stage_U1_dual_bruhat_idempotents_and_cubic_ordering_holonomy` through
  `dual_bruhat_halmos_klein_seam_colimit_analytic_master_poset`.

#### BUCKET 3: OPEN CLOSURE DEBT
- Unbounded spectral theory beyond Banach-algebra norm convergence `‖V‖ < 1`.
-/

noncomputable section

namespace InfoGeometry.Canonical.DualBruhatHalmosKleinSeamColimitAnalyticPoset

open scoped BigOperators Matrix
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.KleinBottleV4SeamSumDifferenceWalshHadamardPoset
open InfoGeometry.Canonical.FirstQuantizedAmariOperatorGeometryPoset
open InfoGeometry.Canonical.ParaKahlerSuperGrassmannianBruhatPushPullDikinPoset
open InfoGeometry.Canonical.AmariBerezinianModularColimitAnalyticClosurePoset

/-! ===========================================================================
    Section 1: The 7-Stage Dual Bruhat Halmos–Klein–Colimit–Analytic Poset (`𝔘₁ ≺ … ≺ 𝔘₇`)
    =========================================================================== -/

/-- The 7-stage causal poset (`𝔘₁ ≺ 𝔘₂ ≺ 𝔘₃ ≺ 𝔘₄ ≺ 𝔘₅ ≺ 𝔘₆ ≺ 𝔘₇`) governing the
Dual Bruhat Super-Grassmannian Idempotents, Halmos Two-Projector Cubic Complementarity,
Klein Bottle `V₄` Walsh–Hadamard Sector Isolation, Telescopic & Norm-Convergent Push–Pull
Series, and Inductive Colimit Continuum Closure. -/
inductive DualBruhatHalmosColimitAnalyticStage : Type
  /-- `𝔘₁`: Forward and dual Bruhat idempotents `P̂, P̂_dual` & cubic ordering holonomy `P̂_dual - P̂ = V J`. -/
  | U1_DualBruhatIdempotentsAndCubicOrderingHolonomy
  /-- `𝔘₂`: Halmos two-projector cubic complementarity `(P̂ + P̂_dual - 1)² + (P̂_dual - P̂)² = 1` & commutator. -/
  | U2_HalmosTwoProjectorCubicComplementarityAndCommutator
  /-- `𝔘₃`: Fourfold Klein Bottle `V₄` Walsh–Hadamard isolation of the dual Bruhat invariants. -/
  | U3_KleinBottleV4WalshHadamardIsolation
  /-- `𝔘₄`: Finite-horizon telescopic Push–Pull partial sums `S_N(Q_+) N_+ = N_+ S_N(Q_-) = S_N(V) N_+`. -/
  | U4_FiniteHorizonTelescopicPushPullPartialSums
  /-- `𝔘₅`: Norm-convergent (`N → ∞`) analytic Push–Pull `tsum` and Hua–Bergman–Dikin metric. -/
  | U5_NormConvergentAnalyticPushPullAndHuaBergmanDikinMetric
  /-- `𝔘₆`: Inductive colimit continuum lift & cyclic trace blindness / chiral supertrace recovery. -/
  | U6_InductiveColimitContinuumAndChiralSupertraceRecovery
  /-- `𝔘₇`: Master synthesis unifying `𝔘₁..𝔘₇`, `𝔓₁..𝔓₇`, `𝔅₁..𝔅₇`, and `𝔛₁..𝔛₈`. -/
  | U7_UnifiedDualBruhatKleinColimitAnalyticClosure
  deriving DecidableEq, Repr, Inhabited

namespace DualBruhatHalmosColimitAnalyticStage

/-- Strictly monotone integer rank `0..6` of `DualBruhatHalmosColimitAnalyticStage`. -/
def rank : DualBruhatHalmosColimitAnalyticStage → ℕ
  | .U1_DualBruhatIdempotentsAndCubicOrderingHolonomy => 0
  | .U2_HalmosTwoProjectorCubicComplementarityAndCommutator => 1
  | .U3_KleinBottleV4WalshHadamardIsolation => 2
  | .U4_FiniteHorizonTelescopicPushPullPartialSums => 3
  | .U5_NormConvergentAnalyticPushPullAndHuaBergmanDikinMetric => 4
  | .U6_InductiveColimitContinuumAndChiralSupertraceRecovery => 5
  | .U7_UnifiedDualBruhatKleinColimitAnalyticClosure => 6

/-- Direct cover relation `𝔘_k ≺ 𝔘_{k+1}`. -/
def coverEdge : DualBruhatHalmosColimitAnalyticStage → DualBruhatHalmosColimitAnalyticStage → Prop
  | s, t => t.rank = s.rank + 1

/-- Transitive causal ordering `s ≺⁺ t`. -/
def causalEdge : DualBruhatHalmosColimitAnalyticStage → DualBruhatHalmosColimitAnalyticStage → Prop
  | s, t => s.rank < t.rank

instance : LT DualBruhatHalmosColimitAnalyticStage := ⟨causalEdge⟩
instance : LE DualBruhatHalmosColimitAnalyticStage := ⟨fun s t => s.rank ≤ t.rank⟩

-- theorem-class: structural API
/-- Strict 7-stage causal chain `𝔘₁ ≺ 𝔘₂ ≺ 𝔘₃ ≺ 𝔘₄ ≺ 𝔘₅ ≺ 𝔘₆ ≺ 𝔘₇` and acyclicity. -/
theorem causalEdge_acyclic :
    (∀ s : DualBruhatHalmosColimitAnalyticStage, ¬ causalEdge s s) ∧
    (∀ a b c : DualBruhatHalmosColimitAnalyticStage,
      causalEdge a b → causalEdge b c → causalEdge a c) ∧
    coverEdge .U1_DualBruhatIdempotentsAndCubicOrderingHolonomy
      .U2_HalmosTwoProjectorCubicComplementarityAndCommutator ∧
    coverEdge .U2_HalmosTwoProjectorCubicComplementarityAndCommutator
      .U3_KleinBottleV4WalshHadamardIsolation ∧
    coverEdge .U3_KleinBottleV4WalshHadamardIsolation
      .U4_FiniteHorizonTelescopicPushPullPartialSums ∧
    coverEdge .U4_FiniteHorizonTelescopicPushPullPartialSums
      .U5_NormConvergentAnalyticPushPullAndHuaBergmanDikinMetric ∧
    coverEdge .U5_NormConvergentAnalyticPushPullAndHuaBergmanDikinMetric
      .U6_InductiveColimitContinuumAndChiralSupertraceRecovery ∧
    coverEdge .U6_InductiveColimitContinuumAndChiralSupertraceRecovery
      .U7_UnifiedDualBruhatKleinColimitAnalyticClosure := by
  refine ⟨fun s h => Nat.lt_irrefl s.rank h,
    fun _ _ _ hab hbc => Nat.lt_trans hab hbc,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

end DualBruhatHalmosColimitAnalyticStage

/-! ===========================================================================
    Section 2: Stage `𝔘₁` — Primal & Dual Bruhat-Dressed Two-Chart
    Idempotents (`P̂` vs. `P̂_dual`) and the Cubic Ordering Holonomy Defect (`V J`)
    =========================================================================== -/

section StageU1DualBruhatIdempotentsAndCubicOrderingHolonomy

variable {B : Type*} [Ring B]

/-- The **Bruhat Ordering Holonomy Defect** between the dual and primal Bruhat
two-chart idempotents:
`Δ_Bruhat(P, A, C) := bruhatDressedDualProjector P A C - bruhatDressedProjector P A C`. -/
def bruhatOrderingHolonomy (P A C : B) : B :=
  bruhatDressedDualProjector P A C - bruhatDressedProjector P A C

/-- The **Centered Bruhat Sum (Halmos Midpoint Involution Candidate)** of the primal and
dual Bruhat two-chart idempotents:
`M_Bruhat(P, A, C) := bruhatDressedProjector P A C + bruhatDressedDualProjector P A C - 1`. -/
def bruhatCenteredSum (P A C : B) : B :=
  bruhatDressedProjector P A C + bruhatDressedDualProjector P A C - 1

-- theorem-class: constructive endpoint
/-- **Stage `𝔘₁` Theorem (`stage_U1_dual_bruhat_idempotents_and_cubic_ordering_holonomy`)**:
In any associative ring `B` with idempotent `P * P = P` and seeds `A C : B`:
1. **Unipotent Two-Chart Group Action in Both Orderings**:
   * Primal Bruhat idempotent (`bruhatDressedProjector P A C`):
     `bruhatDressedProjector P A C = amariExpPlus P (-A) * (amariExpMinus P C * P * amariExpMinus P (-C)) * amariExpPlus P A`,
   * Dual Bruhat idempotent (`bruhatDressedDualProjector P A C`):
     `bruhatDressedDualProjector P A C = amariExpMinus P C * (amariExpPlus P (-A) * P * amariExpPlus P A) * amariExpMinus P (-C)`.
2. **Exact Jordan-Triple Cubic Expansion of the Dual Bruhat Idempotent**:
   * `bruhatDressedDualProjector P A C = P + genPhi P A C - genSig P A C - coneMinus P C * conePlus P A * coneMinus P C`,
   * `bruhatDressedDualProjector P A C = P + genPhi P A C - genSig P A C - qgtMinus P A C * coneMinus P C`,
   * `bruhatDressedDualProjector P A C = P + genPhi P A C - genSig P A C - genV P A C * coneMinus P C`.
3. **Exact Idempotency of Both Primal and Dual Bruhat Projectors**:
   * `bruhatDressedProjector P A C * bruhatDressedProjector P A C = bruhatDressedProjector P A C`,
   * `bruhatDressedDualProjector P A C * bruhatDressedDualProjector P A C = bruhatDressedDualProjector P A C`,
   * `(1 - bruhatDressedDualProjector P A C) * (1 - bruhatDressedDualProjector P A C) = 1 - bruhatDressedDualProjector P A C`,
   * `bruhatDressedDualProjector P A C * (1 - bruhatDressedDualProjector P A C) = 0`.
4. **Exact Cubic Ordering Holonomy & Centered Sum Decomposition**:
   * `bruhatOrderingHolonomy P A C = genV P A C * genJ P A C`,
   * `bruhatOrderingHolonomy P A C = genSig P A C * genPhi P A C`,
   * `bruhatCenteredSum P A C = (invS P - (2 : ℤ) • genSig P A C) + ((2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C)`. -/
theorem stage_U1_dual_bruhat_idempotents_and_cubic_ordering_holonomy
    {P : B} (hP : P * P = P) (A C : B) :
    -- (1) Opposite unipotent group action orderings on P
    (bruhatDressedProjector P A C =
        amariExpPlus P (-A) * (amariExpMinus P C * P * amariExpMinus P (-C)) * amariExpPlus P A ∧
      bruhatDressedDualProjector P A C =
        amariExpMinus P C * (amariExpPlus P (-A) * P * amariExpPlus P A) * amariExpMinus P (-C)) ∧
    -- (2) Exact Jordan-triple cubic expansion of P̂_dual
    (bruhatDressedDualProjector P A C =
        P + genPhi P A C - genSig P A C - coneMinus P C * conePlus P A * coneMinus P C ∧
      bruhatDressedDualProjector P A C =
        P + genPhi P A C - genSig P A C - qgtMinus P A C * coneMinus P C ∧
      bruhatDressedDualProjector P A C =
        P + genPhi P A C - genSig P A C - genV P A C * coneMinus P C) ∧
    -- (3) Exact idempotency of P̂ and P̂_dual
    (bruhatDressedProjector P A C * bruhatDressedProjector P A C =
        bruhatDressedProjector P A C ∧
      bruhatDressedDualProjector P A C * bruhatDressedDualProjector P A C =
        bruhatDressedDualProjector P A C ∧
      (1 - bruhatDressedDualProjector P A C) * (1 - bruhatDressedDualProjector P A C) =
        1 - bruhatDressedDualProjector P A C ∧
      bruhatDressedDualProjector P A C * (1 - bruhatDressedDualProjector P A C) = 0) ∧
    -- (4) Cubic ordering holonomy & centered sum decomposition
    (bruhatOrderingHolonomy P A C = genV P A C * genJ P A C ∧
      bruhatOrderingHolonomy P A C = genSig P A C * genPhi P A C ∧
      bruhatCenteredSum P A C =
        (invS P - (2 : ℤ) • genSig P A C) +
          ((2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C)) := by
  have hP3 := stage_P3_bruhat_dressed_two_chart_idempotent_cancels_aporia hP A C
  refine ⟨⟨by dsimp [bruhatDressedProjector, superGrassmannDualChart, amariExpPlus, amariExpMinus]; peirce_nf hP,
           by dsimp [bruhatDressedDualProjector, superGrassmannPrimalChart, amariExpPlus, amariExpMinus]; peirce_nf hP⟩,
    ⟨by dsimp [bruhatDressedDualProjector, superGrassmannPrimalChart, amariExpMinus]; peirce_nf hP,
     by dsimp [bruhatDressedDualProjector, superGrassmannPrimalChart, amariExpMinus, qgtMinus]; peirce_nf hP,
     hP3.2.2.1.2.1⟩,
    ⟨hP3.2.2.1.1,
     hP3.2.2.1.2.2,
     by dsimp [bruhatDressedDualProjector, superGrassmannPrimalChart, amariExpMinus]; peirce_nf hP,
     by dsimp [bruhatDressedDualProjector, superGrassmannPrimalChart, amariExpMinus]; peirce_nf hP⟩,
    ⟨hP3.2.2.2,
     by dsimp [bruhatOrderingHolonomy, bruhatDressedDualProjector,
          bruhatDressedProjector, superGrassmannPrimalChart, superGrassmannDualChart,
          amariExpPlus, amariExpMinus]; peirce_nf hP,
     by dsimp [bruhatCenteredSum, bruhatDressedDualProjector,
          bruhatDressedProjector, superGrassmannPrimalChart, superGrassmannDualChart,
          amariExpPlus, amariExpMinus]; peirce_nf hP⟩⟩

end StageU1DualBruhatIdempotentsAndCubicOrderingHolonomy

/-! ===========================================================================
    Section 3: Stage `𝔘₂` — Halmos Two-Projector Cubic Complementarity
    (`(P̂ + P̂_dual - 1)² + (P̂_dual - P̂)² = (1 + V³) + (-V³) = 1`) & Dual Bruhat Commutator
    =========================================================================== -/

section StageU2HalmosTwoProjectorCubicComplementarityAndCommutator

variable {B : Type*} [Ring B]

-- theorem-class: constructive endpoint
/-- **Purely `[propext]`-Only Halmos Two-Projector Cubic Complementarity Identity
(`halmos_two_projector_cubic_complementarity`)**:
In any associative ring `B` with idempotent `P * P = P` and seeds `A C : B`:
1. `(P̂ + P̂_dual - 1)² = 1 + V³`,
2. `(P̂_dual - P̂)² = -V³`,
3. `(P̂ + P̂_dual - 1)² + (P̂_dual - P̂)² = 1`,
4. `anticomm (P̂ + P̂_dual - 1) (P̂_dual - P̂) = 0`. -/
theorem halmos_two_projector_cubic_complementarity
    {P : B} (hP : P * P = P) (A C : B) :
    bruhatCenteredSum P A C * bruhatCenteredSum P A C =
        1 + genV P A C * genV P A C * genV P A C ∧
      bruhatOrderingHolonomy P A C * bruhatOrderingHolonomy P A C =
        -(genV P A C * genV P A C * genV P A C) ∧
      bruhatCenteredSum P A C * bruhatCenteredSum P A C +
          bruhatOrderingHolonomy P A C * bruhatOrderingHolonomy P A C = 1 ∧
      anticomm (bruhatCenteredSum P A C) (bruhatOrderingHolonomy P A C) = 0 := by
  refine ⟨by dsimp [bruhatCenteredSum, bruhatDressedProjector,
              bruhatDressedDualProjector, superGrassmannPrimalChart,
              superGrassmannDualChart, amariExpPlus, amariExpMinus]; peirce_nf hP,
    by dsimp [bruhatOrderingHolonomy, bruhatDressedProjector,
        bruhatDressedDualProjector, superGrassmannPrimalChart,
        superGrassmannDualChart, amariExpPlus, amariExpMinus]; peirce_nf hP,
    by dsimp [bruhatCenteredSum, bruhatOrderingHolonomy, bruhatDressedProjector,
        bruhatDressedDualProjector, superGrassmannPrimalChart,
        superGrassmannDualChart, amariExpPlus, amariExpMinus]; peirce_nf hP,
    by dsimp [bruhatCenteredSum, bruhatOrderingHolonomy, bruhatDressedProjector,
        bruhatDressedDualProjector, superGrassmannPrimalChart,
        superGrassmannDualChart, amariExpPlus, amariExpMinus]; peirce_nf hP⟩

-- theorem-class: constructive endpoint
/-- **Stage `𝔘₂` Theorem (`stage_U2_halmos_two_projector_cubic_complementarity_and_commutator`)**:
In any associative ring `B` with idempotent `P * P = P` and seeds `A C : B`:
1. **Even/Odd Anticommutation & Individual Squares of `bruhatCenteredSum`**:
   * `anticomm (invS P - (2 : ℤ) • genSig P A C) ((2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C) = 0`,
   * `(invS P - (2 : ℤ) • genSig P A C) * (invS P - (2 : ℤ) • genSig P A C) =
       (1 - (2 : ℤ) • genV P A C) * (1 - (2 : ℤ) • genV P A C)`,
   * `(1 - (2 : ℤ) • genV P A C) * (1 - (2 : ℤ) • genV P A C) =
       1 - (4 : ℤ) • genV P A C + (4 : ℤ) • (genV P A C * genV P A C)`,
   * `((2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C) *
       ((2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C) =
       (4 : ℤ) • genV P A C - (4 : ℤ) • (genV P A C * genV P A C) +
         genV P A C * genV P A C * genV P A C`.
2. **Halmos Two-Projector Cubic Complementarity Identity**:
   * The degree-1 (`±4 V`) and degree-2 (`∓4 V²`) terms cancel identically:
     `bruhatCenteredSum P A C * bruhatCenteredSum P A C =
       1 + genV P A C * genV P A C * genV P A C`,
   * The cubic ordering holonomy squares to `-V³`:
     `bruhatOrderingHolonomy P A C * bruhatOrderingHolonomy P A C =
       -(genV P A C * genV P A C * genV P A C)`,
   * **Exact Halmos Identity**:
     `bruhatCenteredSum P A C * bruhatCenteredSum P A C +
        bruhatOrderingHolonomy P A C * bruhatOrderingHolonomy P A C = 1`.
3. **Dual Bruhat Commutator `[P̂, P̂_dual]` & Anticommutator Relations**:
   * `comm (bruhatDressedProjector P A C) (bruhatDressedDualProjector P A C) =
       (1 - (2 : ℤ) • genV P A C) * genV P A C * genPhi P A C -
         ((2 : ℤ) • genV P A C - genV P A C * genV P A C) * genSig P A C`,
   * `anticomm (bruhatCenteredSum P A C) (bruhatOrderingHolonomy P A C) = 0`,
   * `comm (bruhatCenteredSum P A C) (bruhatOrderingHolonomy P A C) =
       (2 : ℤ) • comm (bruhatDressedProjector P A C) (bruhatDressedDualProjector P A C)`. -/
theorem stage_U2_halmos_two_projector_cubic_complementarity_and_commutator
    {P : B} (hP : P * P = P) (A C : B) :
    -- (1) Even/odd anticommutation & individual squares
    (anticomm (invS P - (2 : ℤ) • genSig P A C)
        ((2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C) = 0 ∧
      (invS P - (2 : ℤ) • genSig P A C) * (invS P - (2 : ℤ) • genSig P A C) =
        (1 - (2 : ℤ) • genV P A C) * (1 - (2 : ℤ) • genV P A C) ∧
      (1 - (2 : ℤ) • genV P A C) * (1 - (2 : ℤ) • genV P A C) =
        1 - (4 : ℤ) • genV P A C + (4 : ℤ) • (genV P A C * genV P A C) ∧
      ((2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C) *
          ((2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C) =
        (4 : ℤ) • genV P A C - (4 : ℤ) • (genV P A C * genV P A C) +
          genV P A C * genV P A C * genV P A C) ∧
    -- (2) Halmos Two-Projector Cubic Complementarity
    (bruhatCenteredSum P A C * bruhatCenteredSum P A C =
        1 + genV P A C * genV P A C * genV P A C ∧
      bruhatOrderingHolonomy P A C * bruhatOrderingHolonomy P A C =
        -(genV P A C * genV P A C * genV P A C) ∧
      bruhatCenteredSum P A C * bruhatCenteredSum P A C +
          bruhatOrderingHolonomy P A C * bruhatOrderingHolonomy P A C = 1) ∧
    -- (3) Dual Bruhat commutator & anticommutator relations
    (comm (bruhatDressedProjector P A C) (bruhatDressedDualProjector P A C) =
        (1 - (2 : ℤ) • genV P A C) * genV P A C * genPhi P A C -
          ((2 : ℤ) • genV P A C - genV P A C * genV P A C) * genSig P A C ∧
      anticomm (bruhatCenteredSum P A C) (bruhatOrderingHolonomy P A C) = 0 ∧
      comm (bruhatCenteredSum P A C) (bruhatOrderingHolonomy P A C) =
        (2 : ℤ) • comm (bruhatDressedProjector P A C) (bruhatDressedDualProjector P A C)) := by
  refine ⟨⟨by peirce_nf hP,
           by peirce_nf hP,
           by peirce_nf hP,
           by peirce_nf hP⟩,
    ⟨by dsimp [bruhatCenteredSum, bruhatDressedProjector,
          bruhatDressedDualProjector, superGrassmannPrimalChart,
          superGrassmannDualChart, amariExpPlus, amariExpMinus]; peirce_nf hP,
     by dsimp [bruhatOrderingHolonomy, bruhatDressedProjector,
          bruhatDressedDualProjector, superGrassmannPrimalChart,
          superGrassmannDualChart, amariExpPlus, amariExpMinus]; peirce_nf hP,
     by dsimp [bruhatCenteredSum, bruhatOrderingHolonomy, bruhatDressedProjector,
          bruhatDressedDualProjector, superGrassmannPrimalChart,
          superGrassmannDualChart, amariExpPlus, amariExpMinus]; peirce_nf hP⟩,
    ⟨by dsimp [bruhatDressedProjector, bruhatDressedDualProjector,
          superGrassmannPrimalChart, superGrassmannDualChart,
          amariExpPlus, amariExpMinus]; peirce_nf hP,
     by dsimp [bruhatCenteredSum, bruhatOrderingHolonomy, bruhatDressedProjector,
          bruhatDressedDualProjector, superGrassmannPrimalChart,
          superGrassmannDualChart, amariExpPlus, amariExpMinus]; peirce_nf hP,
     by dsimp [bruhatCenteredSum, bruhatOrderingHolonomy, bruhatDressedProjector,
          bruhatDressedDualProjector, superGrassmannPrimalChart,
          superGrassmannDualChart, amariExpPlus, amariExpMinus]; peirce_nf hP⟩⟩

end StageU2HalmosTwoProjectorCubicComplementarityAndCommutator

/-! ===========================================================================
    Section 4: Stage `𝔘₃` — Fourfold Klein Bottle `V₄` Walsh–Hadamard
    Sector Isolation of the Dual Bruhat Super-Grassmannian Pair
    =========================================================================== -/

section StageU3KleinBottleV4WalshHadamardIsolation

variable {B : Type*} [Ring B]

-- theorem-class: constructive endpoint
/-- **Stage `𝔘₃` Theorem (`stage_U3_klein_bottle_v4_walsh_hadamard_isolation_of_dual_bruhat_pair`)**:
Let `P U : B` satisfy `P * P = P`, `U * U = 1`, `invS P * U = -(U * invS P)`, and let `U`
interchange the chiral cones `U * conePlus P A * U = coneMinus P C` and
`U * coneMinus P C * U = conePlus P A`. Then the four `V₄ = ℤ₂ × ℤ₂` Walsh–Hadamard
projectors (`walshHadamardPP`, `walshHadamardPM`, `walshHadamardMP`, `walshHadamardMM`)
isolate the Dual Bruhat Super-Grassmannian invariants into the 4 mutually orthogonal sectors:
1. **`V₄` Eigen-Action on the Bruhat Ordering Holonomy `Δ_Bruhat = V * J`**:
   * `kleinAlpha P (bruhatOrderingHolonomy P A C) = -bruhatOrderingHolonomy P A C`,
   * `kleinBeta U (bruhatOrderingHolonomy P A C) = -bruhatOrderingHolonomy P A C`,
   * `kleinGamma P U (bruhatOrderingHolonomy P A C) = bruhatOrderingHolonomy P A C`.
2. **Sector `χ_{--} = (-1, -1)` (`walshHadamardMM`): Pure Isolation of `bruhatOrderingHolonomy`**:
   * `walshHadamardMM P U (bruhatOrderingHolonomy P A C) = (4 : ℤ) • bruhatOrderingHolonomy P A C`,
   * `walshHadamardPP P U (bruhatOrderingHolonomy P A C) = 0`,
   * `walshHadamardPM P U (bruhatOrderingHolonomy P A C) = 0`,
   * `walshHadamardMP P U (bruhatOrderingHolonomy P A C) = 0`.
3. **Sectors `χ_{+-} = (+1, -1)` & `χ_{-+} = (-1, +1)`: Exact Splitting of `bruhatCenteredSum`**:
   * `walshHadamardPP P U (bruhatCenteredSum P A C) = 0`,
   * `walshHadamardPM P U (bruhatCenteredSum P A C) = (4 : ℤ) • (invS P - (2 : ℤ) • genSig P A C)`,
   * `walshHadamardMP P U (bruhatCenteredSum P A C) =
       (4 : ℤ) • ((2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C)`,
   * `walshHadamardMM P U (bruhatCenteredSum P A C) = 0`.
4. **Sector `χ_{++} = (+1, +1)` (`walshHadamardPP`): Pure Isolation of the Halmos Squares**:
   * `walshHadamardPP P U (bruhatCenteredSum P A C * bruhatCenteredSum P A C) =
       (4 : ℤ) • (bruhatCenteredSum P A C * bruhatCenteredSum P A C)`,
   * `walshHadamardPP P U (bruhatOrderingHolonomy P A C * bruhatOrderingHolonomy P A C) =
       (4 : ℤ) • (bruhatOrderingHolonomy P A C * bruhatOrderingHolonomy P A C)`. -/
theorem stage_U3_klein_bottle_v4_walsh_hadamard_isolation_of_dual_bruhat_pair
    {P U : B} (hP : P * P = P) (hU : U * U = 1)
    (hSU : invS P * U = -(U * invS P))
    {A C : B}
    (hUNp : U * conePlus P A * U = coneMinus P C)
    (hUNm : U * coneMinus P C * U = conePlus P A) :
    -- (1) V₄ eigen-action on Δ_Bruhat = V * J
    (kleinAlpha P (bruhatOrderingHolonomy P A C) = -bruhatOrderingHolonomy P A C ∧
      kleinBeta U (bruhatOrderingHolonomy P A C) = -bruhatOrderingHolonomy P A C ∧
      kleinGamma P U (bruhatOrderingHolonomy P A C) = bruhatOrderingHolonomy P A C) ∧
    -- (2) Sector χ_{--} isolates bruhatOrderingHolonomy = V * J
    (walshHadamardMM P U (bruhatOrderingHolonomy P A C) =
        (4 : ℤ) • bruhatOrderingHolonomy P A C ∧
      walshHadamardPP P U (bruhatOrderingHolonomy P A C) = 0 ∧
      walshHadamardPM P U (bruhatOrderingHolonomy P A C) = 0 ∧
      walshHadamardMP P U (bruhatOrderingHolonomy P A C) = 0) ∧
    -- (3) Sectors χ_{+-} and χ_{-+} split bruhatCenteredSum
    (walshHadamardPP P U (bruhatCenteredSum P A C) = 0 ∧
      walshHadamardPM P U (bruhatCenteredSum P A C) =
        (4 : ℤ) • (invS P - (2 : ℤ) • genSig P A C) ∧
      walshHadamardMP P U (bruhatCenteredSum P A C) =
        (4 : ℤ) • ((2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C) ∧
      walshHadamardMM P U (bruhatCenteredSum P A C) = 0) ∧
    -- (4) Sector χ_{++} isolates the Halmos squares
    (walshHadamardPP P U (bruhatCenteredSum P A C * bruhatCenteredSum P A C) =
        (4 : ℤ) • (bruhatCenteredSum P A C * bruhatCenteredSum P A C) ∧
      walshHadamardPP P U (bruhatOrderingHolonomy P A C * bruhatOrderingHolonomy P A C) =
        (4 : ℤ) • (bruhatOrderingHolonomy P A C * bruhatOrderingHolonomy P A C)) := by
  have hGammaEq : ∀ X : B, kleinGamma P U X = kleinAlpha P (kleinBeta U X) := by
    intro X
    dsimp [kleinGamma, kleinAlpha, kleinBeta]
    noncomm_ring
  have hAlphaNeg : ∀ X : B, kleinAlpha P (-X) = -kleinAlpha P X := by
    intro X; dsimp [kleinAlpha]; noncomm_ring
  have hU_NpNm : U * (conePlus P A * coneMinus P C) * U = coneMinus P C * conePlus P A := by
    calc
      U * (conePlus P A * coneMinus P C) * U =
        U * conePlus P A * (U * U) * coneMinus P C * U := by rw [hU]; noncomm_ring
      _ = (U * conePlus P A * U) * (U * coneMinus P C * U) := by noncomm_ring
      _ = coneMinus P C * conePlus P A := by rw [hUNp, hUNm]
  have hU_NmNp : U * (coneMinus P C * conePlus P A) * U = conePlus P A * coneMinus P C := by
    calc
      U * (coneMinus P C * conePlus P A) * U =
        U * coneMinus P C * (U * U) * conePlus P A * U := by rw [hU]; noncomm_ring
      _ = (U * coneMinus P C * U) * (U * conePlus P A * U) := by noncomm_ring
      _ = conePlus P A * coneMinus P C := by rw [hUNm, hUNp]
  have hBetaV : kleinBeta U (genV P A C) = genV P A C := by
    dsimp [kleinBeta, genV]
    calc
      U * (conePlus P A * coneMinus P C + coneMinus P C * conePlus P A) * U =
        U * (conePlus P A * coneMinus P C) * U + U * (coneMinus P C * conePlus P A) * U := by
        noncomm_ring
      _ = coneMinus P C * conePlus P A + conePlus P A * coneMinus P C := by
        rw [hU_NpNm, hU_NmNp]
      _ = conePlus P A * coneMinus P C + coneMinus P C * conePlus P A := by abel
  have hBetaSig : kleinBeta U (genSig P A C) = -genSig P A C := by
    dsimp [kleinBeta, genSig]
    calc
      U * (conePlus P A * coneMinus P C - coneMinus P C * conePlus P A) * U =
        U * (conePlus P A * coneMinus P C) * U - U * (coneMinus P C * conePlus P A) * U := by
        noncomm_ring
      _ = coneMinus P C * conePlus P A - conePlus P A * coneMinus P C := by
        rw [hU_NpNm, hU_NmNp]
      _ = -(conePlus P A * coneMinus P C - coneMinus P C * conePlus P A) := by abel
  have hBetaPhi : kleinBeta U (genPhi P A C) = genPhi P A C := by
    dsimp [kleinBeta, genPhi]
    calc
      U * (conePlus P A + coneMinus P C) * U =
        U * conePlus P A * U + U * coneMinus P C * U := by noncomm_ring
      _ = coneMinus P C + conePlus P A := by rw [hUNp, hUNm]
      _ = conePlus P A + coneMinus P C := by abel
  have hBetaJ : kleinBeta U (genJ P A C) = -genJ P A C := by
    dsimp [kleinBeta, genJ]
    calc
      U * (conePlus P A - coneMinus P C) * U =
        U * conePlus P A * U - U * coneMinus P C * U := by noncomm_ring
      _ = coneMinus P C - conePlus P A := by rw [hUNp, hUNm]
      _ = -(conePlus P A - coneMinus P C) := by abel
  have hU1 := stage_U1_dual_bruhat_idempotents_and_cubic_ordering_holonomy hP A C
  have hHolVJ : bruhatOrderingHolonomy P A C = genV P A C * genJ P A C := hU1.2.2.2.1
  have hSumDecomp :
      bruhatCenteredSum P A C =
        (invS P - (2 : ℤ) • genSig P A C) +
          ((2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C) := hU1.2.2.2.2.2
  have hU2 := stage_U2_halmos_two_projector_cubic_complementarity_and_commutator hP A C
  have hAlphaHol : kleinAlpha P (bruhatOrderingHolonomy P A C) = -bruhatOrderingHolonomy P A C := by
    rw [hHolVJ]
    dsimp [kleinAlpha]
    peirce_nf hP
  have hBetaHol : kleinBeta U (bruhatOrderingHolonomy P A C) = -bruhatOrderingHolonomy P A C := by
    rw [hHolVJ]
    calc
      kleinBeta U (genV P A C * genJ P A C)
        = U * genV P A C * 1 * genJ P A C * U := by dsimp [kleinBeta]; noncomm_ring
      _ = U * genV P A C * (U * U) * genJ P A C * U := by rw [hU]
      _ = kleinBeta U (genV P A C) * kleinBeta U (genJ P A C) := by
          dsimp [kleinBeta]; noncomm_ring
      _ = genV P A C * (-genJ P A C) := by rw [hBetaV, hBetaJ]
      _ = -(genV P A C * genJ P A C) := by noncomm_ring
  have hGammaHol : kleinGamma P U (bruhatOrderingHolonomy P A C) = bruhatOrderingHolonomy P A C := by
    rw [hGammaEq, hBetaHol, hAlphaNeg, hAlphaHol, neg_neg]
  let E := invS P - (2 : ℤ) • genSig P A C
  let O := (2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C
  have hAlphaE : kleinAlpha P E = E := by
    dsimp [E, kleinAlpha]
    peirce_nf hP
  have hUSPU : U * invS P * U = -invS P := by
    calc
      U * invS P * U = -(-(U * invS P) * U) := by noncomm_ring
      _ = -((invS P * U) * U) := by rw [← hSU]
      _ = -(invS P * (U * U)) := by noncomm_ring
      _ = -invS P := by rw [hU, mul_one]
  have hBetaE : kleinBeta U E = -E := by
    dsimp [E, kleinBeta]
    calc
      U * (invS P - (2 : ℤ) • genSig P A C) * U
        = U * invS P * U - (2 : ℤ) • kleinBeta U (genSig P A C) := by
          dsimp [kleinBeta]; noncomm_ring
      _ = -invS P - (2 : ℤ) • (-genSig P A C) := by
          rw [hUSPU, hBetaSig]
      _ = -(invS P - (2 : ℤ) • genSig P A C) := by abel
  have hGammaE : kleinGamma P U E = -E := by
    rw [hGammaEq, hBetaE, hAlphaNeg, hAlphaE]
  have hAlphaO : kleinAlpha P O = -O := by
    dsimp [O, kleinAlpha]
    peirce_nf hP
  have hBetaVPhi : kleinBeta U (genV P A C * genPhi P A C) = genV P A C * genPhi P A C := by
    calc
      kleinBeta U (genV P A C * genPhi P A C)
        = U * genV P A C * 1 * genPhi P A C * U := by dsimp [kleinBeta]; noncomm_ring
      _ = U * genV P A C * (U * U) * genPhi P A C * U := by rw [hU]
      _ = kleinBeta U (genV P A C) * kleinBeta U (genPhi P A C) := by
          dsimp [kleinBeta]; noncomm_ring
      _ = genV P A C * genPhi P A C := by rw [hBetaV, hBetaPhi]
  have hBetaO : kleinBeta U O = O := by
    dsimp [O]
    calc
      kleinBeta U ((2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C)
        = (2 : ℤ) • kleinBeta U (genPhi P A C) - kleinBeta U (genV P A C * genPhi P A C) := by
          dsimp [kleinBeta]; noncomm_ring
      _ = (2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C := by
          rw [hBetaPhi, hBetaVPhi]
  have hGammaO : kleinGamma P U O = -O := by
    rw [hGammaEq, hBetaO, hAlphaO]
  have hAlphaSum : kleinAlpha P (bruhatCenteredSum P A C) = E - O := by
    rw [hSumDecomp]
    calc
      kleinAlpha P (E + O) = kleinAlpha P E + kleinAlpha P O := by
        dsimp [kleinAlpha]; noncomm_ring
      _ = E - O := by rw [hAlphaE, hAlphaO, sub_eq_add_neg]
  have hBetaSum : kleinBeta U (bruhatCenteredSum P A C) = -E + O := by
    rw [hSumDecomp]
    calc
      kleinBeta U (E + O) = kleinBeta U E + kleinBeta U O := by
        dsimp [kleinBeta]; noncomm_ring
      _ = -E + O := by rw [hBetaE, hBetaO]
  have hGammaSum : kleinGamma P U (bruhatCenteredSum P A C) = -E - O := by
    rw [hSumDecomp]
    calc
      kleinGamma P U (E + O) = kleinGamma P U E + kleinGamma P U O := by
        dsimp [kleinGamma]; noncomm_ring
      _ = -E - O := by rw [hGammaE, hGammaO, sub_eq_add_neg]
  have hUV3 :
      kleinBeta U (genV P A C * genV P A C * genV P A C) =
        genV P A C * genV P A C * genV P A C := by
    dsimp [kleinBeta]
    calc
      U * (genV P A C * genV P A C * genV P A C) * U
        = U * genV P A C * 1 * genV P A C * 1 * genV P A C * U := by noncomm_ring
      _ = U * genV P A C * (U * U) * genV P A C * (U * U) * genV P A C * U := by rw [hU]
      _ = kleinBeta U (genV P A C) * kleinBeta U (genV P A C) * kleinBeta U (genV P A C) := by
          dsimp [kleinBeta]; noncomm_ring
      _ = genV P A C * genV P A C * genV P A C := by rw [hBetaV]
  have hAlphaSq1 :
      kleinAlpha P (bruhatCenteredSum P A C * bruhatCenteredSum P A C) =
        bruhatCenteredSum P A C * bruhatCenteredSum P A C := by
    rw [hU2.2.1.1]
    dsimp [kleinAlpha]
    peirce_nf hP
  have hBetaSq1 :
      kleinBeta U (bruhatCenteredSum P A C * bruhatCenteredSum P A C) =
        bruhatCenteredSum P A C * bruhatCenteredSum P A C := by
    rw [hU2.2.1.1]
    calc
      kleinBeta U (1 + genV P A C * genV P A C * genV P A C)
        = U * U + kleinBeta U (genV P A C * genV P A C * genV P A C) := by
          dsimp [kleinBeta]; noncomm_ring
      _ = 1 + genV P A C * genV P A C * genV P A C := by rw [hU, hUV3]
  have hGammaSq1 :
      kleinGamma P U (bruhatCenteredSum P A C * bruhatCenteredSum P A C) =
        bruhatCenteredSum P A C * bruhatCenteredSum P A C := by
    rw [hGammaEq, hBetaSq1, hAlphaSq1]
  have hAlphaSq2 :
      kleinAlpha P (bruhatOrderingHolonomy P A C * bruhatOrderingHolonomy P A C) =
        bruhatOrderingHolonomy P A C * bruhatOrderingHolonomy P A C := by
    rw [hU2.2.1.2.1]
    dsimp [kleinAlpha]
    peirce_nf hP
  have hBetaSq2 :
      kleinBeta U (bruhatOrderingHolonomy P A C * bruhatOrderingHolonomy P A C) =
        bruhatOrderingHolonomy P A C * bruhatOrderingHolonomy P A C := by
    rw [hU2.2.1.2.1]
    calc
      kleinBeta U (-(genV P A C * genV P A C * genV P A C))
        = -kleinBeta U (genV P A C * genV P A C * genV P A C) := by
          dsimp [kleinBeta]; noncomm_ring
      _ = -(genV P A C * genV P A C * genV P A C) := by rw [hUV3]
  have hGammaSq2 :
      kleinGamma P U (bruhatOrderingHolonomy P A C * bruhatOrderingHolonomy P A C) =
        bruhatOrderingHolonomy P A C * bruhatOrderingHolonomy P A C := by
    rw [hGammaEq, hBetaSq2, hAlphaSq2]
  refine ⟨⟨hAlphaHol, hBetaHol, hGammaHol⟩,
    ⟨by dsimp [walshHadamardMM]; rw [hAlphaHol, hBetaHol, hGammaHol]; abel,
     by dsimp [walshHadamardPP]; rw [hAlphaHol, hBetaHol, hGammaHol]; abel,
     by dsimp [walshHadamardPM]; rw [hAlphaHol, hBetaHol, hGammaHol]; abel,
     by dsimp [walshHadamardMP]; rw [hAlphaHol, hBetaHol, hGammaHol]; abel⟩,
    ⟨by dsimp [walshHadamardPP]; rw [hAlphaSum, hBetaSum, hGammaSum, hSumDecomp]; dsimp [E, O]; abel,
     by dsimp [walshHadamardPM]; rw [hAlphaSum, hBetaSum, hGammaSum, hSumDecomp]; dsimp [E, O]; abel,
     by dsimp [walshHadamardMP]; rw [hAlphaSum, hBetaSum, hGammaSum, hSumDecomp]; dsimp [E, O]; abel,
     by dsimp [walshHadamardMM]; rw [hAlphaSum, hBetaSum, hGammaSum, hSumDecomp]; dsimp [E, O]; abel⟩,
    ⟨by dsimp [walshHadamardPP]; rw [hAlphaSq1, hBetaSq1, hGammaSq1]; abel,
     by dsimp [walshHadamardPP]; rw [hAlphaSq2, hBetaSq2, hGammaSq2]; abel⟩⟩

end StageU3KleinBottleV4WalshHadamardIsolation

/-! ===========================================================================
    Section 5: Stage `𝔘₄` — Finite-Horizon Telescopic Push–Pull Partial Sums
    (`S_N(Q_+) N_+ = N_+ S_N(Q_-) = S_N(V) N_+`)
    =========================================================================== -/

section StageU4FiniteHorizonTelescopicPushPullPartialSums

variable {B : Type*} [Ring B]

/-- The truncated degree-`N` geometric partial sum `S_N(X) := ∑ k ∈ Finset.range N, X ^ k`. -/
def geomPartialSum (X : B) (N : ℕ) : B :=
  ∑ k ∈ Finset.range N, X ^ k

-- theorem-class: structural API
/-- Sheet-projector power absorption for `genV`, `qgtPlus`, and `qgtMinus` at any degree `k : ℕ`. -/
theorem peirce_sheet_pow_absorption
    {P : B} (hP : P * P = P) (A C dA dC : B) (k : ℕ) :
    (genV P A C ^ k * P = qgtPlus P A C ^ k * P ∧
      (1 - P) * genV P A C ^ k = (1 - P) * qgtMinus P A C ^ k) ∧
    (genV P A C ^ k * conePlus P dA = qgtPlus P A C ^ k * conePlus P dA ∧
      conePlus P dA * genV P A C ^ k = conePlus P dA * qgtMinus P A C ^ k ∧
      genV P A C ^ k * coneMinus P dC = qgtMinus P A C ^ k * coneMinus P dC ∧
      coneMinus P dC * genV P A C ^ k = coneMinus P dC * qgtPlus P A C ^ k) := by
  have hProj :
      ∀ m : ℕ,
        genV P A C ^ m * P = qgtPlus P A C ^ m * P ∧
        P * genV P A C ^ m = P * qgtPlus P A C ^ m ∧
        genV P A C ^ m * (1 - P) = qgtMinus P A C ^ m * (1 - P) ∧
        (1 - P) * genV P A C ^ m = (1 - P) * qgtMinus P A C ^ m := by
    intro m
    induction m with
    | zero =>
      simp
    | succ j ih =>
      rcases ih with ⟨ih1, ih2, ih3, ih4⟩
      have hVP : genV P A C * P = P * (qgtPlus P A C * P) := by dsimp [qgtPlus]; peirce_nf hP
      have hQpP : qgtPlus P A C * P = P * (qgtPlus P A C * P) := by dsimp [qgtPlus]; peirce_nf hP
      have hPV : P * genV P A C = (P * qgtPlus P A C) * P := by dsimp [qgtPlus]; peirce_nf hP
      have hPQp : P * qgtPlus P A C = (P * qgtPlus P A C) * P := by dsimp [qgtPlus]; peirce_nf hP
      have hV1mP : genV P A C * (1 - P) = (1 - P) * (qgtMinus P A C * (1 - P)) := by
        dsimp [qgtMinus]; peirce_nf hP
      have hQm1mP : qgtMinus P A C * (1 - P) = (1 - P) * (qgtMinus P A C * (1 - P)) := by
        dsimp [qgtMinus]; peirce_nf hP
      have h1mPV : (1 - P) * genV P A C = ((1 - P) * qgtMinus P A C) * (1 - P) := by
        dsimp [qgtMinus]; peirce_nf hP
      have h1mPQm : (1 - P) * qgtMinus P A C = ((1 - P) * qgtMinus P A C) * (1 - P) := by
        dsimp [qgtMinus]; peirce_nf hP
      refine ⟨?_, ?_, ?_, ?_⟩
      · calc
          genV P A C ^ (j + 1) * P
            = genV P A C ^ j * (genV P A C * P) := by rw [pow_succ, mul_assoc]
          _ = (genV P A C ^ j * P) * (qgtPlus P A C * P) := by rw [hVP, ← mul_assoc]
          _ = (qgtPlus P A C ^ j * P) * (qgtPlus P A C * P) := by rw [ih1]
          _ = qgtPlus P A C ^ j * (qgtPlus P A C * P) := by rw [mul_assoc, ← hQpP]
          _ = qgtPlus P A C ^ (j + 1) * P := by rw [← mul_assoc, ← pow_succ]
      · calc
          P * genV P A C ^ (j + 1)
            = (P * genV P A C) * genV P A C ^ j := by rw [pow_succ', ← mul_assoc]
          _ = (P * qgtPlus P A C) * (P * genV P A C ^ j) := by rw [hPV, mul_assoc]
          _ = (P * qgtPlus P A C) * (P * qgtPlus P A C ^ j) := by rw [ih2]
          _ = (P * qgtPlus P A C) * qgtPlus P A C ^ j := by rw [← mul_assoc, ← hPQp]
          _ = P * qgtPlus P A C ^ (j + 1) := by rw [mul_assoc, ← pow_succ']
      · calc
          genV P A C ^ (j + 1) * (1 - P)
            = genV P A C ^ j * (genV P A C * (1 - P)) := by rw [pow_succ, mul_assoc]
          _ = (genV P A C ^ j * (1 - P)) * (qgtMinus P A C * (1 - P)) := by rw [hV1mP, ← mul_assoc]
          _ = (qgtMinus P A C ^ j * (1 - P)) * (qgtMinus P A C * (1 - P)) := by rw [ih3]
          _ = qgtMinus P A C ^ j * (qgtMinus P A C * (1 - P)) := by rw [mul_assoc, ← hQm1mP]
          _ = qgtMinus P A C ^ (j + 1) * (1 - P) := by rw [← mul_assoc, ← pow_succ]
      · calc
          (1 - P) * genV P A C ^ (j + 1)
            = ((1 - P) * genV P A C) * genV P A C ^ j := by rw [pow_succ', ← mul_assoc]
          _ = ((1 - P) * qgtMinus P A C) * ((1 - P) * genV P A C ^ j) := by rw [h1mPV, mul_assoc]
          _ = ((1 - P) * qgtMinus P A C) * ((1 - P) * qgtMinus P A C ^ j) := by rw [ih4]
          _ = ((1 - P) * qgtMinus P A C) * qgtMinus P A C ^ j := by rw [← mul_assoc, ← h1mPQm]
          _ = (1 - P) * qgtMinus P A C ^ (j + 1) := by rw [mul_assoc, ← pow_succ']
  rcases hProj k with ⟨hk1, hk2, hk3, hk4⟩
  have hPNp : P * conePlus P dA = conePlus P dA := by peirce_nf hP
  have hNp1mP : conePlus P dA * (1 - P) = conePlus P dA := by peirce_nf hP
  have h1mPNm : (1 - P) * coneMinus P dC = coneMinus P dC := by peirce_nf hP
  have hNmP : coneMinus P dC * P = coneMinus P dC := by peirce_nf hP
  refine ⟨⟨hk1, hk4⟩, ?_, ?_, ?_, ?_⟩
  · calc
      genV P A C ^ k * conePlus P dA
        = (genV P A C ^ k * P) * conePlus P dA := by rw [mul_assoc, hPNp]
      _ = (qgtPlus P A C ^ k * P) * conePlus P dA := by rw [hk1]
      _ = qgtPlus P A C ^ k * conePlus P dA := by rw [mul_assoc, hPNp]
  · calc
      conePlus P dA * genV P A C ^ k
        = conePlus P dA * ((1 - P) * genV P A C ^ k) := by rw [← mul_assoc, hNp1mP]
      _ = conePlus P dA * ((1 - P) * qgtMinus P A C ^ k) := by rw [hk4]
      _ = conePlus P dA * qgtMinus P A C ^ k := by rw [← mul_assoc, hNp1mP]
  · calc
      genV P A C ^ k * coneMinus P dC
        = (genV P A C ^ k * (1 - P)) * coneMinus P dC := by rw [mul_assoc, h1mPNm]
      _ = (qgtMinus P A C ^ k * (1 - P)) * coneMinus P dC := by rw [hk3]
      _ = qgtMinus P A C ^ k * coneMinus P dC := by rw [mul_assoc, h1mPNm]
  · calc
      coneMinus P dC * genV P A C ^ k
        = coneMinus P dC * (P * genV P A C ^ k) := by rw [← mul_assoc, hNmP]
      _ = coneMinus P dC * (P * qgtPlus P A C ^ k) := by rw [hk2]
      _ = coneMinus P dC * qgtPlus P A C ^ k := by rw [← mul_assoc, hNmP]

-- theorem-class: constructive endpoint
/-- **Stage `𝔘₄` Theorem (`stage_U4_finite_horizon_telescopic_push_pull_partial_sums`)**:
In any associative ring `B` with idempotent `P * P = P`, seeds `A C dA : B`, and truncation
horizons `N M : ℕ`:
1. **Exact Partial-Sum Push–Pull Intertwining on `N_+(A)` and `N_-(C)`**:
   * `geomPartialSum (qgtPlus P A C) N * conePlus P A =
       conePlus P A * geomPartialSum (qgtMinus P A C) N`,
   * `geomPartialSum (genV P A C) N * conePlus P A =
       geomPartialSum (qgtPlus P A C) N * conePlus P A`,
   * `conePlus P A * geomPartialSum (genV P A C) N =
       conePlus P A * geomPartialSum (qgtMinus P A C) N`,
   * `geomPartialSum (qgtMinus P A C) N * coneMinus P C =
       coneMinus P C * geomPartialSum (qgtPlus P A C) N`,
   * `geomPartialSum (genV P A C) N * coneMinus P C =
       geomPartialSum (qgtMinus P A C) N * coneMinus P C`.
2. **Exact Telescopic Remainder Identity**:
   * `(1 - qgtPlus P A C) * geomPartialSum (qgtPlus P A C) N * conePlus P A =
       (1 - genV P A C ^ N) * conePlus P A`,
   * `(1 - genV P A C) * geomPartialSum (genV P A C) N * conePlus P A =
       (1 - genV P A C ^ N) * conePlus P A`.
3. **Two-Sided Truncated Legendre–Schur Differential Sandwich for Arbitrary `dA`**:
   * `geomPartialSum (qgtPlus P A C) N * conePlus P dA =
       geomPartialSum (genV P A C) N * conePlus P dA`,
   * `conePlus P dA * geomPartialSum (qgtMinus P A C) M =
       conePlus P dA * geomPartialSum (genV P A C) M`,
   * `geomPartialSum (qgtPlus P A C) N * conePlus P dA * geomPartialSum (qgtMinus P A C) M =
       geomPartialSum (genV P A C) N * conePlus P dA * geomPartialSum (genV P A C) M`. -/
theorem stage_U4_finite_horizon_telescopic_push_pull_partial_sums
    {P : B} (hP : P * P = P) (A C dA : B) (N M : ℕ) :
    -- (1) Partial-sum Push-Pull intertwining on N_+(A) and N_-(C)
    (geomPartialSum (qgtPlus P A C) N * conePlus P A =
        conePlus P A * geomPartialSum (qgtMinus P A C) N ∧
      geomPartialSum (genV P A C) N * conePlus P A =
        geomPartialSum (qgtPlus P A C) N * conePlus P A ∧
      conePlus P A * geomPartialSum (genV P A C) N =
        conePlus P A * geomPartialSum (qgtMinus P A C) N ∧
      geomPartialSum (qgtMinus P A C) N * coneMinus P C =
        coneMinus P C * geomPartialSum (qgtPlus P A C) N ∧
      geomPartialSum (genV P A C) N * coneMinus P C =
        geomPartialSum (qgtMinus P A C) N * coneMinus P C) ∧
    -- (2) Telescopic remainder identity
    ((1 - qgtPlus P A C) * geomPartialSum (qgtPlus P A C) N * conePlus P A =
        (1 - genV P A C ^ N) * conePlus P A ∧
      (1 - genV P A C) * geomPartialSum (genV P A C) N * conePlus P A =
        (1 - genV P A C ^ N) * conePlus P A) ∧
    -- (3) Two-sided truncated Legendre-Schur differential sandwich on dA
    (geomPartialSum (qgtPlus P A C) N * conePlus P dA =
        geomPartialSum (genV P A C) N * conePlus P dA ∧
      conePlus P dA * geomPartialSum (qgtMinus P A C) M =
        conePlus P dA * geomPartialSum (genV P A C) M ∧
      geomPartialSum (qgtPlus P A C) N * conePlus P dA * geomPartialSum (qgtMinus P A C) M =
        geomPartialSum (genV P A C) N * conePlus P dA * geomPartialSum (genV P A C) M) := by
  have hS1 :
      geomPartialSum (qgtPlus P A C) N * conePlus P A =
        conePlus P A * geomPartialSum (qgtMinus P A C) N := by
    dsimp [geomPartialSum]
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact (peirce_push_pull_pow hP A C k).1.1
  have hS2 :
      geomPartialSum (genV P A C) N * conePlus P A =
        geomPartialSum (qgtPlus P A C) N * conePlus P A := by
    dsimp [geomPartialSum]
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact (peirce_push_pull_pow hP A C k).1.2.1
  have hS3 :
      conePlus P A * geomPartialSum (genV P A C) N =
        conePlus P A * geomPartialSum (qgtMinus P A C) N := by
    dsimp [geomPartialSum]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact (peirce_push_pull_pow hP A C k).1.2.2
  have hS4 :
      geomPartialSum (qgtMinus P A C) N * coneMinus P C =
        coneMinus P C * geomPartialSum (qgtPlus P A C) N := by
    dsimp [geomPartialSum]
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact (peirce_push_pull_pow hP A C k).2.1
  have hS5 :
      geomPartialSum (genV P A C) N * coneMinus P C =
        geomPartialSum (qgtMinus P A C) N * coneMinus P C := by
    dsimp [geomPartialSum]
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact (peirce_push_pull_pow hP A C k).2.2.1
  have hTelGeom : ∀ (k : ℕ) (X : B), (1 - X) * geomPartialSum X k = 1 - X ^ k := by
    intro k X
    induction k with
    | zero =>
      simp [geomPartialSum]
    | succ m ih =>
      dsimp [geomPartialSum] at ih ⊢
      rw [Finset.sum_range_succ, mul_add, ih]
      have hPow : (1 - X) * X ^ m = X ^ m - X ^ (m + 1) := by
        rw [sub_mul, one_mul, ← pow_succ']
      rw [hPow]
      abel
  have hTelV :
      (1 - genV P A C) * geomPartialSum (genV P A C) N * conePlus P A =
        (1 - genV P A C ^ N) * conePlus P A := by
    rw [hTelGeom N (genV P A C)]
  have hTelQp :
      (1 - qgtPlus P A C) * geomPartialSum (qgtPlus P A C) N * conePlus P A =
        (1 - genV P A C ^ N) * conePlus P A := by
    rw [hTelGeom N (qgtPlus P A C)]
    rw [sub_mul, sub_mul, one_mul, ← (peirce_push_pull_pow hP A C N).1.2.1]
  have hLeftdA :
      geomPartialSum (qgtPlus P A C) N * conePlus P dA =
        geomPartialSum (genV P A C) N * conePlus P dA := by
    dsimp [geomPartialSum]
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact (peirce_sheet_pow_absorption hP A C dA C k).2.1.symm
  have hRightdA :
      conePlus P dA * geomPartialSum (qgtMinus P A C) M =
        conePlus P dA * geomPartialSum (genV P A C) M := by
    dsimp [geomPartialSum]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact (peirce_sheet_pow_absorption hP A C dA C k).2.2.1.symm
  have hSandwich :
      geomPartialSum (qgtPlus P A C) N * conePlus P dA * geomPartialSum (qgtMinus P A C) M =
        geomPartialSum (genV P A C) N * conePlus P dA * geomPartialSum (genV P A C) M := by
    rw [hLeftdA, mul_assoc, hRightdA, ← mul_assoc]
  exact ⟨⟨hS1, hS2, hS3, hS4, hS5⟩, ⟨hTelQp, hTelV⟩, ⟨hLeftdA, hRightdA, hSandwich⟩⟩

end StageU4FiniteHorizonTelescopicPushPullPartialSums

/-! ===========================================================================
    Section 6: Stage `𝔘₅` — Norm-Convergent (`N → ∞`) Analytic Push–Pull Series
    & Analytic Hua–Bergman–Dikin Para-Kähler Metric (`‖V‖ < 1`)
    =========================================================================== -/

section StageU5NormConvergentAnalyticPushPullAndHuaBergmanDikinMetric

variable {B : Type*} [NormedRing B] [CompleteSpace B]

/-- The norm-convergent (`N → ∞`) analytic Legendre–Schur dual coordinate
`η_-^an(P, A, C) := (∑' n : ℕ, (genV P A C) ^ n) * conePlus P A`. -/
def analyticLegendreSchurCoord (P A C : B) : B :=
  (∑' n : ℕ, genV P A C ^ n) * conePlus P A

/-- The norm-convergent (`N → ∞`) analytic Legendre–Schur differential
`dη_-^an(P, A, C, dA) := (∑' n : ℕ, (genV P A C) ^ n) * conePlus P dA * (∑' n : ℕ, (genV P A C) ^ n)`. -/
def analyticLegendreSchurDiff (P A C dA : B) : B :=
  (∑' n : ℕ, genV P A C ^ n) * conePlus P dA * (∑' n : ℕ, genV P A C ^ n)

/-- The norm-convergent (`N → ∞`) analytic Hua–Bergman–Dikin Para-Kähler metric
`G_V^an(P, A, C, dA, dC) := analyticLegendreSchurDiff P A C dA * coneMinus P dC`. -/
def analyticHuaBergmanDikinMetric (P A C dA dC : B) : B :=
  analyticLegendreSchurDiff P A C dA * coneMinus P dC

-- theorem-class: constructive endpoint
/-- **Stage `𝔘₅` Theorem (`stage_U5_norm_convergent_analytic_push_pull_and_hua_bergman_dikin_metric`)**:
In any complete normed algebra `[NormedRing B] [CompleteSpace B]` with idempotent `P * P = P`
and seeds `A C dA dC : B` satisfying `hV : ‖genV P A C‖ < 1`:
1. **Pointwise Sequence Equality of the Three Push–Pull Geometric Series**:
   * `(fun n : ℕ => qgtPlus P A C ^ n * conePlus P A) = (fun n : ℕ => genV P A C ^ n * conePlus P A)`,
   * `(fun n : ℕ => conePlus P A * qgtMinus P A C ^ n) = (fun n : ℕ => genV P A C ^ n * conePlus P A)`.
2. **Norm-Summability & Exact `tsum` Push–Pull Equivariance**:
   * `Summable (fun n : ℕ => genV P A C ^ n)`,
   * `(∑' n : ℕ, qgtPlus P A C ^ n * conePlus P A) = (∑' n : ℕ, conePlus P A * qgtMinus P A C ^ n)`,
   * `(∑' n : ℕ, qgtPlus P A C ^ n * conePlus P A) = (∑' n : ℕ, genV P A C ^ n * conePlus P A)`,
   * `analyticLegendreSchurCoord P A C = Ring.inverse (1 - genV P A C) * conePlus P A`.
3. **Exact Bergman–Krein Inversion of the Analytic Dual Coordinate & Differential**:
   * `(1 - genV P A C) * analyticLegendreSchurCoord P A C = conePlus P A`,
   * `(1 - qgtPlus P A C) * analyticLegendreSchurCoord P A C = conePlus P A`,
   * `(1 - genV P A C) * analyticLegendreSchurDiff P A C dA * (1 - genV P A C) = conePlus P dA`,
   * `(1 - genV P A C) * analyticHuaBergmanDikinMetric P A C dA dC =
       conePlus P dA * (∑' n : ℕ, genV P A C ^ n) * coneMinus P dC`. -/
theorem stage_U5_norm_convergent_analytic_push_pull_and_hua_bergman_dikin_metric
    {P : B} (hP : P * P = P) (A C dA dC : B)
    (hV : ‖genV P A C‖ < 1) :
    -- (1) Pointwise sequence equality of the Push-Pull series
    ((fun n : ℕ => qgtPlus P A C ^ n * conePlus P A) =
        (fun n : ℕ => genV P A C ^ n * conePlus P A) ∧
      (fun n : ℕ => conePlus P A * qgtMinus P A C ^ n) =
        (fun n : ℕ => genV P A C ^ n * conePlus P A)) ∧
    -- (2) Norm-summability & tsum Push-Pull equivariance
    (Summable (fun n : ℕ => genV P A C ^ n) ∧
      (∑' n : ℕ, qgtPlus P A C ^ n * conePlus P A) =
        (∑' n : ℕ, conePlus P A * qgtMinus P A C ^ n) ∧
      (∑' n : ℕ, qgtPlus P A C ^ n * conePlus P A) =
        (∑' n : ℕ, genV P A C ^ n * conePlus P A) ∧
      analyticLegendreSchurCoord P A C =
        Ring.inverse (1 - genV P A C) * conePlus P A) ∧
    -- (3) Bergman-Krein inversion of the analytic coordinate, differential, and metric
    ((1 - genV P A C) * analyticLegendreSchurCoord P A C = conePlus P A ∧
      (1 - qgtPlus P A C) * analyticLegendreSchurCoord P A C = conePlus P A ∧
      (1 - genV P A C) * analyticLegendreSchurDiff P A C dA * (1 - genV P A C) =
        conePlus P dA ∧
      (1 - genV P A C) * analyticHuaBergmanDikinMetric P A C dA dC =
        conePlus P dA * (∑' n : ℕ, genV P A C ^ n) * coneMinus P dC) := by
  have hSeq1 :
      (fun n : ℕ => qgtPlus P A C ^ n * conePlus P A) =
        (fun n : ℕ => genV P A C ^ n * conePlus P A) := by
    funext n
    exact (peirce_push_pull_pow hP A C n).1.2.1.symm
  have hSeq2 :
      (fun n : ℕ => conePlus P A * qgtMinus P A C ^ n) =
        (fun n : ℕ => genV P A C ^ n * conePlus P A) := by
    funext n
    exact ((peirce_push_pull_pow hP A C n).1.1.symm).trans
      (peirce_push_pull_pow hP A C n).1.2.1.symm
  have hSumGeom : Summable (fun n : ℕ => genV P A C ^ n) :=
    summable_geometric_of_norm_lt_one hV
  have hHasSumInv : HasSum (fun n : ℕ => genV P A C ^ n) (Ring.inverse (1 - genV P A C)) :=
    hasSum_geom_series_inverse (genV P A C) hV
  have hTsumInv : (∑' n : ℕ, genV P A C ^ n) = Ring.inverse (1 - genV P A C) :=
    hHasSumInv.tsum_eq
  have hMulLeft : (1 - genV P A C) * (∑' n : ℕ, genV P A C ^ n) = 1 :=
    mul_neg_geom_series (genV P A C) hV
  have hMulRight : (∑' n : ℕ, genV P A C ^ n) * (1 - genV P A C) = 1 :=
    geom_series_mul_neg (genV P A C) hV
  have hInvCoordV : (1 - genV P A C) * analyticLegendreSchurCoord P A C = conePlus P A := by
    dsimp [analyticLegendreSchurCoord]
    rw [← mul_assoc, hMulLeft, one_mul]
  have hPCoord : P * analyticLegendreSchurCoord P A C = analyticLegendreSchurCoord P A C := by
    have hVCoord :
        (1 - genV P A C) * (P * analyticLegendreSchurCoord P A C) =
          (1 - genV P A C) * analyticLegendreSchurCoord P A C := by
      have hVP : (1 - genV P A C) * P = P * (1 - genV P A C) := by peirce_nf hP
      rw [← mul_assoc, hVP, mul_assoc, hInvCoordV]
      peirce_nf hP
    calc
      P * analyticLegendreSchurCoord P A C
        = ((∑' n : ℕ, genV P A C ^ n) * (1 - genV P A C)) *
            (P * analyticLegendreSchurCoord P A C) := by
          rw [hMulRight, one_mul]
      _ = (∑' n : ℕ, genV P A C ^ n) *
            ((1 - genV P A C) * (P * analyticLegendreSchurCoord P A C)) := by
          noncomm_ring
      _ = (∑' n : ℕ, genV P A C ^ n) *
            ((1 - genV P A C) * analyticLegendreSchurCoord P A C) := by
          rw [hVCoord]
      _ = ((∑' n : ℕ, genV P A C ^ n) * (1 - genV P A C)) *
            analyticLegendreSchurCoord P A C := by
          noncomm_ring
      _ = analyticLegendreSchurCoord P A C := by
          rw [hMulRight, one_mul]
  have hInvCoordQp : (1 - qgtPlus P A C) * analyticLegendreSchurCoord P A C = conePlus P A := by
    have hQpP : (1 - qgtPlus P A C) * P = (1 - genV P A C) * P := by
      dsimp [qgtPlus]; peirce_nf hP
    calc
      (1 - qgtPlus P A C) * analyticLegendreSchurCoord P A C
        = (1 - qgtPlus P A C) * (P * analyticLegendreSchurCoord P A C) := by
          rw [hPCoord]
      _ = ((1 - qgtPlus P A C) * P) * analyticLegendreSchurCoord P A C := by
          noncomm_ring
      _ = ((1 - genV P A C) * P) * analyticLegendreSchurCoord P A C := by
          rw [hQpP]
      _ = (1 - genV P A C) * (P * analyticLegendreSchurCoord P A C) := by
          noncomm_ring
      _ = (1 - genV P A C) * analyticLegendreSchurCoord P A C := by
          rw [hPCoord]
      _ = conePlus P A := hInvCoordV
  have hInvDiff :
      (1 - genV P A C) * analyticLegendreSchurDiff P A C dA * (1 - genV P A C) =
        conePlus P dA := by
    dsimp [analyticLegendreSchurDiff]
    calc
      (1 - genV P A C) * ((∑' n : ℕ, genV P A C ^ n) * conePlus P dA *
          (∑' n : ℕ, genV P A C ^ n)) * (1 - genV P A C)
        = ((1 - genV P A C) * (∑' n : ℕ, genV P A C ^ n)) * conePlus P dA *
            ((∑' n : ℕ, genV P A C ^ n) * (1 - genV P A C)) := by
          noncomm_ring
      _ = 1 * conePlus P dA * 1 := by rw [hMulLeft, hMulRight]
      _ = conePlus P dA := by noncomm_ring
  have hInvMetric :
      (1 - genV P A C) * analyticHuaBergmanDikinMetric P A C dA dC =
        conePlus P dA * (∑' n : ℕ, genV P A C ^ n) * coneMinus P dC := by
    dsimp [analyticHuaBergmanDikinMetric, analyticLegendreSchurDiff]
    calc
      (1 - genV P A C) * (((∑' n : ℕ, genV P A C ^ n) * conePlus P dA *
          (∑' n : ℕ, genV P A C ^ n)) * coneMinus P dC)
        = ((1 - genV P A C) * (∑' n : ℕ, genV P A C ^ n)) *
            conePlus P dA * (∑' n : ℕ, genV P A C ^ n) * coneMinus P dC := by
          noncomm_ring
      _ = conePlus P dA * (∑' n : ℕ, genV P A C ^ n) * coneMinus P dC := by
          rw [hMulLeft, one_mul]
  refine ⟨⟨hSeq1, hSeq2⟩,
    ⟨hSumGeom,
     by rw [hSeq1, hSeq2],
     by rw [hSeq1],
     by dsimp [analyticLegendreSchurCoord]; rw [hTsumInv]⟩,
    ⟨hInvCoordV, hInvCoordQp, hInvDiff, hInvMetric⟩⟩

end StageU5NormConvergentAnalyticPushPullAndHuaBergmanDikinMetric

/-! ===========================================================================
    Section 7: Stage `𝔘₆` — Inductive Colimit Continuum Lift & Cyclic Trace
    Blindness vs. Chiral Supertrace Recovery of the Dual Bruhat Deformations
    =========================================================================== -/

section StageU6InductiveColimitContinuumAndChiralSupertraceRecovery

-- theorem-class: constructive endpoint
/-- **Stage `𝔘₆` Theorem (`stage_U6_inductive_colimit_continuum_and_chiral_supertrace_recovery`)**:
1. **Inductive Colimit Continuum Lift (`G : ι → Type*`, `A_inf`)**:
   Given any directed system of operator rings `(G : ι → Type*) [∀ i, Ring (G i)]` with
   transition ring homomorphisms `f : ∀ i j, i ≤ j → G i →+* G j`, a colimit/target ring
   `A_inf` `[Ring A_inf]` with compatible cocone `ι_colim : ∀ i, G i →+* A_inf`, and stage
   elements `P_i A_i C_i : G i` with `hP_i : P_i * P_i = P_i`:
   * Both the primal and dual Bruhat idempotents commute with `ι_colim i`:
     `ι_colim i (bruhatDressedProjector P_i A_i C_i) = bruhatDressedProjector P_inf A_inf_op C_inf_op`,
     `ι_colim i (bruhatDressedDualProjector P_i A_i C_i) = bruhatDressedDualProjector P_inf A_inf_op C_inf_op`,
   * Both continuum Bruhat operators are exact idempotents in `A_inf` satisfying the
     Halmos Two-Projector Cubic Complementarity Identity:
     `bruhatCenteredSum P_inf A_inf_op C_inf_op * bruhatCenteredSum P_inf A_inf_op C_inf_op +
        bruhatOrderingHolonomy P_inf A_inf_op C_inf_op * bruhatOrderingHolonomy P_inf A_inf_op C_inf_op = 1`.
2. **Trace-First Blindness vs. Chiral Supertrace Recovery on the Dual Bruhat Deformations**:
   For any additive group `[AddCommGroup K]` and cyclic trace `tr : G i →+ K`
   (`∀ x y, tr (x * y) = tr (y * x)`):
   * **Ordinary Trace Blindness**:
     `tr (bruhatDressedProjector P_i A_i C_i - P_i) = 0`,
     `tr (bruhatDressedDualProjector P_i A_i C_i - P_i) = 0`, and
     `tr (bruhatOrderingHolonomy P_i A_i C_i) = 0`,
   * **Chiral Supertrace Recovery of the Para-Kähler Metric Trace**:
     `chiralSupertrace tr P_i (bruhatDressedProjector P_i A_i C_i - P_i) = -tr (genV P_i A_i C_i)`,
     `chiralSupertrace tr P_i (bruhatDressedDualProjector P_i A_i C_i - P_i) = -tr (genV P_i A_i C_i)`. -/
theorem stage_U6_inductive_colimit_continuum_and_chiral_supertrace_recovery
    {ι : Type*} [Preorder ι]
    (G : ι → Type*) [∀ i, Ring (G i)]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    {A_inf : Type*} [Ring A_inf]
    (ι_colim : ∀ i : ι, G i →+* A_inf)
    (hι_compat : ∀ i j (hij : i ≤ j) (x : G i), ι_colim j (f i j hij x) = ι_colim i x)
    {i j : ι} (hij : i ≤ j)
    (P_i A_i C_i : G i) (hP_i : P_i * P_i = P_i)
    {K : Type*} [AddCommGroup K] (tr : G i →+ K)
    (hCyclic : ∀ x y : G i, tr (x * y) = tr (y * x)) :
    let of_i := ι_colim i
    let P_inf := of_i P_i
    let A_inf_op := of_i A_i
    let C_inf_op := of_i C_i
    -- (1) Functorial colimit commutation & continuum Halmos complementarity
    (of_i (bruhatDressedProjector P_i A_i C_i) =
        bruhatDressedProjector P_inf A_inf_op C_inf_op ∧
      of_i (bruhatDressedDualProjector P_i A_i C_i) =
        bruhatDressedDualProjector P_inf A_inf_op C_inf_op ∧
      ι_colim j (f i j hij (bruhatDressedProjector P_i A_i C_i)) =
        bruhatDressedProjector P_inf A_inf_op C_inf_op ∧
      bruhatCenteredSum P_inf A_inf_op C_inf_op *
          bruhatCenteredSum P_inf A_inf_op C_inf_op +
        bruhatOrderingHolonomy P_inf A_inf_op C_inf_op *
          bruhatOrderingHolonomy P_inf A_inf_op C_inf_op = 1) ∧
    -- (2) Cyclic trace blindness vs. chiral supertrace recovery
    (tr (bruhatDressedProjector P_i A_i C_i - P_i) = 0 ∧
      tr (bruhatDressedDualProjector P_i A_i C_i - P_i) = 0 ∧
      tr (bruhatOrderingHolonomy P_i A_i C_i) = 0 ∧
      chiralSupertrace tr P_i (bruhatDressedProjector P_i A_i C_i - P_i) =
        -tr (genV P_i A_i C_i) ∧
      chiralSupertrace tr P_i (bruhatDressedDualProjector P_i A_i C_i - P_i) =
        -tr (genV P_i A_i C_i)) := by
  intro of_i P_inf A_inf_op C_inf_op
  have hP_inf : P_inf * P_inf = P_inf := by
    dsimp [P_inf]
    rw [← map_mul, hP_i]
  have hMapPlus :
      of_i (bruhatDressedProjector P_i A_i C_i) =
        bruhatDressedProjector P_inf A_inf_op C_inf_op := by
    dsimp [bruhatDressedProjector, superGrassmannDualChart, amariExpPlus, amariExpMinus,
      conePlus, coneMinus, P_inf, A_inf_op, C_inf_op]
    simp [map_mul, map_add, map_sub, map_neg, map_one]
  have hMapMinus :
      of_i (bruhatDressedDualProjector P_i A_i C_i) =
        bruhatDressedDualProjector P_inf A_inf_op C_inf_op := by
    dsimp [bruhatDressedDualProjector, superGrassmannPrimalChart, amariExpPlus, amariExpMinus,
      conePlus, coneMinus, P_inf, A_inf_op, C_inf_op]
    simp [map_mul, map_add, map_sub, map_neg, map_one]
  have hCompatPlus :
      ι_colim j (f i j hij (bruhatDressedProjector P_i A_i C_i)) =
        bruhatDressedProjector P_inf A_inf_op C_inf_op := by
    rw [hι_compat i j hij, hMapPlus]
  have hHalmosInf :=
    (stage_U2_halmos_two_projector_cubic_complementarity_and_commutator
      hP_inf A_inf_op C_inf_op).2.1.2.2
  -- Trace calculations on G i
  have hQ4 :=
    stage_Q4_theorem_trace_first_blindness_and_chiral_supertrace_recovery
      hP_i tr hCyclic A_i C_i
  have hTrNp : ∀ X : G i, tr (conePlus P_i X) = 0 := fun X =>
    (stage_Q4_theorem_trace_first_blindness_and_chiral_supertrace_recovery
      hP_i tr hCyclic X C_i).1.1
  have hTrNm : ∀ Y : G i, tr (coneMinus P_i Y) = 0 := fun Y =>
    (stage_Q4_theorem_trace_first_blindness_and_chiral_supertrace_recovery
      hP_i tr hCyclic A_i Y).1.2.1
  have hStrNp : ∀ X : G i, chiralSupertrace tr P_i (conePlus P_i X) = 0 := by
    intro X
    dsimp [chiralSupertrace]
    have hSNp : invS P_i * conePlus P_i X = conePlus P_i X := by peirce_nf hP_i
    rw [hSNp, hTrNp X]
  have hStrNm : ∀ Y : G i, chiralSupertrace tr P_i (coneMinus P_i Y) = 0 := by
    intro Y
    dsimp [chiralSupertrace]
    have hSNm : invS P_i * coneMinus P_i Y = -coneMinus P_i Y := by peirce_nf hP_i
    rw [hSNm, map_neg, hTrNm Y, neg_zero]
  have hStrPhi : chiralSupertrace tr P_i (genPhi P_i A_i C_i) = 0 := by
    dsimp [chiralSupertrace]
    have hSPhi : invS P_i * genPhi P_i A_i C_i = genJ P_i A_i C_i := by peirce_nf hP_i
    rw [hSPhi, hQ4.1.2.2.2]
  have hDiffPlus :
      bruhatDressedProjector P_i A_i C_i - P_i =
        genPhi P_i A_i C_i - genSig P_i A_i C_i - conePlus P_i (genV P_i A_i C_i * A_i) := by
    have hVNp : genV P_i A_i C_i * conePlus P_i A_i = conePlus P_i (genV P_i A_i C_i * A_i) := by
      dsimp [conePlus]; peirce_nf hP_i
    rw [← hVNp]
    dsimp [bruhatDressedProjector, superGrassmannDualChart, amariExpPlus, amariExpMinus]
    peirce_nf hP_i
  have hDiffMinus :
      bruhatDressedDualProjector P_i A_i C_i - P_i =
        genPhi P_i A_i C_i - genSig P_i A_i C_i - coneMinus P_i (genV P_i A_i C_i * C_i) := by
    have hVNm : genV P_i A_i C_i * coneMinus P_i C_i = coneMinus P_i (genV P_i A_i C_i * C_i) := by
      dsimp [coneMinus]; peirce_nf hP_i
    rw [← hVNm]
    dsimp [bruhatDressedDualProjector, superGrassmannPrimalChart, amariExpPlus, amariExpMinus]
    peirce_nf hP_i
  have hTrDiffPlus : tr (bruhatDressedProjector P_i A_i C_i - P_i) = 0 := by
    rw [hDiffPlus, map_sub, map_sub, hQ4.1.2.2.1, hQ4.2.2.1.1,
      hTrNp (genV P_i A_i C_i * A_i), sub_zero, sub_zero]
  have hTrDiffMinus : tr (bruhatDressedDualProjector P_i A_i C_i - P_i) = 0 := by
    rw [hDiffMinus, map_sub, map_sub, hQ4.1.2.2.1, hQ4.2.2.1.1,
      hTrNm (genV P_i A_i C_i * C_i), sub_zero, sub_zero]
  have hTrHol : tr (bruhatOrderingHolonomy P_i A_i C_i) = 0 := by
    have hHolSub :
        bruhatOrderingHolonomy P_i A_i C_i =
          (bruhatDressedDualProjector P_i A_i C_i - P_i) -
            (bruhatDressedProjector P_i A_i C_i - P_i) := by
      dsimp [bruhatOrderingHolonomy]
      abel
    rw [hHolSub, map_sub, hTrDiffMinus, hTrDiffPlus, sub_zero]
  have hStrDiffPlus :
      chiralSupertrace tr P_i (bruhatDressedProjector P_i A_i C_i - P_i) =
        -tr (genV P_i A_i C_i) := by
    rw [hDiffPlus]
    dsimp [chiralSupertrace]
    rw [mul_sub, mul_sub, map_sub, map_sub]
    change chiralSupertrace tr P_i (genPhi P_i A_i C_i) -
      chiralSupertrace tr P_i (genSig P_i A_i C_i) -
      chiralSupertrace tr P_i (conePlus P_i (genV P_i A_i C_i * A_i)) =
      -tr (genV P_i A_i C_i)
    rw [hStrPhi, hQ4.2.2.2.2.1, hStrNp (genV P_i A_i C_i * A_i),
      zero_sub, sub_zero]
  have hStrDiffMinus :
      chiralSupertrace tr P_i (bruhatDressedDualProjector P_i A_i C_i - P_i) =
        -tr (genV P_i A_i C_i) := by
    rw [hDiffMinus]
    dsimp [chiralSupertrace]
    rw [mul_sub, mul_sub, map_sub, map_sub]
    change chiralSupertrace tr P_i (genPhi P_i A_i C_i) -
      chiralSupertrace tr P_i (genSig P_i A_i C_i) -
      chiralSupertrace tr P_i (coneMinus P_i (genV P_i A_i C_i * C_i)) =
      -tr (genV P_i A_i C_i)
    rw [hStrPhi, hQ4.2.2.2.2.1, hStrNm (genV P_i A_i C_i * C_i),
      zero_sub, sub_zero]
  exact ⟨⟨hMapPlus, hMapMinus, hCompatPlus, hHalmosInf⟩,
    ⟨hTrDiffPlus, hTrDiffMinus, hTrHol, hStrDiffPlus, hStrDiffMinus⟩⟩

end StageU6InductiveColimitContinuumAndChiralSupertraceRecovery

/-! ===========================================================================
    Section 8: Stage `𝔘₇` — Master Synthesis Unifying Dual Bruhat Halmos
    Complementarity, Klein Bottle `V₄` Isolation, Para-Kähler Super-Grassmannian,
    and Analytic Colimit Closure (`𝔘₁ ≺ … ≺ 𝔘₇`, `𝔓₁ ≺ … ≺ 𝔓₇`, `𝔅₁ ≺ … ≺ 𝔅₇`, `𝔛₁ ≺ … ≺ 𝔛₈`)
    =========================================================================== -/

-- theorem-class: synthesis endpoint
/-- **Master Synthesis Theorem (`dual_bruhat_halmos_klein_seam_colimit_analytic_master_poset`)**:
Unifies the 7-stage Dual Bruhat Halmos–Klein–Colimit–Analytic Poset (`𝔘₁ ≺ … ≺ 𝔘₇`) with:
1. The Para-Kähler Super-Grassmannian Poset (`𝔓₁ ≺ … ≺ 𝔓₇`),
2. The Klein Bottle `V₄` Seam Poset (`𝔅₁ ≺ … ≺ 𝔅₇`), and
3. The Amari–Berezinian Inductive Colimit & Analytic Closure Poset (`𝔛₁ ≺ … ≺ 𝔛₈`). -/
theorem dual_bruhat_halmos_klein_seam_colimit_analytic_master_poset
    {B : Type*} [NormedRing B] [CompleteSpace B]
    {P U : B} (hP : P * P = P) (hU : U * U = 1)
    (hSU : invS P * U = -(U * invS P))
    {A C dA dC : B}
    (hUNp : U * conePlus P A * U = coneMinus P C)
    (hUNm : U * coneMinus P C * U = conePlus P A)
    (hV : ‖genV P A C‖ < 1) (N M : ℕ) :
    -- (1) Acyclicity across the canonical posets (`𝔘`, `𝔓`, `𝔛`)
    (((∀ s : DualBruhatHalmosColimitAnalyticStage,
          ¬ DualBruhatHalmosColimitAnalyticStage.causalEdge s s) ∧
        (∀ a b c : DualBruhatHalmosColimitAnalyticStage,
          DualBruhatHalmosColimitAnalyticStage.causalEdge a b →
            DualBruhatHalmosColimitAnalyticStage.causalEdge b c →
              DualBruhatHalmosColimitAnalyticStage.causalEdge a c) ∧
        DualBruhatHalmosColimitAnalyticStage.coverEdge
          .U1_DualBruhatIdempotentsAndCubicOrderingHolonomy
          .U2_HalmosTwoProjectorCubicComplementarityAndCommutator ∧
        DualBruhatHalmosColimitAnalyticStage.coverEdge
          .U2_HalmosTwoProjectorCubicComplementarityAndCommutator
          .U3_KleinBottleV4WalshHadamardIsolation ∧
        DualBruhatHalmosColimitAnalyticStage.coverEdge
          .U3_KleinBottleV4WalshHadamardIsolation
          .U4_FiniteHorizonTelescopicPushPullPartialSums ∧
        DualBruhatHalmosColimitAnalyticStage.coverEdge
          .U4_FiniteHorizonTelescopicPushPullPartialSums
          .U5_NormConvergentAnalyticPushPullAndHuaBergmanDikinMetric ∧
        DualBruhatHalmosColimitAnalyticStage.coverEdge
          .U5_NormConvergentAnalyticPushPullAndHuaBergmanDikinMetric
          .U6_InductiveColimitContinuumAndChiralSupertraceRecovery ∧
        DualBruhatHalmosColimitAnalyticStage.coverEdge
          .U6_InductiveColimitContinuumAndChiralSupertraceRecovery
          .U7_UnifiedDualBruhatKleinColimitAnalyticClosure) ∧
      (∀ s : ParaKahlerSuperGrassmannianStage,
        ¬ Relation.TransGen ParaKahlerSuperGrassmannianStage.causalEdge s s) ∧
      (∀ s : AmariBerezinianColimitAnalyticStage,
        ¬ Relation.TransGen AmariBerezinianColimitAnalyticStage.causalEdge s s)) ∧
    -- (2) Stages 𝔘₁–𝔘₂: Dual Bruhat idempotents, cubic ordering holonomy & Halmos complementarity
    (bruhatDressedProjector P A C * bruhatDressedProjector P A C =
        bruhatDressedProjector P A C ∧
      bruhatDressedDualProjector P A C * bruhatDressedDualProjector P A C =
        bruhatDressedDualProjector P A C ∧
      bruhatOrderingHolonomy P A C = genV P A C * genJ P A C ∧
      bruhatCenteredSum P A C * bruhatCenteredSum P A C +
          bruhatOrderingHolonomy P A C * bruhatOrderingHolonomy P A C = 1) ∧
    -- (3) Stage 𝔘₃: Fourfold Klein Bottle V₄ Walsh-Hadamard isolation
    (walshHadamardMM P U (bruhatOrderingHolonomy P A C) =
        (4 : ℤ) • bruhatOrderingHolonomy P A C ∧
      walshHadamardPM P U (bruhatCenteredSum P A C) =
        (4 : ℤ) • (invS P - (2 : ℤ) • genSig P A C) ∧
      walshHadamardMP P U (bruhatCenteredSum P A C) =
        (4 : ℤ) • ((2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C)) ∧
    -- (4) Stages 𝔘₄–𝔘₅: Telescopic partial sums & norm-convergent analytic Push-Pull / Dikin metric
    (geomPartialSum (qgtPlus P A C) N * conePlus P dA * geomPartialSum (qgtMinus P A C) M =
        geomPartialSum (genV P A C) N * conePlus P dA * geomPartialSum (genV P A C) M ∧
      (∑' n : ℕ, qgtPlus P A C ^ n * conePlus P A) =
        (∑' n : ℕ, conePlus P A * qgtMinus P A C ^ n) ∧
      (1 - genV P A C) * analyticLegendreSchurDiff P A C dA * (1 - genV P A C) =
        conePlus P dA) := by
  have hU1 := stage_U1_dual_bruhat_idempotents_and_cubic_ordering_holonomy hP A C
  have hU2 := stage_U2_halmos_two_projector_cubic_complementarity_and_commutator hP A C
  have hU3 :=
    stage_U3_klein_bottle_v4_walsh_hadamard_isolation_of_dual_bruhat_pair
      hP hU hSU hUNp hUNm
  have hU4 := stage_U4_finite_horizon_telescopic_push_pull_partial_sums hP A C dA N M
  have hU5 :=
    stage_U5_norm_convergent_analytic_push_pull_and_hua_bergman_dikin_metric
      hP A C dA dC hV
  exact ⟨⟨DualBruhatHalmosColimitAnalyticStage.causalEdge_acyclic,
          ParaKahlerSuperGrassmannianStage.causalEdge_acyclic,
          AmariBerezinianColimitAnalyticStage.causalEdge_acyclic⟩,
    ⟨hU1.2.2.1.1, hU1.2.2.1.2.1, hU1.2.2.2.1, hU2.2.1.2.2⟩,
    ⟨hU3.2.1.1, hU3.2.2.1.2.1, hU3.2.2.1.2.2.1⟩,
    ⟨hU4.2.2.2.2, hU5.2.1.2.1, hU5.2.2.2.2.1⟩⟩

end InfoGeometry.Canonical.DualBruhatHalmosKleinSeamColimitAnalyticPoset

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MoebiusTetraktysKleinBerezinianWeylPoset
import InfoGeometry.Canonical.BerryWilsonLoopHyperplaneCausalTransmutationPoset
import InfoGeometry.Canonical.KleinBottleSeamSumDifferenceConnectionPoset
import InfoGeometry.Canonical.AmariOperatorDuallyFlatGaussianPythagoreanPoset
import InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty
import InfoGeometry.Canonical.SouriauQuantumCramerRaoHelstromBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceEvenObservables
import InfoGeometry.MassSpectrometry.FragmentObservabilityGramian
import InfoGeometry.MassSpectrometry.FiniteExperimentIdentifiability
import Mathlib.Algebra.Colimit.DirectLimit

/-!
===============================================================================
HIVE CONSTITUTIONAL HEADER
===============================================================================
Module: InfoGeometry.Canonical.SupergradedAmariBerezinianColimitObservabilityPoset
Role: Canonical 8-Stage Acyclic Causal Poset (`𝔘₁ ≺ 𝔘₂ ≺ ⋯ ≺ 𝔘₈`) unifying:
  - **Direction A (`𝔘₁ ≺ 𝔘₂ ≺ 𝔘₃`): Supergraded Amari–Berezinian–Weyl Duality**:
    1. `𝔘₁` (`U1_PeirceSuperLUGaussianElimination`): Noncommutative Peirce Super-LU
       factorization of `1 + Φ` (`ℰ_+(A) (1 - Q_+) ℰ_-(C) = 1 + Φ`,
       `ℰ_-(C) (1 - Q_-) ℰ_+(A) = 1 + Φ`) and Super-LU diagonalization of the paired
       Amari Operator Gaussians `𝒢_±` directly to the Berry–Amari skewness factors
       `1 ± Σ` (`ℰ_-(-C) 𝒢_+ ℰ_+(-A) = 1 + Σ`, `ℰ_+(-A) 𝒢_- ℰ_-(-C) = 1 - Σ`),
       together with the `2 × 2` matrix Super-LU factorization `factorL * factorH * factorR = M`,
    2. `𝔘₂` (`U2_BerezinianAmariSuperpotentialAndPowerSeries`): Universal higher-power
       Gramian split (`V^(k+1) = Q_+^(k+1) + Q_-^(k+1)`, `S_P V^(k+1) = Q_+^(k+1) - Q_-^(k+1)`),
       sum/difference connection trace-supertrace duality (`Str(Γ_sum) = tr(Γ_diff)`,
       `Str(Γ_diff) = tr(Γ_sum)`), and Berezinian super-barrier boson/fermion split
       (`superBerezinianBarrier A D = bosonicDetBarrier A - bosonicDetBarrier D`),
    3. `𝔘₃` (`U3_WeylRelativeVolumeAndModularBerezinianShadow`): Weyl gauge invariance
       of the two-sheeted relative volume scale (`LiftedSheetAut.relativeVolumeScale`)
       and equality with the relative modular Berezinian supervolume shadow,
  - **Direction B (`𝔘₄ ≺ 𝔘₅`): Inductive Colimit Lifting of First-Quantized Amari
    Geometry, Klein-Bottle `V₄` Walsh–Hadamard Projectors, & Berry Holonomy**:
    4. `𝔘₄` (`U4_DirectedColimitAmariGaussianAndPythagoreanLift`): Functorial preservation
       of the paired Operator Gaussians `𝒢_±`, Peirce Super-LU diagonalization to `1 ± Σ`,
       Operator Pythagorean Theorem `V² = Q_+² + Q_-² = Σ²`, and direct-limit tracial
       cocone lifting of First-Quantized Amari trace blindness (`τ_∞([n, Σ_n]) = 0`) vs.
       chiral supertrace recovery (`τ_∞([n, S_{P_n} Σ_n]) = τ_∞([n, V_n])`),
    5. `𝔘₅` (`U5_DirectedColimitKleinV4WalshHadamardAndBerryHolonomy`): Functorial lifting
       of the Klein four-group `V₄ = {id, α, β, γ}`, the four scaled Walsh–Hadamard sector
       projectors `P_{++}, P_{+-}, P_{-+}, P_{--}`, the fourfold sum–difference connection
       crossover `[Γ_diff, Φ] = {Γ_sum, J}`, and the continuous Berry rotor causal
       transmutation `J(θ)² = -cos(2θ) V` across scale-refinement homomorphisms,
  - **Direction C (`𝔘₆ ≺ 𝔘₇ ≺ 𝔘₈`): Klein-Seam Parity of `V` vs. `Σ`, Peirce/Stein
    Observability & Experimental Identifiability, and Metriplectic Cramér–Rao Closure**:
    6. `𝔘₆` (`U6_KleinSeamParityOfFisherMetricVsBerrySkewness`): Under the Klein-bottle
       sheet-exchange involution `β(X) = U X U` swapping `N_+ ↔ N_-`, the chiral Gramians
       and paired Gaussians swap (`β(Q_+) = Q_-`, `β(𝒢_+) = 𝒢_-`), placing the Fisher–BKM
       metric `V = Q_+ + Q_-` in the trivial `V₄` character `χ_{++}` (`β(V) = +V`,
       `P_{++}(V) = 4 V`) and the Berry–Amari skewness `Σ = Q_+ - Q_-` in the seam-odd
       character `χ_{+-}` (`β(Σ) = -Σ`, `P_{+-}(Σ) = 4 Σ`). Consequently, unoriented
       seam-symmetrization `X + β(X)` erases `Σ` (`Σ + β(Σ) = 0`), whereas the `χ_{+-}`
       Walsh–Hadamard projector recovers `P_{+-}(𝒢_+) = 2 Σ`,
    7. `𝔘₇` (`U7_PeircePinchingObservabilityAndNilpotentSteinGramian`): Coarse-grained
       even-observable blindness vs. explicit odd-observable separation
       (`even_expectations_iff_equal_blocks`, `exists_odd_hermitian_observable_separating`),
       exact 2-step Stein observability Gramian on square-zero operators (`historyGram_stein`),
       and robust finite-experiment quotient identification (`robust_identification`,
       `robust_observable_class_unique`),
    8. `𝔘₈` (`U8_MetriplecticCramerRaoHelstromMasterClosure`): Full Metriplectic
       Cramér–Rao / Robertson–Schrödinger / Helstrom quantum Fisher closure and
       8-stage master synthesis.
===============================================================================
-/

noncomputable section

namespace InfoGeometry.Canonical.SupergradedAmariBerezinianColimitObservabilityPoset

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder InnerProductSpace
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.Meta
open InfoGeometry.Canonical.BerezinianSuperBarrierBridge
open InfoGeometry.Canonical.WeylGaugeOperatorLift
open InfoGeometry.Canonical.RelativeModularBerezinianBridge
open InfoGeometry.Canonical.RelativeModularOperator
open InfoGeometry.Canonical.RestrictedVolumeCharacter
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RadonNikodymKahlerParaKahlerBregmanPoset
open InfoGeometry.Canonical.BerryWilsonLoopHyperplaneCausalTransmutationPoset
open InfoGeometry.Canonical.KleinBottleSeamSumDifferenceConnectionPoset
open InfoGeometry.Canonical.AmariOperatorDuallyFlatGaussianPythagoreanPoset
open InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceEvenObservables
open InfoGeometry.MassSpectrometry.FragmentObservability
open InfoGeometry.MassSpectrometry

/-!
## Part I: The 8-Stage Acyclic Causal Poset (`𝔘₁ ≺ 𝔘₂ ≺ ⋯ ≺ 𝔘₈`)
-/

/-- The 8-stage causal poset unifying Supergraded Amari–Berezinian–Weyl Duality (`𝔘₁..𝔘₃`),
Inductive Colimit Lifting of Amari/Klein/Berry Geometry (`𝔘₄..𝔘₅`), and Klein-Seam Parity,
Peirce/Stein Observability, & Metriplectic Cramér–Rao Closure (`𝔘₆..𝔘₈`). -/
inductive SupergradedAmariColimitObservabilityStage : Type
  | U1_PeirceSuperLUGaussianElimination
  | U2_BerezinianAmariSuperpotentialAndPowerSeries
  | U3_WeylRelativeVolumeAndModularBerezinianShadow
  | U4_DirectedColimitAmariGaussianAndPythagoreanLift
  | U5_DirectedColimitKleinV4WalshHadamardAndBerryHolonomy
  | U6_KleinSeamParityOfFisherMetricVsBerrySkewness
  | U7_PeircePinchingObservabilityAndNilpotentSteinGramian
  | U8_MetriplecticCramerRaoHelstromMasterClosure
  deriving DecidableEq, Repr, Inhabited

namespace SupergradedAmariColimitObservabilityStage

/-- Strictly monotone integer rank `0..7` witnessing the acyclic causal ordering. -/
def rank : SupergradedAmariColimitObservabilityStage → ℕ
  | .U1_PeirceSuperLUGaussianElimination => 0
  | .U2_BerezinianAmariSuperpotentialAndPowerSeries => 1
  | .U3_WeylRelativeVolumeAndModularBerezinianShadow => 2
  | .U4_DirectedColimitAmariGaussianAndPythagoreanLift => 3
  | .U5_DirectedColimitKleinV4WalshHadamardAndBerryHolonomy => 4
  | .U6_KleinSeamParityOfFisherMetricVsBerrySkewness => 5
  | .U7_PeircePinchingObservabilityAndNilpotentSteinGramian => 6
  | .U8_MetriplecticCramerRaoHelstromMasterClosure => 7

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

/-- Direct causal edge `𝔘_k → 𝔘_{k+1}`. -/
def causalEdge (a b : SupergradedAmariColimitObservabilityStage) : Prop :=
  rank b = rank a + 1

theorem causalEdge_rank_lt {a b : SupergradedAmariColimitObservabilityStage}
    (h : causalEdge a b) : rank a < rank b := by
  dsimp [causalEdge] at h
  omega

theorem transGen_causalEdge_rank_lt {a b : SupergradedAmariColimitObservabilityStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_rank_lt hab
  | tail _ hbc ih => exact lt_trans ih (causalEdge_rank_lt hbc)

/-- **Strict Acyclicity (`𝔘₁ ≺ 𝔘₂ ≺ ⋯ ≺ 𝔘₈`)**: No stage can cycle back to itself. -/
theorem causalEdge_acyclic (s : SupergradedAmariColimitObservabilityStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact Nat.lt_irrefl (rank s) (transGen_causalEdge_rank_lt h)

instance : LinearOrder SupergradedAmariColimitObservabilityStage where
  le a b := rank a ≤ rank b
  lt a b := rank a < rank b
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans
  lt_iff_le_not_ge a b := @lt_iff_le_not_ge Nat _ (rank a) (rank b)
  le_antisymm _ _ h1 h2 := rank_injective (Nat.le_antisymm h1 h2)
  le_total a b := le_total (rank a) (rank b)
  toDecidableLE a b := Nat.decLe (rank a) (rank b)
  toDecidableLT a b := Nat.decLt (rank a) (rank b)
  toDecidableEq := inferInstance

instance : Fintype SupergradedAmariColimitObservabilityStage where
  elems := {
    .U1_PeirceSuperLUGaussianElimination,
    .U2_BerezinianAmariSuperpotentialAndPowerSeries,
    .U3_WeylRelativeVolumeAndModularBerezinianShadow,
    .U4_DirectedColimitAmariGaussianAndPythagoreanLift,
    .U5_DirectedColimitKleinV4WalshHadamardAndBerryHolonomy,
    .U6_KleinSeamParityOfFisherMetricVsBerrySkewness,
    .U7_PeircePinchingObservabilityAndNilpotentSteinGramian,
    .U8_MetriplecticCramerRaoHelstromMasterClosure
  }
  complete x := by cases x <;> simp

theorem card_eq_eight : Fintype.card SupergradedAmariColimitObservabilityStage = 8 := rfl

/-- Monotone representation-depth assignment across `𝔘₁..𝔘₈`. -/
def toRepDepth : SupergradedAmariColimitObservabilityStage → RepDepth
  | .U1_PeirceSuperLUGaussianElimination => .operator
  | .U2_BerezinianAmariSuperpotentialAndPowerSeries => .operator
  | .U3_WeylRelativeVolumeAndModularBerezinianShadow => .transport
  | .U4_DirectedColimitAmariGaussianAndPythagoreanLift => .transport
  | .U5_DirectedColimitKleinV4WalshHadamardAndBerryHolonomy => .transport
  | .U6_KleinSeamParityOfFisherMetricVsBerrySkewness => .transport
  | .U7_PeircePinchingObservabilityAndNilpotentSteinGramian => .thermo
  | .U8_MetriplecticCramerRaoHelstromMasterClosure => .thermo

/-- Monotone ontology meta-level assignment across `𝔘₁..𝔘₈`. -/
def toOntologyMetaLevel : SupergradedAmariColimitObservabilityStage → OntologyMetaLevel
  | .U1_PeirceSuperLUGaussianElimination => .M1_ProjectorClabject
  | .U2_BerezinianAmariSuperpotentialAndPowerSeries => .M1_ProjectorClabject
  | .U3_WeylRelativeVolumeAndModularBerezinianShadow => .M1_ProjectorClabject
  | .U4_DirectedColimitAmariGaussianAndPythagoreanLift => .M2_GrassmannianPowertypeOrbit
  | .U5_DirectedColimitKleinV4WalshHadamardAndBerryHolonomy => .M2_GrassmannianPowertypeOrbit
  | .U6_KleinSeamParityOfFisherMetricVsBerrySkewness => .M2_GrassmannianPowertypeOrbit
  | .U7_PeircePinchingObservabilityAndNilpotentSteinGramian => .M3_ErlangenCasimirMetaLaw
  | .U8_MetriplecticCramerRaoHelstromMasterClosure => .M3_ErlangenCasimirMetaLaw

theorem toRepDepth_monotone {a b : SupergradedAmariColimitObservabilityStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toRepDepth RepDepth.toNat <;>
    decide

theorem toOntologyMetaLevel_monotone {a b : SupergradedAmariColimitObservabilityStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;>
    revert h <;>
    unfold toOntologyMetaLevel OntologyMetaLevel.rank <;>
    decide

end SupergradedAmariColimitObservabilityStage

/-!
## Part II: Direction A (`𝔘₁ ≺ 𝔘₂ ≺ 𝔘₃`) — Supergraded Amari–Berezinian–Weyl Duality
-/

section DirectionA_SupergradedAmariBerezinianWeyl

variable {B : Type*} [Ring B]

/-- **Stage `𝔘₁` Theorem (`u1_peirce_super_lu_and_gaussian_skewness_diagonalization`)**:
In any noncommutative associative ring `B` with Peirce idempotent `P * P = P`:
1. **Cross-Sector Absorption Laws**:
   `Q_+ N_- = 0`, `N_+ Q_+ = 0`, `Q_- N_+ = 0`, and `N_- Q_- = 0`.
2. **Upper-Lower Peirce Super-LU Factorization of `1 + Φ`**:
   `ℰ_+(A) * (1 - Q_+) * ℰ_-(C) = 1 + Φ` and `ℰ_+(-A) * (1 + Φ) * ℰ_-(-C) = 1 - Q_+`.
3. **Lower-Upper Opposite Peirce Super-LU Factorization of `1 + Φ`**:
   `ℰ_-(C) * (1 - Q_-) * ℰ_+(A) = 1 + Φ` and `ℰ_-(-C) * (1 + Φ) * ℰ_+(-A) = 1 - Q_-`.
4. **Two-Sided Unipotent Gramian Invariance & Exact Gaussian Elimination**:
   `ℰ_+(A) * Q_+ * ℰ_-(C) = Q_+`, `ℰ_-(C) * Q_- * ℰ_+(A) = Q_-`,
   `ℰ_+(-A) * 𝒢_+ * ℰ_-(-C) = 1`, and `ℰ_-(-C) * 𝒢_- * ℰ_+(-A) = 1`.
5. **Product of Schur Complements vs. Skew-Schur Complements**:
   `(1 - Q_+) * (1 - Q_-) = 1 - V` while `(1 + Σ) * (1 - Σ) = 1 - V²`. -/
theorem u1_peirce_super_lu_and_gaussian_skewness_diagonalization
    {P : B} (hP : P * P = P) (A C : B) :
    qgtPlus P A C * coneMinus P C = 0 ∧
    conePlus P A * qgtPlus P A C = 0 ∧
    qgtMinus P A C * conePlus P A = 0 ∧
    coneMinus P C * qgtMinus P A C = 0 ∧
    unipotentExpPlus P A * (1 - qgtPlus P A C) * unipotentExpMinus P C =
      1 + genPhi P A C ∧
    unipotentExpPlus P (-A) * (1 + genPhi P A C) * unipotentExpMinus P (-C) =
      1 - qgtPlus P A C ∧
    unipotentExpMinus P C * (1 - qgtMinus P A C) * unipotentExpPlus P A =
      1 + genPhi P A C ∧
    unipotentExpMinus P (-C) * (1 + genPhi P A C) * unipotentExpPlus P (-A) =
      1 - qgtMinus P A C ∧
    unipotentExpPlus P A * qgtPlus P A C * unipotentExpMinus P C =
      qgtPlus P A C ∧
    unipotentExpMinus P C * qgtMinus P A C * unipotentExpPlus P A =
      qgtMinus P A C ∧
    unipotentExpPlus P (-A) * operatorGaussianPlus P A C * unipotentExpMinus P (-C) =
      1 ∧
    unipotentExpMinus P (-C) * operatorGaussianMinus P A C * unipotentExpPlus P (-A) =
      1 ∧
    (1 - qgtPlus P A C) * (1 - qgtMinus P A C) = 1 - genV P A C ∧
    (1 + genSig P A C) * (1 - genSig P A C) = 1 - genV P A C * genV P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold qgtPlus; peirce_nf hP
  · unfold qgtPlus; peirce_nf hP
  · unfold qgtMinus; peirce_nf hP
  · unfold qgtMinus; peirce_nf hP
  · unfold unipotentExpPlus unipotentExpMinus qgtPlus; peirce_nf hP
  · unfold unipotentExpPlus unipotentExpMinus qgtPlus; peirce_nf hP
  · unfold unipotentExpPlus unipotentExpMinus qgtMinus; peirce_nf hP
  · unfold unipotentExpPlus unipotentExpMinus qgtMinus; peirce_nf hP
  · unfold unipotentExpPlus unipotentExpMinus qgtPlus; peirce_nf hP
  · unfold unipotentExpPlus unipotentExpMinus qgtMinus; peirce_nf hP
  · unfold operatorGaussianPlus unipotentExpPlus unipotentExpMinus; peirce_nf hP
  · unfold operatorGaussianMinus unipotentExpPlus unipotentExpMinus; peirce_nf hP
  · unfold qgtPlus qgtMinus; peirce_nf hP
  · peirce_nf hP

/-- **Stage `𝔘₂` Lemma (`u2_gramian_power_sum_and_berezinian_difference`)**:
For every `k : ℕ`, the `(k + 1)`-st power of the Fisher–BKM Casimir `V = Q_+ + Q_-` splits
orthogonally into the sum of the sheet Gramian powers `Q_+^(k+1) + Q_-^(k+1)`, while the
chiral-weighted power `S_P * V^(k+1)` splits into the sheet Gramian difference
`Q_+^(k+1) - Q_-^(k+1)`. -/
theorem u2_gramian_power_sum_and_berezinian_difference
    {P : B} (hP : P * P = P) (A C : B) (k : ℕ) :
    genV P A C ^ (k + 1) = qgtPlus P A C ^ (k + 1) + qgtMinus P A C ^ (k + 1) ∧
    invS P * (genV P A C ^ (k + 1)) = qgtPlus P A C ^ (k + 1) - qgtMinus P A C ^ (k + 1) := by
  have h1 : genV P A C ^ (k + 1) = qgtPlus P A C ^ (k + 1) + qgtMinus P A C ^ (k + 1) := by
    induction k with
    | zero =>
      simp only [Nat.zero_add, pow_one]
      unfold qgtPlus qgtMinus
      peirce_nf hP
    | succ m ih =>
      rw [pow_succ (genV P A C) (m + 1), ih]
      have hCross :
          (qgtPlus P A C ^ (m + 1) + qgtMinus P A C ^ (m + 1)) * genV P A C =
            qgtPlus P A C ^ (m + 1) * qgtPlus P A C +
              qgtMinus P A C ^ (m + 1) * qgtMinus P A C := by
        rw [pow_succ (qgtPlus P A C) m, pow_succ (qgtMinus P A C) m]
        unfold qgtPlus qgtMinus
        peirce_nf hP
      rw [hCross, ← pow_succ (qgtPlus P A C) (m + 1), ← pow_succ (qgtMinus P A C) (m + 1)]
  refine ⟨h1, ?_⟩
  rw [h1, mul_add]
  have hPlus : invS P * qgtPlus P A C ^ (k + 1) = qgtPlus P A C ^ (k + 1) := by
    rw [pow_succ' (qgtPlus P A C) k, ← mul_assoc]
    have h0 : invS P * qgtPlus P A C = qgtPlus P A C := by
      unfold qgtPlus; peirce_nf hP
    rw [h0]
  have hMinus : invS P * qgtMinus P A C ^ (k + 1) = -(qgtMinus P A C ^ (k + 1)) := by
    rw [pow_succ' (qgtMinus P A C) k, ← mul_assoc]
    have h0 : invS P * qgtMinus P A C = -qgtMinus P A C := by
      unfold qgtMinus; peirce_nf hP
    rw [h0, neg_mul]
  rw [hPlus, hMinus, sub_eq_add_neg]

/-- **Stage `𝔘₂` Theorem (`u2_connection_supertrace_duality_and_berezinian_barrier`)**:
1. For any additive functional `tr : B →+ K`, the chiral supertrace swaps the sum connection
   `Γ_sum = ∇_+ + ∇_-` and the difference connection `Γ_diff = ∇_+ - ∇_-`:
   `Str(Γ_sum) = tr(Γ_diff) = tr(∇_+) - tr(∇_-)` and
   `Str(Γ_diff) = tr(Γ_sum) = tr(∇_+) + tr(∇_-)`.
2. On invertible real blocks `A_blk, D_blk : Block ι`, the Berezinian super-barrier
   `superBerezinianBarrier A_blk D_blk` equals the bosonic log-det barrier of `A_blk`
   minus the bosonic log-det barrier of `D_blk`, and is additive under block multiplication. -/
theorem u2_connection_supertrace_duality_and_berezinian_barrier
    {K : Type*} [AddCommGroup K] (tr : B →+ K)
    {P : B} (hP : P * P = P) (W : B)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A_blk D_blk A₁ A₂ D₁ D₂ : Block ι)
    (hA : Matrix.det A_blk ≠ 0) (hD : Matrix.det D_blk ≠ 0)
    (hA₁ : Matrix.det A₁ ≠ 0) (hA₂ : Matrix.det A₂ ≠ 0)
    (hD₁ : Matrix.det D₁ ≠ 0) (hD₂ : Matrix.det D₂ ≠ 0) :
    chiralSupertrace tr P (sheetConnectionSum P W) = tr (sheetConnectionDiff P W) ∧
    chiralSupertrace tr P (sheetConnectionDiff P W) = tr (sheetConnectionSum P W) ∧
    chiralSupertrace tr P (sheetConnectionSum P W) =
      tr (sheetPlusConnection P W) - tr (sheetMinusConnection P W) ∧
    chiralSupertrace tr P (sheetConnectionDiff P W) =
      tr (sheetPlusConnection P W) + tr (sheetMinusConnection P W) ∧
    superBerezinianBarrier A_blk D_blk =
      bosonicDetBarrier A_blk - bosonicDetBarrier D_blk ∧
    superBerezinianBarrier (A₁ * A₂) (D₁ * D₂) =
      superBerezinianBarrier A₁ D₁ + superBerezinianBarrier A₂ D₂ := by
  have hSD1 : invS P * sheetConnectionSum P W = sheetConnectionDiff P W :=
    (sum_difference_chiral_duality_and_squared_split hP W 0).1.1
  have hSD2 : invS P * sheetConnectionDiff P W = sheetConnectionSum P W :=
    (sum_difference_chiral_duality_and_squared_split hP W 0).1.2.2.1
  refine ⟨?_, ?_, ?_, ?_,
    superBerezinianBarrier_eq_bosonic_sub_fermionic A_blk D_blk hA hD,
    superBerezinianBarrier_mul A₁ A₂ D₁ D₂ hA₁ hA₂ hD₁ hD₂⟩
  · unfold chiralSupertrace; rw [hSD1]
  · unfold chiralSupertrace; rw [hSD2]
  · unfold chiralSupertrace; rw [hSD1]; unfold sheetConnectionDiff; exact map_sub tr _ _
  · unfold chiralSupertrace; rw [hSD2]; unfold sheetConnectionSum; exact map_add tr _ _

/-- **Stage `𝔘₃` Theorem (`u3_weyl_relative_volume_and_modular_berezinian_shadow`)**:
1. Common Weyl gauge automorphisms `w : E ≃L[ℝ] E` leave `LiftedSheetAut.relativeVolumeScale`
   invariant, while sequential sheet transport adds `logRelativeVolumePotential`.
2. The restricted volume scale of `relativeModularRestrictedSheetEquiv` equals
   `relativeModularBerezinianShadow`, and its negative logarithm equals
   `relativeModularSupervolumePotential`. -/
theorem u3_weyl_relative_volume_and_modular_berezinian_shadow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (w : E ≃L[ℝ] E) (g h : LiftedSheetAut (E := E))
    {n_mod : ℕ} [Nonempty (Fin n_mod)]
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n_mod)) :
    LiftedSheetAut.relativeVolumeScale { plus := w.trans g.plus, minus := w.trans g.minus } =
      LiftedSheetAut.relativeVolumeScale g ∧
    LiftedSheetAut.logRelativeVolumePotential (LiftedSheetAut.mulTransport g h) =
      LiftedSheetAut.logRelativeVolumePotential g +
        LiftedSheetAut.logRelativeVolumePotential h ∧
    RestrictedSheetEquiv.restrictedVolumeScale (E := (Fin n_mod → ℝ))
      (relativeModularRestrictedSheetEquiv (n := n_mod) qPlus q0Plus qMinus q0Minus) =
      relativeModularBerezinianShadow (n := n_mod) qPlus q0Plus qMinus q0Minus ∧
    -Real.log
      (RestrictedSheetEquiv.restrictedVolumeScale (E := (Fin n_mod → ℝ))
        (relativeModularRestrictedSheetEquiv (n := n_mod) qPlus q0Plus qMinus q0Minus)) =
      relativeModularSupervolumePotential (n := n_mod) qPlus q0Plus qMinus q0Minus :=
  ⟨LiftedSheetAut.relativeVolumeScale_gaugeRescale w g,
   LiftedSheetAut.logRelativeVolumePotential_mulTransport g h,
   relativeModularRestrictedSheetEquiv_restrictedVolumeScale_eq_berezinianShadow
     qPlus q0Plus qMinus q0Minus,
   neg_log_relativeModularRestrictedSheetEquiv_restrictedVolumeScale_eq_supervolumePotential
     qPlus q0Plus qMinus q0Minus⟩

end DirectionA_SupergradedAmariBerezinianWeyl

/-!
## Part III: Direction B (`𝔘₄ ≺ 𝔘₅`) — Inductive Colimit Lifting of First-Quantized Amari Geometry, Klein-Bottle `V₄` Walsh–Hadamard Projectors, & Berry Holonomy
-/

section DirectionB_InductiveColimitLifting

/-- **Stage `𝔘₄` Theorem (`u4_colimit_amari_gaussian_super_lu_and_supertrace_lift`)**:
Given any directed system of rings `(Stage n, f_{m,n})`, a cocone `ι_n : Stage n →+* A_inf`,
and a compatible tracial cocone `τ_n : Stage n →+ K` with `τ_n (x * y) = τ_n (y * x)`:
1. `ι_n` maps the finite-stage paired Operator Gaussians `𝒢_{±,n}` and Gramians `Q_{±,n}`
   compatibly to `𝒢_{±,∞}` and `Q_{±,∞}` in `A_inf`,
2. In the colimit `A_inf`, Peirce Super-LU factorization of `1 + Φ_∞`
   (`ℰ_+(A_∞) (1 - Q_{+,∞}) ℰ_-(C_∞) = 1 + Φ_∞`) and the Operator Pythagorean Theorem
   (`V_∞² = Q_{+,∞}² + Q_{-,∞}² = Σ_∞²`) hold identically,
3. Lifted through `τ_inf := AddCommGroup.DirectLimit.lift Stage f_add K τ hτ_compat`,
   First-Quantized Amari trace blindness and chiral supertrace recovery hold at the direct limit:
   `τ_inf ([n, Σ_n]) = 0`, `τ_inf ([n, S_{P_n} V_n]) = 0`, and
   `τ_inf ([n, S_{P_n} Σ_n]) = τ_inf ([n, V_n])`. -/
theorem u4_colimit_amari_gaussian_super_lu_and_supertrace_lift
    (Stage : ℕ → Type*) [∀ n, Ring (Stage n)]
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+* Stage n)
    [DirectedSystem Stage (fun m n h => (f m n h).toAddMonoidHom)]
    {A_inf : Type*} [Ring A_inf]
    (ι : ∀ n : ℕ, Stage n →+* A_inf)
    {K : Type*} [AddCommGroup K]
    (τ : ∀ n : ℕ, Stage n →+ K)
    (hτ_compat : ∀ m n (h : m ≤ n) (x : Stage m), τ n (f m n h x) = τ m x)
    (hτ_cyclic : ∀ (n : ℕ) (x y : Stage n), τ n (x * y) = τ n (y * x))
    (n : ℕ) (P_n A_n C_n : Stage n) (hP_n : P_n * P_n = P_n) :
    let P_inf := ι n P_n
    let A_inf_op := ι n A_n
    let C_inf_op := ι n C_n
    let f_add : ∀ m l : ℕ, m ≤ l → Stage m →+ Stage l := fun m l h => (f m l h).toAddMonoidHom
    let τ_inf : AddCommGroup.DirectLimit Stage f_add →+ K :=
      AddCommGroup.DirectLimit.lift Stage f_add K τ hτ_compat
    ι n (operatorGaussianPlus P_n A_n C_n) = operatorGaussianPlus P_inf A_inf_op C_inf_op ∧
    ι n (operatorGaussianMinus P_n A_n C_n) = operatorGaussianMinus P_inf A_inf_op C_inf_op ∧
    unipotentExpPlus P_inf A_inf_op * (1 - qgtPlus P_inf A_inf_op C_inf_op) *
        unipotentExpMinus P_inf C_inf_op =
      1 + genPhi P_inf A_inf_op C_inf_op ∧
    genV P_inf A_inf_op C_inf_op * genV P_inf A_inf_op C_inf_op =
      qgtPlus P_inf A_inf_op C_inf_op * qgtPlus P_inf A_inf_op C_inf_op +
        qgtMinus P_inf A_inf_op C_inf_op * qgtMinus P_inf A_inf_op C_inf_op ∧
    genV P_inf A_inf_op C_inf_op * genV P_inf A_inf_op C_inf_op =
      genSig P_inf A_inf_op C_inf_op * genSig P_inf A_inf_op C_inf_op ∧
    τ_inf (AddCommGroup.DirectLimit.of Stage f_add n (genSig P_n A_n C_n)) = 0 ∧
    τ_inf (AddCommGroup.DirectLimit.of Stage f_add n (invS P_n * genV P_n A_n C_n)) = 0 ∧
    τ_inf (AddCommGroup.DirectLimit.of Stage f_add n (invS P_n * genSig P_n A_n C_n)) =
      τ_inf (AddCommGroup.DirectLimit.of Stage f_add n (genV P_n A_n C_n)) := by
  intro P_inf A_inf_op C_inf_op f_add τ_inf
  have hP_inf : P_inf * P_inf = P_inf := by
    dsimp [P_inf]; rw [← map_mul, hP_n]
  have hU1 := u1_peirce_super_lu_and_gaussian_skewness_diagonalization hP_inf A_inf_op C_inf_op
  have hD6 := d6_operator_pythagorean_theorem_and_orthogonal_gramians hP_inf A_inf_op C_inf_op
  have hQ4 := q4_theorem_trace_first_blindness_and_chiral_supertrace_recovery
    (τ n) (hτ_cyclic n) hP_n A_n C_n
  refine ⟨?_, ?_, hU1.2.2.2.2.1, hD6.2.2.2.2.2.2.1, hD6.2.2.2.2.2.2.2.2.1, ?_, ?_, ?_⟩
  · dsimp [P_inf, A_inf_op, C_inf_op]
    unfold operatorGaussianPlus unipotentExpPlus unipotentExpMinus conePlus coneMinus
    simp only [map_mul, map_add, map_sub, map_one]
  · dsimp [P_inf, A_inf_op, C_inf_op]
    unfold operatorGaussianMinus unipotentExpPlus unipotentExpMinus conePlus coneMinus
    simp only [map_mul, map_add, map_sub, map_one]
  · rw [AddCommGroup.DirectLimit.lift_of]; exact hQ4.2.2.2.1
  · rw [AddCommGroup.DirectLimit.lift_of]
    exact hQ4.2.2.2.2.2.2.2.2.2.2.1
  · rw [AddCommGroup.DirectLimit.lift_of, AddCommGroup.DirectLimit.lift_of]
    exact hQ4.2.2.2.2.2.2.2.2.2.2.2.1

/-- **Stage `𝔘₅` Theorem (`u5_colimit_klein_v4_walsh_hadamard_and_berry_holonomy_lift`)**:
Given any ℝ-algebra homomorphism `ι : B_n →ₐ[ℝ] B_inf` (such as a colimit cone map) and a
finite-stage Peirce–Klein datum `(P_n, U_n)` with `P_n * P_n = P_n`, `U_n * U_n = 1`, and
`U_n * P_n * U_n = 1 - P_n`:
1. `ι` preserves the four scaled Walsh–Hadamard sector projectors `P_{++}, P_{+-}, P_{-+}, P_{--}`,
2. In `B_inf`, the Walsh–Hadamard four-sector completeness
   `P_{++}(X) + P_{+-}(X) + P_{-+}(X) + P_{--}(X) = 4 • X` and the fourfold sum–difference
   connection crossover `[Γ_diff, Φ] = {Γ_sum, J}` hold,
3. `ι` preserves the rotated current `J(θ)` and the continuous Berry rotor causal transmutation
   `J_inf(θ) * J_inf(θ) = (-Real.cos (2 * θ)) • V_inf` holds in `B_inf`. -/
theorem u5_colimit_klein_v4_walsh_hadamard_and_berry_holonomy_lift
    {B_n B_inf : Type*} [Ring B_n] [Algebra ℝ B_n] [Ring B_inf] [Algebra ℝ B_inf]
    (ι : B_n →ₐ[ℝ] B_inf)
    {P_n U_n : B_n} (hP_n : P_n * P_n = P_n) (hU_n2 : U_n * U_n = 1)
    (hUP_n : U_n * P_n * U_n = 1 - P_n)
    (W_n A_n C_n X_n : B_n) (θ : ℝ) :
    let P_inf := ι P_n
    let U_inf := ι U_n
    let W_inf := ι W_n
    let A_inf := ι A_n
    let C_inf := ι C_n
    let X_inf := ι X_n
    ι (walshProjPP P_n U_n X_n) = walshProjPP P_inf U_inf X_inf ∧
    ι (walshProjPM P_n U_n X_n) = walshProjPM P_inf U_inf X_inf ∧
    ι (walshProjMP P_n U_n X_n) = walshProjMP P_inf U_inf X_inf ∧
    ι (walshProjMM P_n U_n X_n) = walshProjMM P_inf U_inf X_inf ∧
    walshProjPP P_inf U_inf X_inf + walshProjPM P_inf U_inf X_inf +
        walshProjMP P_inf U_inf X_inf + walshProjMM P_inf U_inf X_inf =
      (4 : ℤ) • X_inf ∧
    kleinAlpha P_inf (kleinBeta U_inf X_inf) = kleinBeta U_inf (kleinAlpha P_inf X_inf) ∧
    kleinGamma P_inf U_inf (kleinGamma P_inf U_inf X_inf) = X_inf ∧
    OperatorAlgebra.PeirceSpine.comm (sheetConnectionDiff P_inf W_inf) (genPhi P_inf A_inf C_inf) =
      OperatorAlgebra.PeirceSpine.anticomm (sheetConnectionSum P_inf W_inf) (genJ P_inf A_inf C_inf) ∧
    ι (rotatedCurrentJ P_n A_n C_n θ) = rotatedCurrentJ P_inf A_inf C_inf θ ∧
    rotatedCurrentJ P_inf A_inf C_inf θ * rotatedCurrentJ P_inf A_inf C_inf θ =
      (-Real.cos (2 * θ)) • genV P_inf A_inf C_inf := by
  intro P_inf U_inf W_inf A_inf C_inf X_inf
  have hP_inf : P_inf * P_inf = P_inf := by
    dsimp [P_inf]; rw [← map_mul, hP_n]
  have hU_inf2 : U_inf * U_inf = 1 := by
    dsimp [U_inf]; rw [← map_mul, hU_n2, map_one]
  have hUP_inf : U_inf * P_inf * U_inf = 1 - P_inf := by
    dsimp [U_inf, P_inf]; rw [← map_mul, ← map_mul, hUP_n, map_sub, map_one]
  have hKlein := seam_reflection_v4_klein_group_closure hP_inf hU_inf2 hUP_inf X_inf
  have hCross := universal_sum_difference_crossover_theorem hP_inf W_inf A_inf C_inf
  have hBerry := stage_W7_trigonometric_berry_rotor_and_wick_transmutation hP_inf A_inf C_inf θ
  refine ⟨?_, ?_, ?_, ?_, ?_,
    hKlein.2.2.2.2.2.1, hKlein.2.2.2.2.2.2, hCross.1.1, ?_, hBerry.2.1.1⟩
  · dsimp [P_inf, U_inf, X_inf]
    unfold walshProjPP kleinAlpha kleinBeta kleinGamma invS
    simp only [map_add, map_sub, map_mul, map_one]
  · dsimp [P_inf, U_inf, X_inf]
    unfold walshProjPM kleinAlpha kleinBeta kleinGamma invS
    simp only [map_add, map_sub, map_mul, map_one]
  · dsimp [P_inf, U_inf, X_inf]
    unfold walshProjMP kleinAlpha kleinBeta kleinGamma invS
    simp only [map_add, map_sub, map_mul, map_one]
  · dsimp [P_inf, U_inf, X_inf]
    unfold walshProjMM kleinAlpha kleinBeta kleinGamma invS
    simp only [map_add, map_sub, map_mul, map_one]
  · unfold walshProjPP walshProjPM walshProjMP walshProjMM
    noncomm_ring
  · dsimp [P_inf, A_inf, C_inf]
    unfold rotatedCurrentJ berryRotor genJ conePlus coneMinus invS
    simp only [map_mul, map_add, map_sub, map_one, AlgHom.map_smul_of_tower]

end DirectionB_InductiveColimitLifting

/-!
## Part IV: Direction C (`𝔘₆ ≺ 𝔘₇ ≺ 𝔘₈`) — Klein-Seam Parity of `V` vs. `Σ`, Peirce/Stein Observability & Experimental Identifiability, and Metriplectic Cramér–Rao Closure
-/

section DirectionC_KleinSeamParityAndObservability

variable {B : Type*} [Ring B]

/-- **Stage `𝔘₆` Theorem (`u6_klein_seam_parity_of_fisher_metric_vs_berry_skewness`)**:
Under the Klein-bottle sheet-exchange involution `β(X) = U X U` with `U² = 1`, `U P U = 1 - P`,
`U N_+ U = N_-`, and `U N_- U = N_+`:
1. **Seam-Exchange of Chiral Gramians & Paired Operator Gaussians**:
   `β(Q_+) = Q_-`, `β(Q_-) = Q_+`, `β(𝒢_+) = 𝒢_-`, and `β(𝒢_-) = 𝒢_+`.
2. **Opposite `V₄` Character Sectors of the Fisher–BKM Metric `V` vs. Berry–Amari Skewness `Σ`**:
   - `V = Q_+ + Q_-` lies in the **trivial `V₄` character `χ_{++}`**:
     `α(V) = V`, `β(V) = V`, `γ(V) = V`, `P_{++}(V) = 4 • V`, and `P_{+-}(V) = 0`.
   - `Σ = Q_+ - Q_-` lies in the **chiral-even, seam-odd `V₄` character `χ_{+-}`**:
     `α(Σ) = Σ`, `β(Σ) = -Σ`, `γ(Σ) = -Σ`, `P_{+-}(Σ) = 4 • Σ`, and `P_{++}(Σ) = 0`.
3. **Unoriented Seam-Quotient Blindness vs. `V₄` Walsh–Hadamard Skewness Recovery**:
   - The unoriented seam-symmetrizer `X + β(X)` preserves `V` (`V + β(V) = 2 • V`) and
     symmetrizes `𝒢_+ + β(𝒢_+) = 2 • (1 + Φ) + V`, but **annihilates `Σ`** (`Σ + β(Σ) = 0`),
   - The seam-antisymmetrizer and `χ_{+-}` Walsh–Hadamard projector recover `Σ`:
     `𝒢_+ - β(𝒢_+) = Σ`, `Σ - β(Σ) = 2 • Σ`, and `P_{+-}(𝒢_+) = 2 • Σ`. -/
theorem u6_klein_seam_parity_of_fisher_metric_vs_berry_skewness
    {P U : B} (hP : P * P = P) (hU2 : U * U = 1) (hUP : U * P * U = 1 - P)
    (A C : B)
    (hUNp : U * conePlus P A * U = coneMinus P C)
    (hUNm : U * coneMinus P C * U = conePlus P A) :
    kleinBeta U (qgtPlus P A C) = qgtMinus P A C ∧
    kleinBeta U (qgtMinus P A C) = qgtPlus P A C ∧
    kleinBeta U (operatorGaussianPlus P A C) = operatorGaussianMinus P A C ∧
    kleinBeta U (operatorGaussianMinus P A C) = operatorGaussianPlus P A C ∧
    kleinAlpha P (genV P A C) = genV P A C ∧
    kleinBeta U (genV P A C) = genV P A C ∧
    kleinGamma P U (genV P A C) = genV P A C ∧
    walshProjPP P U (genV P A C) = (4 : ℤ) • genV P A C ∧
    walshProjPM P U (genV P A C) = 0 ∧
    kleinAlpha P (genSig P A C) = genSig P A C ∧
    kleinBeta U (genSig P A C) = -genSig P A C ∧
    kleinGamma P U (genSig P A C) = -genSig P A C ∧
    walshProjPM P U (genSig P A C) = (4 : ℤ) • genSig P A C ∧
    walshProjPP P U (genSig P A C) = 0 ∧
    genV P A C + kleinBeta U (genV P A C) = (2 : ℤ) • genV P A C ∧
    genSig P A C + kleinBeta U (genSig P A C) = 0 ∧
    operatorGaussianPlus P A C - kleinBeta U (operatorGaussianPlus P A C) = genSig P A C ∧
    walshProjPM P U (operatorGaussianPlus P A C) = (2 : ℤ) • genSig P A C := by
  have hBetaQp : kleinBeta U (qgtPlus P A C) = qgtMinus P A C := by
    unfold kleinBeta qgtPlus qgtMinus
    calc U * (conePlus P A * coneMinus P C) * U
      _ = (U * conePlus P A * 1) * coneMinus P C * U := by noncomm_ring
      _ = (U * conePlus P A * (U * U)) * coneMinus P C * U := by rw [hU2]
      _ = (U * conePlus P A * U) * (U * coneMinus P C * U) := by noncomm_ring
      _ = coneMinus P C * conePlus P A := by rw [hUNp, hUNm]
  have hBetaQm : kleinBeta U (qgtMinus P A C) = qgtPlus P A C := by
    unfold kleinBeta qgtPlus qgtMinus
    calc U * (coneMinus P C * conePlus P A) * U
      _ = (U * coneMinus P C * 1) * conePlus P A * U := by noncomm_ring
      _ = (U * coneMinus P C * (U * U)) * conePlus P A * U := by rw [hU2]
      _ = (U * coneMinus P C * U) * (U * conePlus P A * U) := by noncomm_ring
      _ = conePlus P A * coneMinus P C := by rw [hUNm, hUNp]
  have hV4 := v4_character_eigen_classification hP hU2 hUP (genV P A C) A C
    (by
      have hPl : sheetPlusConnection P (genV P A C) = qgtPlus P A C := by
        unfold sheetPlusConnection qgtPlus; peirce_nf hP
      have hMi : sheetMinusConnection P (genV P A C) = qgtMinus P A C := by
        unfold sheetMinusConnection qgtMinus; peirce_nf hP
      rw [hPl, hMi]
      exact hBetaQp)
    hUNp hUNm
  have hAlphaV : kleinAlpha P (genV P A C) = genV P A C := hV4.1.2.2.2.1
  have hBetaV : kleinBeta U (genV P A C) = genV P A C := hV4.1.2.2.2.2.1
  have hGammaV : kleinGamma P U (genV P A C) = genV P A C := hV4.1.2.2.2.2.2
  have hAlphaSig : kleinAlpha P (genSig P A C) = genSig P A C := hV4.2.1.2.2.2.1
  have hBetaSig : kleinBeta U (genSig P A C) = -genSig P A C := hV4.2.1.2.2.2.2.1
  have hGammaSig : kleinGamma P U (genSig P A C) = -genSig P A C := hV4.2.1.2.2.2.2.2
  have hBetaPhi : kleinBeta U (genPhi P A C) = genPhi P A C := hV4.2.2.1.2.1
  have hBetaGp : kleinBeta U (operatorGaussianPlus P A C) = operatorGaussianMinus P A C := by
    rw [(d3_paired_operator_gaussians_and_polynomial_inversion hP A C).1,
        (d3_paired_operator_gaussians_and_polynomial_inversion hP A C).2.1]
    have hBetaOne : kleinBeta U (1 : B) = 1 := by
      unfold kleinBeta; rw [mul_one, hU2]
    have hAdd : kleinBeta U (1 + genPhi P A C + qgtPlus P A C) =
        kleinBeta U 1 + kleinBeta U (genPhi P A C) + kleinBeta U (qgtPlus P A C) := by
      unfold kleinBeta; noncomm_ring
    rw [hAdd, hBetaOne, hBetaPhi, hBetaQp]
  have hBetaGm : kleinBeta U (operatorGaussianMinus P A C) = operatorGaussianPlus P A C := by
    rw [(d3_paired_operator_gaussians_and_polynomial_inversion hP A C).1,
        (d3_paired_operator_gaussians_and_polynomial_inversion hP A C).2.1]
    have hBetaOne : kleinBeta U (1 : B) = 1 := by
      unfold kleinBeta; rw [mul_one, hU2]
    have hAdd : kleinBeta U (1 + genPhi P A C + qgtMinus P A C) =
        kleinBeta U 1 + kleinBeta U (genPhi P A C) + kleinBeta U (qgtMinus P A C) := by
      unfold kleinBeta; noncomm_ring
    rw [hAdd, hBetaOne, hBetaPhi, hBetaQm]
  have hWalshPP_V : walshProjPP P U (genV P A C) = (4 : ℤ) • genV P A C := by
    unfold walshProjPP
    rw [hAlphaV, hBetaV, hGammaV]
    abel_nf
  have hWalshPM_V : walshProjPM P U (genV P A C) = 0 := by
    unfold walshProjPM
    rw [hAlphaV, hBetaV, hGammaV]
    abel_nf
  have hWalshPM_Sig : walshProjPM P U (genSig P A C) = (4 : ℤ) • genSig P A C := by
    unfold walshProjPM
    rw [hAlphaSig, hBetaSig, hGammaSig]
    abel_nf
  have hWalshPP_Sig : walshProjPP P U (genSig P A C) = 0 := by
    unfold walshProjPP
    rw [hAlphaSig, hBetaSig, hGammaSig]
    abel_nf
  have hWalshPM_Gp : walshProjPM P U (operatorGaussianPlus P A C) = (2 : ℤ) • genSig P A C := by
    have hAlphaGp : kleinAlpha P (operatorGaussianPlus P A C) =
        1 - genPhi P A C + qgtPlus P A C := by
      unfold kleinAlpha operatorGaussianPlus unipotentExpPlus unipotentExpMinus qgtPlus
      peirce_nf hP
    have hGammaGp : kleinGamma P U (operatorGaussianPlus P A C) =
        1 - genPhi P A C + qgtMinus P A C := by
      rw [← (seam_reflection_v4_klein_group_closure hP hU2 hUP (operatorGaussianPlus P A C)).2.2.2.1,
          hBetaGp]
      unfold kleinAlpha operatorGaussianMinus unipotentExpPlus unipotentExpMinus qgtMinus
      peirce_nf hP
    unfold walshProjPM
    rw [hAlphaGp, hBetaGp, hGammaGp,
        (d3_paired_operator_gaussians_and_polynomial_inversion hP A C).1,
        (d3_paired_operator_gaussians_and_polynomial_inversion hP A C).2.1]
    unfold qgtPlus qgtMinus
    peirce_nf hP
  refine ⟨hBetaQp, hBetaQm, hBetaGp, hBetaGm,
    hAlphaV, hBetaV, hGammaV, hWalshPP_V, hWalshPM_V,
    hAlphaSig, hBetaSig, hGammaSig, hWalshPM_Sig, hWalshPP_Sig,
    ?_, ?_, ?_, hWalshPM_Gp⟩
  · rw [hBetaV]; abel_nf
  · rw [hBetaSig, add_neg_cancel]
  · rw [hBetaGp]
    unfold operatorGaussianPlus operatorGaussianMinus unipotentExpPlus unipotentExpMinus
    peirce_nf hP

/-- **Stage `𝔘₇` Theorem (`u7_peirce_pinching_observability_stein_gramian_and_robust_identification`)**:
1. **Coarse-Grained Even-Observable Characterization & Odd-Observable Separation**
   (`even_expectations_iff_equal_blocks`, `exists_odd_hermitian_observable_separating`):
   On `Matrix n n ℂ` with Hermitian projector `P² = P = Pᴴ`, all even observables `O` agree on
   `X` and `Y` (`∀ O, evenGrade P O = O → Tr(O X) = Tr(O Y)`) iff `evenGrade P X = evenGrade P Y`;
   and whenever `X ≠ Y` are Hermitian with `evenGrade P X = evenGrade P Y`, there exists an
   explicit self-adjoint odd observable `O_odd` (`evenGrade P O_odd = 0`) separating
   `Tr(O_odd X) ≠ Tr(O_odd Y)`.
2. **Exact 2-Step Stein Observability Gramian for Nilpotent Dynamics (`K² = 0`)**
   (`historyGram_stein`, `historyGram_stein_unique`):
   Whenever a state transition matrix `K : Matrix ι ι ℝ` satisfies `K ^ 2 = 0`, the 2-step
   observability Gramian `historyGram K C 2` is the unique solution of the discrete Stein
   equation `W - Kᵀ W K = Cᵀ C`.
3. **Robust Finite-Experiment Quotient Identification** (`robust_identification`,
   `robust_observable_class_unique`):
   If a finite experimental condition set `S` separates chemically distinct candidates by `> 2 ε`,
   any two `ε`-fitting candidates `a, b ∈ candidates` are chemically equivalent (`chemical.r a b`)
   and define the same quotient class in `Quotient chemical`. -/
theorem u7_peirce_pinching_observability_stein_gramian_and_robust_identification
    {n : Type*} [Fintype n] [DecidableEq n]
    (P X Y : Matrix n n ℂ) (hP : P * P = P) (hPs : star P = P)
    (hX : star X = X) (hY : star Y = Y) (hne : X ≠ Y) (heven : evenGrade P X = evenGrade P Y)
    {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    (K : Matrix ι ι ℝ) (C : Matrix J ι ℝ) (hK2 : K ^ 2 = 0)
    (W : Matrix ι ι ℝ) (hW : W - K.transpose * W * K = C.transpose * C)
    {M Energy Observation : Type*} [PseudoMetricSpace Observation]
    (F : MultiEnergyForwardModel M Energy Observation)
    (chemical : Setoid M) (candidates : Set M) (S : Finset Energy) (ε : ℝ)
    (hsep : F.RobustlySeparatesOn chemical candidates S ε)
    (observed : Energy → Observation) {a b : M}
    (ha : a ∈ candidates) (hb : b ∈ candidates)
    (hfitA : F.FitsOn S observed ε a) (hfitB : F.FitsOn S observed ε b) :
    ((∀ O : Matrix n n ℂ, evenGrade P O = O → Matrix.trace (O * X) = Matrix.trace (O * Y)) ↔
      evenGrade P X = evenGrade P Y) ∧
    (∃ O : Matrix n n ℂ, star O = O ∧ evenGrade P O = 0 ∧
      Matrix.trace (O * X) ≠ Matrix.trace (O * Y)) ∧
    historyGram K C 2 - K.transpose * historyGram K C 2 * K = C.transpose * C ∧
    W = historyGram K C 2 ∧
    chemical.r a b ∧
    (Quotient.mk chemical a : Quotient chemical) = Quotient.mk chemical b :=
  ⟨even_expectations_iff_equal_blocks P X Y hP hPs,
   exists_odd_hermitian_observable_separating P X Y hX hY hne heven,
   historyGram_stein K C 2 hK2,
   historyGram_stein_unique K C 2 hK2 W hW,
   F.robust_identification chemical candidates S ε hsep observed ha hb hfitA hfitB,
   F.robust_observable_class_unique chemical candidates S ε hsep observed ha hb hfitA hfitB⟩

/-- **Stage `𝔘₈` Theorem (`u8_metriplectic_cramer_rao_helstrom_closure`)**:
Combines the full Metriplectic Cramér–Rao / Robertson–Schrödinger inequality
`g(X, X) * g(Y, Y) ≥ g(X, Y)² + (1 / 4) * Ω(X, Y)²`, the QGT Pythagorean norm-square split
`|QGT(X, Y)|² = g(X, Y)² + (1 / 4) * Ω(X, Y)²`, and the Helstrom SLD Quantum Cramér–Rao bound
`1 / fisherMetric ≤ var` with SLD commutator trace neutrality `Tr(ρ L - L ρ) = 0`. -/
theorem u8_metriplectic_cramer_rao_helstrom_closure
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ψ : InfoGeometry.QuantumGeometry.Projective.NormalizedState H)
    (X_op Y_op : H →L[ℂ] H)
    {n_hel : ℕ} (rho L_sld : Matrix (Fin n_hel) (Fin n_hel) ℝ)
    (var fisherMetric : ℝ) (hI : 0 < fisherMetric) (hQCR : 1 ≤ var * fisherMetric) :
    onsagerDissipativeMetric ψ X_op X_op * onsagerDissipativeMetric ψ Y_op Y_op ≥
      (onsagerDissipativeMetric ψ X_op Y_op) ^ 2 +
        (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X_op Y_op) ^ 2 ∧
    Complex.normSq (InfoGeometry.QuantumGeometry.Projective.QGT ψ X_op Y_op) =
      (InfoGeometry.QuantumGeometry.Projective.fubiniStudyMetric ψ X_op Y_op) ^ 2 +
        (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X_op Y_op) ^ 2 ∧
    1 / fisherMetric ≤ var ∧
    Matrix.trace (rho * L_sld - L_sld * rho) = 0 :=
  ⟨cramerRao_metriplectic_full_bound ψ X_op Y_op,
   onsager_QGT_split ψ X_op Y_op,
   SouriauQuantumCramerRao.quantum_cramer_rao_bound var fisherMetric hI hQCR,
   SouriauQuantumCramerRao.sld_commutator_trace_zero rho L_sld⟩

end DirectionC_KleinSeamParityAndObservability

/-!
## Part V: Master Synthesis Theorem (`𝔘₁ ≺ 𝔘₂ ≺ ⋯ ≺ 𝔘₈`)
-/

/-- **Master Synthesis Theorem (`supergraded_amari_berezinian_colimit_observability_master_synthesis`)**:
Unifies the 8-stage Acyclic Causal Poset (`𝔘₁ ≺ 𝔘₂ ≺ ⋯ ≺ 𝔘₈`), Peirce Super-LU factorization
of `1 + Φ`, two-sided unipotent Gramian invariance (`ℰ_+(A) Q_+ ℰ_-(C) = Q_+`), and exact Gaussian
elimination (`ℰ_+(-A) 𝒢_+ ℰ_-(-C) = 1`), universal higher-power Gramian decomposition and Berezinian
super-barrier split, Weyl-invariant relative volume and modular Berezinian shadow, inductive-colimit
lifting of the paired Operator Gaussians / Super-LU / Operator Pythagorean Theorem / supertrace
recovery / `V₄` Walsh–Hadamard projectors / Berry rotor causal transmutation, Klein-bottle seam
parity separating `V ∈ χ_{++}` from `Σ ∈ χ_{+-}`, Peirce coarse-grained observable pinching vs.
odd-observable separation, 2-step Stein observability Gramian on nilpotent dynamics, robust
finite-experiment identification, and the Metriplectic Cramér–Rao–Helstrom quantum uncertainty bound. -/
theorem supergraded_amari_berezinian_colimit_observability_master_synthesis
    {B : Type*} [Ring B]
    {P U : B} (hP : P * P = P) (hU2 : U * U = 1) (hUP : U * P * U = 1 - P)
    (A C W : B) (k : ℕ)
    (hUNp : U * conePlus P A * U = coneMinus P C)
    (hUNm : U * coneMinus P C * U = conePlus P A)
    {K_tr : Type*} [AddCommGroup K_tr] (tr : B →+ K_tr)
    {ι_blk : Type*} [Fintype ι_blk] [DecidableEq ι_blk]
    (A_blk D_blk : Block ι_blk) (hA_blk : Matrix.det A_blk ≠ 0) (hD_blk : Matrix.det D_blk ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (w_weyl : E ≃L[ℝ] E) (g_aut : LiftedSheetAut (E := E))
    (Stage : ℕ → Type*) [∀ n, Ring (Stage n)]
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+* Stage n)
    [DirectedSystem Stage (fun m n h => (f m n h).toAddMonoidHom)]
    {A_inf : Type*} [Ring A_inf]
    (ι_colim : ∀ n : ℕ, Stage n →+* A_inf)
    (τ : ∀ n : ℕ, Stage n →+ K_tr)
    (hτ_compat : ∀ m n (h : m ≤ n) (x : Stage m), τ n (f m n h x) = τ m x)
    (hτ_cyclic : ∀ (n : ℕ) (x y : Stage n), τ n (x * y) = τ n (y * x))
    (n_st : ℕ) (P_n A_n C_n : Stage n_st) (hP_n : P_n * P_n = P_n)
    {ι_st J_st : Type*} [Fintype ι_st] [DecidableEq ι_st] [Fintype J_st]
    (K_st : Matrix ι_st ι_st ℝ) (C_st : Matrix J_st ι_st ℝ) (hK2 : K_st ^ 2 = 0)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ψ : InfoGeometry.QuantumGeometry.Projective.NormalizedState H)
    (X_op Y_op : H →L[ℂ] H) :
    let f_add : ∀ m l : ℕ, m ≤ l → Stage m →+ Stage l := fun m l h => (f m l h).toAddMonoidHom
    let τ_inf : AddCommGroup.DirectLimit Stage f_add →+ K_tr :=
      AddCommGroup.DirectLimit.lift Stage f_add K_tr τ hτ_compat
    -- 1. 8-Stage Poset Acyclicity & Monotonicity:
    (∀ st : SupergradedAmariColimitObservabilityStage,
      ¬ Relation.TransGen SupergradedAmariColimitObservabilityStage.causalEdge st st) ∧
    Fintype.card SupergradedAmariColimitObservabilityStage = 8 ∧
    -- 2. Stage U1 (Peirce Super-LU Factorization of 1 + Φ & Unipotent Gramian Invariance):
    unipotentExpPlus P A * (1 - qgtPlus P A C) * unipotentExpMinus P C = 1 + genPhi P A C ∧
    unipotentExpMinus P C * (1 - qgtMinus P A C) * unipotentExpPlus P A = 1 + genPhi P A C ∧
    unipotentExpPlus P A * qgtPlus P A C * unipotentExpMinus P C = qgtPlus P A C ∧
    unipotentExpPlus P (-A) * operatorGaussianPlus P A C * unipotentExpMinus P (-C) = 1 ∧
    (1 + genSig P A C) * (1 - genSig P A C) = 1 - genV P A C * genV P A C ∧
    -- 3. Stage U2 & U3 (Power Gramian Split, Connection Supertrace Duality, Berezinian & Weyl):
    genV P A C ^ (k + 1) = qgtPlus P A C ^ (k + 1) + qgtMinus P A C ^ (k + 1) ∧
    invS P * (genV P A C ^ (k + 1)) = qgtPlus P A C ^ (k + 1) - qgtMinus P A C ^ (k + 1) ∧
    chiralSupertrace tr P (sheetConnectionSum P W) = tr (sheetConnectionDiff P W) ∧
    superBerezinianBarrier A_blk D_blk =
      bosonicDetBarrier A_blk - bosonicDetBarrier D_blk ∧
    LiftedSheetAut.relativeVolumeScale { plus := w_weyl.trans g_aut.plus, minus := w_weyl.trans g_aut.minus } =
      LiftedSheetAut.relativeVolumeScale g_aut ∧
    -- 4. Stage U4 (Direct-Limit Lifting of Paired Gaussians & Chiral Supertrace Recovery):
    ι_colim n_st (operatorGaussianPlus P_n A_n C_n) =
      operatorGaussianPlus (ι_colim n_st P_n) (ι_colim n_st A_n) (ι_colim n_st C_n) ∧
    τ_inf (AddCommGroup.DirectLimit.of Stage f_add n_st (genSig P_n A_n C_n)) = 0 ∧
    τ_inf (AddCommGroup.DirectLimit.of Stage f_add n_st (invS P_n * genSig P_n A_n C_n)) =
      τ_inf (AddCommGroup.DirectLimit.of Stage f_add n_st (genV P_n A_n C_n)) ∧
    -- 5. Stage U6 (Klein-Seam Parity of V ∈ χ_{++} vs. Σ ∈ χ_{+-} & Walsh–Hadamard Recovery):
    kleinBeta U (operatorGaussianPlus P A C) = operatorGaussianMinus P A C ∧
    kleinBeta U (genV P A C) = genV P A C ∧
    kleinBeta U (genSig P A C) = -genSig P A C ∧
    genSig P A C + kleinBeta U (genSig P A C) = 0 ∧
    walshProjPM P U (operatorGaussianPlus P A C) = (2 : ℤ) • genSig P A C ∧
    -- 6. Stage U7 & U8 (Nilpotent 2-Step Stein Gramian & Metriplectic Cramér–Rao Bound):
    historyGram K_st C_st 2 - K_st.transpose * historyGram K_st C_st 2 * K_st =
      C_st.transpose * C_st ∧
    onsagerDissipativeMetric ψ X_op X_op * onsagerDissipativeMetric ψ Y_op Y_op ≥
      (onsagerDissipativeMetric ψ X_op Y_op) ^ 2 +
        (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X_op Y_op) ^ 2 := by
  intro f_add τ_inf
  have hStageU1 := u1_peirce_super_lu_and_gaussian_skewness_diagonalization hP A C
  have hStageU2Pow := u2_gramian_power_sum_and_berezinian_difference hP A C k
  have hStageU2 := u2_connection_supertrace_duality_and_berezinian_barrier tr hP W
    A_blk D_blk A_blk A_blk D_blk D_blk hA_blk hD_blk hA_blk hA_blk hD_blk hD_blk
  have hStageU4 := u4_colimit_amari_gaussian_super_lu_and_supertrace_lift
    Stage f ι_colim τ hτ_compat hτ_cyclic n_st P_n A_n C_n hP_n
  have hStageU6 := u6_klein_seam_parity_of_fisher_metric_vs_berry_skewness
    hP hU2 hUP A C hUNp hUNm
  refine ⟨SupergradedAmariColimitObservabilityStage.causalEdge_acyclic,
    SupergradedAmariColimitObservabilityStage.card_eq_eight,
    hStageU1.2.2.2.2.1, hStageU1.2.2.2.2.2.2.1, hStageU1.2.2.2.2.2.2.2.2.1,
    hStageU1.2.2.2.2.2.2.2.2.2.2.1, hStageU1.2.2.2.2.2.2.2.2.2.2.2.2.2,
    hStageU2Pow.1, hStageU2Pow.2, hStageU2.1, hStageU2.2.2.2.2.1,
    LiftedSheetAut.relativeVolumeScale_gaugeRescale w_weyl g_aut,
    hStageU4.1, hStageU4.2.2.2.2.2.1, hStageU4.2.2.2.2.2.2.2,
    hStageU6.2.2.1, hStageU6.2.2.2.2.2.1, hStageU6.2.2.2.2.2.2.2.2.2.2.1,
    hStageU6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hStageU6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    historyGram_stein K_st C_st 2 hK2,
    cramerRao_metriplectic_full_bound ψ X_op Y_op⟩

end InfoGeometry.Canonical.SupergradedAmariBerezinianColimitObservabilityPoset

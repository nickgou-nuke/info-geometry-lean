/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Epistemology.ChentsovUniquenessContinuous
import InfoGeometry.Epistemology.FisherNaturalGradientSteepest
import InfoGeometry.Synthesis.MathlibCliffordUniversalLiftSynthesis
import InfoGeometry.Synthesis.Cl11ChiralVolumeNilpotentQuotientSynthesis
import InfoGeometry.Clifford.Cl11JordanWignerCARBridge
import InfoGeometry.Canonical.ParaKahlerLagrangianDimension
import InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow

/-!
# Categorical Synthesis: Five Theorem Corridors

This module gathers results from five mathematical areas: Chentsov classification under
explicit repository hypotheses, the universal algebra `CliffordAlgebra q11Form`,
para-Kähler null-sheet identities, linear sheet-swap algebra and its set-level orbit
quotient, and finite-stage Jordan–Wigner/KMS readouts on an algebraic UHF carrier.
The sections are an organizational synthesis, not a formally defined causal poset or a
proof that the five carriers are connected by maps. In particular, the final conjunction
has independent carrier data and establishes no quotient-to-KMS compatibility.

1. **Archetype I — Chentsov Scale and Natural-Gradient Representation (`ChentsovUniquenessContinuous` ↔ `FisherNaturalGradientSteepest`)**:
   - Proves left scalar homogeneity `fisherMetric_smul_left` of the Fisher metric and
     establishes the exact covector representation equivalence
     `scaledFisher_represents_covector_iff`: for any nonzero Chentsov scale `c ≠ 0`, a
     tangent vector `n` represents a covector `ℓ` with respect to `scaledFisherFamily c`
     if and only if `n = c⁻¹ • fisherNaturalGradient P ℓ`.
   - Combines `chentsov_classification_of_seqContinuous` with scaled natural gradient
     representation in `chentsov_unique_scale_and_steepest_ascent`.

2. **Archetype II — Universal `CliffordAlgebra q11Form` Nilpotent Ladder** (`MathlibCliffordUniversalLiftSynthesis`):
   - Defines the universal lightcone nilpotent ladder generators `abstractNullPlus` and
     `abstractNullMinus` and the chiral idempotents `abstractVacProj` and `abstractOccProj`
     in `CliffordAlgebra q11Form`.
   - Proves in `CliffordAlgebra q11Form` via `cl11MatrixAlgEquiv.injective` that
     `abstractNullPlus * abstractNullPlus = 0`, `abstractNullMinus * abstractNullMinus = 0`,
     `abstractNullPlus * abstractNullMinus + abstractNullMinus * abstractNullPlus = 1`,
     that `abstractChiralVolume` anticommutes with `abstractNullPlus` and `abstractNullMinus`
     and satisfies `abstractOccProj - abstractVacProj = abstractChiralVolume`, and that
     `abstractVacProj` and `abstractOccProj` form orthogonal idempotents summing to `1`.

3. **Archetype III — Para-Kähler Null-Sheet Identities** (`ParaKahlerLagrangianDimension`):
   - Proves that for any para-Kähler structure `(g, omega, K)`, the diagonal pairings on
     the projected eigen-sheets vanish (`paraKahler_projPlus_projPlus_zero`,
     `paraKahler_projMinus_projMinus_zero`), so the pseudo-Riemannian metric `g` reduces
     identically to the off-diagonal cross-sheet pairing
     `paraKahler_metric_eq_offDiagonal_pairing` and the symplectic form `omega` reduces to
     the antisymmetric cross-sheet pairing `paraKahler_symplectic_eq_offDiagonal_pairing`.

4. **Archetype IV — Linear Sheet-Swap Identities and Set-Level Z₂ Orbit Quotient**:
   - Defines `IsMobiusTwist K M` (`M.comp K = -(K.comp M)`) and proves that any Möbius
     twist swaps the eigen-sheets `InTPlus K` and `InTMinus K` and intertwines the
     spectral projectors `paraProjectorPlus K` and `paraProjectorMinus K`.
   - For any sheet-swapping involution `C` (`IsSheetSwapInvolution K C`), proves that
     `J = inducedComplexStructure C K = C.comp K` is an almost-complex linear endomorphism
     (`J.comp J = -LinearMap.id`). The metric sign-flip and symplectic-preservation
     identities additionally assume that `C` preserves `g`.
   - Forms the set-level orbit quotient `MobiusInvolutionQuotient hC` for the involution
     `C`, proves the cross-sheet quotient identification
     `paraProjectorPlus_eq_paraProjectorMinus_in_mobiusQuotient`, and descends the quadratic
     form to `mobiusQuotientQuadratic`. No topology or orientation structure is defined.

5. **Archetype V — Finite Jordan–Wigner Carrier and Stage-Selected Modular-KMS Readout** (`Cl11ChiralVolumeNilpotentQuotientSynthesis` ↔ `ColimitAttentionTomitaFlow`):
   - Injects finite stage-`k` Jordan–Wigner matrix operators and global chirality into the
     algebraic UHF direct-limit carrier `Carrier` (`colimitJWCreation`,
     `colimitJWAnnihilation`, `colimitGlobalChirality`), proving nilpotency, same-site CAR,
     and chiral parity negation. This is not an algebra equivalence from a general
     `Cl(k,k)` tensor tower to `Carrier`.
   - Bundles colimit Jordan–Wigner chiral parity, a set-level involution-quotient identity,
     and a cross-stage trace-cycling identity for a stage-selected functional in
     `risingSea_three_arrow_colimit_mobius_kms`. These are simultaneous facts with
     independent carriers and parameters; no quotient-to-KMS compatibility or global
     analytic modular flow on `Carrier` is established.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Synthesis.CategoricalInevitabilityPosetSynthesis

open scoped Matrix BigOperators
open Matrix
open InfoGeometry.Epistemology.ChentsovMetricInvariance
open InfoGeometry.Epistemology.ChentsovUniqueness
open InfoGeometry.Epistemology.ChentsovUniquenessContinuous
open InfoGeometry.Epistemology.FisherNaturalGradientSteepest
open InfoGeometry.Epistemology.SubmersionSplitFinrank
open InfoGeometry.Clifford.Cl11Matrix (J1 Eminus Eplus)
open InfoGeometry.Canonical.SuperGrassmannianManifold
open InfoGeometry.Canonical.NaturalGradientSubmersionFlow
open InfoGeometry.Canonical.GrandEpistemicGeometricSynthesis
open InfoGeometry.Canonical.ParaKahlerLagrangianDimension
open InfoGeometry.Synthesis.MathlibCliffordUniversalLiftSynthesis
open InfoGeometry.Synthesis.Cl11ChiralVolumeNilpotentQuotientSynthesis
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.AttentionGNSBridge
open InfoGeometry.QuantumContext.AttentionStageColimitState
open InfoGeometry.QuantumContext.MatrixStageSelectedFunctional
open InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow

/-!
## Archetype I: Chentsov Scale Classification and Scaled Natural-Gradient Representation
-/

section MetricInevitability

variable {α : Type} [Fintype α]

/-- Left scalar homogeneity of the Fisher metric:
`fisherMetric P (c • u) v = c * fisherMetric P u v`. -/
theorem fisherMetric_smul_left (P : ProbInterior α) (c : ℝ) (u v : α → ℝ) :
    fisherMetric P (c • u) v = c * fisherMetric P u v := by
  have h := congrArg (fun f : (α → ℝ) →ₗ[ℝ] ℝ => f v) ((fisherBilin P).map_smul c u)
  simpa only [LinearMap.smul_apply, smul_eq_mul, fisherBilin_apply] using h

/-- **Scaled Fisher Natural Gradient Representation Equivalence**:
For any interior distribution `P : ProbInterior α`, covector `ℓ : α → ℝ`, tangent vector
`n : α → ℝ` (`∑ a, n a = 0`), and nonzero Chentsov scale `c ≠ 0`, `n` represents the
covector pairing `w ↦ ∑ a, ℓ a * w a` on the simplex tangent space under
`scaledFisherFamily c` if and only if `n = c⁻¹ • fisherNaturalGradient P ℓ`. -/
theorem scaledFisher_represents_covector_iff
    (P : ProbInterior α) (ℓ n : α → ℝ) (hn : ∑ a, n a = 0)
    (c : ℝ) (hc : c ≠ 0) :
    (∀ w : α → ℝ, ∑ a, w a = 0 → (scaledFisherFamily c).g α P n w = ∑ a, ℓ a * w a) ↔
      n = c⁻¹ • fisherNaturalGradient P ℓ := by
  constructor
  · intro hrep
    have hcn_tan : ∑ a, (c • n) a = 0 := by
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hn, mul_zero]
    have hcn_rep : ∀ w : α → ℝ, ∑ a, w a = 0 → fisherMetric P (c • n) w = ∑ a, ℓ a * w a := by
      intro w hw
      rw [fisherMetric_smul_left]
      exact hrep w hw
    have hcn_eq : c • n = fisherNaturalGradient P ℓ :=
      fisherNaturalGradient_unique P ℓ (c • n) hcn_tan hcn_rep
    calc
      n = (1 : ℝ) • n := (one_smul ℝ n).symm
      _ = (c⁻¹ * c) • n := by rw [inv_mul_cancel₀ hc]
      _ = c⁻¹ • (c • n) := mul_smul c⁻¹ c n
      _ = c⁻¹ • fisherNaturalGradient P ℓ := by rw [hcn_eq]
  · intro hn_eq w hw
    change c * fisherMetric P n w = ∑ a, ℓ a * w a
    rw [← fisherMetric_smul_left, hn_eq, smul_smul, mul_inv_cancel₀ hc, one_smul]
    exact fisherMetric_naturalGradient P ℓ w hw

/-- **Chentsov Scale and Scaled Natural-Gradient Representation**:
For a fixed `F : InvariantMetricFamily` with `hF : SeqContinuous F`, the repository's
`chentsov_classification_of_seqContinuous` yields a unique scale `c : ℝ` representing `F`
on all finite-simplex tangent spaces as `scaledFisherFamily c`. For this scale, when
`c ≠ 0`, tangent-covector representation is equivalent to
`n = c⁻¹ • fisherNaturalGradient P ℓ`. The scale is unique for the fixed `F`; it is not
fixed independently of `F`, and the result retains the displayed invariance and continuity
hypotheses encoded by these repository types. -/
theorem chentsov_unique_scale_and_steepest_ascent
    (F : InvariantMetricFamily) (hF : SeqContinuous F) :
    ∃! c : ℝ,
      (∀ (β : Type) [Fintype β] [DecidableEq β] (P : ProbInterior β) (u v : β → ℝ),
        ∑ i, u i = 0 → ∑ i, v i = 0 → F.g β P u v = (scaledFisherFamily c).g β P u v) ∧
      (c ≠ 0 → ∀ (β : Type) [Fintype β] [DecidableEq β] (P : ProbInterior β) (ℓ n : β → ℝ),
        ∑ a, n a = 0 →
          ((∀ w : β → ℝ, ∑ a, w a = 0 → F.g β P n w = ∑ a, ℓ a * w a) ↔
            n = c⁻¹ • fisherNaturalGradient P ℓ)) := by
  obtain ⟨c, hc, h_uniq⟩ := chentsov_classification_of_seqContinuous F hF
  refine ⟨c, ⟨hc, ?_⟩, ?_⟩
  · intro hc_ne β _ _ P ℓ n hn
    have h_eq :
        (∀ w : β → ℝ, ∑ a, w a = 0 → F.g β P n w = ∑ a, ℓ a * w a) ↔
          (∀ w : β → ℝ, ∑ a, w a = 0 → (scaledFisherFamily c).g β P n w = ∑ a, ℓ a * w a) := by
      refine forall_congr' (fun w => imp_congr_right (fun hw => ?_))
      rw [hc β P n w hn hw]
    exact h_eq.trans (scaledFisher_represents_covector_iff P ℓ n hn c hc_ne)
  · rintro c' ⟨hc', _⟩
    exact h_uniq c' hc'

end MetricInevitability

/-!
## Archetype II: Universal `CliffordAlgebra q11Form` Nilpotent Ladder
-/

section CellInevitability

/-- The universal positive lightcone nilpotent ladder element
`n₊ = (1/2) • (ι(1, 0) + ι(0, 1))` in `CliffordAlgebra q11Form`. -/
noncomputable def abstractNullPlus : CliffordAlgebra q11Form :=
  (1 / 2 : ℝ) • (CliffordAlgebra.ι q11Form (1, 0) + CliffordAlgebra.ι q11Form (0, 1))

/-- The universal negative lightcone nilpotent ladder element
`n₋ = (1/2) • (ι(1, 0) - ι(0, 1))` in `CliffordAlgebra q11Form`. -/
noncomputable def abstractNullMinus : CliffordAlgebra q11Form :=
  (1 / 2 : ℝ) • (CliffordAlgebra.ι q11Form (1, 0) - CliffordAlgebra.ι q11Form (0, 1))

/-- `abstractNullPlus` coincides with `abstractWittPlus = (1/2) • ι(1, 1)` by linearity of
`CliffordAlgebra.ι q11Form`. -/
theorem abstractNullPlus_eq_abstractWittPlus :
    abstractNullPlus = abstractWittPlus := by
  unfold abstractNullPlus abstractWittPlus
  rw [← map_add]
  have h_pair : ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) = ((1 : ℝ), (1 : ℝ)) := by
    ext <;> norm_num
  rw [h_pair]

/-- `abstractNullMinus` coincides with `abstractWittMinus = (1/2) • ι(1, -1)` by linearity of
`CliffordAlgebra.ι q11Form`. -/
theorem abstractNullMinus_eq_abstractWittMinus :
    abstractNullMinus = abstractWittMinus := by
  unfold abstractNullMinus abstractWittMinus
  rw [← map_sub]
  have h_pair : ((1 : ℝ), (0 : ℝ)) - ((0 : ℝ), (1 : ℝ)) = ((1 : ℝ), (-1 : ℝ)) := by
    ext <;> norm_num
  rw [h_pair]

/-- Image of `abstractNullPlus` under `cl11MatrixAlgEquiv` is the upper-triangular nilpotent
matrix unit `!![0, 1; 0, 0]`. -/
theorem cl11MatrixAlgEquiv_abstractNullPlus :
    cl11MatrixAlgEquiv abstractNullPlus = !![(0 : ℝ), 1; 0, 0] := by
  unfold abstractNullPlus
  rw [map_smul, map_add, cl11MatrixAlgEquiv_ι, cl11MatrixAlgEquiv_ι]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11MatrixLinear, J1, Eminus]

/-- Image of `abstractNullMinus` under `cl11MatrixAlgEquiv` is the lower-triangular nilpotent
matrix unit `!![0, 0; 1, 0]`. -/
theorem cl11MatrixAlgEquiv_abstractNullMinus :
    cl11MatrixAlgEquiv abstractNullMinus = !![(0 : ℝ), 0; 1, 0] := by
  unfold abstractNullMinus
  rw [map_smul, map_sub, cl11MatrixAlgEquiv_ι, cl11MatrixAlgEquiv_ι]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11MatrixLinear, J1, Eminus]

/-- Image of `abstractChiralVolume` under `cl11MatrixAlgEquiv` is the diagonal chiral grading
matrix `!![-1, 0; 0, 1]`. -/
theorem cl11MatrixAlgEquiv_chiralVolume :
    cl11MatrixAlgEquiv abstractChiralVolume = !![(-1 : ℝ), 0; 0, 1] := by
  rw [cl11MatrixAlgEquiv_apply, cl11MatrixAlgHom_abstractChiralVolume]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11ChiralVolume, J1, Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- `abstractNullPlus` is nilpotent of order 2 in `CliffordAlgebra q11Form`: `n₊² = 0`. -/
theorem abstractNullPlus_sq_zero :
    abstractNullPlus * abstractNullPlus = 0 := by
  apply cl11MatrixAlgEquiv.injective
  rw [map_mul, map_zero, cl11MatrixAlgEquiv_abstractNullPlus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- `abstractNullMinus` is nilpotent of order 2 in `CliffordAlgebra q11Form`: `n₋² = 0`. -/
theorem abstractNullMinus_sq_zero :
    abstractNullMinus * abstractNullMinus = 0 := by
  apply cl11MatrixAlgEquiv.injective
  rw [map_mul, map_zero, cl11MatrixAlgEquiv_abstractNullMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Canonical Fermi anticommutation relation `{n₊, n₋} = 1` in `CliffordAlgebra q11Form`. -/
theorem abstractNullPlus_anticomm_abstractNullMinus :
    abstractNullPlus * abstractNullMinus + abstractNullMinus * abstractNullPlus = 1 := by
  apply cl11MatrixAlgEquiv.injective
  rw [map_add, map_mul, map_mul, map_one,
    cl11MatrixAlgEquiv_abstractNullPlus, cl11MatrixAlgEquiv_abstractNullMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- The difference `n₊ - n₋` recovers the negative-square Clifford generator `ι(0, 1)`. -/
theorem abstractNullPlus_sub_abstractNullMinus_eq_ι_eMinus :
    abstractNullPlus - abstractNullMinus = CliffordAlgebra.ι q11Form (0, 1) := by
  apply cl11MatrixAlgEquiv.injective
  rw [map_sub, cl11MatrixAlgEquiv_abstractNullPlus,
    cl11MatrixAlgEquiv_abstractNullMinus, cl11MatrixAlgEquiv_ι]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11MatrixLinear, J1, Eminus]

/-- The sum `n₊ + n₋` recovers the positive-square Clifford generator `ι(1, 0)`. -/
theorem abstractNullPlus_add_abstractNullMinus_eq_ι_ePlus :
    abstractNullPlus + abstractNullMinus = CliffordAlgebra.ι q11Form (1, 0) := by
  apply cl11MatrixAlgEquiv.injective
  rw [map_add, cl11MatrixAlgEquiv_abstractNullPlus,
    cl11MatrixAlgEquiv_abstractNullMinus, cl11MatrixAlgEquiv_ι]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11MatrixLinear, J1, Eminus]

/-- Left chiral grading absorption on `abstractNullPlus`: `ω * n₊ = -n₊`. -/
theorem abstractChiralVolume_mul_abstractNullPlus :
    abstractChiralVolume * abstractNullPlus = -abstractNullPlus := by
  apply cl11MatrixAlgEquiv.injective
  rw [map_mul, map_neg, cl11MatrixAlgEquiv_chiralVolume,
    cl11MatrixAlgEquiv_abstractNullPlus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Right chiral grading absorption on `abstractNullPlus`: `n₊ * ω = n₊`. -/
theorem abstractNullPlus_mul_abstractChiralVolume :
    abstractNullPlus * abstractChiralVolume = abstractNullPlus := by
  apply cl11MatrixAlgEquiv.injective
  rw [map_mul, cl11MatrixAlgEquiv_abstractNullPlus,
    cl11MatrixAlgEquiv_chiralVolume]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Left chiral grading absorption on `abstractNullMinus`: `ω * n₋ = n₋`. -/
theorem abstractChiralVolume_mul_abstractNullMinus :
    abstractChiralVolume * abstractNullMinus = abstractNullMinus := by
  apply cl11MatrixAlgEquiv.injective
  rw [map_mul, cl11MatrixAlgEquiv_chiralVolume,
    cl11MatrixAlgEquiv_abstractNullMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Right chiral grading absorption on `abstractNullMinus`: `n₋ * ω = -n₋`. -/
theorem abstractNullMinus_mul_abstractChiralVolume :
    abstractNullMinus * abstractChiralVolume = -abstractNullMinus := by
  apply cl11MatrixAlgEquiv.injective
  rw [map_mul, map_neg, cl11MatrixAlgEquiv_abstractNullMinus,
    cl11MatrixAlgEquiv_chiralVolume]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Universal chiral volume anticommutation with `abstractNullPlus`:
`ω * n₊ + n₊ * ω = 0`. -/
theorem abstractChiralVolume_anticomm_abstractNullPlus :
    abstractChiralVolume * abstractNullPlus +
      abstractNullPlus * abstractChiralVolume = 0 := by
  rw [abstractChiralVolume_mul_abstractNullPlus,
    abstractNullPlus_mul_abstractChiralVolume, neg_add_cancel]

/-- Universal chiral volume anticommutation with `abstractNullMinus`:
`ω * n₋ + n₋ * ω = 0`. -/
theorem abstractChiralVolume_anticomm_abstractNullMinus :
    abstractChiralVolume * abstractNullMinus +
      abstractNullMinus * abstractChiralVolume = 0 := by
  rw [abstractChiralVolume_mul_abstractNullMinus,
    abstractNullMinus_mul_abstractChiralVolume, add_neg_cancel]

/-- Universal vacuum projector `P₊ = n₊ * n₋` in `CliffordAlgebra q11Form`. -/
noncomputable def abstractVacProj : CliffordAlgebra q11Form :=
  abstractNullPlus * abstractNullMinus

/-- Universal occupied projector `P₋ = n₋ * n₊` in `CliffordAlgebra q11Form`. -/
noncomputable def abstractOccProj : CliffordAlgebra q11Form :=
  abstractNullMinus * abstractNullPlus

/-- `abstractVacProj` is idempotent in `CliffordAlgebra q11Form`: `P₊ * P₊ = P₊`. -/
theorem abstractVacProj_idempotent :
    abstractVacProj * abstractVacProj = abstractVacProj := by
  unfold abstractVacProj
  apply cl11MatrixAlgEquiv.injective
  rw [map_mul, map_mul, cl11MatrixAlgEquiv_abstractNullPlus,
    cl11MatrixAlgEquiv_abstractNullMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- `abstractOccProj` is idempotent in `CliffordAlgebra q11Form`: `P₋ * P₋ = P₋`. -/
theorem abstractOccProj_idempotent :
    abstractOccProj * abstractOccProj = abstractOccProj := by
  unfold abstractOccProj
  apply cl11MatrixAlgEquiv.injective
  rw [map_mul, map_mul, cl11MatrixAlgEquiv_abstractNullPlus,
    cl11MatrixAlgEquiv_abstractNullMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Mutual orthogonality `P₊ * P₋ = 0` in `CliffordAlgebra q11Form`. -/
theorem abstractVacProj_mul_abstractOccProj_zero :
    abstractVacProj * abstractOccProj = 0 := by
  unfold abstractVacProj abstractOccProj
  apply cl11MatrixAlgEquiv.injective
  rw [map_mul, map_mul, map_mul, map_zero,
    cl11MatrixAlgEquiv_abstractNullPlus, cl11MatrixAlgEquiv_abstractNullMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Mutual orthogonality `P₋ * P₊ = 0` in `CliffordAlgebra q11Form`. -/
theorem abstractOccProj_mul_abstractVacProj_zero :
    abstractOccProj * abstractVacProj = 0 := by
  unfold abstractVacProj abstractOccProj
  apply cl11MatrixAlgEquiv.injective
  rw [map_mul, map_mul, map_mul, map_zero,
    cl11MatrixAlgEquiv_abstractNullPlus, cl11MatrixAlgEquiv_abstractNullMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Resolution of the identity `P₊ + P₋ = 1` in `CliffordAlgebra q11Form`. -/
theorem abstractVacProj_add_abstractOccProj_eq_one :
    abstractVacProj + abstractOccProj = 1 :=
  abstractNullPlus_anticomm_abstractNullMinus

/-- Spectral decomposition of the universal chiral volume element:
`P₋ - P₊ = abstractChiralVolume` in `CliffordAlgebra q11Form`. -/
theorem abstractOccProj_sub_abstractVacProj_eq_chiralVolume :
    abstractOccProj - abstractVacProj = abstractChiralVolume := by
  unfold abstractVacProj abstractOccProj
  apply cl11MatrixAlgEquiv.injective
  rw [map_sub, map_mul, map_mul,
    cl11MatrixAlgEquiv_abstractNullPlus, cl11MatrixAlgEquiv_abstractNullMinus,
    cl11MatrixAlgEquiv_chiralVolume]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

end CellInevitability

/-!
## Archetype III: Para-Kähler Null-Sheet Identities and Cross-Sheet Pairings
-/

section NullSheetInevitability

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Diagonal pairing on the positive projected eigen-sheet vanishes identically:
`g (P⁺ v) (P⁺ w) = 0`. -/
theorem paraKahler_projPlus_projPlus_zero
    {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K) (v w : V) :
    g (paraProjectorPlus K v) (paraProjectorPlus K w) = 0 :=
  tplus_isotropic hK hPK (paraProjectorPlus_in_TPlus K hK v) (paraProjectorPlus_in_TPlus K hK w)

/-- Diagonal pairing on the negative projected eigen-sheet vanishes identically:
`g (P⁻ v) (P⁻ w) = 0`. -/
theorem paraKahler_projMinus_projMinus_zero
    {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K) (v w : V) :
    g (paraProjectorMinus K v) (paraProjectorMinus K w) = 0 :=
  tminus_isotropic hK hPK (paraProjectorMinus_in_TMinus K hK v) (paraProjectorMinus_in_TMinus K hK w)

/-- **Off-Diagonal Cross-Sheet Metric Theorem**:
For any para-Kähler structure `(g, omega, K)`, the pseudo-Riemannian metric `g v w` reduces
identically to the symmetric off-diagonal cross-sheet pairing between `P⁺` and `P⁻`. -/
theorem paraKahler_metric_eq_offDiagonal_pairing
    {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K) (v w : V) :
    g v w =
      g (paraProjectorPlus K v) (paraProjectorMinus K w) +
        g (paraProjectorMinus K v) (paraProjectorPlus K w) := by
  conv_lhs => rw [← para_projectors_sum_id K v, ← para_projectors_sum_id K w]
  rw [map_add g, LinearMap.add_apply, map_add, map_add,
    paraKahler_projPlus_projPlus_zero hK hPK v w,
    paraKahler_projMinus_projMinus_zero hK hPK v w,
    zero_add, add_zero]

/-- **Quadratic Cross-Sheet Norm Identity**:
The self-pairing `g v v` of any vector `v` equals twice the cross-sheet pairing between its
positive and negative spectral projections `P⁺ v` and `P⁻ v`. -/
theorem paraKahler_self_metric_eq_two_mul_cross_sheet
    {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K) (v : V) :
    g v v = 2 * g (paraProjectorPlus K v) (paraProjectorMinus K v) := by
  rw [paraKahler_metric_eq_offDiagonal_pairing hK hPK v v,
    hPK.g_symm (paraProjectorMinus K v) (paraProjectorPlus K v), ← two_mul]

/-- Spectral decomposition of the para-complex involution: `K w = P⁺ w - P⁻ w`. -/
theorem apply_eq_paraProjectorPlus_sub_paraProjectorMinus
    (K : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (w : V) :
    K w = paraProjectorPlus K w - paraProjectorMinus K w := by
  have hsum := para_projectors_sum_id K w
  have hplus : K (paraProjectorPlus K w) = paraProjectorPlus K w :=
    paraProjectorPlus_in_TPlus K hK w
  have hminus : K (paraProjectorMinus K w) = -paraProjectorMinus K w :=
    paraProjectorMinus_in_TMinus K hK w
  calc
    K w = K (paraProjectorPlus K w + paraProjectorMinus K w) := by rw [hsum]
    _ = K (paraProjectorPlus K w) + K (paraProjectorMinus K w) := map_add K _ _
    _ = paraProjectorPlus K w - paraProjectorMinus K w := by
      rw [hplus, hminus, sub_eq_add_neg]

/-- Inverse compatibility identity for a para-Kähler structure: `omega v w = g v (K w)`. -/
theorem omega_eq_g_comp_K
    {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K) (v w : V) :
    omega v w = g v (K w) := by
  rw [hPK.compatibility v (K w), hK.involutive w]

/-- **Off-Diagonal Cross-Sheet Symplectic Theorem**:
For any para-Kähler structure `(g, omega, K)`, the symplectic form `omega v w` reduces
identically to the antisymmetric off-diagonal cross-sheet pairing
`g (P⁻ v) (P⁺ w) - g (P⁺ v) (P⁻ w)`. -/
theorem paraKahler_symplectic_eq_offDiagonal_pairing
    {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K) (v w : V) :
    omega v w =
      g (paraProjectorMinus K v) (paraProjectorPlus K w) -
        g (paraProjectorPlus K v) (paraProjectorMinus K w) := by
  rw [omega_eq_g_comp_K hK hPK v w,
    apply_eq_paraProjectorPlus_sub_paraProjectorMinus K hK w]
  conv_lhs => rw [← para_projectors_sum_id K v]
  rw [map_add, LinearMap.add_apply, map_sub, map_sub,
    paraKahler_projPlus_projPlus_zero hK hPK v w,
    paraKahler_projMinus_projMinus_zero hK hPK v w,
    zero_sub, sub_zero, add_comm, ← sub_eq_add_neg]

end NullSheetInevitability

/-!
## Archetype IV: Linear Sheet-Swap Identities and a Set-Level Involution Quotient
-/

section MobiusTwistInevitability

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Möbius Twist Anticommutation Predicate**:
An endomorphism `M : V →ₗ[ℝ] V` is called a Möbius twist relative to `K` here when it
anticommutes with the para-complex polarization `K` (`M ∘ K = - (K ∘ M)`). This predicate
alone imposes no involutivity, invertibility, or nonzero condition on `M`. -/
def IsMobiusTwist (K M : V →ₗ[ℝ] V) : Prop :=
  M.comp K = -(K.comp M)

/-- Pointwise anticommutation `K (M v) = - M (K v)` for any Möbius twist `M`. -/
theorem mobiusTwist_apply_comm (K M : V →ₗ[ℝ] V) (hM : IsMobiusTwist K M) (v : V) :
    K (M v) = -M (K v) := by
  have h := congrArg (fun f : V →ₗ[ℝ] V => f v) hM
  simp only [LinearMap.comp_apply, LinearMap.neg_apply] at h
  exact neg_eq_iff_eq_neg.mp h.symm

/-- Every Möbius twist maps the positive eigen-sheet `T⁺` into the negative eigen-sheet `T⁻`. -/
theorem mobiusTwist_maps_tplus_to_tminus (K M : V →ₗ[ℝ] V) (hM : IsMobiusTwist K M)
    {v : V} (hv : InTPlus K v) : InTMinus K (M v) := by
  dsimp [InTMinus]
  have hv' : K v = v := hv
  rw [mobiusTwist_apply_comm K M hM v, hv']

/-- Every Möbius twist maps the negative eigen-sheet `T⁻` into the positive eigen-sheet `T⁺`. -/
theorem mobiusTwist_maps_tminus_to_tplus (K M : V →ₗ[ℝ] V) (hM : IsMobiusTwist K M)
    {v : V} (hv : InTMinus K v) : InTPlus K (M v) := by
  dsimp [InTPlus]
  have hv' : K v = -v := hv
  rw [mobiusTwist_apply_comm K M hM v, hv', map_neg, neg_neg]

/-- Every Möbius twist intertwines `paraProjectorPlus K` with `paraProjectorMinus K`:
`P⁻ (M v) = M (P⁺ v)`. -/
theorem mobiusTwist_intertwines_paraProjectorPlus (K M : V →ₗ[ℝ] V)
    (hM : IsMobiusTwist K M) (v : V) :
    paraProjectorMinus K (M v) = M (paraProjectorPlus K v) := by
  dsimp [paraProjectorMinus, paraProjectorPlus]
  rw [mobiusTwist_apply_comm K M hM v, smul_neg, sub_neg_eq_add,
    map_add, LinearMap.map_smul, LinearMap.map_smul]

/-- Every Möbius twist intertwines `paraProjectorMinus K` with `paraProjectorPlus K`:
`P⁺ (M v) = M (P⁻ v)`. -/
theorem mobiusTwist_intertwines_paraProjectorMinus (K M : V →ₗ[ℝ] V)
    (hM : IsMobiusTwist K M) (v : V) :
    paraProjectorPlus K (M v) = M (paraProjectorMinus K v) := by
  dsimp [paraProjectorMinus, paraProjectorPlus]
  rw [mobiusTwist_apply_comm K M hM v, smul_neg, ← sub_eq_add_neg,
    map_sub, LinearMap.map_smul, LinearMap.map_smul]

/-- **Sheet-Swapping Involution Predicate**:
`C` is an involution (`C ∘ C = id`) that anticommutes with `K` (`IsMobiusTwist K C`). -/
def IsSheetSwapInvolution (K C : V →ₗ[ℝ] V) : Prop :=
  C.comp C = LinearMap.id ∧ IsMobiusTwist K C

/-- Pointwise involution identity `C (C v) = v` for a sheet-swapping involution. -/
theorem sheetSwapInvolution_apply_sq (K C : V →ₗ[ℝ] V)
    (hC : IsSheetSwapInvolution K C) (v : V) :
    C (C v) = v :=
  congrArg (fun f : V →ₗ[ℝ] V => f v) hC.1

/-- **Induced Complex Structure `J = C ∘ K`**:
Composing a sheet-swapping involution `C` with a para-complex structure `K` yields an
almost-complex structure `J = C ∘ K`. -/
def inducedComplexStructure (C K : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  C.comp K

/-- **Elliptic Square Identity (`J² = -id`)**:
For any para-complex structure `K` (`K² = id`) and sheet-swapping involution `C`
(`C² = id`, `C ∘ K = - K ∘ C`), the induced operator `J = C ∘ K` satisfies `J ∘ J = -id`. -/
theorem inducedComplexStructure_sq_eq_neg_id (K C : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (hC : IsSheetSwapInvolution K C) :
    (inducedComplexStructure C K).comp (inducedComplexStructure C K) = -LinearMap.id := by
  ext v
  dsimp [inducedComplexStructure]
  rw [mobiusTwist_apply_comm K C hC.2 (K v), map_neg, hK.involutive v,
    sheetSwapInvolution_apply_sq K C hC v]

/-- The induced complex structure `J = C ∘ K` is itself a Möbius twist relative to `K`. -/
theorem inducedComplexStructure_isMobiusTwist (K C : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (hC : IsSheetSwapInvolution K C) :
    IsMobiusTwist K (inducedComplexStructure C K) := by
  ext v
  dsimp [inducedComplexStructure]
  rw [hK.involutive v, mobiusTwist_apply_comm K C hC.2 (K v), neg_neg, hK.involutive v]

/-- **Metric Sign Flip under `J = C ∘ K` (`g (J v) (J w) = - g v w`)**:
When `C` preserves the para-Kähler metric `g`, the induced complex structure `J = C ∘ K`
is metric anti-invariant. -/
theorem inducedComplexStructure_metric_neg
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K)
    (hC_iso : ∀ u w, g (C u) (C w) = g u w) (v w : V) :
    g (inducedComplexStructure C K v) (inducedComplexStructure C K w) = -g v w := by
  dsimp [inducedComplexStructure]
  rw [hC_iso (K v) (K w), metric_anti_invariance g omega K hK hPK v w]

/-- **Symplectic Invariance under `J = C ∘ K` (`omega (J v) (J w) = omega v w`)**:
When `C` is a `g`-isometric sheet-swapping involution, the induced complex structure
`J = C ∘ K` preserves the para-Kähler symplectic form `omega`. -/
theorem inducedComplexStructure_symplectic_invariant
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K)
    (hC : IsSheetSwapInvolution K C) (hC_iso : ∀ u w, g (C u) (C w) = g u w) (v w : V) :
    omega (inducedComplexStructure C K v) (inducedComplexStructure C K w) = omega v w := by
  rw [omega_eq_g_comp_K hK hPK, omega_eq_g_comp_K hK hPK]
  dsimp [inducedComplexStructure]
  have h_anti := metric_anti_invariance g omega K hK hPK v (K w)
  rw [hK.involutive w] at h_anti
  rw [mobiusTwist_apply_comm K C hC.2 (K w), hK.involutive w,
    map_neg, hC_iso (K v) w, h_anti, neg_neg]

/-! ### Set-Level Orbit Quotient by the Sheet-Swapping Involution -/

/-- The $\mathbb{Z}_2$ orbit equivalence relation generated by a sheet-swapping involution `C`:
`u ~ w` if and only if `u = w` or `w = C u`. -/
def mobiusInvolutionRel (C : V →ₗ[ℝ] V) (u w : V) : Prop :=
  u = w ∨ w = C u

/-- Reflexivity of `mobiusInvolutionRel`. -/
theorem mobiusInvolutionRel_refl (C : V →ₗ[ℝ] V) (u : V) :
    mobiusInvolutionRel C u u :=
  Or.inl rfl

/-- Symmetry of `mobiusInvolutionRel` for any sheet-swapping involution `C`. -/
theorem mobiusInvolutionRel_symm {K C : V →ₗ[ℝ] V}
    (hC : IsSheetSwapInvolution K C) {u w : V}
    (huw : mobiusInvolutionRel C u w) :
    mobiusInvolutionRel C w u := by
  rcases huw with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (sheetSwapInvolution_apply_sq K C hC u).symm

/-- Transitivity of `mobiusInvolutionRel` for any sheet-swapping involution `C`. -/
theorem mobiusInvolutionRel_trans {K C : V →ₗ[ℝ] V}
    (hC : IsSheetSwapInvolution K C) {u v w : V}
    (huv : mobiusInvolutionRel C u v) (hvw : mobiusInvolutionRel C v w) :
    mobiusInvolutionRel C u w := by
  rcases huv with rfl | rfl <;> rcases hvw with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (sheetSwapInvolution_apply_sq K C hC u).symm

/-- The $\mathbb{Z}_2$ setoid on `V` associated to a sheet-swapping involution `hC`. -/
def mobiusInvolutionSetoid {K C : V →ₗ[ℝ] V}
    (hC : IsSheetSwapInvolution K C) : Setoid V where
  r := mobiusInvolutionRel C
  iseqv := ⟨mobiusInvolutionRel_refl C, mobiusInvolutionRel_symm hC, mobiusInvolutionRel_trans hC⟩

/-- The set-level orbit quotient `V / ⟨C⟩` identifying each state `u` with its partner `C u`.
No topology, orientation, or additional geometric structure is supplied by this quotient. -/
abbrev MobiusInvolutionQuotient {K C : V →ₗ[ℝ] V}
    (hC : IsSheetSwapInvolution K C) : Type _ :=
  Quotient (mobiusInvolutionSetoid hC)

/-- **Coordinate-Free Möbius Quotient Sheet Identification**:
In `MobiusInvolutionQuotient hC`, the positive sheet projection `P⁺ v` of any state `v` is
identified with the negative sheet projection `P⁻ (C v)` of its twisted partner `C v`. -/
theorem paraProjectorPlus_eq_paraProjectorMinus_in_mobiusQuotient
    {K C : V →ₗ[ℝ] V} (hC : IsSheetSwapInvolution K C) (v : V) :
    (Quotient.mk (mobiusInvolutionSetoid hC) (paraProjectorPlus K v) :
        MobiusInvolutionQuotient hC) =
      Quotient.mk (mobiusInvolutionSetoid hC) (paraProjectorMinus K (C v)) := by
  apply Quotient.sound
  exact Or.inr (mobiusTwist_intertwines_paraProjectorPlus K C hC.2 v)

/-- Any `C`-invariant bilinear form `g` has constant quadratic values `g u u = g w w` on
`mobiusInvolutionRel C` orbits. -/
theorem metric_self_eq_of_mobiusInvolutionRel
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {C : V →ₗ[ℝ] V}
    (hC_iso : ∀ u w, g (C u) (C w) = g u w) {u w : V}
    (huw : mobiusInvolutionRel C u w) :
    g u u = g w w := by
  rcases huw with rfl | rfl
  · rfl
  · exact (hC_iso u u).symm

/-- Well-defined descent of the quadratic form `v ↦ g v v` to `MobiusInvolutionQuotient hC`. -/
def mobiusQuotientQuadratic
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {K C : V →ₗ[ℝ] V}
    (hC : IsSheetSwapInvolution K C) (hC_iso : ∀ u w, g (C u) (C w) = g u w) :
    MobiusInvolutionQuotient hC → ℝ :=
  Quotient.lift (fun v => g v v)
    (fun _ _ huw => metric_self_eq_of_mobiusInvolutionRel g hC_iso huw)

@[simp]
theorem mobiusQuotientQuadratic_mk
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {K C : V →ₗ[ℝ] V}
    (hC : IsSheetSwapInvolution K C) (hC_iso : ∀ u w, g (C u) (C w) = g u w) (v : V) :
    mobiusQuotientQuadratic g hC hC_iso
      (Quotient.mk (mobiusInvolutionSetoid hC) v) = g v v :=
  rfl

/-! ### Concrete Non-Vacuity Witness on `Fin 2 → ℝ` -/

/-- The canonical sheet-swapping reflection `v ↦ (v₀, -v₁)` on `Fin 2 → ℝ` relative to
the coordinate-swap para-complex structure `swapK`. -/
def swapSheetInvolution : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v i := if i = 0 then v 0 else -v 1
  map_add' u v := by
    ext i
    fin_cases i <;> simp [add_comm]
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [mul_neg]

@[simp]
theorem swapSheetInvolution_apply_zero (v : Fin 2 → ℝ) :
    swapSheetInvolution v 0 = v 0 := rfl

@[simp]
theorem swapSheetInvolution_apply_one (v : Fin 2 → ℝ) :
    swapSheetInvolution v 1 = -v 1 := rfl

/-- `swapSheetInvolution` is a Möbius twist relative to `swapK`. -/
theorem swapSheetInvolution_isMobiusTwist :
    IsMobiusTwist swapK swapSheetInvolution := by
  ext v i
  fin_cases i <;>
    simp [swapSheetInvolution, swapK, LinearMap.funLeft_apply]

/-- `swapSheetInvolution` is a sheet-swapping involution (`C² = id` and `C ∘ swapK = - swapK ∘ C`). -/
theorem isSheetSwapInvolution_canonical :
    IsSheetSwapInvolution swapK swapSheetInvolution := by
  refine ⟨?_, swapSheetInvolution_isMobiusTwist⟩
  ext v i
  fin_cases i <;> simp [swapSheetInvolution]

/-- `swapSheetInvolution` preserves the split metric `swapG` on `Fin 2 → ℝ`. -/
theorem swapSheetInvolution_preserves_swapG (u w : Fin 2 → ℝ) :
    swapG (swapSheetInvolution u) (swapSheetInvolution w) = swapG u w := by
  simp [swapG, swapSheetInvolution]

/-- Concrete witness: the induced complex structure `swapSheetInvolution ∘ swapK` on
`Fin 2 → ℝ` squares to `-id`. -/
theorem swapInducedComplex_sq_eq_neg_id :
    (inducedComplexStructure swapSheetInvolution swapK).comp
      (inducedComplexStructure swapSheetInvolution swapK) = -LinearMap.id :=
  inducedComplexStructure_sq_eq_neg_id swapK swapSheetInvolution
    swapK_paraComplex isSheetSwapInvolution_canonical

/-- Concrete witness: the induced complex structure on `Fin 2 → ℝ` preserves `swapOmega`. -/
theorem swapInducedComplex_symplectic_invariant (v w : Fin 2 → ℝ) :
    swapOmega (inducedComplexStructure swapSheetInvolution swapK v)
      (inducedComplexStructure swapSheetInvolution swapK w) = swapOmega v w :=
  inducedComplexStructure_symplectic_invariant swapG swapOmega swapK swapSheetInvolution
    swapK_paraComplex swapParaKahler isSheetSwapInvolution_canonical
    swapSheetInvolution_preserves_swapG v w

end MobiusTwistInevitability

/-!
## Archetype V: Finite Jordan–Wigner Carrier and Stage-Selected Modular-KMS Readouts
-/

section RisingSeaColimitSynthesis

/-- Entrywise complexification preserves the zero matrix. -/
theorem complexifyRealMatrix_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    complexifyRealMatrix (0 : Matrix ι ι ℝ) = 0 := by
  ext i j
  simp [complexifyRealMatrix]

/-- Entrywise complexification preserves the identity matrix. -/
theorem complexifyRealMatrix_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    complexifyRealMatrix (1 : Matrix ι ι ℝ) = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [complexifyRealMatrix, Matrix.one_apply, hij]

/-- Entrywise complexification preserves matrix addition. -/
theorem complexifyRealMatrix_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    complexifyRealMatrix (A + B) =
      complexifyRealMatrix A + complexifyRealMatrix B := by
  ext i j
  simp [complexifyRealMatrix]

/-- Entrywise complexification preserves matrix negation. -/
theorem complexifyRealMatrix_neg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    complexifyRealMatrix (-A) = -complexifyRealMatrix A := by
  ext i j
  simp [complexifyRealMatrix]

/-- Stage-`k` Jordan–Wigner creation operator $a_i^\dagger$ injected into the direct-limit
UHF algebra `Carrier` via the spinor reindexing isomorphism `matEquivFinPowTwo k`. -/
noncomputable def colimitJWCreation (k : ℕ) (i : Fin k) : Carrier :=
  stageInjection k
    (complexifyRealMatrix
      (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo k
        (InfoGeometry.Clifford.Cl11TensorTower.jwCreation k i)))

/-- Stage-`k` Jordan–Wigner annihilation operator $a_i$ injected into the direct-limit
UHF algebra `Carrier` via the spinor reindexing isomorphism `matEquivFinPowTwo k`. -/
noncomputable def colimitJWAnnihilation (k : ℕ) (i : Fin k) : Carrier :=
  stageInjection k
    (complexifyRealMatrix
      (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo k
        (InfoGeometry.Clifford.Cl11TensorTower.jwAnnihilation k i)))

/-- Stage-`k` global chiral volume operator $\Gamma_k = \gamma_{\mathrm{chiral}}^{\otimes k}$
injected into the direct-limit UHF algebra `Carrier`. -/
noncomputable def colimitGlobalChirality (k : ℕ) : Carrier :=
  stageInjection k
    (complexifyRealMatrix
      (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo k
        (InfoGeometry.Clifford.Cl11TensorTower.globalChirality k)))

/-- Every colimit Jordan–Wigner creation operator is nilpotent of order 2 in `Carrier`:
$(a_i^\dagger)^2 = 0$. -/
theorem colimitJWCreation_sq_zero (k : ℕ) (i : Fin k) :
    colimitJWCreation k i * colimitJWCreation k i = 0 := by
  unfold colimitJWCreation
  rw [← stageInjection_mul, ← complexifyRealMatrix_mul, ← map_mul,
    jwCreation_sq_zero_all k i, map_zero, complexifyRealMatrix_zero, map_zero]

/-- Every colimit Jordan–Wigner annihilation operator is nilpotent of order 2 in `Carrier`:
$a_i^2 = 0$. -/
theorem colimitJWAnnihilation_sq_zero (k : ℕ) (i : Fin k) :
    colimitJWAnnihilation k i * colimitJWAnnihilation k i = 0 := by
  unfold colimitJWAnnihilation
  rw [← stageInjection_mul, ← complexifyRealMatrix_mul, ← map_mul,
    jwAnnihilation_sq_zero_all k i, map_zero, complexifyRealMatrix_zero, map_zero]

/-- Same-site canonical anticommutation relation $\{a_i^\dagger, a_i\} = 1$ in `Carrier`. -/
theorem colimitJW_car_same_site (k : ℕ) (i : Fin k) :
    colimitJWCreation k i * colimitJWAnnihilation k i +
      colimitJWAnnihilation k i * colimitJWCreation k i = 1 := by
  unfold colimitJWCreation colimitJWAnnihilation
  rw [← stageInjection_mul, ← stageInjection_mul, ← stageInjection_add,
    ← complexifyRealMatrix_mul, ← complexifyRealMatrix_mul, ← complexifyRealMatrix_add,
    ← map_mul, ← map_mul, ← map_add, add_comm,
    InfoGeometry.Clifford.Cl11JordanWignerCARBridge.jw_same_site_car k i,
    map_one, complexifyRealMatrix_one, map_one]

/-- The colimit global chiral volume operator $\Gamma_k$ is an involution in `Carrier`:
$\Gamma_k^2 = 1$. -/
theorem colimitGlobalChirality_sq_one (k : ℕ) :
    colimitGlobalChirality k * colimitGlobalChirality k = 1 := by
  unfold colimitGlobalChirality
  rw [← stageInjection_mul, ← complexifyRealMatrix_mul, ← map_mul,
    InfoGeometry.Clifford.JordanWignerCAR.globalChirality_sq k,
    map_one, complexifyRealMatrix_one, map_one]

/-- Conjugating `colimitJWCreation k i` by `colimitGlobalChirality k` in `Carrier` negates it:
$\Gamma_k a_i^\dagger \Gamma_k = -a_i^\dagger$. -/
theorem colimitGlobalChirality_conj_jwCreation (k : ℕ) (i : Fin k) :
    colimitGlobalChirality k * colimitJWCreation k i * colimitGlobalChirality k =
      -colimitJWCreation k i := by
  unfold colimitGlobalChirality colimitJWCreation
  rw [← stageInjection_mul, ← stageInjection_mul,
    ← complexifyRealMatrix_mul, ← complexifyRealMatrix_mul,
    ← map_mul, ← map_mul,
    globalChirality_conj_jwCreation k i,
    map_neg, complexifyRealMatrix_neg, map_neg]

/-- Conjugating `colimitJWAnnihilation k i` by `colimitGlobalChirality k` in `Carrier` negates it:
$\Gamma_k a_i \Gamma_k = -a_i$. -/
theorem colimitGlobalChirality_conj_jwAnnihilation (k : ℕ) (i : Fin k) :
    colimitGlobalChirality k * colimitJWAnnihilation k i * colimitGlobalChirality k =
      -colimitJWAnnihilation k i := by
  unfold colimitGlobalChirality colimitJWAnnihilation
  rw [← stageInjection_mul, ← stageInjection_mul,
    ← complexifyRealMatrix_mul, ← complexifyRealMatrix_mul,
    ← map_mul, ← map_mul,
    globalChirality_conj_jwAnnihilation k i,
    map_neg, complexifyRealMatrix_neg, map_neg]

/-- **Stage-`k` Colimit Modular Flow Real-Seed Readout**:
Injecting a real stage-`k` observable `A` evolved under the Tomita modular flow
`modularFlow logits β t` into the algebraic UHF colimit `Carrier` reads out the exact
real finite-stage `attentionState logits β A` expectation in `ℂ`. -/
theorem risingSea_colimit_modularFlow_invariance
    (k : ℕ) (logits : Fin (2 ^ k) → ℝ) (β t : ℝ)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) :
    selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (stageInjection k (modularFlow logits β t (complexifyRealMatrix A))) =
      (attentionState logits β A : ℂ) := by
  rw [attentionColimitFunctional_modularFlow_invariant]
  exact attentionColimitFunctional_real_seed_readout k logits β A

/-- **Finite-Stage Modular-Flow and Algebraic KMS Boundary Identity**:
For the finite matrix stage `k`, `modularFlow logits β t` preserves the readout of the
stage-selected functional. The same functional satisfies the algebraic trace-cycling
identity after conjugation by the finite density matrix `ρ = attentionDensityMatrix logits β`
and its inverse. The observable is then injected into `Carrier`, but the state/functional
remains selected by stage `k`; this theorem does not assert analytic continuation or a
global modular automorphism on the direct-limit carrier. -/
theorem risingSea_colimit_modular_kms_synthesis
    (k : ℕ) (logits : Fin (2 ^ k) → ℝ) (β t : ℝ)
    (A B : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) :
    selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (stageInjection k
          (modularFlow logits β t
            (complexifyRealMatrix A *
              complexifyRealMatrix
                (attentionDensityMatrix logits β * B *
                  attentionDensityMatrixInv logits β)))) =
      selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (stageInjection k (complexifyRealMatrix (B * A))) := by
  rw [attentionColimitFunctional_modularFlow_invariant]
  exact attentionColimitFunctional_kms_boundary k logits β A B

/-- **Cross-Stage Propagation of the Stage-Selected Algebraic KMS Readout (`k ≤ n`)**:
For the functional selected by the original finite stage `k`, pushing its modular-evolved,
KMS-conjugated observable through `rawMap h` to stage `n` and injecting into `Carrier`
preserves the finite-stage trace-cycled value of `B * A`. This is propagation of that
stage-`k` functional's readout, not construction of a compatible state on all stages. -/
theorem risingSea_tower_propagation_modular_kms_synthesis
    {k n : ℕ} (h : k ≤ n) (logits : Fin (2 ^ k) → ℝ) (β t : ℝ)
    (A B : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) :
    selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (stageInjection n
          (rawMap h
            (modularFlow logits β t
              (complexifyRealMatrix A *
                complexifyRealMatrix
                  (attentionDensityMatrix logits β * B *
                    attentionDensityMatrixInv logits β))))) =
      selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (stageInjection k (complexifyRealMatrix (B * A))) := by
  rw [attentionColimitFunctional_rawMap_modularFlow_invariant h]
  exact attentionColimitFunctional_kms_boundary k logits β A B

/-- **Rising Sea Bundle of Colimit, Quotient, and KMS Facts**:
Simultaneously bundles three results whose carriers and parameters remain independent:
1. **Jordan–Wigner Colimit Fact**:
   chiral volume negation $\Gamma_k a_i^\dagger \Gamma_k = -a_i^\dagger$ and same-site
   CAR relation $\{a_i^\dagger, a_i\} = 1$ in `Carrier`;
2. **Coordinate-Free Unoriented Möbius $\mathbb{Z}_2$ Quotient Fact**:
   identification of `[P⁺ v]` and `[P⁻ (C v)]` in `MobiusInvolutionQuotient hC`; and
3. **Cross-Stage KMS Modular Context Readout Fact**:
   bonding-map invariance of the modular-evolved KMS trace-cycled expectation in `Carrier`.

The conjunction makes these theorems available together; it does not assert a causal map or
compatibility from the quotient in item 2 to the KMS readout in item 3. -/
theorem risingSea_three_arrow_colimit_mobius_kms
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {K C : V →ₗ[ℝ] V} (hC : IsSheetSwapInvolution K C) (v : V)
    {k n : ℕ} (h : k ≤ n) (i : Fin k)
    (logits : Fin (2 ^ k) → ℝ) (β t : ℝ)
    (A B : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) :
    (colimitGlobalChirality k * colimitJWCreation k i * colimitGlobalChirality k =
        -colimitJWCreation k i ∧
      colimitJWCreation k i * colimitJWAnnihilation k i +
        colimitJWAnnihilation k i * colimitJWCreation k i = 1) ∧
    (Quotient.mk (mobiusInvolutionSetoid hC) (paraProjectorPlus K v) :
        MobiusInvolutionQuotient hC) =
      Quotient.mk (mobiusInvolutionSetoid hC) (paraProjectorMinus K (C v)) ∧
    selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (stageInjection n
          (rawMap h
            (modularFlow logits β t
              (complexifyRealMatrix A *
                complexifyRealMatrix
                  (attentionDensityMatrix logits β * B *
                    attentionDensityMatrixInv logits β))))) =
      selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (stageInjection k (complexifyRealMatrix (B * A))) :=
  ⟨⟨colimitGlobalChirality_conj_jwCreation k i, colimitJW_car_same_site k i⟩,
   paraProjectorPlus_eq_paraProjectorMinus_in_mobiusQuotient hC v,
   risingSea_tower_propagation_modular_kms_synthesis h logits β t A B⟩

end RisingSeaColimitSynthesis

/-!
## 6. Cross-Corridor Bridges, Scaled Steepest Ascent, and Section Index (`InevitabilityStage`)

This section adds:
1. **Scaled Fisher Variance Rate, Steepest Ascent & Petz Adjoint Duality (`ScaledFisherSteepestAscent`)**:
   `covectorVariance`, `fisherNaturalGradient_norm_sq_eq_covectorVariance`,
   `scaledFisher_self_smul_inv_naturalGradient`,
   `scaledFisher_naturalGradient_rate_eq_inv_mul_variance`,
   `scaledFisher_steepest_ascent_of_pos`, `fisherWeightedInner`, `markovPush`,
   `petzAdjointMap`, and `petzAdjointMap_fisher_adjoint`.
2. **Explicit `CliffordAlgebra q11Form` Matrix Action Bridges (`CliffordParaKahlerMobiusWelding`)**:
   `abstractOccProj_eq_half_one_add_chiralVolume`,
   `abstractVacProj_eq_half_one_sub_chiralVolume`,
   `cl11MatrixAlgEquiv_nullSum_mulVec_eq_swapK`,
   `cl11MatrixAlgEquiv_chiralVolume_mulVec_eq_neg_swapSheetInvolution`,
   `cl11MatrixAlgEquiv_nullDiff_mulVec_eq_inducedComplexStructure`,
   `cl11MatrixAlgEquiv_abstractNullPlus_eq_wittCreationBase`,
   `cl11MatrixAlgEquiv_abstractNullMinus_eq_wittAnnihilationBase`,
   `cl11MatrixAlgEquiv_chiralVolume_eq_gamma_chiral_base`,
   `cl11MatrixAlgEquiv_abstractVacProj_eq_cl11VacProj`, and
   `cl11MatrixAlgEquiv_abstractOccProj_eq_cl11OccProj`.
3. **Set-Level Orbit Descent of the Cross-Sheet Pairing, Norden vs. True `J`-Hermitian Metric & Krein Adjoint Duality (`MobiusCrossSheetDescent`)**:
   `crossSheetPairing_sheetSwap_invariant`, `crossSheetPairing_eq_of_mobiusInvolutionRel`,
   `mobiusQuotientCrossSheetPairing`, `mobiusQuotientCrossSheetPairing_mk`,
   `mobiusQuotientQuadratic_eq_two_mul_crossSheetPairing`, `trueHermitianMetric`,
   `inducedComplexStructure_apply_sq`, `trueHermitianMetric_inducedComplexStructure_invariant`,
   `norden_vs_true_hermitian_under_J`, `sheetSwap_krein_selfAdjoint`,
   `trueHermitianMetric_symm`, `sheetSwap_trueHermitianMetric_selfAdjoint`,
   `paraComplex_krein_skewAdjoint`, `paraComplex_trueHermitianMetric_selfAdjoint`,
   `projPlus_krein_adjoint_projMinus`, `projMinus_krein_adjoint_projPlus`,
   `projPlus_trueHermitianMetric_selfAdjoint`, `projMinus_trueHermitianMetric_selfAdjoint`,
   `projPlus_projMinus_trueHermitianMetric_orthogonal`,
   `inducedComplexStructure_krein_selfAdjoint`,
   `inducedComplexStructure_trueHermitianMetric_skewAdjoint`, and
   `krein_adjoint_of_trueHermitianMetric_adjoint`.
4. **Direct `Cl(3,3)` Left-Multiplication Clifford Identity on `ZornSplitOctonion R` (`ZornPolarizedLeftAlternativeCl33`)**:
   `zorn_leftMul_cl33_clifford_identity`.
5. **Full Cross-Site Colimit CAR, Pruned Modular Sink Bound, UHF Trace Doubling & Toomre Stability (`StageVCrossSiteAndPrunedSink`)**:
   `colimitJW_anticomm_creation_all`, `colimitJW_anticomm_annihilation_all`,
   `colimitJW_annihilation_creation_anticomm_all`,
   `prunedColimitFunctional_modularFlow_invariant`,
   `risingSea_pruned_tower_modularFlow_anchor_lower_bound`, `uhfStep`,
   `kms_trace_cycling_and_uhfStep`, and `quadratic_dispersion_nonneg_of_toomre`.
6. **Explicit 5-Element Section Index (`InevitabilityPosetOrder`)**:
   `InevitabilityStage` is equivalent to `Fin 5` for stable enumeration only. This
   index carries no causal or prerequisite order; evidence-supported bridge
   reachability is defined separately in `CategoricalInevitabilityCausalPoset`.
-/

section ScaledFisherSteepestAscent

variable {α : Type} [Fintype α]

/-- The `P`-variance of a covector `ℓ` on the probability simplex interior:
`Var_P(ℓ) = ∑ a, P.p a * ℓ a ^ 2 - (∑ a, P.p a * ℓ a) ^ 2`. -/
def covectorVariance (P : ProbInterior α) (ℓ : α → ℝ) : ℝ :=
  ∑ a, P.p a * ℓ a ^ 2 - (∑ a, P.p a * ℓ a) ^ 2

/-- The squared Fisher length of the natural gradient equals `covectorVariance P ℓ`. -/
theorem fisherNaturalGradient_norm_sq_eq_covectorVariance (P : ProbInterior α) (ℓ : α → ℝ) :
    fisherMetric P (fisherNaturalGradient P ℓ) (fisherNaturalGradient P ℓ) =
      covectorVariance P ℓ := by
  rw [← fisherNaturalGradient_rate_eq_norm_sq, fisherNaturalGradient_rate_eq_variance]
  rfl

/-- The squared `scaledFisherFamily c` norm of the scaled natural gradient
`c⁻¹ • fisherNaturalGradient P ℓ` equals `c⁻¹ * covectorVariance P ℓ`. -/
theorem scaledFisher_self_smul_inv_naturalGradient
    (P : ProbInterior α) (ℓ : α → ℝ) {c : ℝ} (hc : c ≠ 0) :
    (scaledFisherFamily c).g α P
        (c⁻¹ • fisherNaturalGradient P ℓ) (c⁻¹ • fisherNaturalGradient P ℓ) =
      c⁻¹ * covectorVariance P ℓ := by
  change c * fisherMetric P (c⁻¹ • fisherNaturalGradient P ℓ) (c⁻¹ • fisherNaturalGradient P ℓ) =
    c⁻¹ * covectorVariance P ℓ
  rw [fisherMetric_smul_left,
    fisherMetric_symm,
    fisherMetric_smul_left,
    fisherNaturalGradient_norm_sq_eq_covectorVariance,
    mul_inv_cancel_left₀ hc]

/-- The first-order ascent rate of a covector `ℓ` along the scaled natural gradient
`c⁻¹ • fisherNaturalGradient P ℓ` equals `c⁻¹ * covectorVariance P ℓ`. -/
theorem scaledFisher_naturalGradient_rate_eq_inv_mul_variance
    (P : ProbInterior α) (ℓ : α → ℝ) (c : ℝ) :
    ∑ a, ℓ a * (c⁻¹ • fisherNaturalGradient P ℓ) a =
      c⁻¹ * covectorVariance P ℓ := by
  have hterm : ∀ a : α, ℓ a * (c⁻¹ • fisherNaturalGradient P ℓ) a =
      c⁻¹ * (ℓ a * fisherNaturalGradient P ℓ a) := by
    intro a
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp only [hterm, ← Finset.mul_sum]
  rw [fisherNaturalGradient_rate_eq_variance]
  rfl

/-- **Scaled Fisher Steepest Ascent on the `g_P^(c)`-Ball**:
For any positive Chentsov scale `0 < c`, the scaled natural gradient
`c⁻¹ • fisherNaturalGradient P ℓ` maximizes the first-order covector rate `∑ a, ℓ a * w a`
among all tangent vectors `w` (`∑ a, w a = 0`) whose `scaledFisherFamily c` norm does not
exceed that of `c⁻¹ • fisherNaturalGradient P ℓ`. -/
theorem scaledFisher_steepest_ascent_of_pos
    (P : ProbInterior α) (ℓ w : α → ℝ) (hw : ∑ a, w a = 0) {c : ℝ} (hc : 0 < c)
    (h_norm : (scaledFisherFamily c).g α P w w ≤
      (scaledFisherFamily c).g α P
        (c⁻¹ • fisherNaturalGradient P ℓ) (c⁻¹ • fisherNaturalGradient P ℓ)) :
    ∑ a, ℓ a * w a ≤ c⁻¹ * ∑ a, ℓ a * fisherNaturalGradient P ℓ a := by
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hu_tan : ∑ a, (c • w) a = 0 := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hw, mul_zero]
  have h_lhs : fisherMetric P (c • w) (c • w) = c * (scaledFisherFamily c).g α P w w := by
    change fisherMetric P (c • w) (c • w) = c * (c * fisherMetric P w w)
    rw [fisherMetric_smul_left,
      fisherMetric_symm,
      fisherMetric_smul_left]
  have h_rhs :
      c * (scaledFisherFamily c).g α P
        (c⁻¹ • fisherNaturalGradient P ℓ) (c⁻¹ • fisherNaturalGradient P ℓ) =
      fisherMetric P (fisherNaturalGradient P ℓ) (fisherNaturalGradient P ℓ) := by
    change c * (c * fisherMetric P
      (c⁻¹ • fisherNaturalGradient P ℓ) (c⁻¹ • fisherNaturalGradient P ℓ)) = _
    rw [fisherMetric_smul_left,
      fisherMetric_symm,
      fisherMetric_smul_left,
      mul_inv_cancel_left₀ hc_ne, mul_inv_cancel_left₀ hc_ne]
  have hu_len :
      fisherMetric P (c • w) (c • w) ≤
        fisherMetric P (fisherNaturalGradient P ℓ) (fisherNaturalGradient P ℓ) := by
    rw [h_lhs, ← h_rhs]
    exact mul_le_mul_of_nonneg_left h_norm (le_of_lt hc)
  have h_asc := fisherNaturalGradient_steepest_ascent P ℓ (c • w) hu_tan hu_len
  have h_rate_smul : ∑ a, ℓ a * (c • w) a = c * ∑ a, ℓ a * w a := by
    have hterm : ∀ a : α, ℓ a * (c • w) a = c * (ℓ a * w a) := by
      intro a
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    simp only [hterm, ← Finset.mul_sum]
  rw [h_rate_smul] at h_asc
  have h_inv_pos : 0 ≤ c⁻¹ := inv_nonneg.mpr (le_of_lt hc)
  have h_scaled := mul_le_mul_of_nonneg_left h_asc h_inv_pos
  rwa [inv_mul_cancel_left₀ hc_ne] at h_scaled

/-- Weighted Fisher inner product `⟨u, v⟩_ρ = ∑ i, (u i * v i) / ρ i` on `n → ℝ`. -/
def fisherWeightedInner {n : Type*} [Fintype n] (ρ u v : n → ℝ) : ℝ :=
  ∑ i : n, (u i * v i) / ρ i

/-- Markov transition pushforward `(T_* x) j = ∑ i, T j i * x i`. -/
def markovPush {n m : Type*} [Fintype n] (T : Matrix m n ℝ) (x : n → ℝ) (j : m) : ℝ :=
  ∑ i : n, T j i * x i

/-- Petz recovery adjoint `(T^*_ρ y) i = ρ i * ∑ j, T j i * (y j / (T_* ρ) j)`. -/
def petzAdjointMap {n m : Type*} [Fintype n] [Fintype m]
    (ρ : n → ℝ) (T : Matrix m n ℝ) (y : m → ℝ) (i : n) : ℝ :=
  ρ i * ∑ j : m, T j i * (y j / markovPush T ρ j)

private lemma petz_term_rearrange (a b c d : ℝ) :
    a * (b / c) * d = (b * (a * d)) / c := by
  ring

/-- **Petz Adjoint Duality for the Weighted Fisher Inner Product**:
For any strictly nonzero reference density `hρ : ∀ i, ρ i ≠ 0` and transition matrix `T`,
`petzAdjointMap ρ T` is the exact adjoint of `markovPush T` with respect to
`fisherWeightedInner`:
`⟨petzAdjointMap ρ T y, x⟩_ρ = ⟨y, markovPush T x⟩_{markovPush T ρ}`. -/
theorem petzAdjointMap_fisher_adjoint {n m : Type*} [Fintype n] [Fintype m]
    (ρ x : n → ℝ) (T : Matrix m n ℝ) (y : m → ℝ) (hρ : ∀ i : n, ρ i ≠ 0) :
    fisherWeightedInner ρ (petzAdjointMap ρ T y) x =
      fisherWeightedInner (markovPush T ρ) y (markovPush T x) := by
  unfold fisherWeightedInner petzAdjointMap
  calc
    ∑ i : n, (ρ i * (∑ j : m, T j i * (y j / markovPush T ρ j)) * x i) / ρ i
      = ∑ i : n, ((∑ j : m, T j i * (y j / markovPush T ρ j)) * x i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [mul_assoc, mul_div_cancel_left₀ _ (hρ i)]
    _ = ∑ i : n, ∑ j : m, (T j i * (y j / markovPush T ρ j) * x i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_mul]
    _ = ∑ j : m, ∑ i : n, (T j i * (y j / markovPush T ρ j) * x i) := by
          rw [Finset.sum_comm]
    _ = ∑ j : m, (y j * markovPush T x j) / markovPush T ρ j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have h_push : markovPush T x j = ∑ i : n, T j i * x i := rfl
          rw [h_push, Finset.mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact petz_term_rearrange (T j i) (y j) (markovPush T ρ j) (x i)

end ScaledFisherSteepestAscent

section CliffordParaKahlerMobiusWelding

/-- Universal occupied projector spectral decomposition in `CliffordAlgebra q11Form`:
`abstractOccProj = (1 / 2) • (1 + abstractChiralVolume)`. -/
theorem abstractOccProj_eq_half_one_add_chiralVolume :
    abstractOccProj =
      (1 / 2 : ℝ) • ((1 : CliffordAlgebra q11Form) + abstractChiralVolume) := by
  unfold abstractOccProj
  apply cl11MatrixAlgEquiv.injective
  rw [map_mul, map_smul, map_add, map_one,
    cl11MatrixAlgEquiv_abstractNullMinus, cl11MatrixAlgEquiv_abstractNullPlus,
    cl11MatrixAlgEquiv_chiralVolume]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- Universal vacuum projector spectral decomposition in `CliffordAlgebra q11Form`:
`abstractVacProj = (1 / 2) • (1 - abstractChiralVolume)`. -/
theorem abstractVacProj_eq_half_one_sub_chiralVolume :
    abstractVacProj =
      (1 / 2 : ℝ) • ((1 : CliffordAlgebra q11Form) - abstractChiralVolume) := by
  unfold abstractVacProj
  apply cl11MatrixAlgEquiv.injective
  rw [map_mul, map_smul, map_sub, map_one,
    cl11MatrixAlgEquiv_abstractNullPlus, cl11MatrixAlgEquiv_abstractNullMinus,
    cl11MatrixAlgEquiv_chiralVolume]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- **Matrix Action of `abstractNullPlus + abstractNullMinus` Equals `swapK`**:
The matrix image of the positive-square generator `abstractNullPlus + abstractNullMinus`
(`= ι(1, 0)`) in `CliffordAlgebra q11Form` acts on `Fin 2 → ℝ` by `Matrix.mulVec`
identically as the coordinate-swap involution `swapK`. -/
theorem cl11MatrixAlgEquiv_nullSum_mulVec_eq_swapK (v : Fin 2 → ℝ) :
    (cl11MatrixAlgEquiv (abstractNullPlus + abstractNullMinus)).mulVec v = swapK v := by
  rw [map_add, cl11MatrixAlgEquiv_abstractNullPlus, cl11MatrixAlgEquiv_abstractNullMinus]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, swapK_apply_zero]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, swapK_apply_one]

/-- **Matrix Action of `abstractChiralVolume` Equals `-swapSheetInvolution`**:
The matrix image of the universal chiral volume element `abstractChiralVolume` in
`CliffordAlgebra q11Form` acts on `Fin 2 → ℝ` by `Matrix.mulVec` as the negation of the
sheet-swapping involution `swapSheetInvolution`. -/
theorem cl11MatrixAlgEquiv_chiralVolume_mulVec_eq_neg_swapSheetInvolution (v : Fin 2 → ℝ) :
    (cl11MatrixAlgEquiv abstractChiralVolume).mulVec v = -swapSheetInvolution v := by
  rw [cl11MatrixAlgEquiv_chiralVolume]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Matrix Action of `abstractNullPlus - abstractNullMinus` Equals `inducedComplexStructure swapSheetInvolution swapK`**:
The matrix image of the negative-square Clifford generator `abstractNullPlus - abstractNullMinus`
(`= ι(0, 1)`) in `CliffordAlgebra q11Form` acts on `Fin 2 → ℝ` by `Matrix.mulVec` identically
as the induced complex structure `J = inducedComplexStructure swapSheetInvolution swapK`. -/
theorem cl11MatrixAlgEquiv_nullDiff_mulVec_eq_inducedComplexStructure (v : Fin 2 → ℝ) :
    (cl11MatrixAlgEquiv (abstractNullPlus - abstractNullMinus)).mulVec v =
      inducedComplexStructure swapSheetInvolution swapK v := by
  rw [map_sub, cl11MatrixAlgEquiv_abstractNullPlus, cl11MatrixAlgEquiv_abstractNullMinus]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      inducedComplexStructure, swapK_apply_zero]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      inducedComplexStructure, swapK_apply_one]

/-- The matrix image of `abstractNullPlus` under `cl11MatrixAlgEquiv` equals the
Jordan–Wigner base creation matrix `wittCreationBase`. -/
theorem cl11MatrixAlgEquiv_abstractNullPlus_eq_wittCreationBase :
    cl11MatrixAlgEquiv abstractNullPlus =
      InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase := by
  rw [cl11MatrixAlgEquiv_abstractNullPlus, ← cl11NilpotentPlus_eq_wittCreationBase]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11NilpotentPlus, J1, Eminus]

/-- The matrix image of `abstractNullMinus` under `cl11MatrixAlgEquiv` equals the
Jordan–Wigner base annihilation matrix `wittAnnihilationBase`. -/
theorem cl11MatrixAlgEquiv_abstractNullMinus_eq_wittAnnihilationBase :
    cl11MatrixAlgEquiv abstractNullMinus =
      InfoGeometry.Clifford.Cl11TensorTower.wittAnnihilationBase := by
  rw [cl11MatrixAlgEquiv_abstractNullMinus, ← cl11NilpotentMinus_eq_wittAnnihilationBase]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11NilpotentMinus, J1, Eminus]

/-- The matrix image of `abstractChiralVolume` under `cl11MatrixAlgEquiv` equals the
Jordan–Wigner base chiral grading matrix `gamma_chiral_base`. -/
theorem cl11MatrixAlgEquiv_chiralVolume_eq_gamma_chiral_base :
    cl11MatrixAlgEquiv abstractChiralVolume =
      InfoGeometry.Clifford.Cl11TensorTower.gamma_chiral_base := by
  rw [cl11MatrixAlgEquiv_apply, cl11MatrixAlgHom_abstractChiralVolume,
    cl11ChiralVolume_eq_gamma_chiral_base]

/-- The matrix image of `abstractVacProj` under `cl11MatrixAlgEquiv` equals the
atomic vacuum projector `cl11VacProj`. -/
theorem cl11MatrixAlgEquiv_abstractVacProj_eq_cl11VacProj :
    cl11MatrixAlgEquiv abstractVacProj = cl11VacProj := by
  unfold abstractVacProj cl11VacProj
  rw [map_mul, cl11MatrixAlgEquiv_abstractNullPlus_eq_wittCreationBase,
    cl11MatrixAlgEquiv_abstractNullMinus_eq_wittAnnihilationBase,
    cl11NilpotentPlus_eq_wittCreationBase, cl11NilpotentMinus_eq_wittAnnihilationBase]

/-- The matrix image of `abstractOccProj` under `cl11MatrixAlgEquiv` equals the
atomic occupied projector `cl11OccProj`. -/
theorem cl11MatrixAlgEquiv_abstractOccProj_eq_cl11OccProj :
    cl11MatrixAlgEquiv abstractOccProj = cl11OccProj := by
  unfold abstractOccProj cl11OccProj
  rw [map_mul, cl11MatrixAlgEquiv_abstractNullMinus_eq_wittAnnihilationBase,
    cl11MatrixAlgEquiv_abstractNullPlus_eq_wittCreationBase,
    cl11NilpotentMinus_eq_wittAnnihilationBase, cl11NilpotentPlus_eq_wittCreationBase]

end CliffordParaKahlerMobiusWelding

section MobiusCrossSheetDescent

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Sheet-Swap Invariance of the Off-Diagonal Cross-Sheet Pairing**:
For any para-Kähler structure `(g, omega, K)` and `g`-isometric sheet-swapping involution `C`
(`IsSheetSwapInvolution K C`), the cross-sheet pairing `g (P⁺ v) (P⁻ v)` is invariant under
`v ↦ C v`. -/
theorem crossSheetPairing_sheetSwap_invariant
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C : V →ₗ[ℝ] V)
    (hPK : ParaKahlerStructure g omega K)
    (hC : IsSheetSwapInvolution K C)
    (hC_iso : ∀ u w, g (C u) (C w) = g u w) (v : V) :
    g (paraProjectorPlus K (C v)) (paraProjectorMinus K (C v)) =
      g (paraProjectorPlus K v) (paraProjectorMinus K v) := by
  have _ := hPK.compatibility v v
  rw [mobiusTwist_intertwines_paraProjectorMinus K C hC.2 v,
    mobiusTwist_intertwines_paraProjectorPlus K C hC.2 v,
    hC_iso (paraProjectorMinus K v) (paraProjectorPlus K v),
    hPK.g_symm (paraProjectorMinus K v) (paraProjectorPlus K v)]

/-- The off-diagonal cross-sheet pairing `g (P⁺ u) (P⁻ u)` is constant along every
`mobiusInvolutionRel C` orbit. -/
theorem crossSheetPairing_eq_of_mobiusInvolutionRel
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C : V →ₗ[ℝ] V)
    (hPK : ParaKahlerStructure g omega K)
    (hC : IsSheetSwapInvolution K C)
    (hC_iso : ∀ u w, g (C u) (C w) = g u w) {u w : V}
    (huw : mobiusInvolutionRel C u w) :
    g (paraProjectorPlus K u) (paraProjectorMinus K u) =
      g (paraProjectorPlus K w) (paraProjectorMinus K w) := by
  rcases huw with rfl | rfl
  · rfl
  · exact (crossSheetPairing_sheetSwap_invariant g omega K C hPK hC hC_iso u).symm

/-- Well-defined descent of the cross-sheet pairing `v ↦ g (P⁺ v) (P⁻ v)` to the
set-level $\mathbb{Z}_2$ orbit quotient `MobiusInvolutionQuotient hC`. -/
def mobiusQuotientCrossSheetPairing
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {K C : V →ₗ[ℝ] V}
    (hPK : ParaKahlerStructure g omega K)
    (hC : IsSheetSwapInvolution K C)
    (hC_iso : ∀ u w, g (C u) (C w) = g u w) :
    MobiusInvolutionQuotient hC → ℝ :=
  Quotient.lift (fun v => g (paraProjectorPlus K v) (paraProjectorMinus K v))
    (fun _ _ huw => crossSheetPairing_eq_of_mobiusInvolutionRel g omega K C hPK hC hC_iso huw)

@[simp]
theorem mobiusQuotientCrossSheetPairing_mk
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {K C : V →ₗ[ℝ] V}
    (hPK : ParaKahlerStructure g omega K)
    (hC : IsSheetSwapInvolution K C)
    (hC_iso : ∀ u w, g (C u) (C w) = g u w) (v : V) :
    mobiusQuotientCrossSheetPairing g omega hPK hC hC_iso
      (Quotient.mk (mobiusInvolutionSetoid hC) v) =
      g (paraProjectorPlus K v) (paraProjectorMinus K v) :=
  rfl

/-- **Quotient Cross-Sheet Quadratic Identity**:
On the set-level $\mathbb{Z}_2$ orbit quotient `MobiusInvolutionQuotient hC`, the descended
quadratic form `mobiusQuotientQuadratic` equals twice the descended off-diagonal cross-sheet
pairing `mobiusQuotientCrossSheetPairing`. -/
theorem mobiusQuotientQuadratic_eq_two_mul_crossSheetPairing
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {K C : V →ₗ[ℝ] V}
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K)
    (hC : IsSheetSwapInvolution K C)
    (hC_iso : ∀ u w, g (C u) (C w) = g u w)
    (q : MobiusInvolutionQuotient hC) :
    mobiusQuotientQuadratic g hC hC_iso q =
      2 * mobiusQuotientCrossSheetPairing g omega hPK hC hC_iso q :=
  Quotient.inductionOn q (fun v => paraKahler_self_metric_eq_two_mul_cross_sheet hK hPK v)

/-- The true $J$-Hermitian bilinear pairing $g_C(u, v) = g(u, C v)$ twisted by the
sheet-swapping involution `C`. -/
def trueHermitianMetric (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : V →ₗ[ℝ] V) (u v : V) : ℝ :=
  g u (C v)

/-- Pointwise elliptic square identity `J (J v) = -v` for `J = inducedComplexStructure C K`. -/
theorem inducedComplexStructure_apply_sq
    (K C : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (hC : IsSheetSwapInvolution K C) (v : V) :
    inducedComplexStructure C K (inducedComplexStructure C K v) = -v := by
  have h := congrArg (fun f : V →ₗ[ℝ] V => f v) (inducedComplexStructure_sq_eq_neg_id K C hK hC)
  simpa only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply] using h

/-- The twisted pairing `trueHermitianMetric g C` is strictly $J$-Hermitian (invariant)
under `J = inducedComplexStructure C K`. -/
theorem trueHermitianMetric_inducedComplexStructure_invariant
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K)
    (hC : IsSheetSwapInvolution K C)
    (hC_iso : ∀ u v : V, g (C u) (C v) = g u v) (u v : V) :
    trueHermitianMetric g C (inducedComplexStructure C K u) (inducedComplexStructure C K v) =
      trueHermitianMetric g C u v := by
  dsimp [trueHermitianMetric, inducedComplexStructure]
  have h_comm : C (K v) = -K (C v) := by
    rw [mobiusTwist_apply_comm K C hC.2 v, neg_neg]
  rw [hC_iso (K u) (C (K v)), h_comm, map_neg,
    metric_anti_invariance g omega K hK hPK u (C v), neg_neg]

/-- **Norden Anti-Invariance of `g` vs. True `J`-Hermitian Invariance of `trueHermitianMetric g C`**:
For any para-Kähler structure `(g, omega, K)` and `g`-isometric sheet-swapping involution `C`:
1. `J (J v) = -v` for `J = inducedComplexStructure C K`,
2. `g (J u) (J v) = -g u v` (Norden anti-invariance of the neutral metric `g`),
3. `omega (J u) (J v) = omega u v` (symplectic invariance of `omega`), and
4. `trueHermitianMetric g C (J u) (J v) = trueHermitianMetric g C u v` (true $J$-Hermitian
   invariance of the `C`-twisted metric $g_C(u, v) = g(u, C v)$). -/
theorem norden_vs_true_hermitian_under_J
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K)
    (hC : IsSheetSwapInvolution K C)
    (hC_iso : ∀ u v : V, g (C u) (C v) = g u v) (u v : V) :
    inducedComplexStructure C K (inducedComplexStructure C K v) = -v ∧
      g (inducedComplexStructure C K u) (inducedComplexStructure C K v) = -g u v ∧
      omega (inducedComplexStructure C K u) (inducedComplexStructure C K v) = omega u v ∧
      trueHermitianMetric g C (inducedComplexStructure C K u) (inducedComplexStructure C K v) =
        trueHermitianMetric g C u v :=
  ⟨inducedComplexStructure_apply_sq K C hK hC v,
   inducedComplexStructure_metric_neg g omega K C hK hPK hC_iso u v,
   inducedComplexStructure_symplectic_invariant g omega K C hK hPK hC hC_iso u v,
   trueHermitianMetric_inducedComplexStructure_invariant g omega K C hK hPK hC hC_iso u v⟩

/-- **Fundamental Symmetry Krein Self-Adjointness of `C`**:
Because `C` is a `g`-isometric involution (`C (C u) = u`), `C` is self-adjoint with respect to
the indefinite Krein metric `g`: `g (C u) v = g u (C v) = trueHermitianMetric g C u v`. -/
theorem sheetSwap_krein_selfAdjoint
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C : V →ₗ[ℝ] V)
    (hC : IsSheetSwapInvolution K C)
    (hC_iso : ∀ u v : V, g (C u) (C v) = g u v) (u v : V) :
    g (C u) v = g u (C v) := by
  calc
    g (C u) v = g (C (C u)) (C v) := (hC_iso (C u) v).symm
    _ = g u (C v) := by rw [sheetSwapInvolution_apply_sq K C hC u]

/-- Symmetry of the `C`-twisted pairing `trueHermitianMetric g C`:
`trueHermitianMetric g C u v = trueHermitianMetric g C v u`. -/
theorem trueHermitianMetric_symm
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C : V →ₗ[ℝ] V)
    (hPK : ParaKahlerStructure g omega K)
    (hC : IsSheetSwapInvolution K C)
    (hC_iso : ∀ u v : V, g (C u) (C v) = g u v) (u v : V) :
    trueHermitianMetric g C u v = trueHermitianMetric g C v u := by
  dsimp [trueHermitianMetric]
  calc
    g u (C v) = g (C u) v := (sheetSwap_krein_selfAdjoint g K C hC hC_iso u v).symm
    _ = g v (C u) := hPK.g_symm (C u) v

/-- **Krein Skew-Adjointness of the Paracomplex Grading `K`**:
With respect to the indefinite neutral metric `g`, `K` is skew-adjoint (`g (K u) v = -g u (K v)`). -/
theorem paraComplex_krein_skewAdjoint
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K) (u v : V) :
    g (K u) v = -g u (K v) := by
  have h_kv : K (K v) = v := hK.involutive v
  calc
    g (K u) v = g (K u) (K (K v)) := by rw [h_kv]
    _ = -g u (K v) := metric_anti_invariance g omega K hK hPK u (K v)

/-- **`trueHermitianMetric` Self-Adjointness of the Paracomplex Grading `K`**:
Because `K` is `g`-skew-adjoint and anticommutes with `C`, `K` is **self-adjoint** with respect
to the twisted metric `trueHermitianMetric g C`:
`trueHermitianMetric g C (K u) v = trueHermitianMetric g C u (K v)`. -/
theorem paraComplex_trueHermitianMetric_selfAdjoint
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K)
    (hC : IsSheetSwapInvolution K C) (u v : V) :
    trueHermitianMetric g C (K u) v = trueHermitianMetric g C u (K v) := by
  dsimp [trueHermitianMetric]
  calc
    g (K u) (C v) = -g u (K (C v)) :=
      paraComplex_krein_skewAdjoint g omega K hK hPK u (C v)
    _ = -g u (-(C (K v))) := by rw [mobiusTwist_apply_comm K C hC.2 v]
    _ = g u (C (K v)) := by rw [map_neg, neg_neg]

/-- **Krein Self-Adjointness of the Induced Complex Structure `J = C ∘ K`**:
With respect to the indefinite Krein metric `g`, `J = inducedComplexStructure C K` is
**Krein self-adjoint** (`g (J u) v = +g u (J v)`), whereas with respect to `trueHermitianMetric g C`
it is skew-adjoint. -/
theorem inducedComplexStructure_krein_selfAdjoint
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K)
    (hC : IsSheetSwapInvolution K C)
    (hC_iso : ∀ u v : V, g (C u) (C v) = g u v) (u v : V) :
    g (inducedComplexStructure C K u) v = g u (inducedComplexStructure C K v) := by
  dsimp [inducedComplexStructure]
  calc
    g (C (K u)) v = g (K u) (C v) :=
      sheetSwap_krein_selfAdjoint g K C hC hC_iso (K u) v
    _ = g u (C (K v)) :=
      paraComplex_trueHermitianMetric_selfAdjoint g omega K C hK hPK hC u v

/-- **Skew-Adjointness of `J = C ∘ K` under `trueHermitianMetric g C`**:
`trueHermitianMetric g C (J u) v = -trueHermitianMetric g C u (J v)`. -/
theorem inducedComplexStructure_trueHermitianMetric_skewAdjoint
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K)
    (hC : IsSheetSwapInvolution K C)
    (hC_iso : ∀ u v : V, g (C u) (C v) = g u v) (u v : V) :
    trueHermitianMetric g C (inducedComplexStructure C K u) v =
      -trueHermitianMetric g C u (inducedComplexStructure C K v) := by
  calc
    trueHermitianMetric g C (inducedComplexStructure C K u) v
      = -trueHermitianMetric g C (inducedComplexStructure C K u)
          (inducedComplexStructure C K (inducedComplexStructure C K v)) := by
          dsimp [trueHermitianMetric]
          rw [inducedComplexStructure_apply_sq K C hK hC v, map_neg, map_neg, neg_neg]
    _ = -trueHermitianMetric g C u (inducedComplexStructure C K v) := by
          rw [trueHermitianMetric_inducedComplexStructure_invariant g omega K C hK hPK hC hC_iso
            u (inducedComplexStructure C K v)]

/-- **General Krein Adjoint Formula ($A^{[*]_g} = C \circ A^{*_{g_C}} \circ C$)**:
If `A_adj` is the adjoint of `A` with respect to `trueHermitianMetric g C`, then
`C ∘ A_adj ∘ C` is the Krein adjoint of `A` with respect to `g`:
`g (A u) v = g u (C (A_adj (C v)))`. -/
theorem krein_adjoint_of_trueHermitianMetric_adjoint
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K C A A_adj : V →ₗ[ℝ] V)
    (hC : IsSheetSwapInvolution K C)
    (h_adj : ∀ x y : V, trueHermitianMetric g C (A x) y = trueHermitianMetric g C x (A_adj y))
    (u v : V) :
    g (A u) v = g u (C (A_adj (C v))) := by
  calc
    g (A u) v = g (A u) (C (C v)) := by rw [sheetSwapInvolution_apply_sq K C hC v]
    _ = trueHermitianMetric g C (A u) (C v) := rfl
    _ = trueHermitianMetric g C u (A_adj (C v)) := h_adj u (C v)
    _ = g u (C (A_adj (C v))) := rfl

/-- Weighted inner product $\langle u, v \rangle_\pi = \sum_i \pi_i u_i v_i$ on a finite index type. -/
def innerPi {ι : Type*} [Fintype ι] (π u v : ι → ℝ) : ℝ :=
  ∑ i : ι, π i * u i * v i

/-- Off-diagonal neutral Krein pairing
$g_\pi((u_+, u_-), (v_+, v_-)) = \langle u_+, v_- \rangle_\pi + \langle u_-, v_+ \rangle_\pi$
on the Double Real Krein Space $\mathcal{K}_\iota = (\iota \to \mathbb{R}) \times (\iota \to \mathbb{R})$. -/
def gPi {ι : Type*} [Fintype ι] (π : ι → ℝ) (u v : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  innerPi π u.1 v.2 + innerPi π u.2 v.1

/-- Matrix-vector action $(P v)_i = \sum_j P_{ij} v_j$. -/
def matMul {ι : Type*} [Fintype ι] (P : ι → ι → ℝ) (v : ι → ℝ) : ι → ℝ :=
  fun i => ∑ j : ι, P i j * v j

/-- The $\pi$-dual operator $(P^{\#_\pi})_{ij} = (\pi_j / \pi_i) P_{ji}$ acting on the dual null sheet $T^-$. -/
noncomputable def markovDual {ι : Type*} (π : ι → ℝ) (P : ι → ι → ℝ) : ι → ι → ℝ :=
  fun i j => (π j / π i) * P j i

/-- Cross-sheet $\pi$-adjoint duality $\langle P u, v \rangle_\pi = \langle u, P^{\#_\pi} v \rangle_\pi$. -/
theorem matMul_markovDual_adjoint {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (hπ : ∀ i : ι, π i ≠ 0) (P : ι → ι → ℝ) (u v : ι → ℝ) :
    innerPi π (matMul P u) v = innerPi π u (matMul (markovDual π P) v) := by
  unfold innerPi matMul markovDual
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  have hπi : π i ≠ 0 := hπ i
  have hπj : π j ≠ 0 := hπ j
  calc
    π i * (P i j * u j) * v i = π i * P i j * u j * v i := by ring
    _ = π j * ((π i / π j) * P i j) * u j * v i := by
        field_simp [hπi, hπj]
    _ = π j * u j * (((π i / π j) * P i j) * v i) := by ring

/-- The block-diagonal Double Real Krein Operator $\mathcal{T}_P(u_+, u_-) = (P u_+, P^{\#_\pi} u_-)$. -/
noncomputable def kreinOp {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : ι → ι → ℝ) (w : (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) :=
  (matMul P w.1, matMul (markovDual π P) w.2)

/-- **Universal Double Real Krein Self-Adjointness**:
For EVERY matrix $P$ (causal or non-causal), $\mathcal{T}_P(u_+, u_-) = (P u_+, P^{\#_\pi} u_-)$
is strictly self-adjoint with respect to the neutral Krein pairing $g_\pi$:
$g_\pi(\mathcal{T}_P u, v) = g_\pi(u, \mathcal{T}_P v)$. -/
theorem kreinOp_self_adjoint {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (hπ : ∀ i : ι, π i ≠ 0)
    (P : ι → ι → ℝ) (u v : (ι → ℝ) × (ι → ℝ)) :
    gPi π (kreinOp π P u) v = gPi π u (kreinOp π P v) := by
  unfold gPi kreinOp
  dsimp
  rw [matMul_markovDual_adjoint π hπ P u.1 v.2]
  have h2 : innerPi π (matMul (markovDual π P) u.2) v.1 = innerPi π u.2 (matMul P v.1) := by
    have h_symm := matMul_markovDual_adjoint π hπ (markovDual π P) u.2 v.1
    have h_inv : markovDual π (markovDual π P) = P := by
      unfold markovDual
      ext i j
      have hπi : π i ≠ 0 := hπ i
      have hπj : π j ≠ 0 := hπ j
      field_simp [hπi, hπj]
    rw [h_inv] at h_symm
    exact h_symm
  rw [h2]

/-- Strictly causal (lower-triangular) predicate: $P_{ij} = 0$ whenever $i < j$. -/
def IsCausal {ι : Type*} [LinearOrder ι] (P : ι → ι → ℝ) : Prop :=
  ∀ i j : ι, i < j → P i j = 0

/-- Anti-causal (upper-triangular) predicate: $Q_{ij} = 0$ whenever $j < i$. -/
def IsAntiCausal {ι : Type*} [LinearOrder ι] (Q : ι → ι → ℝ) : Prop :=
  ∀ i j : ι, j < i → Q i j = 0

/-- **Causal-to-Anti-Causal Dualization**:
If $P$ is causal (lower-triangular) on $T^+$, then its $\pi$-dual $P^{\#_\pi}$ is strictly
anti-causal (upper-triangular) on $T^-$. -/
theorem causal_dual_is_antiCausal {ι : Type*} [LinearOrder ι]
    (π : ι → ℝ) (P : ι → ι → ℝ) (h_causal : IsCausal P) :
    IsAntiCausal (markovDual π P) := by
  intro i j hji
  dsimp [markovDual]
  rw [h_causal j i hji, mul_zero]

/-- **Resolution of the Causal Triviality Paradox on $\mathcal{K}_2$**:
There exists a strictly non-trivial causal operator ($P \neq I$) on `Fin 2` that is
Krein self-adjoint on $\mathcal{K}_2 = (\operatorname{Fin} 2 \to \mathbb{R}) \times (\operatorname{Fin} 2 \to \mathbb{R})$. -/
theorem exists_nontrivial_causal_krein_operator :
    ∃ (π : Fin 2 → ℝ) (P : Fin 2 → Fin 2 → ℝ),
      (∀ i : Fin 2, 0 < π i) ∧
      IsCausal P ∧
      P ≠ (fun i j => if i = j then 1 else 0) ∧
      (∀ u v : (Fin 2 → ℝ) × (Fin 2 → ℝ),
        gPi π (kreinOp π P u) v = gPi π u (kreinOp π P v)) := by
  let π : Fin 2 → ℝ := fun _ => 1
  let P : Fin 2 → Fin 2 → ℝ := fun i j =>
    if i = 0 ∧ j = 0 then 1
    else if i = 1 ∧ j = 0 then 1
    else if i = 1 ∧ j = 1 then 1
    else 0
  have hπ_pos : ∀ i : Fin 2, 0 < π i := fun _ => one_pos
  have hπ_ne : ∀ i : Fin 2, π i ≠ 0 := fun i => ne_of_gt (hπ_pos i)
  have h_causal : IsCausal P := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (lt_irrefl 0 hij)
    · rfl
    · exact False.elim (not_lt_of_gt Fin.zero_lt_one hij)
    · exact False.elim (lt_irrefl 1 hij)
  have h_ne_id : P ≠ (fun i j => if i = j then 1 else 0) := by
    intro h_eq
    have h_entry := congr_fun (congr_fun h_eq 1) 0
    dsimp [P] at h_entry
    norm_num at h_entry
  exact ⟨π, P, hπ_pos, h_causal, h_ne_id, kreinOp_self_adjoint π hπ_ne P⟩

end MobiusCrossSheetDescent

section ZornPolarizedLeftAlternativeCl33

open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering

/-- **Direct $\operatorname{Cl}(3,3)$ Left-Multiplication Clifford Identity on `ZornSplitOctonion R`**:
By polarized left-alternativity of Zorn's split-octonion vector-matrix algebra, the
left-multiplication operators $L_{\iota(z)}(w) = \operatorname{zornMul}(\operatorname{embedVec} z, w)$
of embedded para-Kähler phase-space vectors $z_1, z_2 \in T^+ \oplus T^-$ satisfy the exact
Clifford anticommutator law on every ket $w \in \operatorname{ZornSplitOctonion} R$:
`L_{z₁}(L_{z₂}(w)) + L_{z₂}(L_{z₁}(w)) = g(z₁, z₂) • w`. -/
theorem zorn_leftMul_cl33_clifford_identity
    {R : Type*} [CommRing R] (z₁ z₂ : ParaKahlerVec R) (w : ZornSplitOctonion R) :
    zornAdd (zornMul (embedVec z₁) (zornMul (embedVec z₂) w))
      (zornMul (embedVec z₂) (zornMul (embedVec z₁) w)) =
      zornSmul (paraKahlerMetric z₁ z₂) w :=
  zorn_left_clifford33_soldering z₁ z₂ w

end ZornPolarizedLeftAlternativeCl33

section StageVCrossSiteAndPrunedSink

/-- Uniform creation-creation anticommutativity $\{a_i^\dagger, a_j^\dagger\} = 0$ in the
algebraic UHF colimit `Carrier` for all sites $i, j \in \operatorname{Fin} k$ (both same-site
and cross-site). -/
theorem colimitJW_anticomm_creation_all (k : ℕ) (i j : Fin k) :
    colimitJWCreation k i * colimitJWCreation k j +
      colimitJWCreation k j * colimitJWCreation k i = 0 := by
  unfold colimitJWCreation
  rw [← stageInjection_mul, ← stageInjection_mul, ← stageInjection_add,
    ← complexifyRealMatrix_mul, ← complexifyRealMatrix_mul, ← complexifyRealMatrix_add,
    ← map_mul, ← map_mul, ← map_add,
    jwCreation_anticomm_all k i j,
    map_zero, complexifyRealMatrix_zero, map_zero]

/-- Uniform annihilation-annihilation anticommutativity $\{a_i, a_j\} = 0$ in the
algebraic UHF colimit `Carrier` for all sites $i, j \in \operatorname{Fin} k$ (both same-site
and cross-site). -/
theorem colimitJW_anticomm_annihilation_all (k : ℕ) (i j : Fin k) :
    colimitJWAnnihilation k i * colimitJWAnnihilation k j +
      colimitJWAnnihilation k j * colimitJWAnnihilation k i = 0 := by
  unfold colimitJWAnnihilation
  rw [← stageInjection_mul, ← stageInjection_mul, ← stageInjection_add,
    ← complexifyRealMatrix_mul, ← complexifyRealMatrix_mul, ← complexifyRealMatrix_add,
    ← map_mul, ← map_mul, ← map_add,
    jwAnnihilation_anticomm_all k i j,
    map_zero, complexifyRealMatrix_zero, map_zero]

/-- Mixed creation-annihilation canonical anticommutation relation in `Carrier`,
including both the diagonal CAR value and the off-diagonal zero relation. -/
theorem colimitJW_annihilation_creation_anticomm_all (k : ℕ) (i j : Fin k) :
    colimitJWAnnihilation k i * colimitJWCreation k j +
      colimitJWCreation k j * colimitJWAnnihilation k i =
        if i = j then 1 else 0 := by
  unfold colimitJWAnnihilation colimitJWCreation
  rw [← stageInjection_mul, ← stageInjection_mul, ← stageInjection_add,
    ← complexifyRealMatrix_mul, ← complexifyRealMatrix_mul, ← complexifyRealMatrix_add,
    ← map_mul, ← map_mul, ← map_add,
    InfoGeometry.Clifford.Cl11JordanWignerCARBridge.jwAnnihilation_creation_anticommutator]
  rcases eq_or_ne i j with rfl | hij
  · simp only [↓reduceIte, map_one, complexifyRealMatrix_one]
  · simp only [hij, ↓reduceIte, map_zero, complexifyRealMatrix_zero]

/-- **Pruned Colimit Functional Modular Flow Invariance**:
Because `prunedStageDensity k pw` is diagonal, the stage-`k`-selected pruned colimit functional
is invariant under the real-time Tomita modular automorphism group `modularFlow logits β t`. -/
theorem prunedColimitFunctional_modularFlow_invariant
    (k : ℕ) (pw : PrunedWeights (Fin (2 ^ k)))
    (logits : Fin (2 ^ k) → ℝ) (β t : ℝ) (A : MatrixStage k) :
    selectedStageColimitFunctional k (prunedStageDensity k pw)
        (stageInjection k (modularFlow logits β t A)) =
      selectedStageColimitFunctional k (prunedStageDensity k pw)
        (stageInjection k A) := by
  rw [selectedStageColimitFunctional_stage, selectedStageColimitFunctional_stage,
    matrixTraceFunctional_apply, matrixTraceFunctional_apply]
  congr 1
  rw [Matrix.trace_mul_comm (modularFlow logits β t A),
    Matrix.trace_mul_comm A]
  dsimp [prunedStageDensity]
  exact trace_diagonal_mul_modularFlow (fun i => (2 ^ k : ℂ) * (pw.weights i : ℂ)) logits β t A

/-- **Cross-Stage Pruned Modular-Evolved Colimit Attention Sink Lower Bound (`k ≤ n`)**:
For any positive-semidefinite observable `Aᵀ A` evolved under the real-time modular flow
`modularFlow logits β t` at stage `k` and pushed through the Cuntz-tower bonding homomorphism
`rawMap h` to stage `n` (`k ≤ n`), the real part of the stage-`k`-selected pruned colimit
functional in `Carrier` is bounded below by `w_anchor * ∑ j, (A_{j,anchor})²`. -/
theorem risingSea_pruned_tower_modularFlow_anchor_lower_bound
    {k n : ℕ} (h : k ≤ n) (pw : PrunedWeights (Fin (2 ^ k)))
    (logits : Fin (2 ^ k) → ℝ) (β t : ℝ) (anchor : Fin (2 ^ k))
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) :
    pw.weights anchor * (∑ j : Fin (2 ^ k), (A j anchor) ^ 2) ≤
      (selectedStageColimitFunctional k (prunedStageDensity k pw)
        (stageInjection n
          (rawMap h
            (modularFlow logits β t
              (complexifyRealMatrix (A.transpose * A)))))).re := by
  rw [stageInjection_transition h,
    prunedColimitFunctional_modularFlow_invariant k pw logits β t
      (complexifyRealMatrix (A.transpose * A))]
  exact prunedColimitFunctional_ge_anchor_column_normSq k pw anchor A

/-- Block-diagonal doubling embedding $A \mapsto \operatorname{diag}(A, A)$ of a matrix into the
next UHF stage $M_{m \oplus m}(\mathbb{R})$. -/
def uhfStep {m : Type*} (A : Matrix m m ℝ) : Matrix (m ⊕ m) (m ⊕ m) ℝ :=
  Matrix.fromBlocks A 0 0 A

/-- **Algebraic KMS Trace Cycling and UHF Doubling Trace Law**:
For any invertible density matrix (`hρ : ρ_inv * ρ = 1`), the KMS-conjugated correlator
$\operatorname{Tr}(\rho (A (\rho B \rho^{-1})))$ equals the swapped correlator
$\operatorname{Tr}(\rho (B A))$, and the block-diagonal UHF doubling `uhfStep` scales the
trace by `2`. -/
theorem kms_trace_cycling_and_uhfStep {m : Type*} [Fintype m] [DecidableEq m]
    (ρ ρ_inv A B : Matrix m m ℝ) (hρ : ρ_inv * ρ = 1) :
    Matrix.trace (ρ * (A * (ρ * B * ρ_inv))) = Matrix.trace (ρ * (B * A)) ∧
      Matrix.trace (uhfStep (ρ * (B * A))) = 2 * Matrix.trace (ρ * (B * A)) := by
  constructor
  · calc
      Matrix.trace (ρ * (A * (ρ * B * ρ_inv)))
        = Matrix.trace ((ρ * A * ρ * B) * ρ_inv) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (ρ_inv * (ρ * A * ρ * B)) :=
            Matrix.trace_mul_comm (ρ * A * ρ * B) ρ_inv
      _ = Matrix.trace ((ρ_inv * ρ) * (A * ρ * B)) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (1 * (A * ρ * B)) := by
            rw [hρ]
      _ = Matrix.trace (A * (ρ * B)) := by
            simp only [Matrix.one_mul, Matrix.mul_assoc]
      _ = Matrix.trace ((ρ * B) * A) :=
            Matrix.trace_mul_comm A (ρ * B)
      _ = Matrix.trace (ρ * (B * A)) := by
            rw [Matrix.mul_assoc]
  · unfold uhfStep
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, ← two_mul]

/-- **Completed-Square Toomre Dispersion Stability**:
Whenever the epicyclic frequency $\kappa$, self-gravity coefficient $b$, and sound speed
$c_s \neq 0$ satisfy the Toomre stability bound $b^2 \le c_s^2 \kappa^2$, the quadratic
dispersion relation $\omega^2(k) = \kappa^2 - 2 b k + c_s^2 k^2$ is nonnegative for all
wavenumbers $k \in \mathbb{R}$. -/
theorem quadratic_dispersion_nonneg_of_toomre (κ b c_s k : ℝ)
    (hcs : c_s ≠ 0) (hQ : b ^ 2 ≤ c_s ^ 2 * κ ^ 2) :
    0 ≤ κ ^ 2 - 2 * b * k + c_s ^ 2 * k ^ 2 := by
  have h_ident :
      κ ^ 2 - 2 * b * k + c_s ^ 2 * k ^ 2 =
        (c_s * k - b / c_s) ^ 2 + (c_s ^ 2 * κ ^ 2 - b ^ 2) / c_s ^ 2 := by
    field_simp [hcs]
    ring
  rw [h_ident]
  have h1 : 0 ≤ (c_s * k - b / c_s) ^ 2 := sq_nonneg (c_s * k - b / c_s)
  have h2 : 0 ≤ (c_s ^ 2 * κ ^ 2 - b ^ 2) / c_s ^ 2 :=
    div_nonneg (sub_nonneg.mpr hQ) (sq_nonneg c_s)
  exact add_nonneg h1 h2

end StageVCrossSiteAndPrunedSink

section InevitabilityPosetOrder

/-- Explicit 5-element type indexing the five sections of this module.
Its constructor order is only an enumeration, not a causal precedence claim. -/
inductive InevitabilityStage : Type
  | metric
  | cell
  | nullSheet
  | mobiusCPT
  | risingSeaColimit
  deriving DecidableEq, Repr

instance instInhabitedInevitabilityStage : Inhabited InevitabilityStage :=
  ⟨.metric⟩

/-- Non-default canonical witness for `InevitabilityStage`. -/
def canonicalInevitabilityStage : InevitabilityStage :=
  .risingSeaColimit

/-- Non-degeneracy witness for `InevitabilityStage`: the top stage `.risingSeaColimit` is
distinct from the base stage `.metric`. -/
theorem canonicalInevitabilityStage_ne_metric :
    canonicalInevitabilityStage ≠ .metric := by
  decide

/-- Enumeration of each `InevitabilityStage` by an element of `Fin 5`.
This is not an order embedding: `InevitabilityStage` has no order structure. -/
def inevitabilityStageRank : InevitabilityStage → Fin 5
  | .metric => 0
  | .cell => 1
  | .nullSheet => 2
  | .mobiusCPT => 3
  | .risingSeaColimit => 4

/-- Explicit inverse of `inevitabilityStageRank`. -/
def inevitabilityStageOfRank : Fin 5 → InevitabilityStage
  | ⟨0, _⟩ => .metric
  | ⟨1, _⟩ => .cell
  | ⟨2, _⟩ => .nullSheet
  | ⟨3, _⟩ => .mobiusCPT
  | ⟨_ + 4, _⟩ => .risingSeaColimit

@[simp]
theorem inevitabilityStageOfRank_rank (s : InevitabilityStage) :
    inevitabilityStageOfRank (inevitabilityStageRank s) = s := by
  cases s <;> rfl

@[simp]
theorem inevitabilityStageRank_ofRank (r : Fin 5) :
    inevitabilityStageRank (inevitabilityStageOfRank r) = r := by
  fin_cases r <;> rfl

/-- `inevitabilityStageRank` is injective. -/
theorem inevitabilityStageRank_injective :
    Function.Injective inevitabilityStageRank :=
  Function.LeftInverse.injective inevitabilityStageOfRank_rank

/-- Explicit equivalence `InevitabilityStage ≃ Fin 5`. -/
def inevitabilityStageEquivFin5 : InevitabilityStage ≃ Fin 5 where
  toFun := inevitabilityStageRank
  invFun := inevitabilityStageOfRank
  left_inv := inevitabilityStageOfRank_rank
  right_inv := inevitabilityStageRank_ofRank

end InevitabilityPosetOrder

end InfoGeometry.Synthesis.CategoricalInevitabilityPosetSynthesis

end

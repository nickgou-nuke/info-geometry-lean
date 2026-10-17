/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Epistemology.ChentsovUniquenessContinuous
import InfoGeometry.Epistemology.FisherNaturalGradientSteepest
import InfoGeometry.Synthesis.MathlibCliffordUniversalLiftSynthesis
import InfoGeometry.Canonical.ParaKahlerLagrangianDimension
import InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow

/-!
# Categorical Inevitability Poset Synthesis

This module formalizes the five-stage causal poset of mathematical inevitability
connecting statistical distinguishability, split Clifford cells, para-Kähler
null sheets, Möbius sheet-swapping twists, and the UHF colimit modular flow:

1. **Archetype I — Metric Inevitability (`ChentsovUniquenessContinuous` ↔ `FisherNaturalGradientSteepest`)**:
   - Proves left scalar homogeneity `fisherMetric_smul_left` of the Fisher metric and
     establishes the exact covector representation equivalence
     `scaledFisher_represents_covector_iff`: for any nonzero Chentsov scale `c ≠ 0`, a
     tangent vector `n` represents a covector `ℓ` with respect to `scaledFisherFamily c`
     if and only if `n = c⁻¹ • fisherNaturalGradient P ℓ`.
   - Combines `chentsov_classification_of_seqContinuous` with scaled natural gradient
     representation in `chentsov_unique_scale_and_steepest_ascent`.

2. **Archetype II — Cell Inevitability (`MathlibCliffordUniversalLiftSynthesis`)**:
   - Defines the universal lightcone nilpotent ladder generators `abstractNullPlus` and
     `abstractNullMinus` in `CliffordAlgebra q11Form`.
   - Computes their images under the algebra isomorphism
     `cl11MatrixAlgEquiv : CliffordAlgebra q11Form ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ`
     and proves in `CliffordAlgebra q11Form` via `cl11MatrixAlgEquiv.injective` that
     `abstractNullPlus * abstractNullPlus = 0`, `abstractNullMinus * abstractNullMinus = 0`,
     `abstractNullPlus * abstractNullMinus + abstractNullMinus * abstractNullPlus = 1`,
     and that their sum and difference recover the split Clifford generators
     `CliffordAlgebra.ι q11Form (1, 0)` and `CliffordAlgebra.ι q11Form (0, 1)`.

3. **Archetype III — Null Sheet Inevitability (`ParaKahlerLagrangianDimension`)**:
   - Proves that for any para-Kähler structure `(g, omega, K)`, the diagonal pairings on
     the projected eigen-sheets vanish (`paraKahler_projPlus_projPlus_zero`,
     `paraKahler_projMinus_projMinus_zero`), so the pseudo-Riemannian metric `g` reduces
     identically to the off-diagonal cross-sheet pairing
     `paraKahler_metric_eq_offDiagonal_pairing` and the symplectic form `omega` reduces to
     the antisymmetric cross-sheet pairing `paraKahler_symplectic_eq_offDiagonal_pairing`.

4. **Archetype IV — Möbius Twist & Induced Complex Structure (`IsMobiusTwist`, `inducedComplexStructure`)**:
   - Defines `IsMobiusTwist K M` (`M.comp K = -(K.comp M)`) and proves that any Möbius
     twist swaps the eigen-sheets `InTPlus K` and `InTMinus K` and intertwines the
     spectral projectors `paraProjectorPlus K` and `paraProjectorMinus K`.
   - For any sheet-swapping involution `C` (`IsSheetSwapInvolution K C`), proves that
     `J = inducedComplexStructure C K = C.comp K` satisfies `J.comp J = -LinearMap.id`,
     flips the sign of the para-Kähler metric (`g (J v) (J w) = -g v w`), and preserves
     the symplectic form (`omega (J v) (J w) = omega v w`), with an explicit non-vacuity
     witness `swapSheetInvolution` on `Fin 2 → ℝ`.

5. **Archetype V — Rising Sea Colimit Synthesis (`ColimitAttentionTomitaFlow`)**:
   - Unifies stage-`k` modular flow state invariance and the algebraic KMS boundary
     trace-cycling identity inside the UHF `TensorTowerColimit.Carrier` via
     `risingSea_colimit_modular_kms_synthesis` and its cross-stage bonding-map
     lifting `risingSea_tower_propagation_modular_kms_synthesis`.
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
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.AttentionGNSBridge
open InfoGeometry.QuantumContext.AttentionStageColimitState
open InfoGeometry.QuantumContext.MatrixStageSelectedFunctional
open InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow

/-!
## Archetype I: Metric Inevitability — Chentsov Scale Uniqueness & Scaled Natural Gradient Representation
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

/-- **Chentsov Unique Scale & Scaled Natural Gradient Representation Synthesis**:
Every sequentially continuous Markov-invariant metric family `F` is uniquely determined on
all simplex tangent spaces by a single real Chentsov scale `c : ℝ` via `scaledFisherFamily c`,
and whenever `c ≠ 0`, a tangent vector `n` represents a covector `ℓ` under `F.g β P` on the
simplex tangent space if and only if `n = c⁻¹ • fisherNaturalGradient P ℓ`. -/
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
## Archetype II: Cell Inevitability — Universal $\operatorname{Cl}(1,1)$ Nilpotent Lightcone Generators
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

end CellInevitability

/-!
## Archetype III: Null Sheet Inevitability — Off-Diagonal Cross-Sheet Metric & Symplectic Pairing on $T^+ \oplus T^-$
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
## Archetype IV: Inevitability of the Möbius Twist $M \circ K = - (K \circ M)$ and Induced Complex Structure $J = C \circ K$
-/

section MobiusTwistInevitability

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Möbius Twist Anticommutation Predicate**:
A linear endomorphism `M : V →ₗ[ℝ] V` is a Möbius twist relative to `K` if it anticommutes
with the para-complex polarization `K` (`M ∘ K = - (K ∘ M)`). -/
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
## Archetype V: The Rising Sea Colimit Synthesis — Stage-$k$ Modular Flow & KMS Context Readout
-/

section RisingSeaColimitSynthesis

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

/-- **Rising Sea Colimit Modular-KMS Synthesis**:
Unifies real-time Tomita modular flow invariance (`modularFlow logits β t`) with the
imaginary-time KMS boundary trace-cycling relation inside the UHF direct-limit `Carrier`:
evolving the KMS-conjugated product `A (ρ B ρ⁻¹)` under `modularFlow logits β t` at
stage `k` and injecting into `Carrier` yields the exact colimit expectation of `B * A`. -/
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

/-- **Cross-Stage Tower Propagation of the Modular-KMS Colimit Synthesis (`k ≤ n`)**:
Pushing the modular-evolved KMS-conjugated observable forward from stage `k` to any higher
stage `n` (`k ≤ n`) along the Cuntz–UHF bonding homomorphism `rawMap h` and injecting into
`Carrier` preserves the exact KMS trace-cycled expectation of `B * A`. -/
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

end RisingSeaColimitSynthesis

end InfoGeometry.Synthesis.CategoricalInevitabilityPosetSynthesis

end

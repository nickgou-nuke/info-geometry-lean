import InfoGeometry.Lie.SplitOctonionEllNativeSupportGrading
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Exact dimensions of the native split-octonion ell-flow sectors

The actual basis
`(N₁⁻, N₂⁻, N₃⁻, 1, ℓ, N₁⁺, N₂⁺, N₃⁺)` diagonalizes
`ellGrading`.  This owner turns the counted basis weights into genuine
`Module.finrank` theorems for the ranges of the three polynomial projectors.

The proof is basis-native: active basis vectors give a lower bound on the
range, inactive basis vectors give the complementary lower bound on the
kernel, and rank-nullity forces equality.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllFlowDimension

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionEllFlowDecomposition
open InfoGeometry.Lie.SplitOctonionEllNativeTrifactor
open InfoGeometry.Lie.SplitOctonionEllPolarization

abbrev CZ := CanonicalZorn
abbrev EndCZ := Module.End ℝ CZ

private def lowerIndex (i : Fin 3) : Fin 8 := ⟨i.1, by omega⟩
private def centerIndex (i : Fin 2) : Fin 8 := ⟨i.1 + 3, by omega⟩
private def upperIndex (i : Fin 3) : Fin 8 := ⟨i.1 + 5, by omega⟩

private theorem lowerIndex_injective : Function.Injective lowerIndex := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 8 => x.val) h

private theorem centerIndex_injective : Function.Injective centerIndex := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [centerIndex] at this
  omega

private theorem upperIndex_injective : Function.Injective upperIndex := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [upperIndex] at this
  omega

private def lowerCenterIndex : Fin 3 ⊕ Fin 2 → Fin 8
  | Sum.inl i => lowerIndex i
  | Sum.inr i => centerIndex i

private def centerUpperIndex : Fin 2 ⊕ Fin 3 → Fin 8
  | Sum.inl i => centerIndex i
  | Sum.inr i => upperIndex i

private def lowerUpperIndex : Fin 3 ⊕ Fin 3 → Fin 8
  | Sum.inl i => lowerIndex i
  | Sum.inr i => upperIndex i

private theorem lowerCenterIndex_injective :
    Function.Injective lowerCenterIndex := by
  intro i j h
  cases i with
  | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (lowerIndex_injective h)
      | inr j =>
          have hv := congrArg Fin.val h
          simp [lowerCenterIndex, lowerIndex, centerIndex] at hv
          omega
  | inr i =>
      cases j with
      | inl j =>
          have hv := congrArg Fin.val h
          simp [lowerCenterIndex, lowerIndex, centerIndex] at hv
          omega
      | inr j => exact congrArg Sum.inr (centerIndex_injective h)

private theorem centerUpperIndex_injective :
    Function.Injective centerUpperIndex := by
  intro i j h
  cases i with
  | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (centerIndex_injective h)
      | inr j =>
          have hv := congrArg Fin.val h
          simp [centerUpperIndex, centerIndex, upperIndex] at hv
          omega
  | inr i =>
      cases j with
      | inl j =>
          have hv := congrArg Fin.val h
          simp [centerUpperIndex, centerIndex, upperIndex] at hv
          omega
      | inr j => exact congrArg Sum.inr (upperIndex_injective h)

private theorem lowerUpperIndex_injective :
    Function.Injective lowerUpperIndex := by
  intro i j h
  cases i with
  | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (lowerIndex_injective h)
      | inr j =>
          have hv := congrArg Fin.val h
          simp [lowerUpperIndex, lowerIndex, upperIndex] at hv
          omega
  | inr i =>
      cases j with
      | inl j =>
          have hv := congrArg Fin.val h
          simp [lowerUpperIndex, lowerIndex, upperIndex] at hv
          omega
      | inr j => exact congrArg Sum.inr (upperIndex_injective h)

/-- A rank-nullity lemma for an endomorphism whose active and inactive vectors
are disjoint subfamilies of a fixed eight-dimensional basis. -/
private theorem finrank_range_eq_card_of_basis_action
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : EndCZ) (active : ι → Fin 8) (inactive : κ → Fin 8)
    (hactive : Function.Injective active)
    (hinactive : Function.Injective inactive)
    (hf_active : ∀ i, f (ellWeightBasisReal (active i)) =
      ellWeightBasisReal (active i))
    (hf_inactive : ∀ i, f (ellWeightBasisReal (inactive i)) = 0)
    (hcard : Fintype.card ι + Fintype.card κ = 8) :
    Module.finrank ℝ (LinearMap.range f) = Fintype.card ι := by
  letI : FiniteDimensional ℝ CZ :=
    Module.Basis.finiteDimensional_of_finite ellWeightBasisReal
  let activeFamily : ι → CZ := fun i => ellWeightBasisReal (active i)
  let inactiveFamily : κ → CZ := fun i => ellWeightBasisReal (inactive i)
  have hliActive : LinearIndependent ℝ activeFamily :=
    ellWeightBasisReal.linearIndependent.comp active hactive
  have hliInactive : LinearIndependent ℝ inactiveFamily :=
    ellWeightBasisReal.linearIndependent.comp inactive hinactive
  have hspanActive :
      Submodule.span ℝ (Set.range activeFamily) ≤ LinearMap.range f := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨i, rfl⟩
    exact ⟨activeFamily i, hf_active i⟩
  have hspanInactive :
      Submodule.span ℝ (Set.range inactiveFamily) ≤ LinearMap.ker f := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨i, rfl⟩
    exact LinearMap.mem_ker.mpr (hf_inactive i)
  have hactiveLe :
      Fintype.card ι ≤ Module.finrank ℝ (LinearMap.range f) := by
    rw [← finrank_span_eq_card hliActive]
    exact Submodule.finrank_mono hspanActive
  have hinactiveLe :
      Fintype.card κ ≤ Module.finrank ℝ (LinearMap.ker f) := by
    rw [← finrank_span_eq_card hliInactive]
    exact Submodule.finrank_mono hspanInactive
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hdim : Module.finrank ℝ CZ = 8 := by
    rw [Module.finrank_eq_card_basis ellWeightBasisReal]
    simp
  rw [hdim] at hrank
  omega

private theorem flowPlus_on_upper (i : Fin 3) :
    flowPlus (ellWeightBasisReal (upperIndex i)) =
      ellWeightBasisReal (upperIndex i) := by
  rw [flowPlus_ellWeightBasisReal]
  fin_cases i <;> simp [upperIndex, InfoGeometry.Lie.SplitOctonionEllFlowDecomposition.ellWeight]

private theorem flowPlus_on_lowerCenter (i : Fin 3 ⊕ Fin 2) :
    flowPlus (ellWeightBasisReal (lowerCenterIndex i)) = 0 := by
  rw [flowPlus_ellWeightBasisReal]
  cases i with
  | inl i => fin_cases i <;> simp [lowerCenterIndex, lowerIndex,
      InfoGeometry.Lie.SplitOctonionEllFlowDecomposition.ellWeight]
  | inr i => fin_cases i <;> simp [lowerCenterIndex, centerIndex,
      InfoGeometry.Lie.SplitOctonionEllFlowDecomposition.ellWeight]

private theorem flowMinus_on_lower (i : Fin 3) :
    flowMinus (ellWeightBasisReal (lowerIndex i)) =
      ellWeightBasisReal (lowerIndex i) := by
  rw [flowMinus_ellWeightBasisReal]
  fin_cases i <;> simp [lowerIndex, InfoGeometry.Lie.SplitOctonionEllFlowDecomposition.ellWeight]

private theorem flowMinus_on_centerUpper (i : Fin 2 ⊕ Fin 3) :
    flowMinus (ellWeightBasisReal (centerUpperIndex i)) = 0 := by
  rw [flowMinus_ellWeightBasisReal]
  cases i with
  | inl i => fin_cases i <;> simp [centerUpperIndex, centerIndex,
      InfoGeometry.Lie.SplitOctonionEllFlowDecomposition.ellWeight]
  | inr i => fin_cases i <;> simp [centerUpperIndex, upperIndex,
      InfoGeometry.Lie.SplitOctonionEllFlowDecomposition.ellWeight]

private theorem flowZero_on_center (i : Fin 2) :
    flowZero (ellWeightBasisReal (centerIndex i)) =
      ellWeightBasisReal (centerIndex i) := by
  rw [flowZero_ellWeightBasisReal]
  fin_cases i <;> simp [centerIndex, InfoGeometry.Lie.SplitOctonionEllFlowDecomposition.ellWeight]

private theorem flowZero_on_lowerUpper (i : Fin 3 ⊕ Fin 3) :
    flowZero (ellWeightBasisReal (lowerUpperIndex i)) = 0 := by
  rw [flowZero_ellWeightBasisReal]
  cases i with
  | inl i => fin_cases i <;> simp [lowerUpperIndex, lowerIndex,
      InfoGeometry.Lie.SplitOctonionEllFlowDecomposition.ellWeight]
  | inr i => fin_cases i <;> simp [lowerUpperIndex, upperIndex,
      InfoGeometry.Lie.SplitOctonionEllFlowDecomposition.ellWeight]

/-- The positive ell-flow sector has real dimension three. -/
@[simp] theorem flowPlus_range_finrank :
    Module.finrank ℝ (LinearMap.range flowPlus) = 3 := by
  simpa using finrank_range_eq_card_of_basis_action flowPlus upperIndex
    lowerCenterIndex upperIndex_injective lowerCenterIndex_injective
    flowPlus_on_upper flowPlus_on_lowerCenter (by decide)

/-- The stationary/Drazin-defect ell-flow sector has real dimension two. -/
@[simp] theorem flowZero_range_finrank :
    Module.finrank ℝ (LinearMap.range flowZero) = 2 := by
  simpa using finrank_range_eq_card_of_basis_action flowZero centerIndex
    lowerUpperIndex centerIndex_injective lowerUpperIndex_injective
    flowZero_on_center flowZero_on_lowerUpper (by decide)

/-- The negative ell-flow sector has real dimension three. -/
@[simp] theorem flowMinus_range_finrank :
    Module.finrank ℝ (LinearMap.range flowMinus) = 3 := by
  simpa using finrank_range_eq_card_of_basis_action flowMinus lowerIndex
    centerUpperIndex lowerIndex_injective centerUpperIndex_injective
    flowMinus_on_lower flowMinus_on_centerUpper (by decide)

end InfoGeometry.Lie.SplitOctonionEllFlowDimension

import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import InfoGeometry.Canonical.CanonicalZornCompositionFiveGradeBridge
import InfoGeometry.Canonical.IntegralZornII44Bridge

/-!
# Canonical Clifford representation from Zorn composition triality

The two typed semispinor copies are combined into a sixteen-dimensional Dirac
carrier.  Zorn multiplication and canonical conjugation define an off-diagonal
gamma operator.  Its square is scalar multiplication by the Zorn norm, so the
universal property produces an actual representation of the Clifford algebra.

This is a representation of the Clifford algebra of the complexified split
quadratic space.  It does not yet package a real `Spin(4,4)` subgroup action.
-/

noncomputable section

namespace CanonicalZornCliffordRepresentation

open InfoGeometry.Physics.SplitOctonionBraidSU3
open CanonicalZornCompositionFiveGradeBridge
open CanonicalZornCompositionTriality
open CanonicalZornFiveGradedClosure

/-! ## The quadratic form on the typed vector carrier -/

/-- Zorn determinant in the fixed eight-coordinate presentation. -/
def coordinateQuadraticFun (x : Fin 8 → ℂ) : ℂ :=
  x 0 * x 7 - x 1 * x 4 - x 2 * x 5 - x 3 * x 6

/-- The coordinate Zorn determinant as a genuine quadratic form. -/
def coordinateQuadratic : QuadraticForm ℂ (Fin 8 → ℂ) :=
  QuadraticMap.ofPolar coordinateQuadraticFun
    (by
      intro c x
      simp [coordinateQuadraticFun]
      ring)
    (by
      intro x x' y
      simp [QuadraticMap.polar, coordinateQuadraticFun]
      ring)
    (by
      intro c x y
      simp [QuadraticMap.polar, coordinateQuadraticFun]
      ring)

/-- Pull the coordinate determinant back to the typed vector copy. -/
def vectorQuadratic : QuadraticForm ℂ Vector8 :=
  coordinateQuadratic.comp
    (copyLinearEquivCoordinates TrialitySector.vector :
      Vector8 →ₗ[ℂ] (Fin 8 → ℂ))

theorem coordinateQuadratic_apply (x : Fin 8 → ℂ) :
    coordinateQuadratic x = coordinateQuadraticFun x := by
  rfl

theorem vectorQuadratic_apply (V : Vector8) :
    vectorQuadratic V = vectorNorm V := by
  change coordinateQuadraticFun
      (CanonicalZornCompositionTriality.zornCoordinates V.val) = zornNorm V.val
  simp [coordinateQuadraticFun, CanonicalZornCompositionTriality.zornCoordinates,
    zornNorm, dot3]
  ring

/-! ## Linear structure of the two typed semispinor copies -/

theorem copy_add_val {s : TrialitySector} (X Y : ZornCopy s) :
    (X + Y).val = zornAdd X.val Y.val := by
  apply CanonicalZornCompositionTriality.zornCoordinates_injective
  change (copyLinearEquivCoordinates s) (X + Y) =
    CanonicalZornCompositionTriality.zornCoordinates (zornAdd X.val Y.val)
  rw [(copyLinearEquivCoordinates s).map_add]
  funext i
  fin_cases i <;>
    simp [copyLinearEquivCoordinates, copyEquivCoordinates,
      CanonicalZornCompositionTriality.zornCoordinates, zornAdd]

theorem copy_smul_val {s : TrialitySector} (c : ℂ) (X : ZornCopy s) :
    (c • X).val = zornSmul c X.val := by
  apply CanonicalZornCompositionTriality.zornCoordinates_injective
  change (copyLinearEquivCoordinates s) (c • X) =
    CanonicalZornCompositionTriality.zornCoordinates (zornSmul c X.val)
  rw [(copyLinearEquivCoordinates s).map_smul]
  funext i
  fin_cases i <;>
    simp [copyLinearEquivCoordinates, copyEquivCoordinates,
      CanonicalZornCompositionTriality.zornCoordinates, zornSmul]

/-- Direct sum of the two chiral eight-dimensional carriers. -/
abbrev DiracSpinor16 := SpinorPlus8 × SpinorMinus8

theorem diracSpinor_finrank : Module.finrank ℂ DiracSpinor16 = 16 := by
  rw [Module.finrank_prod, copy_finrank_eight, copy_finrank_eight]

/-! ## Gamma operators -/

/-- Off-diagonal gamma action associated with a typed vector. -/
def diracGamma (V : Vector8) : Module.End ℂ DiracSpinor16 where
  toFun Ψ := (cliffordMinus V Ψ.2, cliffordPlus V Ψ.1)
  map_add' Ψ Φ := by
    apply Prod.ext
    · apply ZornCopy.ext
      simp [cliffordMinus, copy_add_val, zornMul_add]
    · apply ZornCopy.ext
      simp [cliffordPlus, copy_add_val, zornMul_add]
  map_smul' c Ψ := by
    apply Prod.ext
    · apply ZornCopy.ext
      simp [cliffordMinus, copy_smul_val, zornMul_smul]
    · apply ZornCopy.ext
      simp [cliffordPlus, copy_smul_val, zornMul_smul]

theorem diracGamma_sq_apply (V : Vector8) (Ψ : DiracSpinor16) :
    diracGamma V (diracGamma V Ψ) = vectorQuadratic V • Ψ := by
  apply Prod.ext
  · apply ZornCopy.ext
    change (cliffordMinus V (cliffordPlus V Ψ.1)).val =
      ((vectorQuadratic V) • Ψ.1).val
    rw [copy_smul_val, vectorQuadratic_apply]
    exact cliffordMinus_plus V Ψ.1
  · apply ZornCopy.ext
    change (cliffordPlus V (cliffordMinus V Ψ.2)).val =
      ((vectorQuadratic V) • Ψ.2).val
    rw [copy_smul_val, vectorQuadratic_apply]
    exact cliffordPlus_minus V Ψ.2

theorem diracGamma_sq (V : Vector8) :
    diracGamma V * diracGamma V =
      algebraMap ℂ (Module.End ℂ DiracSpinor16) (vectorQuadratic V) := by
  apply LinearMap.ext
  intro Ψ
  exact diracGamma_sq_apply V Ψ

/-- Gamma depends linearly on its vector argument. -/
def diracGammaLinear : Vector8 →ₗ[ℂ] Module.End ℂ DiracSpinor16 where
  toFun := diracGamma
  map_add' V W := by
    apply LinearMap.ext
    intro Ψ
    apply Prod.ext
    · apply ZornCopy.ext
      simp [diracGamma, cliffordMinus, copy_add_val, zornConj_add,
        add_zornMul]
    · apply ZornCopy.ext
      simp [diracGamma, cliffordPlus, copy_add_val, add_zornMul]
  map_smul' c V := by
    apply LinearMap.ext
    intro Ψ
    apply Prod.ext
    · apply ZornCopy.ext
      simp [diracGamma, cliffordMinus, copy_smul_val, zornConj_smul,
        smul_zornMul]
    · apply ZornCopy.ext
      simp [diracGamma, cliffordPlus, copy_smul_val, smul_zornMul]

/-- The universal Clifford-algebra representation on the Zorn Dirac carrier. -/
def zornCliffordRepresentation :
    CliffordAlgebra vectorQuadratic →ₐ[ℂ] Module.End ℂ DiracSpinor16 :=
  CliffordAlgebra.lift vectorQuadratic ⟨diracGammaLinear, diracGamma_sq⟩

@[simp] theorem zornCliffordRepresentation_ι (V : Vector8) :
    zornCliffordRepresentation (CliffordAlgebra.ι vectorQuadratic V) =
      diracGamma V := by
  exact CliffordAlgebra.lift_ι_apply diracGammaLinear diracGamma_sq V

/-- The constructed representation restricts to the two chiral Zorn actions
on the Clifford generators. -/
theorem zornCliffordRepresentation_generator_action
    (V : Vector8) (S : SpinorPlus8) (C : SpinorMinus8) :
    zornCliffordRepresentation (CliffordAlgebra.ι vectorQuadratic V) (S, C) =
      (cliffordMinus V C, cliffordPlus V S) := by
  rw [zornCliffordRepresentation_ι]
  rfl

/-! ## Restriction to the complex spin group -/

/-- The universal Clifford representation sends Clifford units to invertible
linear operators.  Restricting along Mathlib's spin group gives a genuine
group representation on the sixteen-dimensional Dirac carrier. -/
def complexSpinDiracRepresentation :
    spinGroup vectorQuadratic →* LinearMap.GeneralLinearGroup ℂ DiracSpinor16 :=
  (Units.map zornCliffordRepresentation.toRingHom.toMonoidHom).comp
    spinGroup.toUnits

theorem complexSpinDiracRepresentation_val
    (g : spinGroup vectorQuadratic) :
    ((complexSpinDiracRepresentation g :
      LinearMap.GeneralLinearGroup ℂ DiracSpinor16) :
        Module.End ℂ DiracSpinor16) =
      zornCliffordRepresentation (g : CliffordAlgebra vectorQuadratic) := by
  rfl

theorem complexSpinDiracRepresentation_mul
    (g h : spinGroup vectorQuadratic) :
    complexSpinDiracRepresentation (g * h) =
      complexSpinDiracRepresentation g * complexSpinDiracRepresentation h := by
  exact map_mul complexSpinDiracRepresentation g h

theorem complexSpinDiracRepresentation_inv
    (g : spinGroup vectorQuadratic) :
    complexSpinDiracRepresentation g⁻¹ =
      (complexSpinDiracRepresentation g)⁻¹ := by
  exact map_inv complexSpinDiracRepresentation g

/-! ## Integral `II₄,₄` compatibility -/

/-- An integral Zorn lattice point in the typed vector carrier. -/
def integralVector8 (X : IntegralZornII44Bridge.IntegralZorn) : Vector8 :=
  realVector8 (IntegralZornII44Bridge.integralToCoreZorn X)

/-- The Clifford quadratic form restricts to the integral `II₄,₄`
quadratic refinement. -/
theorem vectorQuadratic_integralVector8
    (X : IntegralZornII44Bridge.IntegralZorn) :
    vectorQuadratic (integralVector8 X) =
      (IntegralZornII44Bridge.integralZornNorm X : ℂ) := by
  rw [vectorQuadratic_apply]
  change zornNorm
    (CanonicalZornProjectiveTKKBridge.coreToCanonical
      (IntegralZornII44Bridge.integralToCoreZorn X)) = _
  rw [CanonicalZornProjectiveTKKBridge.coreToCanonical_norm,
    IntegralZornII44Bridge.integralToCoreZorn_det]
  norm_num

/-- Integral lattice vectors act on the Dirac carrier with square equal to
their integral `II₄,₄` norm. -/
theorem integralVector8_gamma_sq
    (X : IntegralZornII44Bridge.IntegralZorn) :
    diracGamma (integralVector8 X) * diracGamma (integralVector8 X) =
      algebraMap ℂ (Module.End ℂ DiracSpinor16)
        (IntegralZornII44Bridge.integralZornNorm X : ℂ) := by
  rw [diracGamma_sq, vectorQuadratic_integralVector8]

/-- Final compiler-visible bridge from an integral `II₄,₄` point through
the affine projective null lift and concrete five-grading to the universal
Clifford representation generated by Zorn triality. -/
theorem integral_triality_clifford_five_grade_projective_closure
    (X : IntegralZornII44Bridge.IntegralZorn)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    conformalVectorQuadratic
      (zornProjectiveVector (IntegralZornII44Bridge.integralToCoreZorn X)) = 0 ∧
    vectorGradePlus (integralVector8 X) ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 ∧
    spinorPlusGradePlus S ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 ∧
    zornCliffordRepresentation
        (CliffordAlgebra.ι vectorQuadratic (integralVector8 X)) (S, C) =
      (cliffordMinus (integralVector8 X) C,
        cliffordPlus (integralVector8 X) S) ∧
    diracGamma (integralVector8 X) * diracGamma (integralVector8 X) =
      algebraMap ℂ (Module.End ℂ DiracSpinor16)
        (IntegralZornII44Bridge.integralZornNorm X : ℂ) := by
  have hbridge := composition_triality_five_grade_projective_bridge
    (IntegralZornII44Bridge.integralToCoreZorn X) S
  exact ⟨hbridge.1, hbridge.2.1, hbridge.2.2.1,
    zornCliffordRepresentation_generator_action _ S C,
    integralVector8_gamma_sq X⟩

end CanonicalZornCliffordRepresentation

end noncomputable section

import CanonicalZornRealSpin44

/-!
# Triality covariance of the canonical Zorn Clifford and spin actions

There are two different order-three structures in the preceding files:

* Cartan composition triality cyclically relates the typed carriers
  `8v`, `8s`, and `8c` through the invariant trilinear form;
* the cyclic permutation of the three Zorn vector axes is an internal
  order-three algebra automorphism.

This file lifts the second, genuine quadratic isometry to the Clifford
algebra, proves covariance of the gamma operators on `8s ⊕ 8c`, and transports
the spin representation by the resulting order-three change of basis.  It
does not identify the internal axis cycle with the outer Cartan triality.
-/

noncomputable section

namespace CanonicalZornTrialitySpinEquivariance

open SplitOctonionBraidSU3
open CanonicalZornProjectiveTKKBridge
open CanonicalZornFiveGradedClosure
open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation

/-! ## The internal order-three Zorn automorphism on every typed copy -/

/-- Coordinate reindexing implementing the canonical cyclic Zorn-axis map. -/
def axisCycleCoordinates : (Fin 8 → ℂ) ≃ₗ[ℂ] (Fin 8 → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ trialityCoordinateEquiv.symm

/-- The same order-three coordinate isometry on any typed triality copy. -/
def axisCycleCopy (sector : TrialitySector) :
    ZornCopy sector ≃ₗ[ℂ] ZornCopy sector :=
  (copyLinearEquivCoordinates sector).trans
    (axisCycleCoordinates.trans (copyLinearEquivCoordinates sector).symm)

theorem axisCycleCopy_val {sector : TrialitySector} (X : ZornCopy sector) :
    (axisCycleCopy sector X).val = canonicalTriality X.val := by
  apply zornCoordinates_injective
  funext i
  fin_cases i <;> rfl

theorem canonicalTriality_conj (X : Zorn) :
    canonicalTriality (zornConj X) = zornConj (canonicalTriality X) := by
  apply zorn_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem axisCycleCopy_order_three {sector : TrialitySector}
    (X : ZornCopy sector) :
    axisCycleCopy sector (axisCycleCopy sector (axisCycleCopy sector X)) = X := by
  apply ZornCopy.ext
  rw [axisCycleCopy_val, axisCycleCopy_val, axisCycleCopy_val]
  exact canonicalTriality_order_three X.val

abbrev vectorAxisCycle : Vector8 ≃ₗ[ℂ] Vector8 := axisCycleCopy .vector
abbrev spinorPlusAxisCycle : SpinorPlus8 ≃ₗ[ℂ] SpinorPlus8 :=
  axisCycleCopy .spinorPlus
abbrev spinorMinusAxisCycle : SpinorMinus8 ≃ₗ[ℂ] SpinorMinus8 :=
  axisCycleCopy .spinorMinus

theorem vectorAxisCycle_norm (V : Vector8) :
    vectorNorm (vectorAxisCycle V) = vectorNorm V := by
  change zornNorm (vectorAxisCycle V).val = zornNorm V.val
  rw [axisCycleCopy_val, canonicalTriality_norm]

theorem vectorAxisCycle_order_three (V : Vector8) :
    vectorAxisCycle (vectorAxisCycle (vectorAxisCycle V)) = V :=
  axisCycleCopy_order_three V

/-- The vector-axis cycle as an isometry of the Clifford quadratic form. -/
def vectorAxisIsometry : vectorQuadratic →qᵢ vectorQuadratic where
  toLinearMap := vectorAxisCycle
  map_app' V := by
    rw [vectorQuadratic_apply, vectorQuadratic_apply]
    exact vectorAxisCycle_norm V

/-! ## Clifford and gamma covariance -/

/-- Algebra endomorphism induced by the order-three quadratic isometry. -/
def cliffordAxisCycle :
    CliffordAlgebra vectorQuadratic →ₐ[ℂ] CliffordAlgebra vectorQuadratic :=
  CliffordAlgebra.map vectorAxisIsometry

@[simp] theorem cliffordAxisCycle_ι (V : Vector8) :
    cliffordAxisCycle (CliffordAlgebra.ι vectorQuadratic V) =
      CliffordAlgebra.ι vectorQuadratic (vectorAxisCycle V) := by
  exact CliffordAlgebra.map_apply_ι vectorAxisIsometry V

/-- The induced Clifford algebra endomorphism itself has order three. -/
theorem cliffordAxisCycle_order_three :
    cliffordAxisCycle.comp (cliffordAxisCycle.comp cliffordAxisCycle) =
      AlgHom.id ℂ (CliffordAlgebra vectorQuadratic) := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro V
  simp [LinearMap.comp_apply, cliffordAxisCycle_ι,
    vectorAxisCycle_order_three]

/-- Simultaneous order-three change of basis on the two semispinor copies. -/
def diracAxisCycle : DiracSpinor16 ≃ₗ[ℂ] DiracSpinor16 :=
  LinearEquiv.prodCongr spinorPlusAxisCycle spinorMinusAxisCycle

theorem diracAxisCycle_order_three (Ψ : DiracSpinor16) :
    diracAxisCycle (diracAxisCycle (diracAxisCycle Ψ)) = Ψ := by
  apply Prod.ext
  · change spinorPlusAxisCycle
      (spinorPlusAxisCycle (spinorPlusAxisCycle Ψ.1)) = Ψ.1
    exact axisCycleCopy_order_three Ψ.1
  · change spinorMinusAxisCycle
      (spinorMinusAxisCycle (spinorMinusAxisCycle Ψ.2)) = Ψ.2
    exact axisCycleCopy_order_three Ψ.2

/-- The Zorn gamma action is equivariant for the simultaneous axis cycle. -/
theorem diracGamma_axis_covariant (V : Vector8) (Ψ : DiracSpinor16) :
    diracAxisCycle (diracGamma V Ψ) =
      diracGamma (vectorAxisCycle V) (diracAxisCycle Ψ) := by
  apply Prod.ext
  · apply ZornCopy.ext
    change (axisCycleCopy .spinorPlus (cliffordMinus V Ψ.2)).val =
      (cliffordMinus (axisCycleCopy .vector V)
        (axisCycleCopy .spinorMinus Ψ.2)).val
    rw [axisCycleCopy_val]
    change canonicalTriality (zornMul (zornConj V.val) Ψ.2.val) =
      zornMul (zornConj (axisCycleCopy .vector V).val)
        (axisCycleCopy .spinorMinus Ψ.2).val
    rw [axisCycleCopy_val, axisCycleCopy_val]
    rw [canonicalTriality_mul, canonicalTriality_conj]
  · apply ZornCopy.ext
    change (axisCycleCopy .spinorMinus (cliffordPlus V Ψ.1)).val =
      (cliffordPlus (axisCycleCopy .vector V)
        (axisCycleCopy .spinorPlus Ψ.1)).val
    rw [axisCycleCopy_val]
    change canonicalTriality (zornMul V.val Ψ.1.val) =
      zornMul (axisCycleCopy .vector V).val
        (axisCycleCopy .spinorPlus Ψ.1).val
    rw [axisCycleCopy_val, axisCycleCopy_val]
    rw [canonicalTriality_mul]

theorem zornCliffordRepresentation_axis_generator_covariant
    (V : Vector8) (Ψ : DiracSpinor16) :
    diracAxisCycle
        (zornCliffordRepresentation
          (CliffordAlgebra.ι vectorQuadratic V) Ψ) =
      zornCliffordRepresentation
        (cliffordAxisCycle (CliffordAlgebra.ι vectorQuadratic V))
        (diracAxisCycle Ψ) := by
  rw [zornCliffordRepresentation_ι, cliffordAxisCycle_ι,
    zornCliffordRepresentation_ι]
  exact diracGamma_axis_covariant V Ψ

/-- Equivariance extends from generators to every element of the Clifford
algebra. -/
theorem zornCliffordRepresentation_axis_covariant
    (a : CliffordAlgebra vectorQuadratic) (Ψ : DiracSpinor16) :
    diracAxisCycle (zornCliffordRepresentation a Ψ) =
      zornCliffordRepresentation (cliffordAxisCycle a) (diracAxisCycle Ψ) := by
  induction a using CliffordAlgebra.induction generalizing Ψ with
  | algebraMap r =>
      simp
  | ι V =>
      exact zornCliffordRepresentation_axis_generator_covariant V Ψ
  | mul a b ha hb =>
      rw [map_mul zornCliffordRepresentation,
        map_mul cliffordAxisCycle, map_mul zornCliffordRepresentation]
      change diracAxisCycle
          (zornCliffordRepresentation a (zornCliffordRepresentation b Ψ)) =
        zornCliffordRepresentation (cliffordAxisCycle a)
          (zornCliffordRepresentation (cliffordAxisCycle b)
            (diracAxisCycle Ψ))
      rw [ha, hb]
  | add a b ha hb =>
      rw [map_add zornCliffordRepresentation,
        map_add cliffordAxisCycle, map_add zornCliffordRepresentation]
      change diracAxisCycle
          (zornCliffordRepresentation a Ψ + zornCliffordRepresentation b Ψ) =
        zornCliffordRepresentation (cliffordAxisCycle a) (diracAxisCycle Ψ) +
          zornCliffordRepresentation (cliffordAxisCycle b) (diracAxisCycle Ψ)
      rw [map_add, ha, hb]

/-! ## Transport of the spin representation -/

def diracAxisCycleUnit : LinearMap.GeneralLinearGroup ℂ DiracSpinor16 :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv diracAxisCycle

theorem diracAxisCycleUnit_pow_three : diracAxisCycleUnit ^ 3 = 1 := by
  apply Units.ext
  apply LinearMap.ext
  intro Ψ
  change diracAxisCycle (diracAxisCycle (diracAxisCycle Ψ)) = Ψ
  exact diracAxisCycle_order_three Ψ

/-- Apply the Clifford axis automorphism to spin elements, regarded in the
ambient Clifford unit group.  Preservation of Mathlib's particular
`spinGroup` subtype is deliberately not asserted here. -/
def axisMappedSpinUnits :
    spinGroup vectorQuadratic →* (CliffordAlgebra vectorQuadratic)ˣ :=
  (Units.map cliffordAxisCycle.toRingHom.toMonoidHom).comp spinGroup.toUnits

theorem complexSpinDirac_axis_covariant
    (g : spinGroup vectorQuadratic) (Ψ : DiracSpinor16) :
    diracAxisCycle
        ((complexSpinDiracRepresentation g : Module.End ℂ DiracSpinor16) Ψ) =
      zornCliffordRepresentation ((axisMappedSpinUnits g :
        (CliffordAlgebra vectorQuadratic)ˣ) : CliffordAlgebra vectorQuadratic)
        (diracAxisCycle Ψ) := by
  rw [complexSpinDiracRepresentation_val]
  exact zornCliffordRepresentation_axis_covariant (g :
    CliffordAlgebra vectorQuadratic) Ψ

/-- The canonical complex spin representation transported by the order-three
Dirac change of basis. -/
def axisTransportedSpinRepresentation :
    spinGroup vectorQuadratic →*
      LinearMap.GeneralLinearGroup ℂ DiracSpinor16 where
  toFun g := diracAxisCycleUnit * complexSpinDiracRepresentation g *
    diracAxisCycleUnit⁻¹
  map_one' := by
    rw [map_one, mul_one, mul_inv_cancel]
  map_mul' g h := by
    simp only [map_mul]
    group

theorem axisTransportedSpinRepresentation_apply
    (g : spinGroup vectorQuadratic) :
    axisTransportedSpinRepresentation g =
      diracAxisCycleUnit * complexSpinDiracRepresentation g *
        diracAxisCycleUnit⁻¹ := by
  rfl

/-- Composition triality, internal axis covariance, the Clifford lift, the
five-graded automorphism, and spin transport are simultaneously present. -/
theorem triality_clifford_spin_five_grade_closure
    (V : Vector8) (Ψ : DiracSpinor16) (A B : ConformalMatrix) :
    trialityForm V Ψ.1 Ψ.2 =
      trialityForm (spinorMinusToVector Ψ.2)
        (vectorToSpinorPlus V) (spinorPlusToSpinorMinus Ψ.1) ∧
    diracAxisCycle (diracGamma V Ψ) =
      diracGamma (vectorAxisCycle V) (diracAxisCycle Ψ) ∧
    (∀ a : CliffordAlgebra vectorQuadratic,
      diracAxisCycle (zornCliffordRepresentation a Ψ) =
        zornCliffordRepresentation (cliffordAxisCycle a)
          (diracAxisCycle Ψ)) ∧
    cliffordAxisCycle (CliffordAlgebra.ι vectorQuadratic V) =
      CliffordAlgebra.ι vectorQuadratic (vectorAxisCycle V) ∧
    conformalTriality ⁅A, B⁆ =
      ⁅conformalTriality A, conformalTriality B⁆ := by
  exact ⟨trialityForm_cyclic V Ψ.1 Ψ.2,
    diracGamma_axis_covariant V Ψ,
    fun a => zornCliffordRepresentation_axis_covariant a Ψ,
    cliffordAxisCycle_ι V,
    conformalTriality_bracket A B⟩

end CanonicalZornTrialitySpinEquivariance

end noncomputable section

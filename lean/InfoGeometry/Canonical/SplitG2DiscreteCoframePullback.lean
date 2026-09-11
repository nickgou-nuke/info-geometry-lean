import InfoGeometry.Canonical.SplitG2DiscreteHodgeCalibration
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitG2HodgeDualFourForm

namespace InfoGeometry.Canonical

/-!
# Coframe pullback for the discrete split-`G₂` layer

The pointwise alternating forms and the cellular cochains have different
carriers.  This owner supplies the missing coframe map explicitly.  It uses
scalar cochains, since a differential form evaluates to a scalar rather than
to a split-octonion coefficient vector.
-/

abbrev RationalScalarCochain
    (K : FiniteOrientedCellComplex) (p : ℕ) :=
  K.Cell p → ℚ

def rationalScalarCoboundary
    (K : FiniteOrientedCellComplex)
    (p : ℕ) :
    RationalScalarCochain K p →ₗ[ℚ]
      RationalScalarCochain K (p + 1) := by
  letI := K.fintypeCell p
  exact
    { toFun := fun omega sigma =>
        ∑ tau : K.Cell p, (K.incidence p sigma tau : ℚ) * omega tau
      map_add' := by
        intro omega psi
        funext sigma
        simp [Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro a omega
        funext sigma
        change
          (∑ tau : K.Cell p,
            (K.incidence p sigma tau : ℚ) * (a * omega tau)) =
            a * (∑ tau : K.Cell p,
              (K.incidence p sigma tau : ℚ) * omega tau)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro tau ht
        ring }

theorem rationalScalarCoboundary_sq_zero
    (K : FiniteOrientedCellComplex)
    (p : ℕ) :
    (rationalScalarCoboundary K (p + 1)).comp
        (rationalScalarCoboundary K p) = 0 := by
  classical
  letI := K.fintypeCell p
  letI := K.fintypeCell (p + 1)
  apply LinearMap.ext
  intro omega
  funext sigma
  simp only [LinearMap.comp_apply, rationalScalarCoboundary,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
  change
    (∑ rho : K.Cell (p + 1),
      (K.incidence (p + 1) sigma rho : ℚ) *
        (∑ tau : K.Cell p,
          (K.incidence p rho tau : ℚ) * omega tau)) = 0
  calc
    (∑ rho : K.Cell (p + 1),
        (K.incidence (p + 1) sigma rho : ℚ) *
          (∑ tau : K.Cell p,
            (K.incidence p rho tau : ℚ) * omega tau)) =
      ∑ rho : K.Cell (p + 1),
        ∑ tau : K.Cell p,
          ((K.incidence (p + 1) sigma rho : ℚ) *
            (K.incidence p rho tau : ℚ)) * omega tau := by
          apply Finset.sum_congr rfl
          intro rho hr
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro tau ht
          ring
    _ = ∑ tau : K.Cell p,
        ∑ rho : K.Cell (p + 1),
          ((K.incidence (p + 1) sigma rho : ℚ) *
            (K.incidence p rho tau : ℚ)) * omega tau := by
          rw [Finset.sum_comm]
    _ = ∑ tau : K.Cell p,
        (∑ rho : K.Cell (p + 1),
          ((K.incidence (p + 1) sigma rho : ℚ) *
            (K.incidence p rho tau : ℚ))) * omega tau := by
          apply Finset.sum_congr rfl
          intro tau ht
          rw [Finset.sum_mul]
    _ = 0 := by
          have hzero : ∀ tau : K.Cell p,
              (∑ rho : K.Cell (p + 1),
                ((K.incidence (p + 1) sigma rho : ℚ) *
                  (K.incidence p rho tau : ℚ))) = 0 := by
            intro tau
            norm_cast
            exact K.incidence_sq_zero p sigma tau
          simp [hzero]

structure SplitG2DiscreteCoframe (K : FiniteOrientedCellComplex) where
  frame3 : K.Cell 3 → Fin 3 → imaginarySplitOctonion
  frame4 : K.Cell 4 → Fin 4 → imaginarySplitOctonion

def pullbackThreeForm
    {K : FiniteOrientedCellComplex}
    (F : SplitG2DiscreteCoframe K)
    (φ : SplitG2ThreeForms) :
    RationalScalarCochain K 3 :=
  fun sigma => φ (F.frame3 sigma)

def pullbackFourForm
    {K : FiniteOrientedCellComplex}
    (F : SplitG2DiscreteCoframe K)
    (ψ : SplitG2FourForms) :
    RationalScalarCochain K 4 :=
  fun sigma => ψ (F.frame4 sigma)

@[simp] theorem pullbackThreeForm_apply
    {K : FiniteOrientedCellComplex}
    (F : SplitG2DiscreteCoframe K)
    (φ : SplitG2ThreeForms) (sigma : K.Cell 3) :
    pullbackThreeForm F φ sigma = φ (F.frame3 sigma) := rfl

@[simp] theorem pullbackFourForm_apply
    {K : FiniteOrientedCellComplex}
    (F : SplitG2DiscreteCoframe K)
    (ψ : SplitG2FourForms) (sigma : K.Cell 4) :
    pullbackFourForm F ψ sigma = ψ (F.frame4 sigma) := rfl

def pullbackHodgePair
    {K : FiniteOrientedCellComplex}
    (F : SplitG2DiscreteCoframe K)
    (H : SplitG2HodgeDualData)
    (φ : SplitG2ThreeForms) :
    RationalScalarCochain K 3 × RationalScalarCochain K 4 :=
  (pullbackThreeForm F φ,
    pullbackFourForm F (SplitG2HodgeDualData.star34 H φ))

end InfoGeometry.Canonical

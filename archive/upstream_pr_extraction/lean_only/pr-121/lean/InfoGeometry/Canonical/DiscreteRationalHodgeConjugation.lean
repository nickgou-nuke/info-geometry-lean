import Mathlib
import InfoGeometry.Canonical.DiscreteOrientedCellComplex

namespace InfoGeometry.Canonical

/-!
Rational coefficient and Hodge-conjugation layer for the finite incidence
complex.  The `star` field is deliberately an explicit linear equivalence:
metric, orientation, and degree-reversal data are not inferred from it.
-/

abbrev StandardSplitOctonionQ := IntegralSplitBasis → ℚ

abbrev RationalColorCochain
    (K : FiniteOrientedCellComplex) (p : ℕ) :=
  K.Cell p → StandardSplitOctonionQ

def rationalCoboundary
    (K : FiniteOrientedCellComplex)
    (p : ℕ) :
    RationalColorCochain K p →ₗ[ℚ]
      RationalColorCochain K (p + 1) := by
  letI := K.fintypeCell p
  exact
    { toFun := fun omega sigma =>
        ∑ tau : K.Cell p, (K.incidence p sigma tau : ℚ) • omega tau
      map_add' := by
        intro omega psi
        funext sigma
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro a omega
        funext sigma
        change
          (∑ tau : K.Cell p,
            (K.incidence p sigma tau : ℚ) • (a • omega tau)) =
            a • (∑ tau : K.Cell p,
              (K.incidence p sigma tau : ℚ) • omega tau)
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro tau ht
        simp [smul_smul, mul_comm]
        }

theorem rationalCoboundary_sq_zero
    (K : FiniteOrientedCellComplex)
    (p : ℕ) :
    (rationalCoboundary K (p + 1)).comp
        (rationalCoboundary K p) = 0 := by
  classical
  letI := K.fintypeCell p
  letI := K.fintypeCell (p + 1)
  apply LinearMap.ext
  intro omega
  funext sigma
  simp only [LinearMap.comp_apply, rationalCoboundary, LinearMap.coe_mk,
    AddHom.coe_mk]
  change
    (∑ rho : K.Cell (p + 1),
      (K.incidence (p + 1) sigma rho : ℚ) •
        (∑ tau : K.Cell p,
          (K.incidence p rho tau : ℚ) • omega tau)) = 0
  calc
    (∑ rho : K.Cell (p + 1),
        (K.incidence (p + 1) sigma rho : ℚ) •
          (∑ tau : K.Cell p,
            (K.incidence p rho tau : ℚ) • omega tau)) =
      ∑ rho : K.Cell (p + 1),
        ∑ tau : K.Cell p,
          ((K.incidence (p + 1) sigma rho : ℚ) *
            (K.incidence p rho tau : ℚ)) • omega tau := by
          apply Finset.sum_congr rfl
          intro rho hr
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro tau ht
          simp [smul_smul]
    _ = ∑ tau : K.Cell p,
        ∑ rho : K.Cell (p + 1),
          ((K.incidence (p + 1) sigma rho : ℚ) *
            (K.incidence p rho tau : ℚ)) • omega tau := by
          rw [Finset.sum_comm]
    _ = ∑ tau : K.Cell p,
        (∑ rho : K.Cell (p + 1),
          ((K.incidence (p + 1) sigma rho : ℚ) *
            (K.incidence p rho tau : ℚ))) • omega tau := by
          apply Finset.sum_congr rfl
          intro tau ht
          rw [Finset.sum_smul]
    _ = 0 := by
          have hzero : ∀ tau : K.Cell p,
              (∑ rho : K.Cell (p + 1),
                ((K.incidence (p + 1) sigma rho : ℚ) *
                  (K.incidence p rho tau : ℚ))) = 0 := by
            intro tau
            norm_cast
            exact K.incidence_sq_zero p sigma tau
          simp [hzero]

abbrev RationalHodgeData (V : Type*) [AddCommGroup V] [Module ℚ V] :=
  V ≃ₗ[ℚ] V

namespace RationalHodgeData

/-- Compatibility accessor for the native rational Hodge equivalence. -/
def star {V : Type*} [AddCommGroup V] [Module ℚ V]
    (H : RationalHodgeData V) : V ≃ₗ[ℚ] V := H

end RationalHodgeData

def conjugateCodifferential
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (H : RationalHodgeData V)
    (d : V →ₗ[ℚ] V) : V →ₗ[ℚ] V :=
  (RationalHodgeData.star H).symm.toLinearMap.comp
    (d.comp (RationalHodgeData.star H).toLinearMap)

theorem conjugateCodifferential_sq_zero
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (H : RationalHodgeData V)
    (d : V →ₗ[ℚ] V)
    (hd : d.comp d = 0) :
    (conjugateCodifferential H d).comp
        (conjugateCodifferential H d) = 0 := by
  ext x
  have hdx : d (d ((RationalHodgeData.star H) x)) = 0 := by
    have h := congrArg
      (fun f : V →ₗ[ℚ] V => f ((RationalHodgeData.star H) x)) hd
    simpa [LinearMap.comp_apply] using h
  change (RationalHodgeData.star H).symm
      (d ((RationalHodgeData.star H)
        ((RationalHodgeData.star H).symm
          (d ((RationalHodgeData.star H) x))))) = 0
  rw [(RationalHodgeData.star H).apply_symm_apply, hdx]
  simp

def rationalDiracKahler
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (d cod : V →ₗ[ℚ] V) : V →ₗ[ℚ] V :=
  d + cod

def rationalHodgeLaplacian
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (d cod : V →ₗ[ℚ] V) : V →ₗ[ℚ] V :=
  d.comp cod + cod.comp d

theorem rationalDiracKahler_sq_eq_hodgeLaplacian
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (d cod : V →ₗ[ℚ] V)
    (hd : d.comp d = 0)
    (hcod : cod.comp cod = 0) :
    (rationalDiracKahler d cod).comp
        (rationalDiracKahler d cod) =
      rationalHodgeLaplacian d cod := by
  ext x
  simp only [rationalDiracKahler, rationalHodgeLaplacian,
    LinearMap.add_apply, LinearMap.comp_apply]
  have hd_x : d (d x) = 0 := by
    have h := congrArg (fun f : V →ₗ[ℚ] V => f x) hd
    simpa [LinearMap.comp_apply] using h
  have hcod_x : cod (cod x) = 0 := by
    have h := congrArg (fun f : V →ₗ[ℚ] V => f x) hcod
    simpa [LinearMap.comp_apply] using h
  simp [rationalDiracKahler, rationalHodgeLaplacian,
    LinearMap.add_apply, LinearMap.comp_apply,
    hd_x, hcod_x, add_comm, add_left_comm, add_assoc]

end InfoGeometry.Canonical

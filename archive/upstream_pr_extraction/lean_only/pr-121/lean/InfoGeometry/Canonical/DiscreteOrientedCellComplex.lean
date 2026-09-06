import Mathlib
import InfoGeometry.Canonical.ThreeColorIntegralCliffordEmbedding

namespace InfoGeometry.Canonical

/-!
This file separates the cellular coboundary from any coefficient algebra.
The incidence relation is part of the finite oriented cell complex and the
equation `incidence_sq_zero` is the only input needed for `d ^ 2 = 0`.
-/

structure FiniteOrientedCellComplex where
  Cell : ℕ → Type
  fintypeCell : ∀ p, Fintype (Cell p)
  incidence : ∀ p, Cell (p + 1) → Cell p → ℤ
  incidence_sq_zero :
    ∀ p (sigma : Cell (p + 2)) (tau : Cell p),
      ∑ rho : Cell (p + 1),
        incidence (p + 1) sigma rho * incidence p rho tau = 0

abbrev ColorCochain
    (K : FiniteOrientedCellComplex) (p : ℕ) :=
  K.Cell p → StandardIntegralSplitOctonion

def colorCoboundary
    (K : FiniteOrientedCellComplex)
    (p : ℕ) :
    ColorCochain K p →ₗ[ℤ] ColorCochain K (p + 1) := by
  letI := K.fintypeCell p
  exact
    { toFun := fun omega sigma =>
        ∑ tau : K.Cell p, K.incidence p sigma tau • omega tau
      map_add' := by
        intro omega psi
        funext sigma
        simp [Finset.smul_sum, Finset.sum_add_distrib]
      map_smul' := by
        intro a omega
        funext sigma
        change
          (∑ tau : K.Cell p,
            K.incidence p sigma tau • (a • omega tau)) =
            a • (∑ tau : K.Cell p,
              K.incidence p sigma tau • omega tau)
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro tau ht
        simp [smul_smul, mul_comm]
        ring }

theorem colorCoboundary_sq_zero
    (K : FiniteOrientedCellComplex)
    (p : ℕ) :
    (colorCoboundary K (p + 1)).comp
        (colorCoboundary K p) = 0 := by
  classical
  letI := K.fintypeCell p
  letI := K.fintypeCell (p + 1)
  apply LinearMap.ext
  intro omega
  funext sigma
  simp only [LinearMap.comp_apply, colorCoboundary, LinearMap.coe_mk,
    AddHom.coe_mk, Pi.zero_apply]
  change
    (∑ rho : K.Cell (p + 1),
      K.incidence (p + 1) sigma rho •
        (∑ tau : K.Cell p,
          K.incidence p rho tau • omega tau)) = 0
  calc
    (∑ rho : K.Cell (p + 1),
        K.incidence (p + 1) sigma rho •
          (∑ tau : K.Cell p,
            K.incidence p rho tau • omega tau)) =
      ∑ rho : K.Cell (p + 1),
        ∑ tau : K.Cell p,
          (K.incidence (p + 1) sigma rho * K.incidence p rho tau) •
            omega tau := by
          apply Finset.sum_congr rfl
          intro rho hr
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro tau ht
          simp [smul_smul]
          ring
    _ = ∑ tau : K.Cell p,
        ∑ rho : K.Cell (p + 1),
          (K.incidence (p + 1) sigma rho * K.incidence p rho tau) •
            omega tau := by
          rw [Finset.sum_comm]
    _ = ∑ tau : K.Cell p,
        (∑ rho : K.Cell (p + 1),
          K.incidence (p + 1) sigma rho * K.incidence p rho tau) •
            omega tau := by
          apply Finset.sum_congr rfl
          intro tau ht
          rw [Finset.sum_smul]
    _ = 0 := by
          simp [K.incidence_sq_zero]

end InfoGeometry.Canonical

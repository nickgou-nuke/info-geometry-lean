import InfoGeometry.Canonical.DiscreteSplitOctonionAssociator
import InfoGeometry.Canonical.DiscreteRationalHodgeConjugation

namespace InfoGeometry.Canonical

/-!
# Finite Stokes pairing for split-octonion-valued cochains

The incidence matrix already owns the cellular coboundary.  This file adds
the dual boundary on rational chains and proves the finite summation-by-parts
identity.  Coefficients remain the native rational split-octonion module; no
associativity or smooth boundary theorem is used.
-/

abbrev RationalCellChain
    (K : FiniteOrientedCellComplex) (p : ℕ) := K.Cell p → ℚ

def rationalBoundary
    (K : FiniteOrientedCellComplex) (p : ℕ) :
    RationalCellChain K (p + 1) →ₗ[ℚ] RationalCellChain K p := by
  letI := K.fintypeCell (p + 1)
  exact
    { toFun := fun c tau =>
        ∑ sigma : K.Cell (p + 1),
          (K.incidence p sigma tau : ℚ) * c sigma
      map_add' := by
        intro c d
        funext tau
        simp [Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro a c
        funext tau
        change
          (∑ sigma : K.Cell (p + 1),
            (K.incidence p sigma tau : ℚ) * (a * c sigma)) =
            a * (∑ sigma : K.Cell (p + 1),
              (K.incidence p sigma tau : ℚ) * c sigma)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro sigma hs
        ring }

def rationalCellPairing
    {K : FiniteOrientedCellComplex} {p : ℕ}
    (c : RationalCellChain K p)
    (ω : K.Cell p → StandardSplitOctonionQ) :
    StandardSplitOctonionQ := by
  letI := K.fintypeCell p
  exact ∑ sigma : K.Cell p, c sigma • ω sigma

theorem rationalCellPairing_add_right
    {K : FiniteOrientedCellComplex} {p : ℕ}
    (c : RationalCellChain K p)
    (ω η : K.Cell p → StandardSplitOctonionQ) :
    rationalCellPairing c (ω + η) =
      rationalCellPairing c ω + rationalCellPairing c η := by
  classical
  simp [rationalCellPairing, Finset.sum_add_distrib, smul_add]

theorem rationalStokes_pairing
    (K : FiniteOrientedCellComplex) (p : ℕ)
    (c : RationalCellChain K (p + 1))
    (ω : RationalColorCochain K p) :
    rationalCellPairing c (rationalCoboundary K p ω) =
      rationalCellPairing (rationalBoundary K p c) ω := by
  classical
  letI := K.fintypeCell p
  letI := K.fintypeCell (p + 1)
  unfold rationalCellPairing rationalCoboundary rationalBoundary
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  calc
    (∑ sigma : K.Cell (p + 1), c sigma •
        (∑ tau : K.Cell p,
          (K.incidence p sigma tau : ℚ) • ω tau)) =
        ∑ sigma : K.Cell (p + 1),
          ∑ tau : K.Cell p,
            c sigma • ((K.incidence p sigma tau : ℚ) • ω tau) := by
      apply Finset.sum_congr rfl
      intro sigma hs
      rw [Finset.smul_sum]
    _ = ∑ tau : K.Cell p,
        ∑ sigma : K.Cell (p + 1),
          c sigma • ((K.incidence p sigma tau : ℚ) • ω tau) := by
      rw [Finset.sum_comm]
    _ = ∑ tau : K.Cell p,
        (∑ sigma : K.Cell (p + 1),
          (K.incidence p sigma tau : ℚ) * c sigma) • ω tau := by
      apply Finset.sum_congr rfl
      intro tau ht
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro sigma hs
      simp only [smul_smul]
      ring

theorem rationalBoundary_squared_zero
    (K : FiniteOrientedCellComplex) (p : ℕ)
    (c : RationalCellChain K (p + 2)) :
    rationalBoundary K p (rationalBoundary K (p + 1) c) = 0 := by
  classical
  letI := K.fintypeCell p
  letI := K.fintypeCell (p + 1)
  letI := K.fintypeCell (p + 2)
  funext tau
  simp [rationalBoundary]
  have hzero : ∀ sigma : K.Cell (p + 2),
      ∑ rho : K.Cell (p + 1),
        (K.incidence (p + 1) sigma rho : ℚ) *
          (K.incidence p rho tau : ℚ) = 0 := by
    intro sigma
    norm_cast
    exact K.incidence_sq_zero p sigma tau
  calc
    (∑ x : K.Cell (p + 1),
        (K.incidence p x tau : ℚ) *
          (∑ sigma : K.Cell (p + 2),
            (K.incidence (p + 1) sigma x : ℚ) * c sigma)) =
        ∑ x : K.Cell (p + 1),
          ∑ sigma : K.Cell (p + 2),
            ((K.incidence p x tau : ℚ) *
              (K.incidence (p + 1) sigma x : ℚ)) * c sigma := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sigma hs
      ring
    _ = ∑ sigma : K.Cell (p + 2),
        ∑ x : K.Cell (p + 1),
          ((K.incidence (p + 1) sigma x : ℚ) *
            (K.incidence p x tau : ℚ)) * c sigma := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro sigma hs
      ring
    _ = ∑ sigma : K.Cell (p + 2),
        (∑ x : K.Cell (p + 1),
          ((K.incidence (p + 1) sigma x : ℚ) *
            (K.incidence p x tau : ℚ))) * c sigma := by
      apply Finset.sum_congr rfl
      intro sigma hs
      rw [Finset.sum_mul]
    _ = 0 := by simp [hzero]

end InfoGeometry.Canonical

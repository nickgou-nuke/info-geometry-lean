import InfoGeometry.Canonical.DiscreteSplitOctonionStokes

namespace InfoGeometry.Canonical

/-!
# Linear-equivalence covariance of split-octonion cochains

This is the generic version of the colour transport result.  A linear
equivalence of the rational split-octonion coefficient module acts pointwise
on cellular cochains, commutes with the incidence coboundary, and passes
through the finite Stokes pairing.
-/

noncomputable def linearEquivCochain
    {K : FiniteOrientedCellComplex}
    (g : StandardSplitOctonionQ ≃ₗ[ℚ] StandardSplitOctonionQ)
    (p : ℕ) (ω : RationalColorCochain K p) :
    RationalColorCochain K p :=
  fun sigma => g (ω sigma)

theorem linearEquivCochain_coboundary_commutes
    (K : FiniteOrientedCellComplex) (p : ℕ)
    (g : StandardSplitOctonionQ ≃ₗ[ℚ] StandardSplitOctonionQ)
    (ω : RationalColorCochain K p) :
    linearEquivCochain g (p + 1) (rationalCoboundary K p ω) =
      rationalCoboundary K p (linearEquivCochain g p ω) := by
  classical
  letI := K.fintypeCell p
  funext sigma
  simp only [linearEquivCochain, rationalCoboundary, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro tau ht
  rw [map_smul]

theorem linearEquivCochain_pairing_commutes
    {K : FiniteOrientedCellComplex} {p : ℕ}
    (g : StandardSplitOctonionQ ≃ₗ[ℚ] StandardSplitOctonionQ)
    (c : RationalCellChain K p)
    (ω : RationalColorCochain K p) :
    rationalCellPairing c (linearEquivCochain g p ω) =
      g (rationalCellPairing c ω) := by
  classical
  letI := K.fintypeCell p
  unfold rationalCellPairing linearEquivCochain
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro sigma hs
  rw [map_smul]

theorem linearEquiv_transport_stokes
    (K : FiniteOrientedCellComplex) (p : ℕ)
    (g : StandardSplitOctonionQ ≃ₗ[ℚ] StandardSplitOctonionQ)
    (c : RationalCellChain K (p + 1))
    (ω : RationalColorCochain K p) :
    rationalCellPairing c
        (linearEquivCochain g (p + 1) (rationalCoboundary K p ω)) =
      g (rationalCellPairing (rationalBoundary K p c) ω) := by
  rw [linearEquivCochain_coboundary_commutes]
  calc
    rationalCellPairing c
        (rationalCoboundary K p (linearEquivCochain g p ω)) =
      rationalCellPairing (rationalBoundary K p c)
        (linearEquivCochain g p ω) :=
      rationalStokes_pairing K p c (linearEquivCochain g p ω)
    _ = g (rationalCellPairing (rationalBoundary K p c) ω) :=
      linearEquivCochain_pairing_commutes g (rationalBoundary K p c) ω

theorem trialityColorCycle_coboundary_commutes
    (K : FiniteOrientedCellComplex) (p : ℕ)
    (ω : RationalColorCochain K p) :
    linearEquivCochain trialityColorCycle (p + 1)
        (rationalCoboundary K p ω) =
      rationalCoboundary K p
        (linearEquivCochain trialityColorCycle p ω) :=
  linearEquivCochain_coboundary_commutes K p trialityColorCycle ω

theorem colorReflection_coboundary_commutes
    (K : FiniteOrientedCellComplex) (p : ℕ)
    (ω : RationalColorCochain K p) :
    linearEquivCochain colorReflection (p + 1)
        (rationalCoboundary K p ω) =
      rationalCoboundary K p
        (linearEquivCochain colorReflection p ω) :=
  linearEquivCochain_coboundary_commutes K p colorReflection ω

end InfoGeometry.Canonical

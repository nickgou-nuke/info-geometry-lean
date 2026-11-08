import InfoGeometry.Canonical.DiscreteSplitOctonionStokes
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-!
# Colour-automorphism transport of the finite Stokes pairing

The cellular coefficient model is the full rational split-octonion carrier,
where the already verified `trialityColorCycle` acts.  This owner proves that
the linear automorphism commutes with the incidence coboundary and can be
moved through the finite chain/cochain pairing.  It deliberately keeps this
8-dimensional coefficient statement separate from the 7-dimensional
`SplitG2Automorphism` carrier.
-/

noncomputable def colorCycleCochain
    {K : FiniteOrientedCellComplex} (p : ℕ)
    (ω : RationalColorCochain K p) : RationalColorCochain K p :=
  fun sigma => trialityColorCycle (ω sigma)

theorem colorCycleCochain_coboundary_commutes
    (K : FiniteOrientedCellComplex) (p : ℕ)
    (ω : RationalColorCochain K p) :
    colorCycleCochain (p + 1) (rationalCoboundary K p ω) =
      rationalCoboundary K p (colorCycleCochain p ω) := by
  classical
  letI := K.fintypeCell p
  funext sigma
  simp only [colorCycleCochain, rationalCoboundary, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro tau ht
  rw [map_smul]

theorem colorCycleCochain_pairing_commutes
    {K : FiniteOrientedCellComplex} {p : ℕ}
    (c : RationalCellChain K p)
    (ω : RationalColorCochain K p) :
    rationalCellPairing c (colorCycleCochain p ω) =
      trialityColorCycle (rationalCellPairing c ω) := by
  classical
  letI := K.fintypeCell p
  unfold rationalCellPairing colorCycleCochain
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro sigma hs
  rw [map_smul]

theorem colorCycle_transport_stokes
    (K : FiniteOrientedCellComplex) (p : ℕ)
    (c : RationalCellChain K (p + 1))
    (ω : RationalColorCochain K p) :
    rationalCellPairing c
        (colorCycleCochain (p + 1) (rationalCoboundary K p ω)) =
      trialityColorCycle
        (rationalCellPairing (rationalBoundary K p c) ω) := by
  rw [colorCycleCochain_coboundary_commutes]
  calc
    rationalCellPairing c
        (rationalCoboundary K p (colorCycleCochain p ω)) =
      rationalCellPairing (rationalBoundary K p c)
        (colorCycleCochain p ω) :=
      rationalStokes_pairing K p c (colorCycleCochain p ω)
    _ = trialityColorCycle
        (rationalCellPairing (rationalBoundary K p c) ω) :=
      colorCycleCochain_pairing_commutes (rationalBoundary K p c) ω

end InfoGeometry.Canonical

import InfoGeometry.Canonical.DiscreteSplitOctonionCochainEquivariance
import InfoGeometry.Canonical.SplitOctonionColorCycleMultiplicativity

namespace InfoGeometry.Canonical

/-!
# Finite cochain action of the verified colour symmetries

The underlying coefficient maps have order three and order two.  This owner
transports those relations pointwise to cellular cochains.  It records the
available cyclic/involutive action only; the mixed braid relation is not
asserted here because it is not an owner theorem for these linear maps.
-/

theorem trialityColorCycleCochain_order_three
    {K : FiniteOrientedCellComplex} (p : ℕ)
    (ω : RationalColorCochain K p) :
    linearEquivCochain trialityColorCycle p
        (linearEquivCochain trialityColorCycle p
          (linearEquivCochain trialityColorCycle p ω)) = ω := by
  funext sigma
  exact colorCycle_order_three (ω sigma)

theorem colorReflectionCochain_order_two
    {K : FiniteOrientedCellComplex} (p : ℕ)
    (ω : RationalColorCochain K p) :
    linearEquivCochain colorReflection p
        (linearEquivCochain colorReflection p ω) = ω := by
  funext sigma
  have h := congrArg (fun e => e (ω sigma)) colorReflection_sq
  simpa using h

theorem trialityColorCycleCochain_preserves_coboundary
    {K : FiniteOrientedCellComplex} (p : ℕ)
    (ω : RationalColorCochain K p) :
    linearEquivCochain trialityColorCycle (p + 1)
        (rationalCoboundary K p ω) =
      rationalCoboundary K p
        (linearEquivCochain trialityColorCycle p ω) :=
  trialityColorCycle_coboundary_commutes K p ω

theorem colorReflectionCochain_preserves_coboundary
    {K : FiniteOrientedCellComplex} (p : ℕ)
    (ω : RationalColorCochain K p) :
    linearEquivCochain colorReflection (p + 1)
        (rationalCoboundary K p ω) =
      rationalCoboundary K p
        (linearEquivCochain colorReflection p ω) :=
  colorReflection_coboundary_commutes K p ω

end InfoGeometry.Canonical

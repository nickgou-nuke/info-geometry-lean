import Mathlib.Data.Real.Basic

/-!
# Supplied Graded Readout and Finite Pairing

This file records a calibration interface between two scalar readouts.  It
does not construct a supercharge, heat kernel, Möbius Dirichlet series,
McKean--Singer index, or analytic reciprocal of ζ.
-/

namespace InfoGeometry.Canonical.PrimonSupertrace

/-- Supplied graded-partition readouts and their calibration equality. -/
structure GradedPartitionFunction (S : Type*) [CommRing S] where
  (zeta_inverse : S)
  (supertrace   : S)
  /-- Historical field name: this is only a supplied scalar calibration. -/
  (mckean_singer : supertrace = zeta_inverse)

/-- A supplied Witten-style scalar readout agrees with the calibrated
    supertrace.  No Witten-index or Möbius interpretation is derived. -/
theorem witten_index_is_supertrace {S : Type*} [CommRing S] 
    (Z : GradedPartitionFunction S) 
    (WittenIndex : S) 
    (h_witten : WittenIndex = Z.supertrace) : 
    WittenIndex = Z.zeta_inverse := by
  rw [h_witten]
  exact Z.mckean_singer

/-- Conditional scalar pairing: if the supplied inverse readout multiplies a
    supplied value to one, then the calibrated supertrace has the same law. -/
theorem supersymmetric_pairing {S : Type*} [CommRing S] 
    (Z : GradedPartitionFunction S) 
    (zeta : S) 
    (h_inverse : zeta * Z.zeta_inverse = 1) : 
    zeta * Z.supertrace = 1 := by
  rw [Z.mckean_singer]
  exact h_inverse

end InfoGeometry.Canonical.PrimonSupertrace

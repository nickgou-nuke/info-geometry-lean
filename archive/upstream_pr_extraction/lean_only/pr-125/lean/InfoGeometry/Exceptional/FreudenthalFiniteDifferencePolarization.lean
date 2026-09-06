import InfoGeometry.Exceptional.STUQuarticPolarization

/-!
# Finite-difference polarization of a quartic invariant

This file defines the standard finite-difference polarization operator.  The
comparison with the explicit STU permutation formula is intentionally left as
a separate theorem: defining the operator must not be confused with proving
the normalization and reindexing identity.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Polarization operator for a quartic polynomial `P`. -/
def finiteDifferenceQuarticPolarization
    (P : V → ℝ) (Q : Fin 4 → V) : ℝ :=
  (1 / 24 : ℝ) * ∑ s : Finset (Fin 4),
    (-1 : ℝ) ^ (4 - s.card) * P (∑ i ∈ s, Q i)

end InfoGeometry.Exceptional.Freudenthal

namespace InfoGeometry.Exceptional.STUDatum

open InfoGeometry.Exceptional.Freudenthal

/-- The finite-difference polarization of the concrete STU quartic. -/
def stuFiniteDifferenceQuarticPolarization
    (Q : Fin 4 → FreudenthalCharge STUCarrier) : ℝ :=
  finiteDifferenceQuarticPolarization
    (FreudenthalCharge.quarticInvariant STU_Datum) Q

end InfoGeometry.Exceptional.STUDatum

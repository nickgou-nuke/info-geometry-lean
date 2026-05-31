import Mathlib

/-!
# InfoGeometry.Canonical.CompactifiedThermalOperators

Exact algebraic Cayley/Möbius thermal recurrences.

This file stays at the ring level: no Taylor series, no analytic continuation,
and no functional-calculus wrapper.
-/

namespace InfoGeometry.Canonical.CompactifiedThermalOperators

/--
The inductive addition step for the Cayley/Möbius compactification map.

If `Tn * (1 + qn) = 1 - qn` and `T1 * (1 + q) = 1 - q`, then
`(Tn + T1) * (1 + qn * q) = (1 + Tn * T1) * (1 - qn * q)`.
-/
theorem compactified_inductive_step
    {R : Type*} [CommRing R]
    (qn q Tn T1 : R)
    (hTn : Tn * (1 + qn) = 1 - qn)
    (hT1 : T1 * (1 + q) = 1 - q) :
    (Tn + T1) * (1 + qn * q) = (1 + Tn * T1) * (1 - qn * q) := by
  linear_combination q * (1 + T1) * hTn + (1 - Tn) * hT1

/--
Cross-multiplied doubling step for the compactified thermal operator.

This is the exact ring-level form compatible with the recurrence
`T_{2n} = 2 T_n (1 + T_n^2)⁻¹` when the inverse exists.
-/
theorem compactified_doubling_step
    {R : Type*} [CommRing R]
    (qn Tn T2n : R)
    (hTn : Tn * (1 + qn) = 1 - qn)
    (hT2n : T2n * (1 + Tn * Tn) = 2 * Tn) :
    T2n * (1 + qn * qn) * (1 + Tn * Tn) = (1 - qn * qn) * (1 + Tn * Tn) := by
  have hadd :=
    compactified_inductive_step (R := R) (qn := qn) (q := qn) (Tn := Tn) (T1 := Tn) hTn hTn
  have h2 : (2 : R) * Tn * (1 + qn * qn) = (1 + Tn * Tn) * (1 - qn * qn) := by
    calc
      (2 : R) * Tn * (1 + qn * qn) = (Tn + Tn) * (1 + qn * qn) := by ring
      _ = (1 + Tn * Tn) * (1 - qn * qn) := hadd
  calc
    T2n * (1 + qn * qn) * (1 + Tn * Tn)
        = (T2n * (1 + Tn * Tn)) * (1 + qn * qn) := by ring
    _ = ((2 : R) * Tn) * (1 + qn * qn) := by rw [hT2n]
    _ = (2 : R) * Tn * (1 + qn * qn) := by ring
    _ = (1 + Tn * Tn) * (1 - qn * qn) := h2
    _ = (1 - qn * qn) * (1 + Tn * Tn) := by ring

end InfoGeometry.Canonical.CompactifiedThermalOperators

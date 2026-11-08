import InfoGeometry.Orthogonal.O55ContactCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Small reusable coordinate lemmas for the native `(5,5)` carrier. -/

noncomputable section
namespace InfoGeometry.Orthogonal.O55Contact

@[simp] theorem coordinateVector_apply (i j : Fin 10) :
    coordinateVector i j = if j = i then 1 else 0 := rfl

theorem coordinateVector_eq_zero_iff (i : Fin 10) :
    coordinateVector i ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [coordinateVector] at hi

theorem coordinateVector_dual_pairing (i j : Fin 10) :
    splitPairing (coordinateVector i)
        (coordinateVector (dualIndex j)) =
      if j = 5 ∨ j = 6 ∨ j = 7 then
        if i = j then -1 else 0
      else if i = j then 1 else 0 := by
  rw [splitPairing_coordinate_right]
  by_cases h : j = 5 ∨ j = 6 ∨ j = 7
  · by_cases hij : i = j <;> simp [coordinateVector, h, hij, eq_comm]
  · by_cases hij : i = j <;> simp [coordinateVector, h, hij, eq_comm]

theorem coordinateVector_pairing_dual (i j : Fin 10) :
    splitPairing (coordinateVector (dualIndex i))
        (coordinateVector j) =
      if i = 5 ∨ i = 6 ∨ i = 7 then
        if i = j then -1 else 0
      else if i = j then 1 else 0 := by
  rw [splitPairing_comm]
  simpa [eq_comm] using coordinateVector_dual_pairing j i

end InfoGeometry.Orthogonal.O55Contact

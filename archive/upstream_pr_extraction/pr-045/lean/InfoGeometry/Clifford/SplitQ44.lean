import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Clifford

/--
The split quadratic form of signature `(4,4)` on `Fin 8 → ℝ`.

This is the direct diagonal model used by the `Cl(4,4)` split-Witt tower:
the first four coordinates have positive sign, the last four negative sign.
-/
noncomputable def splitQ44 : QuadraticForm ℝ (Fin 8 → ℝ) :=
  QuadraticMap.proj (R := ℝ) (0 : Fin 8) 0 + QuadraticMap.proj 1 1 +
    QuadraticMap.proj 2 2 + QuadraticMap.proj 3 3 -
    (QuadraticMap.proj 4 4 + QuadraticMap.proj 5 5 + QuadraticMap.proj 6 6 +
      QuadraticMap.proj 7 7)

@[simp] theorem splitQ44_apply (x : Fin 8 → ℝ) :
    splitQ44 x =
      x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3 -
        (x 4 * x 4 + x 5 * x 5 + x 6 * x 6 + x 7 * x 7) := by
  simp [splitQ44, QuadraticMap.proj_apply, add_comm, add_left_comm, add_assoc,
    sub_eq_add_neg]

abbrev Cl44 :=
  CliffordAlgebra (splitQ44)

end InfoGeometry.Clifford

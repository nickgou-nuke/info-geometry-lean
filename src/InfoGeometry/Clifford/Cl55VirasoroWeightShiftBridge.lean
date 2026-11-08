import InfoGeometry.Clifford.Cl55FourierGradeReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! The finite, proved predecessor of a Virasoro level-shift statement.
Only the number-adjoint grade is used; no Virasoro bracket or central
extension is asserted here. -/
namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.OperatorAlgebra

theorem creation55_shifts_grade (i : Fin 5) (k : ℤ) {X : Cl55}
    (hX : X ∈ cl55GradeSubmodule k) :
    creation55 i * X ∈ cl55GradeSubmodule (1 + k) := by
  exact grade_mul (creation55_mem_grade_one i) hX

theorem annihilation55_shifts_grade (i : Fin 5) (k : ℤ) {X : Cl55}
    (hX : X ∈ cl55GradeSubmodule k) :
    annihilation55 i * X ∈ cl55GradeSubmodule (-1 + k) := by
  exact grade_mul (annihilation55_mem_grade_neg_one i) hX

theorem creation55_commutator_shifts_grade (i : Fin 5) (k : ℤ) {X : Cl55}
    (hX : X ∈ cl55GradeSubmodule k) :
    creation55 i * X - X * creation55 i ∈
      cl55GradeSubmodule (1 + k) := by
  exact grade_commutator (creation55_mem_grade_one i) hX

theorem annihilation55_commutator_shifts_grade (i : Fin 5) (k : ℤ) {X : Cl55}
    (hX : X ∈ cl55GradeSubmodule k) :
    annihilation55 i * X - X * annihilation55 i ∈
      cl55GradeSubmodule (-1 + k) := by
  exact grade_commutator (annihilation55_mem_grade_neg_one i) hX

end InfoGeometry.Clifford.Clifford55

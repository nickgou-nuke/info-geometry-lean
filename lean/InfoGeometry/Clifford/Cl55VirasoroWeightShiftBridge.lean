import InfoGeometry.Clifford.Cl55FourierGradeReadout

/-! The rigorous finite predecessor of a Virasoro level-shift theorem.
The number-adjoint grade is used as the weight operator; no Virasoro bracket
or central extension is asserted. -/
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

theorem creation55_maps_grade_family (i : Fin 5) :
    MapsToGrade
      (fun k : ℤ => (cl55GradeSubmodule k : Set Cl55))
      (fun _ : Unit => fun X => creation55 i * X)
      (fun _ k => k + 1) := by
  intro _ k X hX
  simpa [add_comm] using creation55_shifts_grade i k hX

theorem annihilation55_maps_grade_family (i : Fin 5) :
    MapsToGrade
      (fun k : ℤ => (cl55GradeSubmodule k : Set Cl55))
      (fun _ : Unit => fun X => annihilation55 i * X)
      (fun _ k => k - 1) := by
  intro _ k X hX
  simpa [sub_eq_add_neg, add_comm] using annihilation55_shifts_grade i k hX

theorem creation55_commutator_maps_grade_family (i : Fin 5) :
    MapsToGrade
      (fun k : ℤ => (cl55GradeSubmodule k : Set Cl55))
      (fun _ : Unit => fun X => creation55 i * X - X * creation55 i)
      (fun _ k => k + 1) := by
  intro _ k X hX
  simpa [add_comm] using creation55_commutator_shifts_grade i k hX

theorem annihilation55_commutator_maps_grade_family (i : Fin 5) :
    MapsToGrade
      (fun k : ℤ => (cl55GradeSubmodule k : Set Cl55))
      (fun _ : Unit => fun X => annihilation55 i * X - X * annihilation55 i)
      (fun _ k => k - 1) := by
  intro _ k X hX
  simpa [sub_eq_add_neg, add_comm] using annihilation55_commutator_shifts_grade i k hX

end InfoGeometry.Clifford.Clifford55

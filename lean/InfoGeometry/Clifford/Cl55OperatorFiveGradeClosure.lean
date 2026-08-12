import InfoGeometry.Clifford.Cl55CARSpinAutomorphism
import InfoGeometry.OperatorAlgebra.ChiralRetainedWordFiveGradeClosure

/-!
# Operatorial five-grade routing on the native `Cl(5,5)` carrier

The carrier is the existing Clifford algebra `Cl55`.  The grading element is
the already-proved CAR number operator.  No second carrier and no realization
record are introduced here.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.OperatorAlgebra

def cl55GradeSubmodule (k : ℤ) : Submodule ℝ Cl55 :=
  gradeSubmodule numberOperator55 k

def spinTransportedCl55GradeSubmodule (g : Spin55) (k : ℤ) :
    Submodule ℝ Cl55 :=
  gradeSubmodule (spinTransportedNumberOperator55 g) k

theorem creation55_mem_grade_one (i : Fin 5) :
    creation55 i ∈ cl55GradeSubmodule 1 := by
  change HasOperatorGrade numberOperator55 (creation55 i) 1
  simpa [HasOperatorGrade] using numberOperator55_commutator_creation i

theorem annihilation55_mem_grade_neg_one (i : Fin 5) :
    annihilation55 i ∈ cl55GradeSubmodule (-1) := by
  change HasOperatorGrade numberOperator55 (annihilation55 i) (-1)
  simpa [HasOperatorGrade] using numberOperator55_commutator_annihilation i

theorem spinTransported_creation55_mem_grade_one (g : Spin55) (i : Fin 5) :
    spinCliffordRingEquiv g (creation55 i) ∈
      spinTransportedCl55GradeSubmodule g 1 := by
  change HasOperatorGrade (spinTransportedNumberOperator55 g)
    (spinCliffordRingEquiv g (creation55 i)) 1
  simpa [HasOperatorGrade] using
    spinTransportedNumberOperator55_commutator_creation g i

theorem spinTransported_annihilation55_mem_grade_neg_one
    (g : Spin55) (i : Fin 5) :
    spinCliffordRingEquiv g (annihilation55 i) ∈
      spinTransportedCl55GradeSubmodule g (-1) := by
  change HasOperatorGrade (spinTransportedNumberOperator55 g)
    (spinCliffordRingEquiv g (annihilation55 i)) (-1)
  simpa [HasOperatorGrade] using
    spinTransportedNumberOperator55_commutator_annihilation g i

theorem creation55_mul_creation55_mem_grade_two (i j : Fin 5) :
    creation55 i * creation55 j ∈ cl55GradeSubmodule 2 := by
  exact grade_mul (creation55_mem_grade_one i)
    (creation55_mem_grade_one j)

theorem annihilation55_mul_annihilation55_mem_grade_neg_two (i j : Fin 5) :
    annihilation55 i * annihilation55 j ∈ cl55GradeSubmodule (-2) := by
  exact grade_mul (annihilation55_mem_grade_neg_one i)
    (annihilation55_mem_grade_neg_one j)

theorem creation55_mul_annihilation55_mem_grade_zero (i j : Fin 5) :
    creation55 i * annihilation55 j ∈ cl55GradeSubmodule 0 := by
  exact grade_mul (creation55_mem_grade_one i)
    (annihilation55_mem_grade_neg_one j)

theorem annihilation55_mul_creation55_mem_grade_zero (i j : Fin 5) :
    annihilation55 i * creation55 j ∈ cl55GradeSubmodule 0 := by
  exact grade_mul (annihilation55_mem_grade_neg_one i)
    (creation55_mem_grade_one j)

theorem cl55_pos_one_pos_one_commutator_mem_grade_two
    {X Y : Cl55}
    (hX : X ∈ cl55GradeSubmodule 1)
    (hY : Y ∈ cl55GradeSubmodule 1) :
    X * Y - Y * X ∈ cl55GradeSubmodule 2 := by
  exact grade_commutator hX hY

theorem cl55_neg_one_neg_one_commutator_mem_grade_neg_two
    {X Y : Cl55}
    (hX : X ∈ cl55GradeSubmodule (-1))
    (hY : Y ∈ cl55GradeSubmodule (-1)) :
    X * Y - Y * X ∈ cl55GradeSubmodule (-2) := by
  exact grade_commutator hX hY

theorem cl55_mixed_commutator_mem_grade_zero
    {X Y : Cl55}
    (hX : X ∈ cl55GradeSubmodule 1)
    (hY : Y ∈ cl55GradeSubmodule (-1)) :
    X * Y - Y * X ∈ cl55GradeSubmodule 0 := by
  exact grade_commutator hX hY

theorem cl55_same_grade_anticommutator_mem_grade_two
    {X Y : Cl55}
    (hX : X ∈ cl55GradeSubmodule 1)
    (hY : Y ∈ cl55GradeSubmodule 1) :
    X * Y + Y * X ∈ cl55GradeSubmodule 2 := by
  exact grade_anticommutator hX hY

theorem cl55_mixed_anticommutator_mem_grade_zero
    {X Y : Cl55}
    (hX : X ∈ cl55GradeSubmodule 1)
    (hY : Y ∈ cl55GradeSubmodule (-1)) :
    X * Y + Y * X ∈ cl55GradeSubmodule 0 := by
  exact grade_anticommutator hX hY

def cl55Associator (X Y Z : Cl55) : Cl55 :=
  (X * Y) * Z - X * (Y * Z)

theorem cl55_associator_zero (X Y Z : Cl55) :
    cl55Associator X Y Z = 0 := by
  simp [cl55Associator, mul_assoc]

end InfoGeometry.Clifford.Clifford55

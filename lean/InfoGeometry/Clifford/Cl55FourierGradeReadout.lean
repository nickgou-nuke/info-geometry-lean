import InfoGeometry.Clifford.Cl55OperatorFiveGradeClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Native five-grade readout using the repository's grade submodules. -/
namespace InfoGeometry.Clifford.Clifford55
open InfoGeometry.OperatorAlgebra

theorem fourierClifford_grade_readout (i j : Fin 5) :
    creation55 i ∈ cl55GradeSubmodule 1 ∧
    annihilation55 i ∈ cl55GradeSubmodule (-1) ∧
    creation55 i * creation55 j ∈ cl55GradeSubmodule 2 ∧
    annihilation55 i * annihilation55 j ∈ cl55GradeSubmodule (-2) := by
  exact ⟨creation55_mem_grade_one i, annihilation55_mem_grade_neg_one i,
    creation55_mul_creation55_mem_grade_two i j,
    annihilation55_mul_annihilation55_mem_grade_neg_two i j⟩

theorem fourierClifford_grade_zero_readout (i j : Fin 5) :
    creation55 i * annihilation55 j ∈ cl55GradeSubmodule 0 ∧
    annihilation55 i * creation55 j ∈ cl55GradeSubmodule 0 := by
  exact ⟨creation55_mul_annihilation55_mem_grade_zero i j,
    annihilation55_mul_creation55_mem_grade_zero i j⟩

theorem fourierClifford_commutator_grade_add (k l : ℤ)
    {X Y : Cl55} (hX : X ∈ cl55GradeSubmodule k)
    (hY : Y ∈ cl55GradeSubmodule l) :
    X * Y - Y * X ∈ cl55GradeSubmodule (k + l) := by
  exact grade_commutator hX hY

theorem fourierClifford_anticommutator_grade_add (k l : ℤ)
    {X Y : Cl55} (hX : X ∈ cl55GradeSubmodule k)
    (hY : Y ∈ cl55GradeSubmodule l) :
    X * Y + Y * X ∈ cl55GradeSubmodule (k + l) := by
  exact grade_anticommutator hX hY

end InfoGeometry.Clifford.Clifford55

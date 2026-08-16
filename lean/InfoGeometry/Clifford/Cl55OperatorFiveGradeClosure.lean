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

theorem spinTransported_grade_mem_of_mem
    (g : Spin55) (k : ℤ) {X : Cl55}
    (hX : X ∈ cl55GradeSubmodule k) :
    spinCliffordRingEquiv g X ∈ spinTransportedCl55GradeSubmodule g k := by
  change HasOperatorGrade (spinTransportedNumberOperator55 g)
    (spinCliffordRingEquiv g X) k
  unfold HasOperatorGrade spinTransportedNumberOperator55 at *
  rw [← (spinCliffordRingEquiv g).map_mul,
    ← (spinCliffordRingEquiv g).map_mul,
    ← (spinCliffordRingEquiv g).map_sub, hX]
  simp

theorem spinTransported_grade_mem_iff
    (g : Spin55) (k : ℤ) (X : Cl55) :
    spinCliffordRingEquiv g X ∈ spinTransportedCl55GradeSubmodule g k ↔
      X ∈ cl55GradeSubmodule k := by
  constructor
  · intro hX
    change HasOperatorGrade (spinTransportedNumberOperator55 g)
      (spinCliffordRingEquiv g X) k at hX
    unfold HasOperatorGrade spinTransportedNumberOperator55 at hX
    have hMapped := congrArg (fun Y => (spinCliffordRingEquiv g).symm Y) hX
    have hscalar :
        (spinCliffordRingEquiv g).symm
            ((k : ℝ) • (spinCliffordRingEquiv g) X) =
          (k : ℝ) • X := by
      change InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation
          (spinGroup.toUnits g)⁻¹
          ((k : ℝ) • InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation
            (spinGroup.toUnits g) X) = (k : ℝ) • X
      rw [InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_smul]
      rw [← InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_comp]
      simp [InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation]
    change HasOperatorGrade numberOperator55 X k
    unfold HasOperatorGrade numberOperator55
    dsimp only at hMapped
    rw [hscalar] at hMapped
    simpa only [map_sub, map_mul, map_smul,
      RingEquiv.symm_apply_apply] using hMapped
  · exact spinTransported_grade_mem_of_mem g k

theorem spinTransported_grade_commutator_mem_of_mem
    (g : Spin55) (k l : ℤ) {X Y : Cl55}
    (hX : X ∈ cl55GradeSubmodule k)
    (hY : Y ∈ cl55GradeSubmodule l) :
    spinCliffordRingEquiv g (X * Y - Y * X) ∈
      spinTransportedCl55GradeSubmodule g (k + l) := by
  change HasOperatorGrade (spinTransportedNumberOperator55 g)
    (spinCliffordRingEquiv g (X * Y - Y * X)) (k + l)
  rw [(spinCliffordRingEquiv g).map_sub,
    (spinCliffordRingEquiv g).map_mul,
    (spinCliffordRingEquiv g).map_mul]
  exact grade_commutator
    (spinTransported_grade_mem_of_mem g k hX)
    (spinTransported_grade_mem_of_mem g l hY)

theorem spinTransported_grade_anticommutator_mem_of_mem
    (g : Spin55) (k l : ℤ) {X Y : Cl55}
    (hX : X ∈ cl55GradeSubmodule k)
    (hY : Y ∈ cl55GradeSubmodule l) :
    spinCliffordRingEquiv g (X * Y + Y * X) ∈
      spinTransportedCl55GradeSubmodule g (k + l) := by
  change HasOperatorGrade (spinTransportedNumberOperator55 g)
    (spinCliffordRingEquiv g (X * Y + Y * X)) (k + l)
  rw [(spinCliffordRingEquiv g).map_add,
    (spinCliffordRingEquiv g).map_mul,
    (spinCliffordRingEquiv g).map_mul]
  exact grade_anticommutator
    (spinTransported_grade_mem_of_mem g k hX)
    (spinTransported_grade_mem_of_mem g l hY)

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

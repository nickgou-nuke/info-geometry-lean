import InfoGeometry.Clifford.Cl55ModularDerivation
import InfoGeometry.Clifford.Cl55OperatorFiveGradeClosure
import InfoGeometry.Algebra.SupergradedJordanLieSplit

/-!
# Supergraded modular action on the native `Cl(5,5)` operator algebra

This file joins the existing integer number-operator grading and the native
associative superbracket.  The parity used by the bracket is the parity of the
integer operator grade.  Consequently the bracket is homogeneous of summed
integer grade, and an inner derivation generated in grade zero preserves that
bracket and every homogeneous grade.

This is an operator-algebra statement on `Cl55`; it does not identify the
integer number grading with the distinct five-weight TKK grading or identify
`Cl55` with the doubled real Krein carrier.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.OperatorAlgebra

/-- The `Z₂` parity attached to an integer number-operator grade. -/
def cl55GradeParity (k : ℤ) : Bool := decide (k % 2 = 1)

/-- The associative superbracket of homogeneous `Cl55` operators has the
sum of their integer number-operator grades.  The parity arguments are
computed from those grades, so the odd-odd case is the anticommutator. -/
theorem cl55_superBracket_mem_grade_sum
    {k l : ℤ} {X Y : Cl55}
    (hX : X ∈ cl55GradeSubmodule k)
    (hY : Y ∈ cl55GradeSubmodule l) :
    InfoGeometry.Algebra.SupergradedBracket.superBracket
        (cl55GradeParity k) (cl55GradeParity l) X Y ∈
      cl55GradeSubmodule (k + l) := by
  change HasOperatorGrade numberOperator55 X k at hX
  change HasOperatorGrade numberOperator55 Y l at hY
  change HasOperatorGrade numberOperator55
    (InfoGeometry.Algebra.SupergradedBracket.superBracket
      (cl55GradeParity k) (cl55GradeParity l) X Y) (k + l)
  cases hp : cl55GradeParity k <;> cases hq : cl55GradeParity l
  · simpa [InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator, hp, hq,
      InfoGeometry.OperatorAlgebra.operatorCommutator] using
      (grade_commutator hX hY)
  · simpa [InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator, hp, hq,
      InfoGeometry.OperatorAlgebra.operatorCommutator] using
      (grade_commutator hX hY)
  · simpa [InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator, hp, hq,
      InfoGeometry.OperatorAlgebra.operatorCommutator] using
      (grade_commutator hX hY)
  · simpa [InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator, hp, hq,
      InfoGeometry.OperatorAlgebra.operatorAnticommutator] using
      (grade_anticommutator hX hY)

/-- An inner commutator derivation acts by derivations on both the even
commutator and odd anticommutator branches of the associative superbracket. -/
theorem cl55ModularDerivation_superBracket_leibniz
    (K X Y : Cl55) (p q : Bool) :
    cl55ModularDerivation K
        (InfoGeometry.Algebra.SupergradedBracket.superBracket p q X Y) =
      InfoGeometry.Algebra.SupergradedBracket.superBracket p q
          (cl55ModularDerivation K X) Y +
        InfoGeometry.Algebra.SupergradedBracket.superBracket p q
          X (cl55ModularDerivation K Y) := by
  cases p <;> cases q <;>
    simp [InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator] <;> noncomm_ring

/-- A grade-zero inner derivation preserves the superbracket of homogeneous
operators and its summed number-operator grade. -/
theorem cl55GradeZeroModular_preserves_superBracket
    (K : Cl55) {k l : ℤ} {X Y : Cl55}
    (hK : K ∈ gradeSubmodule numberOperator55 0)
    (hX : X ∈ cl55GradeSubmodule k)
    (hY : Y ∈ cl55GradeSubmodule l) :
    cl55ModularDerivation K
        (InfoGeometry.Algebra.SupergradedBracket.superBracket
          (cl55GradeParity k) (cl55GradeParity l) X Y) ∈
      cl55GradeSubmodule (k + l) := by
  apply cl55ModularDerivation_preserves_grade K _ (k + l) hK
  exact cl55_superBracket_mem_grade_sum hX hY

end InfoGeometry.Clifford.Clifford55

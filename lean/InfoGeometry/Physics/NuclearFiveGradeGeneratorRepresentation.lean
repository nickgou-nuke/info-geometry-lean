import InfoGeometry.Physics.NuclearTwoModeCARFiveGrade

/-!
# A concrete grade-preserving nuclear generator representation

This finite generator set records the nonzero degrees of the two-mode CAR
five-grading. Its representation lands in the associative endomorphism Lie
algebra, and brackets add degrees by the adjoint-weight theorem.

It is not definitionally identified with the generic Freudenthal/TKK carrier;
that comparison requires an explicit intertwining Lie homomorphism.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation

open InfoGeometry.Physics.NuclearTwoModeCARFiveGrade

inductive Generator : Type
  | pairAnnihilation
  | annihilationOne
  | annihilationTwo
  | cartan
  | creationOne
  | creationTwo
  | pairCreation
  deriving DecidableEq, Fintype, Repr

/-- Integer grade of each named generator. -/
def degree : Generator → ℤ
  | .pairAnnihilation => -2
  | .annihilationOne => -1
  | .annihilationTwo => -1
  | .cartan => 0
  | .creationOne => 1
  | .creationTwo => 1
  | .pairCreation => 2

/-- Concrete representation in the four-state operator algebra. -/
def represent : Generator → Op
  | .pairAnnihilation => NuclearTwoModeCARFiveGrade.pairAnnihilation
  | .annihilationOne => NuclearTwoModeCARFiveGrade.annihilationOne
  | .annihilationTwo => NuclearTwoModeCARFiveGrade.annihilationTwo
  | .cartan => gradeCartan
  | .creationOne => NuclearTwoModeCARFiveGrade.creationOne
  | .creationTwo => NuclearTwoModeCARFiveGrade.creationTwo
  | .pairCreation => NuclearTwoModeCARFiveGrade.pairCreation

/-- Every named generator lies in its declared Cartan grade. -/
theorem represent_hasGrade (g : Generator) :
    HasGrade (degree g) (represent g) := by
  cases g <;> simp [degree, represent]

/-- The commutator of represented generators lies in the sum grade. -/
theorem represented_commutator_hasGrade (g h : Generator) :
    HasGrade (degree g + degree h)
      (commutator (represent g) (represent h)) :=
  (represent_hasGrade g).commutator (represent_hasGrade h)

/-- Degree reversal exchanging creation and annihilation. -/
def opposite : Generator → Generator
  | .pairAnnihilation => .pairCreation
  | .annihilationOne => .creationOne
  | .annihilationTwo => .creationTwo
  | .cartan => .cartan
  | .creationOne => .annihilationOne
  | .creationTwo => .annihilationTwo
  | .pairCreation => .pairAnnihilation

@[simp] theorem opposite_involutive (g : Generator) :
    opposite (opposite g) = g := by
  cases g <;> rfl

@[simp] theorem degree_opposite (g : Generator) :
    degree (opposite g) = -degree g := by
  cases g <;> rfl

/-- Every one of the five grades has an explicit generator. -/
theorem five_grades_are_occupied :
    (∃ g, degree g = -2) ∧
      (∃ g, degree g = -1) ∧
      (∃ g, degree g = 0) ∧
      (∃ g, degree g = 1) ∧
      (∃ g, degree g = 2) := by
  exact ⟨⟨.pairAnnihilation, rfl⟩,
    ⟨.annihilationOne, rfl⟩,
    ⟨.cartan, rfl⟩,
    ⟨.creationOne, rfl⟩,
    ⟨.pairCreation, rfl⟩⟩

/-- Compact representation packet. -/
theorem nuclear_five_grade_representation_packet :
    (∀ g, HasGrade (degree g) (represent g)) ∧
      (∀ g h, HasGrade (degree g + degree h)
        (commutator (represent g) (represent h))) ∧
      (∀ g, opposite (opposite g) = g) ∧
      (∀ g, degree (opposite g) = -degree g) := by
  exact ⟨represent_hasGrade, represented_commutator_hasGrade,
    opposite_involutive, degree_opposite⟩

end InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation

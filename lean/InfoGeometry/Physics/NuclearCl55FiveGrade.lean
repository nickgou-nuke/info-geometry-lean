import InfoGeometry.Physics.NuclearCl55NativeSoldering

/-!
# A finite five-grade label carrier for the native `Cl(5,5)` CAR

The grade labels are an algebraic index for the already constructed creation,
annihilation, and neutral sectors.  This file does not identify a label with
an operator subspace and does not assert unproved bracket closure.  The
operator-level content is supplied by the existing Cartan weight theorems.
-/

namespace InfoGeometry.Physics.NuclearCl55FiveGrade

open InfoGeometry.Physics.NuclearCl55NativeSoldering
open InfoGeometry.Physics.NuclearCl55CartanParityDictionary
open InfoGeometry.Physics.Cl55SpinorCartanFock
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55WittLieRouting

inductive Grade5 : Type
  | minusTwo
  | minusOne
  | zero
  | plusOne
  | plusTwo
  deriving DecidableEq, Repr

def gradeValue : Grade5 → ℤ
  | .minusTwo => -2
  | .minusOne => -1
  | .zero => 0
  | .plusOne => 1
  | .plusTwo => 2

def particleHoleDual : Grade5 → Grade5
  | .minusTwo => .plusTwo
  | .minusOne => .plusOne
  | .zero => .zero
  | .plusOne => .minusOne
  | .plusTwo => .minusTwo

@[simp] theorem particleHoleDual_involutive (g : Grade5) :
    particleHoleDual (particleHoleDual g) = g := by
  cases g <;> rfl

@[simp] theorem particleHoleDual_gradeValue (g : Grade5) :
    gradeValue (particleHoleDual g) = -gradeValue g := by
  cases g <;> rfl

def gradeDimension : Grade5 → ℕ
  | .minusTwo => 10
  | .minusOne => 5
  | .zero => 26
  | .plusOne => 5
  | .plusTwo => 10

theorem even_grade_dimension :
    gradeDimension .minusTwo + gradeDimension .zero +
      gradeDimension .plusTwo = 46 := by
  rfl

theorem traceless_even_operator_dimension :
    gradeDimension .minusTwo + 25 + gradeDimension .plusTwo = 45 := by
  rfl

/-! The scalar identity direction belongs to the associative operator algebra,
but not to the traceless orthogonal core.  These two dimension readouts keep
the ambient CAR carrier and the `so(5,5)` even core distinct. -/

theorem full_five_grade_dimension :
    gradeDimension .minusTwo + gradeDimension .minusOne +
      gradeDimension .zero + gradeDimension .plusOne +
      gradeDimension .plusTwo = 56 := by
  rfl

theorem traceless_even_grade_dimension :
    gradeDimension .minusTwo + 25 + gradeDimension .plusTwo = 45 := by
  exact traceless_even_operator_dimension

@[simp] theorem particleHoleDual_gradeDimension (g : Grade5) :
    gradeDimension (particleHoleDual g) = gradeDimension g := by
  cases g <;> rfl

inductive OddRoot : Type
  | annihilation
  | creation
  deriving DecidableEq, Repr

def oddRootGrade : OddRoot → Grade5
  | .annihilation => .minusOne
  | .creation => .plusOne

noncomputable def oddRootOperator (r : OddRoot) (i : Fin 5) : MatStage 5 :=
  match r with
  | .annihilation => cl55CAR.a i
  | .creation => cl55CAR.adag i

theorem oddRoot_gradeValue (r : OddRoot) :
    gradeValue (oddRootGrade r) =
      match r with
      | .annihilation => -1
      | .creation => 1 := by
  cases r <;> rfl

theorem oddRoot_square_zero (r : OddRoot) (i : Fin 5) :
    oddRootOperator r i * oddRootOperator r i = 0 := by
  cases r
  · exact cl55CAR.a_sq i
  · exact cl55CAR.adag_sq i

theorem oddRoot_cartan_weight (r : OddRoot) (i : Fin 5) :
    bracket (normalizedCl55Cartan i) (oddRootOperator r i) =
      (match r with
       | .annihilation => (-2 : ℝ)
       | .creation => (2 : ℝ)) • oddRootOperator r i := by
  cases r
  · simpa [oddRootOperator] using
      (cl55CAR_cartan_annihilation_normalized i)
  · simpa [oddRootOperator] using
      (cl55CAR_cartan_creation_normalized i)

theorem oddRoot_particleHole_swaps (r : OddRoot) :
    oddRootGrade (match r with
      | .annihilation => OddRoot.creation
      | .creation => OddRoot.annihilation) =
      particleHoleDual (oddRootGrade r) := by
  cases r <;> rfl

end InfoGeometry.Physics.NuclearCl55FiveGrade

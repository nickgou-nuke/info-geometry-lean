import Mathlib

/-!
# Regular actions, commutants, and the nonassociative obstruction

On an associative algebra the left and right regular actions commute. On its
star carrier, conjugation `J x = star x` swaps them. These are algebraic facts,
not identifications of a commutant with negative samples or reverse time.

The final theorem needs no associative multiplication. It records the precise
associator obstruction, which must be retained for operator-Zorn payloads.
-/

namespace InfoGeometry.SignedNetwork.RegularBimoduleSeparation

section Associative

variable {A : Type*} [Ring A]

def leftAction (a : A) : A →+ A where
  toFun x := a * x
  map_zero' := mul_zero a
  map_add' := mul_add a

def rightAction (b : A) : A →+ A where
  toFun x := x * b
  map_zero' := zero_mul b
  map_add' x y := add_mul x y b

@[simp] theorem leftAction_apply (a x : A) : leftAction a x = a * x := rfl
@[simp] theorem rightAction_apply (b x : A) : rightAction b x = x * b := rfl

/-- The regular bimodule relation, derived from associativity. -/
theorem left_right_commute (a b : A) :
    (leftAction a).comp (rightAction b) = (rightAction b).comp (leftAction a) := by
  ext x
  exact (mul_assoc a x b).symm

/-- Right multiplication is a representation of the opposite multiplication. -/
theorem rightAction_comp (a b : A) :
    (rightAction a).comp (rightAction b) = rightAction (b * a) := by
  ext x
  exact mul_assoc x b a

/-- Every function commuting with all left multiplications is right
multiplication by its value at one. No sign or causal orientation enters. -/
theorem commutes_left_iff_right (T : A → A) :
    (∀ a x, T (a * x) = a * T x) ↔ ∀ x, T x = x * T 1 := by
  constructor
  · intro h x
    simpa only [mul_one] using h x 1
  · intro h a x
    rw [h (a * x), h x, mul_assoc]

end Associative

section Star

variable {A : Type*} [Ring A] [StarRing A]

/-- Algebraic conjugation on the standard regular carrier. In the matrix
Hilbert--Schmidt realization this is the modular conjugation for its standard form. -/
def conjugation (x : A) : A := star x

@[simp] theorem conjugation_involutive (x : A) :
    conjugation (conjugation x) = x := by simp [conjugation]

/-- `J L_a J = R_(a*)`; it is not multiplication by a sample sign. -/
theorem conjugation_left (a x : A) :
    conjugation (leftAction a (conjugation x)) = rightAction (star a) x := by
  simp [conjugation, star_mul]

/-- `J R_a J = L_(a*)`. -/
theorem conjugation_right (a x : A) :
    conjugation (rightAction a (conjugation x)) = leftAction (star a) x := by
  simp [conjugation, star_mul]

end Star

section Nonassociative

variable {Z : Type*} [AddCommGroup Z] [Mul Z]

/-- The multiplication is deliberately unbundled from any associativity law. -/
def associator (a x b : Z) : Z := (a * x) * b - a * (x * b)

/-- For a genuinely nonassociative payload, the regular left/right action
commutator is minus the associator; it cannot be set to zero by reassociation. -/
theorem left_right_defect (a x b : Z) :
    a * (x * b) - (a * x) * b = -associator a x b := by
  unfold associator
  abel

/-- Commutation at one triple is equivalent to vanishing of that associator. -/
theorem left_right_commute_iff (a x b : Z) :
    a * (x * b) = (a * x) * b ↔ associator a x b = 0 := by
  unfold associator
  rw [sub_eq_zero, eq_comm]

end Nonassociative

end InfoGeometry.SignedNetwork.RegularBimoduleSeparation

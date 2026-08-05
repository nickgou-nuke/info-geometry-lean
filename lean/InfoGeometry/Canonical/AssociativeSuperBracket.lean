import InfoGeometry.Canonical.SuperAnomaly
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.AssociativeSuperBracket

Mathlib-aligned graded bracket on an associative `ℝ`-algebra.

This file does not introduce a new graded tensor or Clifford layer. It only
packages the standard super-commutator formula on an associative algebra using
the repo's existing `SuperParity` tags.
-/

namespace InfoGeometry.Canonical.AssociativeSuperBracket

open InfoGeometry.Canonical.SuperAnomaly

variable {A B : Type*} [Ring A] [Algebra ℝ A] [Ring B] [Algebra ℝ B]

/-- Graded bracket `[a,b}` on an associative `ℝ`-algebra. -/
@[rep_depth krein]
noncomputable def superBracket (p q : SuperParity) (a b : A) : A :=
  a * b - paritySign p q • (b * a)

def parityAdd : SuperParity → SuperParity → SuperParity
  | .even, q => q
  | .odd, .even => .odd
  | .odd, .odd => .even

@[simp] theorem parityAdd_even_left (p : SuperParity) :
    parityAdd .even p = p := by
  cases p <;> rfl

@[simp] theorem parityAdd_even_right (p : SuperParity) :
    parityAdd p .even = p := by
  cases p <;> rfl

@[simp] theorem parityAdd_self (p : SuperParity) :
    parityAdd p p = .even := by
  cases p <;> rfl

theorem parityAdd_comm (p q : SuperParity) :
    parityAdd p q = parityAdd q p := by
  cases p <;> cases q <;> rfl

theorem parityAdd_assoc (p q r : SuperParity) :
    parityAdd (parityAdd p q) r =
      parityAdd p (parityAdd q r) := by
  cases p <;> cases q <;> cases r <;> rfl

theorem superBracket_graded_jacobi
    (p q r : SuperParity) (x y z : A) :
    paritySign p r • superBracket p (parityAdd q r) x
        (superBracket q r y z) +
      paritySign q p • superBracket q (parityAdd r p) y
        (superBracket r p z x) +
      paritySign r q • superBracket r (parityAdd p q) z
        (superBracket p q x y) = 0 := by
  cases p <;> cases q <;> cases r <;>
    simp [superBracket, paritySign, parityAdd, sub_eq_add_neg,
      Algebra.smul_def] <;>
    noncomm_ring

/-- Even-even channel: the ordinary commutator. -/
@[rep_depth krein]
noncomputable abbrev commutator (a b : A) : A :=
  superBracket SuperParity.even SuperParity.even a b

/-- Odd-odd channel: the ordinary anticommutator. -/
@[rep_depth krein]
noncomputable abbrev anticommutator (a b : A) : A :=
  superBracket SuperParity.odd SuperParity.odd a b

@[rep_depth krein] lemma superBracket_add_left
    (p q : SuperParity) (a₁ a₂ b : A) :
    superBracket p q (a₁ + a₂) b
      = superBracket p q a₁ b + superBracket p q a₂ b := by
  unfold superBracket
  simp [sub_eq_add_neg, add_mul, mul_add, smul_add, add_assoc, add_left_comm, add_comm]

@[rep_depth krein] lemma superBracket_add_right
    (p q : SuperParity) (a b₁ b₂ : A) :
    superBracket p q a (b₁ + b₂)
      = superBracket p q a b₁ + superBracket p q a b₂ := by
  unfold superBracket
  simp [sub_eq_add_neg, add_mul, mul_add, smul_add, add_assoc, add_left_comm, add_comm]

@[rep_depth krein] lemma superBracket_smul_left
    (p q : SuperParity) (r : ℝ) (a b : A) :
    superBracket p q (r • a) b = r • superBracket p q a b := by
  unfold superBracket
  simp [sub_eq_add_neg, smul_smul, mul_comm]

@[rep_depth krein] lemma superBracket_smul_right
    (p q : SuperParity) (r : ℝ) (a b : A) :
    superBracket p q a (r • b) = r • superBracket p q a b := by
  unfold superBracket
  simp [sub_eq_add_neg, smul_smul, mul_comm]

/-- Algebra homomorphisms preserve the graded superbracket. -/
@[rep_depth krein, simp] theorem map_superBracket
    (f : A →ₐ[ℝ] B) (p q : SuperParity) (a b : A) :
    f (superBracket p q a b) = superBracket p q (f a) (f b) := by
  simp [superBracket]

@[rep_depth krein, simp] lemma superBracket_even_left
    (q : SuperParity) (a b : A) :
    superBracket SuperParity.even q a b = a * b - b * a := by
  simp [superBracket, paritySign]

@[rep_depth krein, simp] lemma superBracket_even_right
    (p : SuperParity) (a b : A) :
    superBracket p SuperParity.even a b = a * b - b * a := by
  simp [superBracket, paritySign]

@[rep_depth krein, simp] lemma superBracket_even_even
    (a b : A) :
    superBracket .even .even a b = a * b - b * a := by
  simp [superBracket, paritySign]

@[rep_depth krein, simp] lemma superBracket_odd_odd
    (a b : A) :
    superBracket SuperParity.odd SuperParity.odd a b = a * b + b * a := by
  simp [superBracket, paritySign, sub_eq_add_neg]

theorem superBracket_swap
    (p q : SuperParity) (a b : A) :
    superBracket p q a b =
      - paritySign p q • superBracket q p b a := by
  cases p <;> cases q <;>
    simp [superBracket, paritySign, sub_eq_add_neg,
      Algebra.smul_def]
  all_goals first | noncomm_ring | abel

end InfoGeometry.Canonical.AssociativeSuperBracket

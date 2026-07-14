import InfoGeometry.Canonical.SuperAnomaly
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.AssociativeSuperBracket

Mathlib-aligned graded bracket on an associative `ℝ`-algebra.

This file does not introduce a new graded tensor or Clifford layer. It only
packages the standard super-commutator formula on an associative algebra using
the repo's existing `SuperParity` tags.
-/

namespace AssociativeSuperBracket

open InfoGeometry.Canonical.SuperAnomaly

variable {A B : Type*} [Ring A] [Algebra ℝ A] [Ring B] [Algebra ℝ B]

/-- Graded bracket `[a,b}` on an associative `ℝ`-algebra. -/
@[rep_depth krein]
noncomputable def superBracket (p q : SuperParity) (a b : A) : A :=
  a * b - paritySign p q • (b * a)

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

@[rep_depth krein, simp] lemma superBracket_odd_odd
    (a b : A) :
    superBracket SuperParity.odd SuperParity.odd a b = a * b + b * a := by
  simp [superBracket, paritySign, sub_eq_add_neg]

end AssociativeSuperBracket

import Mathlib

/-!
# Projective center quotient for the finite Pin(5,5) spinor carrier

This module is the Lean twin of `tools/sympy/projective_center_quotient.py`.
It records the finite matrix facts for the signed identity center `{+I,-I}` on
the `32 × 32` spinor carrier used by the Pin(5,5) glide core.

#### BUCKET 1: CLOSED FINITE THEOREMS
The declarations below prove, in the Lean kernel:

* `(-I)² = I`;
* `±I` commute with every `32 × 32` integer spinor matrix;
* left/right multiplication by `-I` is matrix negation;
* the projective relation `A ~ B` iff `B = A` or `B = -A` is reflexive,
  symmetric, and transitive;
* every matrix is projectively equivalent to its central sign flip.

#### BUCKET 3: OPEN CLOSURE DEBT
This is a finite signed-identity quotient surface.  It does not construct the
full topological quotient group `Pin(5,5)/{±1}` or prove any Cuntz/crystal charge
classification theorem.
-/

namespace InfoGeometry.OperatorAlgebra.ProjectiveCenter

open Matrix

abbrev Spin32Matrix := Matrix (Fin 32) (Fin 32) ℤ

/-- The nontrivial central signed identity. -/
def negId : Spin32Matrix := -(1 : Spin32Matrix)

/-- Projective equivalence under the signed-identity center `{+I,-I}`. -/
def ProjectivelyEquivalent (A B : Spin32Matrix) : Prop := B = A ∨ B = -A

/-- Structure packaging the nontrivial center element. -/
structure PinCenter where
  I_neg : Spin32Matrix
  h_center_def : I_neg = negId

/-- The concrete signed-identity center element. -/
def concreteCenter : PinCenter where
  I_neg := negId
  h_center_def := rfl

/-- The negative identity is an involution. -/
theorem negId_sq : negId * negId = 1 := by
  unfold negId
  simp

/-- Left multiplication by the negative identity is matrix negation. -/
theorem negId_mul (A : Spin32Matrix) : negId * A = -A := by
  unfold negId
  simp

/-- Right multiplication by the negative identity is matrix negation. -/
theorem mul_negId (A : Spin32Matrix) : A * negId = -A := by
  unfold negId
  simp

/-- The negative identity commutes with every finite spinor matrix. -/
theorem negId_commutes (A : Spin32Matrix) : negId * A = A * negId := by
  rw [negId_mul, mul_negId]

/-- The positive identity commutes with every finite spinor matrix. -/
theorem id_commutes (A : Spin32Matrix) : (1 : Spin32Matrix) * A = A * 1 := by
  simp

/-- The packaged center element is involutive. -/
theorem projective_center_involution (sys : PinCenter) : sys.I_neg * sys.I_neg = 1 := by
  rw [sys.h_center_def]
  exact negId_sq

/-- The packaged center element commutes with every finite spinor matrix. -/
theorem projective_center_commutes (sys : PinCenter) (A : Spin32Matrix) :
    sys.I_neg * A = A * sys.I_neg := by
  rw [sys.h_center_def]
  exact negId_commutes A

/-- Projective signed-center equivalence is reflexive. -/
theorem projectivelyEquivalent_refl (A : Spin32Matrix) : ProjectivelyEquivalent A A := by
  exact Or.inl rfl

/-- Projective signed-center equivalence is symmetric. -/
theorem projectivelyEquivalent_symm {A B : Spin32Matrix} :
    ProjectivelyEquivalent A B → ProjectivelyEquivalent B A := by
  intro h
  rcases h with h | h
  · exact Or.inl h.symm
  · subst B
    exact Or.inr (by simp)

/-- Projective signed-center equivalence is transitive. -/
theorem projectivelyEquivalent_trans {A B C : Spin32Matrix} :
    ProjectivelyEquivalent A B → ProjectivelyEquivalent B C → ProjectivelyEquivalent A C := by
  intro hAB hBC
  rcases hAB with hAB | hAB <;> rcases hBC with hBC | hBC
  · subst B
    exact Or.inl hBC
  · subst B
    exact Or.inr hBC
  · subst B
    subst C
    exact Or.inr rfl
  · subst B
    subst C
    exact Or.inl (by simp)

/-- Every matrix is projectively equivalent to its central sign flip. -/
theorem projectivelyEquivalent_neg (A : Spin32Matrix) : ProjectivelyEquivalent A (-A) := by
  exact Or.inr rfl

/-- Applying the nontrivial central sign twice returns the same representative. -/
theorem projective_double_flip (A : Spin32Matrix) : negId * (negId * A) = A := by
  rw [negId_mul, negId_mul]
  simp

/-- Finite kernel packet for the projective signed-center quotient surface. -/
theorem projective_center_packet :
    negId * negId = 1 ∧
      (∀ A : Spin32Matrix, negId * A = A * negId) ∧
      (∀ A : Spin32Matrix, negId * A = -A) ∧
      (∀ A : Spin32Matrix, ProjectivelyEquivalent A (-A)) ∧
      (∀ A : Spin32Matrix, negId * (negId * A) = A) := by
  exact ⟨negId_sq, negId_commutes, negId_mul, projectivelyEquivalent_neg,
    projective_double_flip⟩

end InfoGeometry.OperatorAlgebra.ProjectiveCenter

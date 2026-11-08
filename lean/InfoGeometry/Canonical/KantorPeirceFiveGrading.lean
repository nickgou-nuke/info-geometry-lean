import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TKKJordanPairData

/-!
# Commutator grading data

This owner records the part of the Peirce/TKK calculation which is valid for
an arbitrary associative algebra: an inner commutator is a derivation, and
eigenvector hypotheses are stable under products.  A tripotent by itself does
not produce a five-grading; the relevant component hypotheses remain explicit.
-/

namespace InfoGeometry.Canonical

section

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The commutator derivation associated with an element of an associative algebra. -/
def commutatorAction (e x : A) : A := e * x - x * e

/-- A tripotent is an element satisfying the cubic relation `e^3 = e`. -/
def IsTripotent (e : A) : Prop := e * e * e = e

/-- An eigencomponent for the commutator action, with a real weight. -/
def IsCommutatorComponent (e x : A) (weight : ℝ) : Prop :=
  commutatorAction e x = weight • x

@[simp] theorem commutatorAction_apply (e x : A) :
    commutatorAction e x = e * x - x * e := rfl

theorem commutatorAction_leibniz (e x y : A) :
    commutatorAction e (x * y) =
      commutatorAction e x * y + x * commutatorAction e y := by
  simp only [commutatorAction]
  noncomm_ring

theorem commutatorAction_add (e x y : A) :
    commutatorAction e (x + y) =
      commutatorAction e x + commutatorAction e y := by
  simp only [commutatorAction]
  noncomm_ring

theorem commutatorAction_smul (e : A) (r : ℝ) (x : A) :
    commutatorAction e (r • x) = r • commutatorAction e x := by
  simp only [commutatorAction]
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  simp only [smul_sub]

theorem commutatorAction_is_derivation (e : A) :
    (∀ x y : A, commutatorAction e (x * y) =
      commutatorAction e x * y + x * commutatorAction e y) ∧
    (∀ x y : A, commutatorAction e (x + y) =
      commutatorAction e x + commutatorAction e y) :=
  ⟨fun x y => commutatorAction_leibniz e x y,
   fun x y => commutatorAction_add e x y⟩

theorem commutatorAction_product_component
    {e x y : A} {r s : ℝ}
    (hx : IsCommutatorComponent e x r)
    (hy : IsCommutatorComponent e y s) :
    IsCommutatorComponent e (x * y) (r + s) := by
  unfold IsCommutatorComponent at *
  rw [commutatorAction_leibniz, hx, hy]
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← add_smul]

theorem commutatorAction_zero_component (e : A) :
    IsCommutatorComponent e (0 : A) 0 := by
  simp [IsCommutatorComponent, commutatorAction]

theorem tripotent_commutator_derivation
    (e : A) (_he : IsTripotent e) :
    ∀ x y : A, commutatorAction e (x * y) =
      commutatorAction e x * y + x * commutatorAction e y := by
  intro x y
  exact commutatorAction_leibniz e x y

end

end InfoGeometry.Canonical

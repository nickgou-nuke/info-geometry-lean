import Mathlib.Algebra.Algebra.Unitization

/-!
# Nonassociative unitization lift

This file packages a generic unitization lift for nonassociative targets.
-/

namespace Unitization

universe u v

variable {R : Type u} {N : Type v} {A : Type*}

variable [CommRing R]
variable [NonUnitalNonAssocRing N] [Module R N]

variable [NonAssocRing A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- Extend a nonunital nonassociative algebra homomorphism to the unitization.

The target multiplication only needs to be nonassociative. -/
noncomputable def liftNonAssoc (φ : N →ₙₐ[R] A) : Unitization R N →+* A := by
  refine
    { toFun := fun x => x.fst • (1 : A) + φ x.snd
      map_zero' := by simp
      map_one' := by simp
      map_add' := by
        intro x y
        rcases x with ⟨r, a⟩
        rcases y with ⟨s, b⟩
        simp only [Unitization.fst_add, Unitization.snd_add, add_smul, map_add]
        abel
      map_mul' := by
        intro x y
        rcases x with ⟨r, a⟩
        rcases y with ⟨s, b⟩
        simp only [Unitization.fst_mul, Unitization.snd_mul, map_add, map_smul, map_mul]
        rw [add_mul, mul_add, mul_add]
        simp only [smul_one_mul, mul_smul_comm, mul_one, smul_smul]
        ac_rfl }

@[simp] theorem liftNonAssoc_inl (φ : N →ₙₐ[R] A) (r : R) :
    liftNonAssoc (R := R) (N := N) (A := A) φ (Unitization.inl r : Unitization R N) =
      r • (1 : A) := by
  simp [liftNonAssoc]

@[simp] theorem liftNonAssoc_inr (φ : N →ₙₐ[R] A) (x : N) :
    liftNonAssoc (R := R) (N := N) (A := A) φ (x : Unitization R N) = φ x := by
  simp [liftNonAssoc]

/-- A homomorphism out of a unitization is determined by its scalar and generator values. -/
theorem liftNonAssoc_unique (φ : N →ₙₐ[R] A) (g : Unitization R N →+* A)
    (hscalar : ∀ r : R, g (Unitization.inl r : Unitization R N) = r • (1 : A))
    (hinr : ∀ x : N, g (x : Unitization R N) = φ x) :
    g = liftNonAssoc (R := R) (N := N) (A := A) φ := by
  ext x
  induction x using Unitization.ind with
  | inl_add_inr r a =>
      simp [liftNonAssoc, hscalar, hinr]

end Unitization

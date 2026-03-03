import Mathlib

namespace InfoGeometry.Singular.MoorePenroseAdjoint

/-- 
A typeclass for a generic adjoint operation. 
This abstracts away from standard complex-Hermitian conjugation,
allowing the Cartan metric anti-automorphism (φ) to govern the geometry. 
-/
class AdjointLike (R : Type*) [Ring R] where
  adj : R → R
  invol : ∀ A, adj (adj A) = A
  mul_rev : ∀ A B, adj (A * B) = adj B * adj A
  add : ∀ A B, adj (A + B) = adj A + adj B
  zero : adj 0 = 0
  one : adj 1 = 1
  neg : ∀ A, adj (-A) = -adj A

-- Canonical postfix notation for the geometric adjoint
postfix:max "†" => AdjointLike.adj

section MP
variable {R : Type*} [Ring R] [AdjointLike R]

/-- The Four Penrose Equations defining the Moore-Penrose Inverse. -/
structure IsMoorePenroseInverse (A B : R) : Prop where
  eq1 : A * B * A = A
  eq2 : B * A * B = B
  eq3 : (A * B)† = A * B
  eq4 : (B * A)† = B * A

lemma adjoint_mul_triple (X Y Z : R) : (X * Y * Z)† = Z† * Y† * X† := by
  calc (X * Y * Z)† = ((X * Y) * Z)† := rfl
    _ = Z† * (X * Y)† := by rw [AdjointLike.mul_rev]
    _ = Z† * (Y† * X†) := by rw [AdjointLike.mul_rev]
    _ = Z† * Y† * X† := by rw [← mul_assoc]

/-- The Uniqueness Theorem: The Geometric Mirror is absolute. -/
theorem MoorePenrose_unique {A B C : R} 
    (hB : IsMoorePenroseInverse A B) 
    (hC : IsMoorePenroseInverse A C) : B = C := by
  have h1 : A * B = A * C := by
    calc
      A * B = (A * B)† := hB.eq3.symm
      _ = B† * A† := by rw [AdjointLike.mul_rev]
      _ = B† * (A * C * A)† := by rw [hC.eq1]
      _ = B† * (A† * C† * A†) := by rw [adjoint_mul_triple]
      _ = (B† * A†) * C† * A† := by simp [mul_assoc]
      _ = (A * B)† * C† * A† := by rw [AdjointLike.mul_rev]
      _ = (A * B) * C† * A† := by rw [hB.eq3]
      _ = A * B * (C† * A†) := by rw [mul_assoc]
      _ = A * B * (A * C)† := by rw [AdjointLike.mul_rev]
      _ = A * B * (A * C) := by rw [hC.eq3]
      _ = (A * B * A) * C := by simp [mul_assoc]
      _ = A * C := by rw [hB.eq1]
  have h2 : B * A = C * A := by
    calc
      B * A = (B * A)† := hB.eq4.symm
      _ = A† * B† := by rw [AdjointLike.mul_rev]
      _ = (A * C * A)† * B† := by rw [hC.eq1]
      _ = (A† * C† * A†) * B† := by rw [adjoint_mul_triple]
      _ = A† * C† * (A† * B†) := by simp [mul_assoc]
      _ = A† * C† * (B * A)† := by rw [AdjointLike.mul_rev]
      _ = A† * C† * (B * A) := by rw [hB.eq4]
      _ = (C * A)† * (B * A) := by rw [AdjointLike.mul_rev]
      _ = (C * A) * (B * A) := by rw [hC.eq4]
      _ = C * (A * B * A) := by simp [mul_assoc]
      _ = C * A := by rw [hB.eq1]
  calc
    B = B * A * B := hB.eq2.symm
    _ = (B * A) * B := by rw [mul_assoc]
    _ = (C * A) * B := by rw [h2]
    _ = C * (A * B) := by rw [← mul_assoc]
    _ = C * (A * C) := by rw [h1]
    _ = C * A * C := by rw [mul_assoc]
    _ = C := hC.eq2

/-- The Geometric/Metric Support Projector P_{MP} = A * A^+ -/
def MP_Projector (A B : R) (_h : IsMoorePenroseInverse A B) : R := A * B

lemma MP_Projector_idempotent {A B : R} (h : IsMoorePenroseInverse A B) : 
    (MP_Projector A B h) * (MP_Projector A B h) = MP_Projector A B h := by
  unfold MP_Projector
  calc
    (A * B) * (A * B) = (A * B * A) * B := by simp [mul_assoc]
    _ = A * B := by rw [h.eq1]

lemma MP_Projector_self_adjoint {A B : R} (h : IsMoorePenroseInverse A B) : 
    (MP_Projector A B h)† = MP_Projector A B h := h.eq3

end MP
end InfoGeometry.Singular.MoorePenroseAdjoint

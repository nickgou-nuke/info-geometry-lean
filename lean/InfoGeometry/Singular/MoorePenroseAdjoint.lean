import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic

namespace InfoGeometry.Singular.MoorePenroseAdjoint

-- Canonical postfix notation for the geometric adjoint.
postfix:max "†" => star

section MP
variable {R : Type*} [Ring R] [StarRing R]

/-- The Four Penrose equations as a direct predicate. -/
def IsMoorePenroseInverse (A B : R) : Prop :=
  A * B * A = A ∧
  B * A * B = B ∧
  (A * B)† = A * B ∧
  (B * A)† = B * A

namespace IsMoorePenroseInverse

variable {A B : R}

theorem mk
    (h1 : A * B * A = A)
    (h2 : B * A * B = B)
    (h3 : (A * B)† = A * B)
    (h4 : (B * A)† = B * A) :
    IsMoorePenroseInverse A B :=
  ⟨h1, h2, h3, h4⟩

theorem aba_eq_a (h : IsMoorePenroseInverse A B) : A * B * A = A := h.1

theorem bab_eq_b (h : IsMoorePenroseInverse A B) : B * A * B = B := h.2.1

theorem ab_adj_eq (h : IsMoorePenroseInverse A B) : (A * B)† = A * B := h.2.2.1

theorem ba_adj_eq (h : IsMoorePenroseInverse A B) : (B * A)† = B * A := h.2.2.2

-- Backward-compatible aliases.
theorem eq1 (h : IsMoorePenroseInverse A B) : A * B * A = A := h.aba_eq_a

theorem eq2 (h : IsMoorePenroseInverse A B) : B * A * B = B := h.bab_eq_b

theorem eq3 (h : IsMoorePenroseInverse A B) : (A * B)† = A * B := h.ab_adj_eq

theorem eq4 (h : IsMoorePenroseInverse A B) : (B * A)† = B * A := h.ba_adj_eq

end IsMoorePenroseInverse

lemma adjoint_mul_triple (X Y Z : R) : (X * Y * Z)† = Z† * Y† * X† := by
  calc (X * Y * Z)† = ((X * Y) * Z)† := rfl
    _ = Z† * (X * Y)† := by rw [star_mul]
    _ = Z† * (Y† * X†) := by rw [star_mul]
    _ = Z† * Y† * X† := by rw [← mul_assoc]

/-- The Uniqueness Theorem: The Geometric Mirror is absolute. -/
theorem MoorePenrose_unique {A B C : R} 
    (hB : IsMoorePenroseInverse A B) 
    (hC : IsMoorePenroseInverse A C) : B = C := by
  have h1 : A * B = A * C := by
    calc
      A * B = (A * B)† := hB.ab_adj_eq.symm
      _ = B† * A† := by rw [star_mul]
      _ = B† * (A * C * A)† := by rw [hC.aba_eq_a]
      _ = B† * (A† * C† * A†) := by rw [adjoint_mul_triple]
      _ = (B† * A†) * C† * A† := by simp [mul_assoc]
      _ = (A * B)† * C† * A† := by rw [star_mul]
      _ = (A * B) * C† * A† := by rw [hB.ab_adj_eq]
      _ = A * B * (C† * A†) := by rw [mul_assoc]
      _ = A * B * (A * C)† := by rw [star_mul]
      _ = A * B * (A * C) := by rw [hC.ab_adj_eq]
      _ = (A * B * A) * C := by simp [mul_assoc]
      _ = A * C := by rw [hB.aba_eq_a]
  have h2 : B * A = C * A := by
    calc
      B * A = (B * A)† := hB.ba_adj_eq.symm
      _ = A† * B† := by rw [star_mul]
      _ = (A * C * A)† * B† := by rw [hC.aba_eq_a]
      _ = (A† * C† * A†) * B† := by rw [adjoint_mul_triple]
      _ = A† * C† * (A† * B†) := by simp [mul_assoc]
      _ = A† * C† * (B * A)† := by rw [star_mul]
      _ = A† * C† * (B * A) := by rw [hB.ba_adj_eq]
      _ = (C * A)† * (B * A) := by rw [star_mul]
      _ = (C * A) * (B * A) := by rw [hC.ba_adj_eq]
      _ = C * (A * B * A) := by simp [mul_assoc]
      _ = C * A := by rw [hB.aba_eq_a]
  calc
    B = B * A * B := hB.bab_eq_b.symm
    _ = (B * A) * B := by rw [mul_assoc]
    _ = (C * A) * B := by rw [h2]
    _ = C * (A * B) := by rw [← mul_assoc]
    _ = C * (A * C) := by rw [h1]
    _ = C * A * C := by rw [mul_assoc]
    _ = C := hC.bab_eq_b

/-- The Geometric/Metric Support Projector P_{MP} = A * A^+ -/
def MP_Projector (A B : R) (_h : IsMoorePenroseInverse A B) : R := A * B

lemma MP_Projector_idempotent {A B : R} (h : IsMoorePenroseInverse A B) : 
    (MP_Projector A B h) * (MP_Projector A B h) = MP_Projector A B h := by
  unfold MP_Projector
  calc
    (A * B) * (A * B) = (A * B * A) * B := by simp [mul_assoc]
    _ = A * B := by rw [h.eq1]

lemma MP_Projector_self_adjoint {A B : R} (h : IsMoorePenroseInverse A B) : 
    (MP_Projector A B h)† = MP_Projector A B h := h.ab_adj_eq

end MP
end InfoGeometry.Singular.MoorePenroseAdjoint

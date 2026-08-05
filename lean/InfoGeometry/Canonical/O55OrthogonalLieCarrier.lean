import InfoGeometry.Canonical.SplitCliffordO55TKKClosure

/-!
# Real module structure on the diagonal `O(5,5)` infinitesimal carrier

The upstream owner supplies the orthogonality equation.  This owner bundles
that same predicate as a real submodule, which is the prerequisite for any
finite-dimensional Lie-algebra statement.
-/

noncomputable section

namespace InfoGeometry.Canonical.O55Representation

open Matrix

abbrev O55Matrix := Matrix (Fin 10) (Fin 10) ℝ

def orthogonal55Predicate (A : O55Matrix) : Prop :=
  Aᵀ * O55Form + O55Form * A = 0

theorem orthogonal55Predicate_smul (r : ℝ) {A : O55Matrix}
    (hA : orthogonal55Predicate A) :
    orthogonal55Predicate (r • A) := by
  change (r • A)ᵀ * O55Form + O55Form * (r • A) = 0
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
  rw [← smul_add, hA, smul_zero]

theorem orthogonal55Predicate_add {A B : O55Matrix}
    (hA : orthogonal55Predicate A) (hB : orthogonal55Predicate B) :
    orthogonal55Predicate (A + B) := by
  change (A + B)ᵀ * O55Form + O55Form * (A + B) = 0
  rw [Matrix.transpose_add, add_mul, mul_add]
  change (Aᵀ * O55Form + Bᵀ * O55Form) +
      (O55Form * A + O55Form * B) = 0
  calc
    (Aᵀ * O55Form + Bᵀ * O55Form) +
        (O55Form * A + O55Form * B) =
        (Aᵀ * O55Form + O55Form * A) +
          (Bᵀ * O55Form + O55Form * B) := by abel
    _ = 0 := by rw [hA, hB, add_zero]

theorem orthogonal55Predicate_neg {A : O55Matrix}
    (hA : orthogonal55Predicate A) :
    orthogonal55Predicate (-A) := by
  simpa [orthogonal55Predicate, Matrix.transpose_neg, neg_mul, mul_neg,
    neg_add, add_comm] using congrArg Neg.neg hA

theorem orthogonal55Predicate_commutator {A B : O55Matrix}
    (hA : orthogonal55Predicate A) (hB : orthogonal55Predicate B) :
    orthogonal55Predicate (A * B - B * A) := by
  have hA' : Aᵀ * O55Form = -(O55Form * A) :=
    eq_neg_of_add_eq_zero_left hA
  have hB' : Bᵀ * O55Form = -(O55Form * B) :=
    eq_neg_of_add_eq_zero_left hB
  change (A * B - B * A)ᵀ * O55Form +
      O55Form * (A * B - B * A) = 0
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
    sub_mul, mul_sub, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hA', hB']
  simp only [mul_neg, sub_eq_add_neg]
  rw [← Matrix.mul_assoc Bᵀ O55Form A,
    ← Matrix.mul_assoc Aᵀ O55Form B]
  rw [hB', hA']
  simp only [neg_mul, sub_eq_add_neg]
  simp only [neg_neg]
  have h₁ : (-1 : ℝ) • (O55Form * A * B) = -(O55Form * A * B) := by
    exact neg_one_smul ℝ (O55Form * A * B)
  have h₂ : (-1 : ℝ) • (O55Form * B * A) = -(O55Form * B * A) := by
    exact neg_one_smul ℝ (O55Form * B * A)
  rw [← Matrix.mul_assoc O55Form A B,
    ← Matrix.mul_assoc O55Form B A]
  abel

noncomputable def orthogonal55Submodule : Submodule ℝ O55Matrix where
  carrier := {A | orthogonal55Predicate A}
  zero_mem' := by
    simp [orthogonal55Predicate]
  add_mem' := by
    intro A B hA hB
    exact orthogonal55Predicate_add hA hB
  smul_mem' := by
    intro r A hA
    exact orthogonal55Predicate_smul r hA

abbrev Orthogonal55 := orthogonal55Submodule

theorem orthogonal55Predicate_iff_mem (A : O55Matrix) :
    orthogonal55Predicate A ↔ A ∈ orthogonal55Submodule := Iff.rfl

@[simp] theorem orthogonal55_smul_val (r : ℝ) (A : Orthogonal55) :
    ((r • A : Orthogonal55) : O55Matrix) = r • (A : O55Matrix) := rfl

def orthogonal55Bracket (A B : Orthogonal55) : Orthogonal55 :=
  ⟨(A : O55Matrix) * (B : O55Matrix) -
      (B : O55Matrix) * (A : O55Matrix),
    orthogonal55Predicate_commutator A.property B.property⟩

noncomputable instance : LieRing Orthogonal55 where
  bracket := orthogonal55Bracket
  add_lie := by
    intro A B C
    apply Subtype.ext
    change ((A : O55Matrix) + (B : O55Matrix)) * (C : O55Matrix) -
      (C : O55Matrix) * ((A : O55Matrix) + (B : O55Matrix)) =
      ((A : O55Matrix) * (C : O55Matrix) -
        (C : O55Matrix) * (A : O55Matrix)) +
      ((B : O55Matrix) * (C : O55Matrix) -
        (C : O55Matrix) * (B : O55Matrix))
    rw [add_mul, mul_add]
    abel
  lie_add := by
    intro A B C
    apply Subtype.ext
    change (A : O55Matrix) * ((B : O55Matrix) + (C : O55Matrix)) -
      ((B : O55Matrix) + (C : O55Matrix)) * (A : O55Matrix) =
      ((A : O55Matrix) * (B : O55Matrix) -
        (B : O55Matrix) * (A : O55Matrix)) +
      ((A : O55Matrix) * (C : O55Matrix) -
        (C : O55Matrix) * (A : O55Matrix))
    rw [mul_add, add_mul]
    abel
  lie_self := by
    intro A
    apply Subtype.ext
    simp only [orthogonal55Bracket, Subtype.coe_mk]
    simp
  leibniz_lie := by
    intro A B C
    apply Subtype.ext
    simp [orthogonal55Bracket]
    noncomm_ring

noncomputable instance : LieAlgebra ℝ Orthogonal55 where
  lie_smul := by
    intro r A B
    apply Subtype.ext
    change (A : O55Matrix) * (r • (B : O55Matrix)) -
      (r • (B : O55Matrix)) * (A : O55Matrix) =
      r • ((A : O55Matrix) * (B : O55Matrix) -
        (B : O55Matrix) * (A : O55Matrix))
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

end InfoGeometry.Canonical.O55Representation

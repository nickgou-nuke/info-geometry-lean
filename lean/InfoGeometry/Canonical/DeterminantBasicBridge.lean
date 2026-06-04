import Mathlib

namespace InfoGeometry.Canonical.DeterminantBasicBridge

/-!
BUCKET 1: CLOSED FINITE THEOREMS:
  - det2_identity
  - det2_duplicate_rows_zero
  - det2_duplicate_cols_zero
  - det2_swap_rows
  - det2_swap_cols
  - det2_row1_add
  - det2_row2_add
  - det2_col1_add
  - det2_col2_add
  - det2_row1_smul
  - det2_row2_smul
  - det2_col1_smul
  - det2_col2_smul
  - det2_upper_triangular
  - det2_lower_triangular
  - det2_mul
  - det2_chain_append
  - finite_colimit_det_succ
  - finite_colimit_det_add
  - berDiag_one
  - berDiag_mul
  - berDiag_inv_cancel

BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES:
  - tensorDet2_kron_rule, conditional on an explicit determinant-of-tensor witness.

BUCKET 3: OPEN CLOSURE DEBT:
  - No infinite determinant is asserted for the colimit.
  - No Fredholm, Fuglede-Kadison, zeta-regularized, or Berezin-Schur theorem is asserted.
  - Berezinian is closed only for diagonal 1|1 blocks.
-/

section Det2

variable {R : Type*} [CommRing R]

def det2 (a b c d : R) : R :=
  a * d - b * c

@[simp] theorem det2_identity :
    det2 (1 : R) 0 0 1 = 1 := by
  unfold det2
  ring

@[simp] theorem det2_duplicate_rows_zero (a b : R) :
    det2 a b a b = 0 := by
  unfold det2
  ring

@[simp] theorem det2_duplicate_cols_zero (a b : R) :
    det2 a a b b = 0 := by
  unfold det2
  ring

theorem det2_swap_rows (a b c d : R) :
    det2 c d a b = - det2 a b c d := by
  unfold det2
  ring

theorem det2_swap_cols (a b c d : R) :
    det2 b a d c = - det2 a b c d := by
  unfold det2
  ring

theorem det2_row1_add (a b a' b' c d : R) :
    det2 (a + a') (b + b') c d = det2 a b c d + det2 a' b' c d := by
  unfold det2
  ring

theorem det2_row2_add (a b c d c' d' : R) :
    det2 a b (c + c') (d + d') = det2 a b c d + det2 a b c' d' := by
  unfold det2
  ring

theorem det2_col1_add (a c a' c' b d : R) :
    det2 (a + a') b (c + c') d = det2 a b c d + det2 a' b c' d := by
  unfold det2
  ring

theorem det2_col2_add (a c b d b' d' : R) :
    det2 a (b + b') c (d + d') = det2 a b c d + det2 a b' c d' := by
  unfold det2
  ring

theorem det2_row1_smul (r a b c d : R) :
    det2 (r * a) (r * b) c d = r * det2 a b c d := by
  unfold det2
  ring

theorem det2_row2_smul (r a b c d : R) :
    det2 a b (r * c) (r * d) = r * det2 a b c d := by
  unfold det2
  ring

theorem det2_col1_smul (r a b c d : R) :
    det2 (r * a) b (r * c) d = r * det2 a b c d := by
  unfold det2
  ring

theorem det2_col2_smul (r a b c d : R) :
    det2 a (r * b) c (r * d) = r * det2 a b c d := by
  unfold det2
  ring

theorem det2_upper_triangular (a b d : R) :
    det2 a b 0 d = a * d := by
  unfold det2
  ring

theorem det2_lower_triangular (a c d : R) :
    det2 a 0 c d = a * d := by
  unfold det2
  ring

theorem det2_mul
    (a b c d e f g h : R) :
    det2 (a * e + b * g) (a * f + b * h)
      (c * e + d * g) (c * f + d * h)
      = det2 a b c d * det2 e f g h := by
  unfold det2
  ring

structure Mat2 (R : Type*) where
  a11 : R
  a12 : R
  a21 : R
  a22 : R

def Mat2.det (A : Mat2 R) : R :=
  det2 A.a11 A.a12 A.a21 A.a22

def det2Chain : List (Mat2 R) → R
  | [] => 1
  | A :: As => A.det * det2Chain As

@[simp] theorem det2_chain_nil :
    det2Chain ([] : List (Mat2 R)) = 1 := rfl

@[simp] theorem det2_chain_cons (A : Mat2 R) (As : List (Mat2 R)) :
    det2Chain (A :: As) = A.det * det2Chain As := rfl

theorem det2_chain_append (As Bs : List (Mat2 R)) :
    det2Chain (As ++ Bs) = det2Chain As * det2Chain Bs := by
  induction As with
  | nil => simp [det2Chain]
  | cons A As ih => simp [det2Chain, ih, mul_assoc]

def finiteColimitDet (chain : ℕ → Mat2 R) : ℕ → R
  | 0 => 1
  | n + 1 => finiteColimitDet chain n * (chain n).det

@[simp] theorem finite_colimit_det_zero (chain : ℕ → Mat2 R) :
    finiteColimitDet chain 0 = 1 := rfl

theorem finite_colimit_det_succ (chain : ℕ → Mat2 R) (n : ℕ) :
    finiteColimitDet chain (n + 1) = finiteColimitDet chain n * (chain n).det := rfl

theorem finite_colimit_det_add
    (chain : ℕ → Mat2 R) :
    ∀ m n : ℕ,
      finiteColimitDet chain (m + n) =
        finiteColimitDet chain m * finiteColimitDet (fun k => chain (m + k)) n
  | m, 0 => by
      simp [finiteColimitDet]
  | m, n + 1 => by
      rw [Nat.add_succ]
      rw [finite_colimit_det_succ]
      rw [finite_colimit_det_add chain m n]
      rw [finite_colimit_det_succ]
      ring

def tensorDet2Witness (A B : Mat2 R) (detTensor : Mat2 R → Mat2 R → R) : Prop :=
  detTensor A B = (A.det) ^ 2 * (B.det) ^ 2

theorem tensorDet2_kron_rule
    (A B : Mat2 R) (detTensor : Mat2 R → Mat2 R → R)
    (h : tensorDet2Witness A B detTensor) :
    detTensor A B = (A.det) ^ 2 * (B.det) ^ 2 := h

end Det2

section BerezinianDiagonal

variable {K : Type*} [Field K]

def berDiag (a d : K) : K :=
  a / d

@[simp] theorem berDiag_one :
    berDiag (1 : K) 1 = 1 := by
  unfold berDiag
  simp

theorem berDiag_mul (a₁ d₁ a₂ d₂ : K) :
    berDiag (a₁ * a₂) (d₁ * d₂) = berDiag a₁ d₁ * berDiag a₂ d₂ := by
  unfold berDiag
  by_cases hd1 : d₁ = 0
  · simp [hd1]
  · by_cases hd2 : d₂ = 0
    · simp [hd2]
    · field_simp [hd1, hd2]
      ring

theorem berDiag_inv_cancel (a d : K) (ha : a ≠ 0) (hd : d ≠ 0) :
    berDiag a d * berDiag d a = 1 := by
  unfold berDiag
  field_simp [ha, hd]
  ring

def berDiagUnitsHom : Kˣ × Kˣ →* Kˣ where
  toFun x := x.1 / x.2
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

@[simp] theorem berDiagUnitsHom_apply (a d : Kˣ) :
    berDiagUnitsHom (K := K) (a, d) = a / d := rfl

end BerezinianDiagonal

end InfoGeometry.Canonical.DeterminantBasicBridge

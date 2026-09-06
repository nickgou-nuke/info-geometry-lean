import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic
import InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge

/-!
# Witt44 Into Witt55 Bridge

This owner module formalizes the isometric carrier embedding and Lie algebra inclusion
of the 8-dimensional split-octonion Witt carrier $W_{4,4}$ into the 10-dimensional
Clifford Witt space $W_{5,5} = W_{4,4} \oplus H$:

1. **Carrier Isometric Injection:**
   $$j : W_{4,4} \hookrightarrow W_{5,5}, \qquad \langle j(x), j(y) \rangle_{W_{5,5}} = \langle x, y \rangle_{W_{4,4}}$$

2. **Block Lie Algebra Extension ($\mathfrak{so}(4,4) \hookrightarrow_{\mathrm{Lie}} \mathfrak{so}(5,5)$):**
   $$\operatorname{ext}_H \begin{pmatrix} A & B \\ C & D \end{pmatrix} = \begin{pmatrix} \operatorname{ext}(A) & \operatorname{ext}(B) \\ \operatorname{ext}(C) & \operatorname{ext}(D) \end{pmatrix}$$
   with:
   $$\operatorname{IsWittSkew}(M) \implies \operatorname{IsWittSkew}_5(\operatorname{ext}_H(M))$$

3. **Injective Lie Embedding:**
   $$\operatorname{ext}_H(M) = 0 \implies M = 0$$

4. **Commutative Action Intertwiner:**
   $$\operatorname{ext}_H(M) \cdot j(w) = j(M \cdot w)$$
-/

noncomputable section

namespace InfoGeometry.Canonical.Witt44IntoWitt55Bridge

open Matrix
open InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge

abbrev VPlus4 := Fin 4 → ℝ
abbrev VMinus4 := Fin 4 → ℝ
abbrev VPlus5 := Fin 5 → ℝ
abbrev VMinus5 := Fin 5 → ℝ

abbrev W44 := VPlus4 × VMinus4
abbrev W55 := VPlus5 × VMinus5

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev Mat5 := Matrix (Fin 5) (Fin 5) ℝ
abbrev Mat8 := Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ
abbrev Mat10 := Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) ℝ

structure WittBlock5 where
  A : Mat5
  B : Mat5
  C : Mat5
  D : Mat5

def etaW5 : Mat10 := fromBlocks 0 1 1 0

def toMat10 (M : WittBlock5) : Mat10 :=
  fromBlocks M.A M.B M.C M.D

def IsWittOrthogonalLie5 (M : WittBlock5) : Prop :=
  M.D = - M.Aᵀ ∧ M.Bᵀ = - M.B ∧ M.Cᵀ = - M.C

def IsWittSkew5 (M : WittBlock5) : Prop :=
  (toMat10 M)ᵀ * etaW5 + etaW5 * toMat10 M = 0

theorem isWittSkew5_iff (M : WittBlock5) :
    IsWittSkew5 M ↔ IsWittOrthogonalLie5 M := by
  dsimp [IsWittSkew5, IsWittOrthogonalLie5, toMat10, etaW5]
  rw [fromBlocks_transpose]
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
  rw [fromBlocks_add]
  rw [← (fromBlocks_zero : fromBlocks (0 : Mat5) 0 0 0 = (0 : Mat10))]
  rw [fromBlocks_inj]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(add_eq_zero_iff_neg_eq.mp h2).symm, eq_neg_of_add_eq_zero_left h4, eq_neg_of_add_eq_zero_left h1⟩
  · rintro ⟨hD, hB, hC⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hC, neg_add_cancel]
    · rw [hD, add_neg_cancel]
    · rw [hD, transpose_neg, transpose_transpose, neg_add_cancel]
    · rw [hB, neg_add_cancel]

/-- Zero-extension of a 4x4 matrix to a 5x5 matrix. -/
def ext4to5 (A : Mat4) : Mat5 :=
  Matrix.of (fun i j =>
    if hi : i.val < 4 then
      if hj : j.val < 4 then
        A ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else 0
    else 0)

/-- Block extension from 4x4 WittBlockMatrix to 5x5 WittBlock5. -/
def extWittBlock (M : WittBlockMatrix) : WittBlock5 where
  A := ext4to5 M.A
  B := ext4to5 M.B
  C := ext4to5 M.C
  D := ext4to5 M.D

/-- Canonical embedding of $V_+^{(4)}$ into $V_+^{(5)}$ via index injection. -/
def embedVPlus (u : VPlus4) : VPlus5 :=
  fun i => if h : i.val < 4 then u ⟨i.val, h⟩ else 0

/-- Canonical embedding of $V_-^{(4)}$ into $V_-^{(5)}$ via index injection. -/
def embedVMinus (v : VMinus4) : VMinus5 :=
  fun i => if h : i.val < 4 then v ⟨i.val, h⟩ else 0

/-- Embedding of the 8D split-octonion Witt carrier $W_{4,4}$ into $W_{5,5}$. -/
def embedW4toW5 (w : W44) : W55 :=
  (embedVPlus w.1, embedVMinus w.2)

/-- 5D Witt cross-pairing. -/
def wittPairing5 (u : VPlus5) (v : VMinus5) : ℝ :=
  ∑ i : Fin 5, u i * v i

/-- 4D Witt cross-pairing. -/
def wittPairing4 (u : VPlus4) (v : VMinus4) : ℝ :=
  ∑ i : Fin 4, u i * v i

/-- 🏆 THEOREM 1: The cross-tower embedding preserves the Witt pairing isometrically. -/
theorem embedW4toW5_preserves_pairing (u : VPlus4) (v : VMinus4) :
    wittPairing5 (embedVPlus u) (embedVMinus v) = wittPairing4 u v := by
  dsimp [wittPairing5, wittPairing4, embedVPlus, embedVMinus]
  rw [Fin.sum_univ_five, Fin.sum_univ_four]
  simp

/-- Transpose of extended matrix equals extension of transpose. -/
theorem ext4to5_transpose (A : Mat4) :
    (ext4to5 A)ᵀ = ext4to5 Aᵀ := by
  ext i j
  dsimp [ext4to5, Matrix.transpose]
  split_ifs <;> rfl

theorem ext4to5_neg (A : Mat4) :
    ext4to5 (-A) = - ext4to5 A := by
  ext i j
  dsimp [ext4to5]
  split_ifs <;> ring

theorem ext4to5_injective :
    Function.Injective ext4to5 := by
  intro A B h
  ext i j
  have hij := congrFun (congrFun h ⟨i.val, by omega⟩) ⟨j.val, by omega⟩
  dsimp [ext4to5] at hij
  simp only [i.is_lt, j.is_lt] at hij
  exact hij

/-- 🏆 THEOREM 2: Block Lie algebra extension embeds $\mathfrak{so}(4,4)$ into $\mathfrak{so}(5,5)$. -/
theorem extWittBlock_preserves_isWittOrthogonalLie (M : WittBlockMatrix)
    (h : IsWittOrthogonalLie M) :
    IsWittOrthogonalLie5 (extWittBlock M) := by
  dsimp [IsWittOrthogonalLie] at h
  dsimp [IsWittOrthogonalLie5, extWittBlock]
  rcases h with ⟨hD, hB, hC⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hD, ext4to5_neg, ext4to5_transpose]
  · rw [ext4to5_transpose, hB, ext4to5_neg]
  · rw [ext4to5_transpose, hC, ext4to5_neg]

/-- 🏆 THEOREM 3: The extension map sends Witt-skew matrices to Witt-skew matrices. -/
theorem extWittBlock_preserves_isWittSkew (M : WittBlockMatrix)
    (h : IsWittSkew M) :
    IsWittSkew5 (extWittBlock M) := by
  rw [isWittSkew5_iff]
  rw [isWittSkew_iff_isWittOrthogonalLie] at h
  exact extWittBlock_preserves_isWittOrthogonalLie M h

/-- 🏆 THEOREM 4: The block extension is injective. -/
theorem extWittBlock_injective :
    Function.Injective extWittBlock := by
  intro M N h
  cases M; cases N
  dsimp [extWittBlock] at h
  injection h with hA hB hC hD
  rw [ext4to5_injective hA, ext4to5_injective hB, ext4to5_injective hC, ext4to5_injective hD]

/-- 🏆 THEOREM 5: Commutative Intertwiner:
    $\operatorname{ext}(A) \cdot j(u) = j(A \cdot u)$ on $V_+$. -/
theorem ext4to5_mulVec_embedVPlus (A : Mat4) (u : VPlus4) :
    mulVec (ext4to5 A) (embedVPlus u) = embedVPlus (mulVec A u) := by
  ext ⟨i, hi⟩
  dsimp [mulVec, dotProduct, ext4to5, embedVPlus]
  split_ifs with hi4
  · rw [Fin.sum_univ_five, Fin.sum_univ_four]
    simp
  · rw [Fin.sum_univ_five]
    simp

/-- 🏆 THEOREM 6: Commutative Intertwiner:
    $\operatorname{ext}(A) \cdot j(v) = j(A \cdot v)$ on $V_-$. -/
theorem ext4to5_mulVec_embedVMinus (A : Mat4) (v : VMinus4) :
    mulVec (ext4to5 A) (embedVMinus v) = embedVMinus (mulVec A v) := by
  ext ⟨i, hi⟩
  dsimp [mulVec, dotProduct, ext4to5, embedVMinus]
  split_ifs with hi4
  · rw [Fin.sum_univ_five, Fin.sum_univ_four]
    simp
  · rw [Fin.sum_univ_five]
    simp

end InfoGeometry.Canonical.Witt44IntoWitt55Bridge

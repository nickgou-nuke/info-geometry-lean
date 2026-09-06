import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic
import InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge

set_option linter.unusedSimpArgs false

/-!
# Witt44 into Witt55 Carrier and Lie Embedding Bridge

This owner module formalizes the canonical isometric inclusion of the 8-dimensional
split-octonion Witt carrier into the 10-dimensional $\mathrm{Cl}(5,5)$ Witt carrier:

1. **Carrier Infiltration:**
   $$W_{5,5} = W_{4,4} \oplus H_5$$
   via $j : W_{4,4} \hookrightarrow W_{5,5}$, $j(u, v) = (\operatorname{embedVPlus}(u), \operatorname{embedVMinus}(v))$.

2. **Witt Pairing and Quadratic Form Isometry:**
   $$\langle j(w), j(w') \rangle_{5,5} = \langle w, w' \rangle_{4,4}, \qquad q_{5,5}(j(w)) = q_{4,4}(w).$$

3. **Block Endomorphism Extension $\operatorname{extBlock}$:**
   $$\operatorname{extBlock} \begin{pmatrix} A & B \\ C & D \end{pmatrix} =
     \begin{pmatrix} \operatorname{embedBlock}(A) & \operatorname{embedBlock}(B) \\
                     \operatorname{embedBlock}(C) & \operatorname{embedBlock}(D) \end{pmatrix}$$
   mapping $\mathfrak{so}(4,4) \hookrightarrow \mathfrak{so}(5,5)$.

4. **Action Intertwining Law:**
   $$j(T \cdot w) = \operatorname{extBlock}(T) \cdot j(w)$$
   establishing the exact commutative square between 8D split-octonion derivations and 10D $\mathrm{Cl}(5,5)$ Witt actions.
-/

noncomputable section

namespace InfoGeometry.Lie.Witt44IntoWitt55Bridge

open Matrix
open InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev Mat5 := Matrix (Fin 5) (Fin 5) ℝ
abbrev Mat8 := Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ
abbrev Mat10 := Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) ℝ

abbrev VPlus4 := Fin 4 → ℝ
abbrev VMinus4 := Fin 4 → ℝ
abbrev VPlus5 := Fin 5 → ℝ
abbrev VMinus5 := Fin 5 → ℝ

abbrev W44 := VPlus4 × VMinus4
abbrev W55 := VPlus5 × VMinus5

/-- Canonical embedding of $V_+^{(4)}$ into $V_+^{(5)}$ via zero padding at index 4. -/
def embedVPlus (u : VPlus4) : VPlus5 :=
  fun i => if h : i.val < 4 then u ⟨i.val, h⟩ else 0

/-- Canonical embedding of $V_-^{(4)}$ into $V_-^{(5)}$ via zero padding at index 4. -/
def embedVMinus (v : VMinus4) : VMinus5 :=
  fun i => if h : i.val < 4 then v ⟨i.val, h⟩ else 0

/-- Isometric inclusion $j : W_{4,4} \hookrightarrow W_{5,5}$. -/
def jEmbed (w : W44) : W55 :=
  (embedVPlus w.1, embedVMinus w.2)

def wittPairing4 (u : VPlus4) (v : VMinus4) : ℝ :=
  ∑ i : Fin 4, u i * v i

def wittPairing5 (u : VPlus5) (v : VMinus5) : ℝ :=
  ∑ i : Fin 5, u i * v i

def q44 (w : W44) : ℝ :=
  wittPairing4 w.1 w.2

def q55 (w : W55) : ℝ :=
  wittPairing5 w.1 w.2

/-- 🏆 THEOREM 1: The embedding $j$ preserves the Witt pairing isometrically. -/
theorem jEmbed_preserves_pairing (u : VPlus4) (v : VMinus4) :
    wittPairing5 (embedVPlus u) (embedVMinus v) = wittPairing4 u v := by
  dsimp [wittPairing5, wittPairing4, embedVPlus, embedVMinus]
  rw [Fin.sum_univ_five, Fin.sum_univ_four]
  simp

/-- 🏆 THEOREM 2: The embedding $j$ preserves the quadratic form: $q_{5,5}(j(w)) = q_{4,4}(w)$. -/
theorem jEmbed_preserves_quadratic (w : W44) :
    q55 (jEmbed w) = q44 w :=
  jEmbed_preserves_pairing w.1 w.2

/-- Embedding of 4x4 matrix block into 5x5 matrix block by zero padding. -/
def embedBlock (M : Mat4) : Mat5 :=
  fun i j =>
    if hi : i.val < 4 then
      if hj : j.val < 4 then
        M ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else 0
    else 0

@[simp] theorem embedBlock_zero :
    embedBlock (0 : Mat4) = 0 := by
  ext i j
  dsimp [embedBlock]
  by_cases hi : i.val < 4 <;> by_cases hj : j.val < 4 <;> simp [hi, hj]

@[simp] theorem embedBlock_transpose (M : Mat4) :
    (embedBlock M)ᵀ = embedBlock (Mᵀ) := by
  ext i j
  dsimp [embedBlock, Matrix.transpose]
  by_cases hi : i.val < 4 <;> by_cases hj : j.val < 4 <;> simp [hi, hj]

@[simp] theorem embedBlock_add (M N : Mat4) :
    embedBlock (M + N) = embedBlock M + embedBlock N := by
  ext i j
  dsimp [embedBlock]
  by_cases hi : i.val < 4 <;> by_cases hj : j.val < 4 <;> simp [hi, hj]

@[simp] theorem embedBlock_neg (M : Mat4) :
    embedBlock (-M) = - embedBlock M := by
  ext i j
  dsimp [embedBlock]
  by_cases hi : i.val < 4 <;> by_cases hj : j.val < 4 <;> simp [hi, hj]

@[simp] theorem embedBlock_sub (M N : Mat4) :
    embedBlock (M - N) = embedBlock M - embedBlock N := by
  ext i j
  dsimp [embedBlock]
  by_cases hi : i.val < 4 <;> by_cases hj : j.val < 4 <;> simp [hi, hj]

@[simp] theorem embedBlock_mul (M N : Mat4) :
    embedBlock (M * N) = embedBlock M * embedBlock N := by
  ext i j
  by_cases hi : i.val < 4
  · by_cases hj : j.val < 4
    · dsimp [embedBlock, mul_apply]
      simp only [dif_pos hi, dif_pos hj]
      rw [Fin.sum_univ_five, Fin.sum_univ_four]
      dsimp [embedBlock]
      simp
    · have h_lhs : embedBlock (M * N) i j = 0 := by
        dsimp [embedBlock]; rw [dif_pos hi, dif_neg hj]
      have h_rhs : (embedBlock M * embedBlock N) i j = 0 := by
        dsimp [mul_apply]
        have h_zero (k : Fin 5) : embedBlock N k j = 0 := by
          dsimp [embedBlock]
          by_cases hk : k.val < 4
          · rw [dif_pos hk, dif_neg hj]
          · rw [dif_neg hk]
        have : (∑ k : Fin 5, embedBlock M i k * embedBlock N k j) =
               (∑ k : Fin 5, (0 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [h_zero k, mul_zero]
        rw [this, Finset.sum_const_zero]
      rw [h_lhs, h_rhs]
  · have h_lhs : embedBlock (M * N) i j = 0 := by
      dsimp [embedBlock]; rw [dif_neg hi]
    have h_rhs : (embedBlock M * embedBlock N) i j = 0 := by
      dsimp [mul_apply]
      have h_zero (k : Fin 5) : embedBlock M i k = 0 := by
        dsimp [embedBlock]; rw [dif_neg hi]
      have : (∑ k : Fin 5, embedBlock M i k * embedBlock N k j) =
             (∑ k : Fin 5, (0 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [h_zero k, zero_mul]
      rw [this, Finset.sum_const_zero]
    rw [h_lhs, h_rhs]

theorem embedBlock_injective : Function.Injective embedBlock := by
  intro M N h
  ext i j
  have hi := i.is_lt
  have hj := j.is_lt
  have hij := congrFun (congrFun h ⟨i.val, by omega⟩) ⟨j.val, by omega⟩
  dsimp [embedBlock] at hij
  rw [if_pos hi, if_pos hj, if_pos hi, if_pos hj] at hij
  exact hij

/-- 5x5 Witt Block Matrix structure. -/
structure WittBlockMatrix55 where
  A : Mat5
  B : Mat5
  C : Mat5
  D : Mat5

def toMat10 (M : WittBlockMatrix55) : Mat10 :=
  fromBlocks M.A M.B M.C M.D

def etaW55 : Mat10 :=
  fromBlocks 0 1 1 0

def IsWittOrthogonalLie55 (M : WittBlockMatrix55) : Prop :=
  M.D = - M.Aᵀ ∧ M.Bᵀ = - M.B ∧ M.Cᵀ = - M.C

def IsWittSkew55 (M : WittBlockMatrix55) : Prop :=
  (toMat10 M)ᵀ * etaW55 + etaW55 * (toMat10 M) = 0

theorem isWittSkew55_iff_isWittOrthogonalLie (M : WittBlockMatrix55) :
    IsWittSkew55 M ↔ IsWittOrthogonalLie55 M := by
  dsimp [IsWittSkew55, IsWittOrthogonalLie55, toMat10, etaW55]
  rw [fromBlocks_transpose]
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
  rw [fromBlocks_add]
  rw [← (fromBlocks_zero : fromBlocks (0 : Mat5) 0 0 0 = (0 : Mat10))]
  rw [fromBlocks_inj]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨eq_neg_of_add_eq_zero_right h2,
           eq_neg_of_add_eq_zero_left h4,
           eq_neg_of_add_eq_zero_left h1⟩
  · rintro ⟨hD, hB, hC⟩
    exact ⟨by rw [hC, neg_add_cancel],
           by rw [hD, add_neg_cancel],
           by rw [hD, transpose_neg, transpose_transpose, neg_add_cancel],
           by rw [hB, neg_add_cancel]⟩

/-- Extension of a 4x4 WittBlockMatrix to 5x5 WittBlockMatrix. -/
def extBlock (T : WittBlockMatrix) : WittBlockMatrix55 :=
  ⟨embedBlock T.A, embedBlock T.B, embedBlock T.C, embedBlock T.D⟩

/-- 🏆 THEOREM 3: $\operatorname{extBlock}$ maps $\mathfrak{so}(4,4)$ into $\mathfrak{so}(5,5)$. -/
theorem extBlock_witt_skew (T : WittBlockMatrix) (hT : IsWittOrthogonalLie T) :
    IsWittOrthogonalLie55 (extBlock T) := by
  rcases hT with ⟨hD, hB, hC⟩
  dsimp [IsWittOrthogonalLie55, extBlock]
  refine ⟨?_, ?_, ?_⟩
  · rw [embedBlock_transpose, hD, embedBlock_neg]
  · rw [embedBlock_transpose, hB, embedBlock_neg]
  · rw [embedBlock_transpose, hC, embedBlock_neg]

/-- Extension of WittBlockMatrix to Mat10. -/
def extMat8 (T : WittBlockMatrix) : Mat10 :=
  toMat10 (extBlock T)

theorem extMat8_isWittSkew55 (T : WittBlockMatrix) (hT : IsWittOrthogonalLie T) :
    IsWittSkew55 (extBlock T) :=
  (isWittSkew55_iff_isWittOrthogonalLie (extBlock T)).mpr (extBlock_witt_skew T hT)

/-- 🏆 THEOREM 4: $\operatorname{extBlock}$ is injective. -/
theorem extBlock_injective : Function.Injective extBlock := by
  intro T1 T2 h
  dsimp [extBlock] at h
  cases T1; cases T2
  simp only [WittBlockMatrix55.mk.injEq] at h
  rcases h with ⟨hA, hB, hC, hD⟩
  congr
  · exact embedBlock_injective hA
  · exact embedBlock_injective hB
  · exact embedBlock_injective hC
  · exact embedBlock_injective hD

/-- 🏆 THEOREM 5: Action Intertwining: $j(T \cdot w) = \operatorname{extBlock}(T) \cdot j(w)$. -/
theorem extBlock_intertwine_action (T : WittBlockMatrix) (u : VPlus4) (v : VMinus4) :
    (embedVPlus (T.A *ᵥ u + T.B *ᵥ v) =
      (embedBlock T.A) *ᵥ (embedVPlus u) + (embedBlock T.B) *ᵥ (embedVMinus v)) ∧
    (embedVMinus (T.C *ᵥ u + T.D *ᵥ v) =
      (embedBlock T.C) *ᵥ (embedVPlus u) + (embedBlock T.D) *ᵥ (embedVMinus v)) := by
  constructor
  · ext i
    dsimp [embedVPlus, embedVMinus, embedBlock, Matrix.mulVec, dotProduct]
    by_cases hi : i.val < 4
    · simp only [dif_pos hi]
      rw [Fin.sum_univ_five, Fin.sum_univ_five, Fin.sum_univ_four, Fin.sum_univ_four]
      simp
    · simp only [dif_neg hi]
      rw [Fin.sum_univ_five, Fin.sum_univ_five]
      simp [hi]
  · ext i
    dsimp [embedVPlus, embedVMinus, embedBlock, Matrix.mulVec, dotProduct]
    by_cases hi : i.val < 4
    · simp only [dif_pos hi]
      rw [Fin.sum_univ_five, Fin.sum_univ_five, Fin.sum_univ_four, Fin.sum_univ_four]
      simp
    · simp only [dif_neg hi]
      rw [Fin.sum_univ_five, Fin.sum_univ_five]
      simp [hi]

end InfoGeometry.Lie.Witt44IntoWitt55Bridge

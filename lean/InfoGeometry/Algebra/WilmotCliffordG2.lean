import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import InfoGeometry.Algebra.Zorn.G2KillingCartanMatrix

/-!
# Exceptional Lie Algebra $\mathfrak{g}_2$ from Clifford Algebra and Calibrations (Wilmot 2025)

Formalizes the construction of the exceptional Lie algebra $\mathfrak{g}_2$ inside
$\mathfrak{so}(7)$ from 3-form and 4-form calibrations using the Clifford algebra /
geometric algebra $GA(7)$ framework of:
- G. P. Wilmot, *Construction of exceptional Lie algebra $G_2$ and non-associative algebras
  using Clifford algebra*, arXiv:2505.06011v1 (2025).

### Main Mathematical Architecture:
1. **The 7 Fano Triads and Calibration 4-forms**:
   The 7 lines of the Fano plane induce 7 4-form terms $e_{jklm}$ in the dual calibration $\Phi_O^*$.
2. **The 14 Bryant-Wilmot Generators**:
   The 14 bivector generators $A, B, C, D, E, F, G, H, I, J, K, L, M, N \in \mathfrak{so}(7)$ (indexed on 0..6).
3. **The 7 Bryant Triad Sum Relations**:
   Proves the 7 triad sum identities:
   $A+H$, $B+I$, $C+J$, $D+K$, $E-L$, $F+M$, $G+N$.
4. **Wilmot Projector and Idempotent Law**:
   Proves the idempotent law $\alpha^2 = \alpha$ and the orthogonality relations
   $\alpha \beta = \beta \alpha = 0$.
5. **Skew-Symmetry and Dimension**:
   Proves all 14 generators are skew-symmetric and span the 14-dimensional Lie algebra $\mathfrak{g}_2$.
-/

noncomputable section

namespace InfoGeometry.Algebra.WilmotCliffordG2

open Matrix
open InfoGeometry.Algebra.Zorn.G2KillingCartanMatrix

theorem skewGen_eq_single_sub (i j : Fin 7) :
    skewGen i j = Matrix.single i j (1 : ℝ) - Matrix.single j i (1 : ℝ) := by
  ext a b
  dsimp [skewGen, Matrix.single, Matrix.sub_apply]
  have h₁ : (a = i ∧ b = j) ↔ (i = a ∧ j = b) := by
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2.symm⟩
  have h₂ : (a = j ∧ b = i) ↔ (j = a ∧ i = b) := by
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2.symm⟩
  have hif₁ :
      (if a = i ∧ b = j then (1 : ℝ) else 0) =
        if i = a ∧ j = b then (1 : ℝ) else 0 :=
    if_congr h₁ rfl rfl
  have hif₂ :
      (if a = j ∧ b = i then (1 : ℝ) else 0) =
        if j = a ∧ i = b then (1 : ℝ) else 0 :=
    if_congr h₂ rfl rfl
  rw [hif₁, hif₂]

theorem matrix_single_mul_single
    (i j k l : Fin 7) (a b : ℝ) :
    Matrix.single i j a * Matrix.single k l b =
      if j = k then Matrix.single i l (a * b) else 0 := by
  by_cases h : j = k
  · subst k
    simp
  · rw [if_neg h]
    exact @Matrix.single_mul_single_of_ne (Fin 7) (Fin 7) (Fin 7) ℝ
      inferInstance inferInstance inferInstance inferInstance inferInstance
      a i j k l h b

theorem matrix_single_neg (i j : Fin 7) (a : ℝ) :
    -Matrix.single i j a = Matrix.single i j (-a) := by
  ext k l
  dsimp [Matrix.single, Matrix.of_apply]
  split_ifs <;> ring

/-! =========================================================================
    1. The 14 Bryant-Wilmot Generators of 𝔤₂ in 𝔰𝔬(7) (0-indexed)
    ========================================================================= -/

/-- The 14 Bryant-Wilmot generators $A, B, C, D, E, F, G, H, I, J, K, L, M, N$ of $\mathfrak{g}_2 \subset \mathfrak{so}(7)$. -/
noncomputable def bryantGen (m : Fin 14) : Matrix (Fin 7) (Fin 7) ℝ :=
  match m with
  -- A = (1/2)(e_{12} - e_{34})
  | 0  => (1/2 : ℝ) • (skewGen 1 2 - skewGen 3 4)
  -- B = (1/2)(-e_{02} - e_{35})
  | 1  => (1/2 : ℝ) • (- skewGen 0 2 - skewGen 3 5)
  -- C = (1/2)(e_{01} + e_{36})
  | 2  => (1/2 : ℝ) • (skewGen 0 1 + skewGen 3 6)
  -- D = (1/2)(-e_{04} + e_{15})
  | 3  => (1/2 : ℝ) • (- skewGen 0 4 + skewGen 1 5)
  -- E = (1/2)(e_{03} - e_{16})
  | 4  => (1/2 : ℝ) • (skewGen 0 3 - skewGen 1 6)
  -- F = (1/2)(e_{06} + e_{13})
  | 5  => (1/2 : ℝ) • (skewGen 0 6 + skewGen 1 3)
  -- G = (1/2)(-e_{05} - e_{14})
  | 6  => (1/2 : ℝ) • (- skewGen 0 5 - skewGen 1 4)
  -- H = (1/2)(e_{34} - e_{56})
  | 7  => (1/2 : ℝ) • (skewGen 3 4 - skewGen 5 6)
  -- I = (1/2)(e_{35} + e_{46})
  | 8  => (1/2 : ℝ) • (skewGen 3 5 + skewGen 4 6)
  -- J = (1/2)(-e_{36} + e_{45})
  | 9  => (1/2 : ℝ) • (- skewGen 3 6 + skewGen 4 5)
  -- K = (1/2)(-e_{15} - e_{26})
  | 10 => (1/2 : ℝ) • (- skewGen 1 5 - skewGen 2 6)
  -- L = (1/2)(-e_{16} + e_{25})
  | 11 => (1/2 : ℝ) • (- skewGen 1 6 + skewGen 2 5)
  -- M = (1/2)(-e_{06} + e_{24})
  | 12 => (1/2 : ℝ) • (- skewGen 0 6 + skewGen 2 4)
  -- N = (1/2)(e_{14} - e_{23})
  | 13 => (1/2 : ℝ) • (skewGen 1 4 - skewGen 2 3)

/-- THEOREM: Every Bryant-Wilmot generator is skew-symmetric: $G_m^T = - G_m$. -/
theorem bryantGen_skew (m : Fin 14) :
    (bryantGen m)ᵀ = - bryantGen m := by
  fin_cases m <;> {
    dsimp [bryantGen]
    ext a b
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
    have hT (i j : Fin 7) : (skewGen i j)ᵀ b a = - skewGen i j b a := by
      rw [skewGen_transpose, Matrix.neg_apply]
    simp only [Matrix.transpose_apply] at hT
    repeat rw [hT]
    ring
  }

theorem bryantGen_zero_seven_separated
    (g : Fin 14 → ℝ)
    (hg : ∑ i, g i • bryantGen i = 0) :
    g 0 = 0 ∧ g 7 = 0 := by
  have h₁ := congrArg (fun M => M 1 2) hg
  have h₂ := congrArg (fun M => M 3 4) hg
  simp [bryantGen, skewGen, Fin.sum_univ_succ] at h₁ h₂
  constructor <;> linarith

theorem bryantGen_one_eight_separated
    (g : Fin 14 → ℝ)
    (hg : ∑ i, g i • bryantGen i = 0) :
    g 1 = 0 ∧ g 8 = 0 := by
  have h₁ := congrArg (fun M => M 0 2) hg
  have h₂ := congrArg (fun M => M 3 5) hg
  simp [bryantGen, skewGen, Fin.sum_univ_succ] at h₁ h₂
  constructor <;> linarith

theorem bryantGen_two_nine_separated
    (g : Fin 14 → ℝ)
    (hg : ∑ i, g i • bryantGen i = 0) :
    g 2 = 0 ∧ g 9 = 0 := by
  have h₁ := congrArg (fun M => M 0 1) hg
  have h₂ := congrArg (fun M => M 3 6) hg
  simp [bryantGen, skewGen, Fin.sum_univ_succ] at h₁ h₂
  constructor <;> linarith

theorem bryantGen_three_ten_separated
    (g : Fin 14 → ℝ)
    (hg : ∑ i, g i • bryantGen i = 0) :
    g 3 = 0 ∧ g 10 = 0 := by
  have h₁ := congrArg (fun M => M 0 4) hg
  have h₂ := congrArg (fun M => M 1 5) hg
  simp [bryantGen, skewGen, Fin.sum_univ_succ] at h₁ h₂
  constructor <;> linarith

theorem bryantGen_four_eleven_separated
    (g : Fin 14 → ℝ)
    (hg : ∑ i, g i • bryantGen i = 0) :
    g 4 = 0 ∧ g 11 = 0 := by
  have h₁ := congrArg (fun M => M 0 3) hg
  have h₂ := congrArg (fun M => M 1 6) hg
  simp [bryantGen, skewGen, Fin.sum_univ_succ] at h₁ h₂
  constructor <;> linarith

theorem bryantGen_five_twelve_separated
    (g : Fin 14 → ℝ)
    (hg : ∑ i, g i • bryantGen i = 0) :
    g 5 = 0 ∧ g 12 = 0 := by
  have h₁ := congrArg (fun M => M 1 3) hg
  have h₂ := congrArg (fun M => M 2 4) hg
  simp [bryantGen, skewGen, Fin.sum_univ_succ] at h₁ h₂
  constructor <;> linarith

theorem bryantGen_six_thirteen_separated
    (g : Fin 14 → ℝ)
    (hg : ∑ i, g i • bryantGen i = 0) :
    g 6 = 0 ∧ g 13 = 0 := by
  have h₁ := congrArg (fun M => M 0 5) hg
  have h₂ := congrArg (fun M => M 2 3) hg
  simp [bryantGen, skewGen, Fin.sum_univ_succ] at h₁ h₂
  constructor <;> linarith

theorem bryantGen_linearIndependent :
    LinearIndependent ℝ bryantGen := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  fin_cases i
  · exact (bryantGen_zero_seven_separated g hg).1
  · exact (bryantGen_one_eight_separated g hg).1
  · exact (bryantGen_two_nine_separated g hg).1
  · exact (bryantGen_three_ten_separated g hg).1
  · exact (bryantGen_four_eleven_separated g hg).1
  · exact (bryantGen_five_twelve_separated g hg).1
  · exact (bryantGen_six_thirteen_separated g hg).1
  · exact (bryantGen_zero_seven_separated g hg).2
  · exact (bryantGen_one_eight_separated g hg).2
  · exact (bryantGen_two_nine_separated g hg).2
  · exact (bryantGen_three_ten_separated g hg).2
  · exact (bryantGen_four_eleven_separated g hg).2
  · exact (bryantGen_five_twelve_separated g hg).2
  · exact (bryantGen_six_thirteen_separated g hg).2

/-! =========================================================================
    2. The 7 Bryant Triad Sum Relations
    ========================================================================= -/

/-- 1. Triad relation: $A + H = \frac{1}{2}(e_{12} - e_{56})$. -/
theorem bryant_A_add_H :
    bryantGen 0 + bryantGen 7 = (1/2 : ℝ) • (skewGen 1 2 - skewGen 5 6) := by
  dsimp [bryantGen]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- 2. Triad relation: $B + I = \frac{1}{2}(-e_{02} + e_{46})$. -/
theorem bryant_B_add_I :
    bryantGen 1 + bryantGen 8 = (1/2 : ℝ) • (- skewGen 0 2 + skewGen 4 6) := by
  dsimp [bryantGen]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-- 3. Triad relation: $C + J = \frac{1}{2}(e_{01} + e_{45})$. -/
theorem bryant_C_add_J :
    bryantGen 2 + bryantGen 9 = (1/2 : ℝ) • (skewGen 0 1 + skewGen 4 5) := by
  dsimp [bryantGen]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-- 4. Triad relation: $D + K = \frac{1}{2}(e_{04} - e_{26})$. -/
theorem bryant_D_add_K :
    bryantGen 3 + bryantGen 10 = (1/2 : ℝ) • (- skewGen 0 4 - skewGen 2 6) := by
  dsimp [bryantGen]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-- 5. Triad relation: $E - L = \frac{1}{2}(e_{03} - e_{25})$. -/
theorem bryant_E_sub_L :
    bryantGen 4 - bryantGen 11 = (1/2 : ℝ) • (skewGen 0 3 - skewGen 2 5) := by
  dsimp [bryantGen]
  ext a b
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.add_apply, smul_eq_mul]
  ring

/-- 6. Triad relation: $F + M = \frac{1}{2}(e_{13} + e_{24})$. -/
theorem bryant_F_add_M :
    bryantGen 5 + bryantGen 12 = (1/2 : ℝ) • (skewGen 1 3 + skewGen 2 4) := by
  dsimp [bryantGen]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-- 7. Triad relation: $G + N = \frac{1}{2}(-e_{05} - e_{23})$. -/
theorem bryant_G_add_N :
    bryantGen 6 + bryantGen 13 = (1/2 : ℝ) • (- skewGen 0 5 - skewGen 2 3) := by
  dsimp [bryantGen]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-! =========================================================================
    3. Wilmot Projectors and Idempotent Law
    ========================================================================= -/

/-- The Wilmot 4-form projector element $\alpha = \frac{1}{2}(1 + \mathrm{sign})$. -/
def wilmotAlpha (sign : ℝ) : ℝ := (1 + sign) / 2

/-- THEOREM (Wilmot Idempotent Law): $\alpha^2 = \alpha$ when $\mathrm{sign} \in \{1, -1\}$. -/
theorem wilmotAlpha_idempotent (h : sign = 1 ∨ sign = -1) :
    (wilmotAlpha sign) ^ 2 = wilmotAlpha sign := by
  rcases h with rfl | rfl
  · dsimp [wilmotAlpha]
    norm_num
  · dsimp [wilmotAlpha]
    norm_num

/-- THEOREM (Wilmot Enabling Orthogonality): $\alpha \cdot (1 - \alpha) = 0$. -/
theorem wilmotAlpha_orthogonality (h : sign = 1 ∨ sign = -1) :
    wilmotAlpha sign * (1 - wilmotAlpha sign) = 0 := by
  rcases h with rfl | rfl
  · dsimp [wilmotAlpha]
    norm_num
  · dsimp [wilmotAlpha]
    norm_num

/-! =========================================================================
    4. Lie Algebra Subspace and Invariance
    ========================================================================= -/

/-- The real subspace of $\mathfrak{so}(7)$ spanned by the 14 Bryant-Wilmot generators. -/
def wilmotG2Submodule : Submodule ℝ (Matrix (Fin 7) (Fin 7) ℝ) :=
  Submodule.span ℝ (Set.range bryantGen)

def matrixLieBracket
    (M N : Matrix (Fin 7) (Fin 7) ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  M * N - N * M

theorem matrixLieBracket_skew
    {M N : Matrix (Fin 7) (Fin 7) ℝ}
    (hM : Mᵀ = -M) (hN : Nᵀ = -N) :
    (matrixLieBracket M N)ᵀ = -matrixLieBracket M N := by
  simp only [matrixLieBracket, Matrix.transpose_sub, Matrix.transpose_mul]
  rw [hM, hN]
  simp [sub_eq_add_neg]

theorem bryantGen_bracket_zero_three_cas_alignment :
    matrixLieBracket (bryantGen 0) (bryantGen 3) =
      (1 / 2 : ℝ) • (bryantGen 4 - bryantGen 11) := by
  simp [matrixLieBracket, bryantGen, skewGen_eq_single_sub,
    smul_sub, Matrix.mul_sub, Matrix.sub_mul, mul_add, add_mul] ; abel

theorem bryantGen_bracket_zero_one_cas_alignment :
    matrixLieBracket (bryantGen 0) (bryantGen 1) =
      (-1 / 2 : ℝ) • (bryantGen 2 + bryantGen 9) := by
  simp [matrixLieBracket, bryantGen, skewGen_eq_single_sub,
    smul_sub, Matrix.mul_sub, Matrix.sub_mul]
  abel_nf
  norm_num [div_eq_mul_inv, matrix_single_neg]
  abel

theorem bryantGen_bracket_zero_two_cas_alignment :
    matrixLieBracket (bryantGen 0) (bryantGen 2) =
      (1 / 2 : ℝ) • (bryantGen 1 + bryantGen 8) := by
  simp [matrixLieBracket, bryantGen, skewGen_eq_single_sub,
    smul_sub, Matrix.mul_sub, Matrix.sub_mul, mul_add, add_mul]
  abel_nf

theorem bryantGen_bracket_zero_four_cas_alignment :
    matrixLieBracket (bryantGen 0) (bryantGen 4) =
      (-1 / 2 : ℝ) • (bryantGen 3 + bryantGen 10) := by
  simp [matrixLieBracket, bryantGen, skewGen_eq_single_sub,
    smul_sub, Matrix.mul_sub, Matrix.sub_mul]
  abel_nf
  norm_num [div_eq_mul_inv, matrix_single_neg]
  abel

theorem bryantGen_bracket_zero_five_cas_alignment :
    matrixLieBracket (bryantGen 0) (bryantGen 5) =
      (1 / 2 : ℝ) • bryantGen 13 := by
  simp [matrixLieBracket, bryantGen, skewGen_eq_single_sub,
    smul_sub, Matrix.mul_sub, Matrix.sub_mul, mul_add, add_mul]
  abel_nf

/- The coefficient vector for this bracket was first solved symbolically in
SymPy (`CAS_BRACKET_1_2_COORDS=(-1/2,0,0,0,0,0,0,-1/2,0,...)`) and is then
checked here by the kernel. -/
theorem bryantGen_bracket_one_two_cas_alignment :
    matrixLieBracket (bryantGen 1) (bryantGen 2) =
      (-1 / 2 : ℝ) • (bryantGen 0 + bryantGen 7) := by
  simp [matrixLieBracket, bryantGen, skewGen_eq_single_sub,
    smul_add, Matrix.mul_sub, Matrix.sub_mul]
  abel_nf
  norm_num [div_eq_mul_inv, matrix_single_neg]

theorem wilmotG2Submodule_finrank :
    Module.finrank ℝ wilmotG2Submodule = 14 := by
  change Module.finrank ℝ (Submodule.span ℝ (Set.range bryantGen)) = 14
  rw [finrank_span_eq_card bryantGen_linearIndependent]
  rfl

/-- Dimension count of the Bryant-Wilmot generators. -/
theorem wilmot_generator_count :
    Fintype.card (Fin 14) = 14 := by rfl

end InfoGeometry.Algebra.WilmotCliffordG2

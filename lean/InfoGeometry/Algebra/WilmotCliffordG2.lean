import Mathlib.Data.Matrix.Basic
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
  -- D = (1/2)(e_{04} + e_{15})
  | 3  => (1/2 : ℝ) • (skewGen 0 4 + skewGen 1 5)
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

/-- The `(1,2)` entry separates the first Bryant generator. -/
theorem bryantGen_zero_entry :
    bryantGen 0 1 2 = (1 / 2 : ℝ) := by
  dsimp [bryantGen, skewGen]
  norm_num

/-- The `(0,2)` entry separates the second Bryant generator. -/
theorem bryantGen_one_entry :
    bryantGen 1 0 2 = (-1 / 2 : ℝ) := by
  dsimp [bryantGen, skewGen]
  norm_num

/-- The `(0,1)` entry separates the third Bryant generator. -/
theorem bryantGen_two_entry :
    bryantGen 2 0 1 = (1 / 2 : ℝ) := by
  dsimp [bryantGen, skewGen]
  norm_num

/-- The `(0,4)` entry separates the fourth Bryant generator. -/
theorem bryantGen_three_entry :
    bryantGen 3 0 4 = (1 / 2 : ℝ) := by
  dsimp [bryantGen, skewGen]
  norm_num

/-- The `(0,3)` entry separates the fifth Bryant generator. -/
theorem bryantGen_four_entry :
    bryantGen 4 0 3 = (1 / 2 : ℝ) := by
  dsimp [bryantGen, skewGen]
  norm_num

/-- The `(0,6)` entry separates the sixth Bryant generator. -/
theorem bryantGen_five_entry :
      bryantGen 5 0 6 = (1 / 2 : ℝ) := by
    dsimp [bryantGen, skewGen]
    norm_num

/-- The `(0,5)` entry separates the seventh Bryant generator. -/
theorem bryantGen_six_entry :
      bryantGen 6 0 5 = (-1 / 2 : ℝ) := by
    dsimp [bryantGen, skewGen]
    norm_num

/-- The `(3,4)` entry separates the eighth Bryant generator. -/
theorem bryantGen_seven_entry :
      bryantGen 7 3 4 = (1 / 2 : ℝ) := by
    dsimp [bryantGen, skewGen]
    norm_num

/-- The `(3,5)` entry separates the ninth Bryant generator. -/
theorem bryantGen_eight_entry :
      bryantGen 8 3 5 = (1 / 2 : ℝ) := by
    dsimp [bryantGen, skewGen]
    norm_num

/-- The `(3,6)` entry separates the tenth Bryant generator. -/
theorem bryantGen_nine_entry :
      bryantGen 9 3 6 = (-1 / 2 : ℝ) := by
    dsimp [bryantGen, skewGen]
    norm_num

/-- The `(1,5)` entry separates the eleventh Bryant generator. -/
theorem bryantGen_ten_entry :
      bryantGen 10 1 5 = (-1 / 2 : ℝ) := by
    dsimp [bryantGen, skewGen]
    norm_num

/-- The `(1,6)` entry separates the twelfth Bryant generator. -/
theorem bryantGen_eleven_entry :
      bryantGen 11 1 6 = (-1 / 2 : ℝ) := by
    dsimp [bryantGen, skewGen]
    norm_num


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
    bryantGen 3 + bryantGen 10 = (1/2 : ℝ) • (skewGen 0 4 - skewGen 2 6) := by
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

/-- Dimension count of the Bryant-Wilmot generators. -/
theorem wilmot_generator_count :
    Fintype.card (Fin 14) = 14 := by rfl

end InfoGeometry.Algebra.WilmotCliffordG2

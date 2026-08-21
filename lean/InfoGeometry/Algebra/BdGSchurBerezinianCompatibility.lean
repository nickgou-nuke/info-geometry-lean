import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# BdG Schur Complement, Berezinian Compatibility, and Scalar Zorn Norm

This module formalizes the exact algebraic relations connecting:
1. **Associative Supermatrix Berezinian**:
   $$\operatorname{Ber}\begin{pmatrix} A & B \\ C & D \end{pmatrix} = \frac{\det(A - B D^{-1} C)}{\det D}$$
2. **Scalar (1|1) Specialization**:
   For scalar blocks $Z = \begin{pmatrix} \alpha & u \\ v & \beta \end{pmatrix}$ with $\beta \neq 0$:
   $$\operatorname{Schur}(\alpha, \beta, u, v) = \alpha - u \beta^{-1} v = \frac{\alpha\beta - uv}{\beta} = \frac{N(Z)}{\beta}$$
   $$\operatorname{Ber}(Z) = \frac{\operatorname{Schur}(Z)}{\beta} = \frac{\det Z}{\beta^2} = \frac{N(Z)}{\beta^2}$$
3. **Reconstruction of the Composition Norm**:
   $$N(Z) = \operatorname{Schur}(Z) \cdot \beta$$

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

open Matrix

noncomputable section

namespace InfoGeometry.Algebra.BdGSchurBerezinianCompatibility

variable {F : Type*} [Field F]

/-- Associative 2x2 scalar block supermatrix -/
def superMatrix (A B C D : F) : Matrix (Fin 2) (Fin 2) F :=
  !![A, B; C, D]

/-- Associative scalar Schur complement: A - B D⁻¹ C -/
def schurComplement (A B C D : F) : F :=
  A - B * D⁻¹ * C

/-- Graded Berezinian: Ber(M) = det(A - B D⁻¹ C) / det(D) = (A - B D⁻¹ C) / D -/
def berezinian (A B C D : F) : F :=
  (schurComplement A B C D) / D

/-- Scalar Zorn composition norm shadow N(Z) = α β - u v -/
def zornNormScalar (α β u v : F) : F :=
  α * β - u * v

/-- 
  🏆 THEOREM 1: The Berezinian equals the determinant divided by D²:
  Ber(M) = (A D - B C) / D² = det(M) / D².
-/
theorem berezinian_eq_det_div_sq (A B C D : F) (hD : D ≠ 0) :
    berezinian A B C D = (Matrix.det (superMatrix A B C D)) / (D^2) := by
  dsimp [berezinian, schurComplement, superMatrix]
  rw [Matrix.det_fin_two]
  dsimp
  have : (A - B * D⁻¹ * C) / D = (A * D - B * (D⁻¹ * D) * C) / D^2 := by
    calc
      (A - B * D⁻¹ * C) / D = ((A - B * D⁻¹ * C) * D) / (D * D) := by
        rw [mul_div_mul_right (A - B * D⁻¹ * C) D hD]
      _ = (A * D - B * (D⁻¹ * D) * C) / D^2 := by
        congr 1 <;> ring
  rw [this, inv_mul_cancel₀ hD, mul_one]

/-- 
  🏆 THEOREM 2: The scalar Schur complement is the Zorn norm divided by the pivot β:
  Schur(α, β, u, v) = N(Z) / β.
-/
theorem schur_eq_zornNorm_div_beta (α β u v : F) (hβ : β ≠ 0) :
    schurComplement α u v β = zornNormScalar α β u v / β := by
  dsimp [schurComplement, zornNormScalar]
  field_simp [hβ]
  ring

/-- 
  🏆 THEOREM 3: The scalar Zorn norm reconstructs from the Schur complement times the pivot β:
  N(Z) = Schur(Z) · β.
-/
theorem zornNorm_eq_schur_mul_beta (α β u v : F) (hβ : β ≠ 0) :
    zornNormScalar α β u v = (schurComplement α u v β) * β := by
  rw [schur_eq_zornNorm_div_beta α β u v hβ]
  exact (div_mul_cancel₀ (zornNormScalar α β u v) hβ).symm

/-- 
  🏆 THEOREM 4: The Berezinian equals the scalar Zorn norm divided by the squared pivot:
  Ber(Z) = N(Z) / β².
-/
theorem berezinian_eq_zornNorm_div_sq (α β u v : F) (hβ : β ≠ 0) :
    berezinian α u v β = zornNormScalar α β u v / (β^2) := by
  rw [berezinian_eq_det_div_sq α u v β hβ]
  dsimp [superMatrix, zornNormScalar]
  rw [Matrix.det_fin_two]
  dsimp

end InfoGeometry.Algebra.BdGSchurBerezinianCompatibility

end noncomputable section

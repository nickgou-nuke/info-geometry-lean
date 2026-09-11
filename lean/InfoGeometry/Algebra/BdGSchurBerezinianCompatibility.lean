import Mathlib.Algebra.Field.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace InfoGeometry.Algebra.BdGSchurBerezinianCompatibility

variable {F : Type*} [Field F]

def blockMatrix (α β u v : F) : Matrix (Fin 2) (Fin 2) F :=
  !![α, u; v, β]

def schurComplement (α β u v : F) : F :=
  α - u * β⁻¹ * v

def berezinianScalar (α β u v : F) : F :=
  schurComplement α β u v / β

def zornNorm (α β u v : F) : F :=
  α * β - u * v

@[simp] theorem det_blockMatrix (α β u v : F) :
    Matrix.det (blockMatrix α β u v) = zornNorm α β u v := by
  simp [blockMatrix, zornNorm, Matrix.det_fin_two]

theorem schur_scalar_eq_zorn_norm_div_beta
    (α β u v : F) (hβ : β ≠ 0) :
    schurComplement α β u v = zornNorm α β u v / β := by
  unfold schurComplement zornNorm
  field_simp [hβ]

theorem berezinian_scalar_eq_zorn_norm_div_sq
    (α β u v : F) (hβ : β ≠ 0) :
    berezinianScalar α β u v = zornNorm α β u v / β ^ 2 := by
  unfold berezinianScalar
  rw [schur_scalar_eq_zorn_norm_div_beta α β u v hβ]
  field_simp [hβ]

theorem zorn_norm_from_schur
    (α β u v : F) (hβ : β ≠ 0) :
    zornNorm α β u v = schurComplement α β u v * β := by
  rw [schur_scalar_eq_zorn_norm_div_beta α β u v hβ]
  exact (div_mul_cancel₀ (zornNorm α β u v) hβ).symm

end InfoGeometry.Algebra.BdGSchurBerezinianCompatibility

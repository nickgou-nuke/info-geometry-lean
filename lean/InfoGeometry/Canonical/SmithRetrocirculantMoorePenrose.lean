import Mathlib.Tactic

/-!
# Moore--Penrose inverse of a retrocirculant

Theorem-safe Lean scaffold for Ronald L. Smith,
"The Moore-Penrose Inverse of a Retrocirculant", Linear Algebra Appl. 22,
1--8 (1978).

Smith proves that a retrocirculant `A = P C`, where `P` is a Fourier-commuting
involutory permutation matrix and `C` is circulant, has Moore--Penrose inverse
`A⁺ = C⁺ Pᵀ`; moreover `A⁺` is again retrocirculant and the nonzero eigenvalues
are reciprocals.  The analytic/unitary Fourier layer is kept as explicit
certificates.  A concrete exact `2 × 2` Penrose calculation is proved directly.
-/

namespace InfoGeometry.Canonical.SmithRetrocirculantMoorePenrose

noncomputable section

universe u

/-- Algebraic doubly-sided Penrose equations without conjugation.  This is the
finite exact-rational form used by the CAS witnesses; the complex/unitary
Moore--Penrose interpretation is supplied by owner certificates below. -/
def AlgebraicMoorePenrosePair {K : Type u} [Field K] {n : ℕ}
    (A Aplus : Matrix (Fin n) (Fin n) K) : Prop :=
  A * Aplus * A = A ∧
    Aplus * A * Aplus = Aplus ∧
      Matrix.transpose (A * Aplus) = A * Aplus ∧
        Matrix.transpose (Aplus * A) = Aplus * A

/-- The `2 × 2` retrocirculant block `P * diag(a,b)`. -/
def retro2 {K : Type u} [Zero K] (a b : K) : Matrix (Fin 2) (Fin 2) K :=
  !![0, b; a, 0]

/-- Its inverse/Penrose inverse when `a` and `b` are nonzero. -/
def retro2Plus {K : Type u} [DivisionSemiring K] (a b : K) : Matrix (Fin 2) (Fin 2) K :=
  !![0, a⁻¹; b⁻¹, 0]

/-- Exact Penrose equations for the nonzero `2 × 2` retrocirculant block. -/
theorem retro2_penrose {K : Type u} [Field K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    AlgebraicMoorePenrosePair (retro2 a b) (retro2Plus a b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [retro2, retro2Plus, Matrix.mul_apply, ha, hb]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [retro2, retro2Plus, Matrix.mul_apply, ha, hb]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [retro2, retro2Plus, Matrix.mul_apply, ha, hb]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [retro2, retro2Plus, Matrix.mul_apply, ha, hb]

/-- Smith retrocirculant data: `A = P C`, with Fourier-commutation and
circulant status left as explicit predicates owned by the spectral layer. -/
def RetrocirculantData (K : Type u) [Field K] {n : ℕ}
    (A P C : Matrix (Fin n) (Fin n) K) : Prop := A = P * C

namespace RetrocirculantData

variable {K : Type u} [Field K] {n : ℕ}
variable {A P C : Matrix (Fin n) (Fin n) K}

/-- Read out Smith's definition of a retrocirculant. -/
theorem as_product (R : RetrocirculantData K A P C) : A = P * C := R

end RetrocirculantData

/-- Certificate for Smith Theorem 1: `A = P C` is retrocirculant iff `A⁺` is
retrocirculant, and in that case `A⁺ = C⁺ Pᵀ`. -/
def SmithMoorePenroseRetrocirculantData
    (K : Type u) [Field K] {n : ℕ}
    (A Aplus P C Cplus : Matrix (Fin n) (Fin n) K) : Prop :=
  RetrocirculantData K A P C ∧
    AlgebraicMoorePenrosePair C Cplus ∧
      AlgebraicMoorePenrosePair A Aplus ∧
        Aplus = Cplus * Matrix.transpose P ∧
          RetrocirculantData K Aplus (Matrix.transpose P) Cplus

namespace SmithMoorePenroseRetrocirculantData

variable {K : Type u} [Field K] {n : ℕ}
variable {A Aplus P C Cplus : Matrix (Fin n) (Fin n) K}

/-- Smith's Moore--Penrose inverse formula. -/
theorem moorePenrose_formula
    (S : SmithMoorePenroseRetrocirculantData K A Aplus P C Cplus) :
    Aplus = Cplus * Matrix.transpose P := by
    exact S.2.2.2.1

/-- Smith's retrocirculant closure readout for the Moore--Penrose inverse. -/
theorem plus_is_retrocirculant
    (S : SmithMoorePenroseRetrocirculantData K A Aplus P C Cplus) :
    RetrocirculantData K Aplus (Matrix.transpose P) Cplus := S.2.2.2.2

end SmithMoorePenroseRetrocirculantData

end

end InfoGeometry.Canonical.SmithRetrocirculantMoorePenrose

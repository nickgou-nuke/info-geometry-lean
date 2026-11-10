import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Section 52 / Supergeometry: 2×2 Super-LU Berezinian Factorization & Orthogonal Balance
Target: `InfoGeometry/Supergeometry/BerezinianDecomposition.lean`

Formalizes finite 2×2 matrix identities over a commutative ring `R`:
1. Matrix Carrier & Regularity:
   - Carrier: M ∈ Matrix (Fin 2) (Fin 2) R
   - Regularity of denominator block: M₁₁ · invD = 1
2. The Berezinian Superdeterminant Operator:
   - Ber(M) = (M₀₀ - M₀₁ · invD · M₁₀) · invD
3. The Super-LU Trifactor Matrix Decomposition:
   - L(M) = !![1, M₀₁ · invD; 0, 1]
   - H(M) = !![M₀₀ - M₀₁ · invD · M₁₀, 0; 0, M₁₁]
   - R(M) = !![1, 0; invD · M₁₀, 1]
   - Exact factorization theorem: L(M) * H(M) * R(M) = M.
4. Unipotent Triangular Supermatrix Factorization:
   - Ber(L(x)) = 1, Ber(R(y)) = 1
   - Unipotent shear composition: L(x) * L(y) = L(x + y).
5. Diagonal Berezinian Evaluation:
   - Ber(diag(a, d)) = a · invD.
6. The Berezinian Scaling Invariance Law:
   - For balanced (1|1) superspace: Ber(c • M) = Ber(M).
7. Orthogonal Superstructures (OSp Balance):
   - When fermionic cross-coupling vanishes (M₀₁ = 0), Ber(M) = M₀₀ · invD.
-/

namespace InfoGeometry.Supergeometry.Berezinian

open Matrix

variable {R : Type*} [Ring R]

/-- The first diagonal matrix unit. -/
def matrixE00 : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, 0]

/-- The upper off-diagonal matrix unit. -/
def matrixE01 : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]

/-- The 2×2 matrix carrier is noncommutative when its coefficient ring is nontrivial. -/
theorem matrix_algebra_noncommutative [Nontrivial R] :
    matrixE00 (R := R) * matrixE01 (R := R) ≠
      matrixE01 (R := R) * matrixE00 (R := R) := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 1) h
  simp [matrixE00, matrixE01, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-! ### 1. Matrix Carrier and Regularity -/

/-! ### 2. The Berezinian Superdeterminant Operator -/

/-- The Berezinian superdeterminant via Schur complement operator contraction:
    Ber(M) = (M₀₀ - M₀₁ · invD · M₁₀) · invD. -/
def berezinian (M : Matrix (Fin 2) (Fin 2) R) (invD : R) : R :=
  (M 0 0 - M 0 1 * invD * M 1 0) * invD

/-- Scalar expansion used by the balanced Berezinian scaling law. -/
private theorem balancedScaling_expand {R : Type*} [CommRing R]
    (a b d invD c inv_c : R) :
    (c * a - c * b * (inv_c * invD) * (c * d)) * (inv_c * invD) =
      (c * inv_c) * (a * invD) - (c * inv_c)^2 * (b * invD * d * invD) := by
  ring

/-- Scalar contraction used after the inverse-scaling hypothesis is applied. -/
private theorem balancedScaling_contract
    (a b d invD : R) :
    1 * (a * invD) - 1^2 * (b * invD * d * invD) =
      (a - b * invD * d) * invD := by
  noncomm_ring

/-! ### 3. The Super-LU Trifactor Matrix Decomposition -/

/-- Upper unipotent triangular matrix factor L. -/
def factorL (M : Matrix (Fin 2) (Fin 2) R) (invD : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, M 0 1 * invD; 0, 1]

/-- Diagonal Schur complement matrix factor H. -/
def factorH (M : Matrix (Fin 2) (Fin 2) R) (invD : R) : Matrix (Fin 2) (Fin 2) R :=
  !![M 0 0 - M 0 1 * invD * M 1 0, 0; 0, M 1 1]

/-- Lower unipotent triangular matrix factor R. -/
def factorR (M : Matrix (Fin 2) (Fin 2) R) (invD : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; invD * M 1 0, 1]

/-- Exact Super-LU Trifactor Matrix Factorization Theorem:
    L(M) * H(M) * R(M) = M on all 2x2 matrix operators. -/
theorem super_lu_factorization {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (invD : R) (hD : M 1 1 * invD = 1) :
    factorL M invD * factorH M invD * factorR M invD = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [factorL, factorH, factorR, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination M 0 1 * invD * M 1 0 * hD
  · linear_combination M 0 1 * hD
  · linear_combination M 1 0 * hD

/-! ### 4. Unipotent Triangular Factors -/

/-- Upper unipotent factor has Berezinian 1. -/
theorem unipotent_L_berezinian (x : R) :
    berezinian (!![1, x; 0, 1]) 1 = 1 := by
  dsimp [berezinian]
  noncomm_ring

/-- Lower unipotent factor has Berezinian 1. -/
theorem unipotent_R_berezinian (y : R) :
    berezinian (!![1, 0; y, 1]) 1 = 1 := by
  dsimp [berezinian]
  noncomm_ring

/-- Unipotent group multiplication law: L(x) * L(y) = L(x + y). -/
theorem unipotent_group_mul (x y : R) :
    (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) R) * !![1, y; 0, 1] = !![1, x + y; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  )

/-! ### 5. Diagonal Berezinian Evaluation -/

/-- Diagonal supermatrix Berezinian reduces to a · invD. -/
theorem diagonal_berezinian (a d invD : R) :
    berezinian (!![a, 0; 0, d]) invD = a * invD := by
  dsimp [berezinian]
  noncomm_ring

/-! ### 6. Berezinian Scaling Invariance Law -/

/-- Berezinian Scaling Invariance for balanced (1|1) superspace:
    Scaling the matrix operator M by c leaves the Berezinian invariant: Ber(c • M) = Ber(M). -/
theorem berezinian_scaling_balanced {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R)
    (invD : R)
    (c inv_c : R)
    (hc : c * inv_c = 1) :
    berezinian (c • M) (inv_c * invD) = berezinian M invD := by
  unfold berezinian
  simp only [Matrix.smul_apply, smul_eq_mul]
  calc
    (c * M 0 0 - c * M 0 1 * (inv_c * invD) * (c * M 1 0)) * (inv_c * invD)
      = (c * inv_c) * (M 0 0 * invD) - (c * inv_c)^2 * (M 0 1 * invD * M 1 0 * invD) := by
        exact balancedScaling_expand _ _ _ _ _ _
    _ = 1 * (M 0 0 * invD) - 1^2 * (M 0 1 * invD * M 1 0 * invD) := by
        rw [hc]
    _ = (M 0 0 - M 0 1 * invD * M 1 0) * invD := by
        exact balancedScaling_contract _ _ _ _

/-! ### 7. Orthogonal Superstructures (OSp Balance) -/

/-- Under super-orthogonal balance (M₀₁ = 0), the Berezinian reduces strictly to M₀₀ · invD. -/
theorem berezinian_of_orthogonal
    (M : Matrix (Fin 2) (Fin 2) R)
    (invD : R)
    (h_orth : M 0 1 = 0) :
    berezinian M invD = M 0 0 * invD := by
  dsimp [berezinian]
  rw [h_orth]
  noncomm_ring

end InfoGeometry.Supergeometry.Berezinian

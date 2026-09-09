import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Stratum 36: Doubled Krein Space and Fundamental Cartan Symmetry η

This module formalizes the indefinite Krein space geometry and split Peirce grading
governing the doubled particle-hole space $\mathcal{K} = \mathcal{H}_+ \oplus \mathcal{H}_-$:

1. **Fundamental Symmetry η:**
   The involution $\eta = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix} = \sigma_3$ satisfies $\eta^2 = \mathbf{1}$.
2. **Split Peirce Idempotents:**
   Orthogonal projectors $P_+ = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$ and
   $P_- = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$ satisfying $P_\pm^2 = P_\pm$,
   $P_+ P_- = P_- P_+ = 0$, $P_+ + P_- = \mathbf{1}$, and $\eta = P_+ - P_-$.
3. **Cartan Involution on 2×2 Endomorphisms:**
   $\theta(X) = \eta X \eta$ decomposes matrices into even diagonal blocks ($\theta(X) = X$,
   eigenvalue $+1$) and odd off-diagonal blocks ($\theta(X) = -X$, eigenvalue $-1$).
4. **Indefinite Krein Bilinear Metric:**
   $\langle u, v \rangle_\eta = u_0 v_0 - u_1 v_1 = u \cdot (\eta v)$ with signature $(1, 1)$.
-/

namespace InfoGeometry.Canonical.KreinDoubledCartanPeirce

open Matrix

variable {R : Type*} [CommRing R]

/-- The fundamental Krein symmetry matrix η = σ₃. -/
def eta : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, -1]

/-- Positive split Peirce idempotent P_+ = (1 + η)/2. -/
def P_plus : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, 0]

/-- Negative split Peirce idempotent P_- = (1 - η)/2. -/
def P_minus : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0; 0, 1]

/-- η is an involution: η² = 1. -/
theorem eta_sq : eta (R := R) * eta = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta, mul_apply, Fin.sum_univ_two]

/-- P_+ is idempotent: P_+² = P_+. -/
theorem P_plus_sq : P_plus (R := R) * P_plus = P_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P_plus, mul_apply, Fin.sum_univ_two]

/-- P_- is idempotent: P_-² = P_-. -/
theorem P_minus_sq : P_minus (R := R) * P_minus = P_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P_minus, mul_apply, Fin.sum_univ_two]

/-- P_+ and P_- are orthogonal: P_+ P_- = 0. -/
theorem P_plus_mul_P_minus : P_plus (R := R) * P_minus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P_plus, P_minus, mul_apply, Fin.sum_univ_two]

/-- P_- and P_+ are orthogonal: P_- P_+ = 0. -/
theorem P_minus_mul_P_plus : P_minus (R := R) * P_plus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P_plus, P_minus, mul_apply, Fin.sum_univ_two]

/-- Completeness: P_+ + P_- = 1. -/
theorem P_plus_add_P_minus : P_plus (R := R) + P_minus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P_plus, P_minus]

/-- Fundamental symmetry decomposition: η = P_+ - P_-. -/
theorem eta_eq_sub : eta (R := R) = P_plus - P_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta, P_plus, P_minus]

/-- Cartan involution preserves diagonal matrices (eigenvalue +1): η X_diag η = X_diag. -/
theorem cartan_involution_diagonal (a d : R) :
    let X : Matrix (Fin 2) (Fin 2) R := !![a, 0; 0, d]
    eta * X * eta = X := by
  intro X
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta, X, mul_apply, Fin.sum_univ_two]

/-- Cartan involution inverts off-diagonal matrices (eigenvalue -1): η X_off η = -X_off. -/
theorem cartan_involution_off_diagonal (b c : R) :
    let X : Matrix (Fin 2) (Fin 2) R := !![0, b; c, 0]
    eta * X * eta = -X := by
  intro X
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta, X, mul_apply, Fin.sum_univ_two]

/-- Indefinite Krein inner product on R²: ⟨u, v⟩_η = u₀ v₀ - u₁ v₁. -/
def kreinBilinear (u v : Fin 2 → R) : R :=
  u 0 * v 0 - u 1 * v 1

/-- Matrix evaluation: ⟨u, v⟩_η = u · (η v). -/
theorem kreinBilinear_matrix_eval (u v : Fin 2 → R) :
    kreinBilinear u v = u 0 * (eta *ᵥ v) 0 + u 1 * (eta *ᵥ v) 1 := by
  simp [kreinBilinear, Matrix.mulVec, eta, Matrix.vecHead, Matrix.vecTail]
  ring

/-- Symmetry of the Krein inner product: ⟨u, v⟩_η = ⟨v, u⟩_η. -/
theorem kreinBilinear_symm (u v : Fin 2 → R) :
    kreinBilinear u v = kreinBilinear v u := by
  simp [kreinBilinear]
  ring

/-- Master synthesis packet for Stratum 36. -/
structure KreinCartanPeircePacket (R : Type*) [CommRing R] where
  eta_is_involution : eta (R := R) * eta = 1
  peirce_completeness : P_plus (R := R) + P_minus = 1
  eta_is_peirce_diff : eta (R := R) = P_plus - P_minus
  cartan_even_preserved : ∀ a d : R, eta * !![a, 0; 0, d] * eta = !![a, 0; 0, d]
  cartan_odd_inverted : ∀ b c : R, eta * !![0, b; c, 0] * eta = -!![0, b; c, 0]

/-- Zero-debt constructor for Stratum 36 packet. -/
def makeKreinCartanPeircePacket (R : Type*) [CommRing R] : KreinCartanPeircePacket R where
  eta_is_involution := eta_sq
  peirce_completeness := P_plus_add_P_minus
  eta_is_peirce_diff := eta_eq_sub
  cartan_even_preserved := cartan_involution_diagonal
  cartan_odd_inverted := cartan_involution_off_diagonal

end InfoGeometry.Canonical.KreinDoubledCartanPeirce

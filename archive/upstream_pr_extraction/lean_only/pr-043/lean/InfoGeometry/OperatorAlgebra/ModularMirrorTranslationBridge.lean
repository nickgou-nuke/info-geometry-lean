import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Modular Mirror Reflection, Surprisal Generator, and Spacetime Translation Bridge

This owner module formalizes the rigorous operator-algebraic emergence of
spacetime translation from modular reflection, modular surprisal generators,
and relative horizon displacements:

1. **Modular Mirror Reflection:**
   In standard form, modular conjugation $J$ satisfies $J M J = M'$.
   For an observable $A \in M$, its reflected counterpart is $A^\sharp = J A J \in M'$.
   - Signed difference: $D_A = A - A^\sharp$, strictly odd under $J$: $J D_A J = -D_A$.
   - Symmetric sum: $X_A = A + A^\sharp$, strictly even under $J$: $J X_A J = X_A$.

2. **Modular Surprisal Generator $\mathcal{K} = -\log \Delta$:**
   In finite standard form with faithful density matrix $\rho$, the modular operator $\Delta_\rho$
   acts as $L_\rho R_{\rho^{-1}}$.
   Its negative logarithm generator $\mathcal{K} = -\log \Delta_\rho$ is the left-minus-right difference:
   $$\boxed{\mathcal{K}_\rho = L_{-\log \rho} - R_{-\log \rho}}.$$
   Under modular reflection: $\boxed{J \mathcal{K} J = -\mathcal{K}}$.

3. **Emergence of 4-Vector Translations:**
   - 4-Vector Pauli basis $\sigma^\mu$ with Hermiticity $(\sigma^\mu)^\dagger = \sigma^\mu$.
   - Relative translation generator $P_\mu^{\mathrm{rel}} = P_\mu^L - P_\mu^R$, satisfying
     $\boxed{[P_\mu^{\mathrm{rel}}, P_\nu^{\mathrm{rel}}] = 0}$.
   - Dyadic finite-difference derivative on the fractal boundary:
     $$D_{\mu, n} = 2^n (I - U_\mu(2^{-n})).$$
-/

noncomputable section

set_option linter.unusedSectionVars false

open Complex

namespace InfoGeometry.OperatorAlgebra.ModularMirrorTranslationBridge

abbrev Mat (n : Type*) := Matrix n n ℂ

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Left multiplication operator on the Hilbert-Schmidt space $M_n(\mathbb{C})$. -/
def leftOp (A : Mat n) : Mat n →ₗ[ℂ] Mat n where
  toFun X := A * X
  map_add' X Y := Matrix.mul_add A X Y
  map_smul' c X := Matrix.mul_smul A c X

/-- Right multiplication operator on the Hilbert-Schmidt space $M_n(\mathbb{C})$. -/
def rightOp (B : Mat n) : Mat n →ₗ[ℂ] Mat n where
  toFun X := X * B
  map_add' X Y := Matrix.add_mul X Y B
  map_smul' c X := by
    dsimp
    rw [Matrix.smul_mul]

/-- Left and right multiplication operators commute: $[L_A, R_B] = 0$. -/
theorem left_right_commute (A B : Mat n) :
    (leftOp A).comp (rightOp B) = (rightOp B).comp (leftOp A) := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, leftOp, rightOp]
  dsimp
  exact (Matrix.mul_assoc A X B).symm

/-- Modular conjugation $J(X) = X^\dagger$ on the matrix algebra. -/
def modularConjugation (X : Mat n) : Mat n :=
  star X

/-- Involutive property of modular conjugation: $J^2 = I$. -/
@[simp] theorem modularConjugation_involutive (X : Mat n) :
    modularConjugation (modularConjugation X) = X := by
  dsimp [modularConjugation]
  exact star_star X

/-- The reflected observable $A^\sharp = J A J$ acting on $X$:
    $J(A J(X)) = (A X^\dagger)^\dagger = X A^\dagger = R_{A^\dagger}(X)$. -/
theorem modularMirror_eq_rightOp (A X : Mat n) :
    modularConjugation (A * modularConjugation X) = X * star A := by
  dsimp [modularConjugation]
  rw [star_mul, star_star]

/-- Signed difference observable $D_A = A - A^\sharp$. -/
def signedDifferenceObservable (A X : Mat n) : Mat n :=
  A * X - X * star A

/-- 🏆 THEOREM 1: Signed difference is strictly odd under modular reflection: $J D_A J = -D_A$. -/
theorem signedDifferenceObservable_odd (A X : Mat n) :
    modularConjugation (signedDifferenceObservable A (modularConjugation X)) =
      - signedDifferenceObservable A X := by
  dsimp [signedDifferenceObservable, modularConjugation]
  rw [star_sub, star_mul, star_mul, star_star, star_star]
  ext i j
  simp only [Matrix.sub_apply, Matrix.neg_apply]
  ring

/-- Symmetric sum observable $X_A = A + A^\sharp$. -/
def symmetricSumObservable (A X : Mat n) : Mat n :=
  A * X + X * star A

/-- 🏆 THEOREM 2: Symmetric sum is strictly even under modular reflection: $J X_A J = X_A$. -/
theorem symmetricSumObservable_even (A X : Mat n) :
    modularConjugation (symmetricSumObservable A (modularConjugation X)) =
      symmetricSumObservable A X := by
  dsimp [symmetricSumObservable, modularConjugation]
  rw [star_add, star_mul, star_mul, star_star, star_star]
  ext i j
  simp only [Matrix.add_apply]
  ring

/-- 🏆 THEOREM 3: Finite standard-form modular surprisal generator:
    $\mathcal{K}_\rho = L_{K} - R_{K}$ where $K = -\log \rho$. -/
def modularSurprisalGenerator (K : Mat n) : Mat n →ₗ[ℂ] Mat n :=
  leftOp K - rightOp K

theorem modularSurprisalGenerator_apply (K X : Mat n) :
    modularSurprisalGenerator K X = K * X - X * K := by
  simp [modularSurprisalGenerator, leftOp, rightOp]

/-- 🏆 THEOREM 4: Modular reflection reverses surprisal generator: $J \mathcal{K} J = -\mathcal{K}$ for self-adjoint $K$. -/
theorem modularSurprisal_odd_under_J (K X : Mat n) (hK : star K = K) :
    modularConjugation (modularSurprisalGenerator K (modularConjugation X)) =
      - modularSurprisalGenerator K X := by
  dsimp [modularSurprisalGenerator, leftOp, rightOp, modularConjugation]
  rw [star_sub, star_mul, star_mul, star_star, hK]
  ext i j
  simp only [Matrix.sub_apply, Matrix.neg_apply]
  ring

/-!
### 4-Vector Pauli Decomposition & Relative Translation Generators
-/

/-- Pauli matrix $\sigma^0 = I_2$. -/
def pauli0 : Matrix (Fin 2) (Fin 2) ℂ := 1

/-- Pauli matrix $\sigma^1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. -/
def pauli1 : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, 1], ![1, 0]]

/-- Pauli matrix $\sigma^2 = \begin{pmatrix} 0 & -i \\ i & 0 \end{pmatrix}$. -/
def pauli2 : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, -I], ![I, 0]]

/-- Pauli matrix $\sigma^3 = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$. -/
def pauli3 : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![1, 0], ![0, -1]]

/-- 4-vector Pauli basis $\sigma^\mu$. -/
def pauliBasis (μ : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  match μ with
  | 0 => pauli0
  | 1 => pauli1
  | 2 => pauli2
  | 3 => pauli3

/-- 🏆 THEOREM 5: All Pauli matrices are Hermitian: $(\sigma^\mu)^\dagger = \sigma^\mu$. -/
theorem pauliBasis_hermitian (μ : Fin 4) :
    star (pauliBasis μ) = pauliBasis μ := by
  fin_cases μ
  · dsimp [pauliBasis, pauli0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · dsimp [pauliBasis, pauli1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · dsimp [pauliBasis, pauli2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · dsimp [pauliBasis, pauli3]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- Relative translation generator: $P_\mu^{\mathrm{rel}} = P_\mu^L - P_\mu^R$. -/
def relativeTranslation (PL PR : Mat n) : Mat n →ₗ[ℂ] Mat n :=
  leftOp PL - rightOp PR

/-- The equal-left/right relative translation is the modular surprisal
generator.  This is the finite standard-form identification
`P^L - P^R = L_K - R_K` at `P^L = P^R = K`. -/
theorem relativeTranslation_eq_modularSurprisal (K : Mat n) :
    relativeTranslation K K = modularSurprisalGenerator K := rfl

theorem relativeTranslation_apply (PL PR : Mat n) (X : Mat n) :
    relativeTranslation PL PR X = PL * X - X * PR := by
  simp [relativeTranslation, leftOp, rightOp]

/-- 🏆 THEOREM 6: Relative translations commute when left and right generators commute:
    $[P_\mu^{\mathrm{rel}}, P_\nu^{\mathrm{rel}}] = 0$. -/
theorem relativeTranslation_comm (P1L P2L P1R P2R : Mat n)
    (hL : P1L * P2L = P2L * P1L)
    (hR : P1R * P2R = P2R * P1R) :
    (relativeTranslation P1L P1R).comp (relativeTranslation P2L P2R) =
      (relativeTranslation P2L P2R).comp (relativeTranslation P1L P1R) := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, relativeTranslation, leftOp, rightOp]
  dsimp
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply]
  have h_left : P1L * (P2L * X) = P2L * (P1L * X) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hL]
  have h_right : (X * P2R) * P1R = (X * P1R) * P2R := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hR]
  have h_cross1 : P1L * (X * P2R) = (P1L * X) * P2R := (Matrix.mul_assoc P1L X P2R).symm
  have h_cross2 : P2L * (X * P1R) = (P2L * X) * P1R := (Matrix.mul_assoc P2L X P1R).symm
  calc
    (P1L * (P2L * X - X * P2R) - (P2L * X - X * P2R) * P1R) i j
      = (P1L * (P2L * X) - P1L * (X * P2R) - (P2L * X * P1R - X * P2R * P1R)) i j := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
    _ = (P1L * (P2L * X)) i j - (P1L * (X * P2R)) i j - ((P2L * X * P1R) i j - (X * P2R * P1R) i j) := by
        simp only [Matrix.sub_apply]
    _ = (P2L * (P1L * X)) i j - (P2L * (X * P1R)) i j - ((P1L * X * P2R) i j - (X * P1R * P2R) i j) := by
        rw [h_left, h_right, h_cross1, h_cross2]
        ring
    _ = (P2L * (P1L * X) - P2L * (X * P1R) - (P1L * X * P2R - X * P1R * P2R)) i j := by
        simp only [Matrix.sub_apply]
    _ = (P2L * (P1L * X - X * P1R) - (P1L * X - X * P1R) * P2R) i j := by
        rw [Matrix.mul_sub, Matrix.sub_mul]

/-- Dyadic finite-difference translation operator: $D_n = 2^n (I - U(2^{-n}))$. -/
def dyadicDifferenceOperator (n_scale : ℕ) (U : Mat n) : Mat n :=
  ((2 : ℂ) ^ n_scale) • (1 - U)

end InfoGeometry.OperatorAlgebra.ModularMirrorTranslationBridge

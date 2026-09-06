import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Lie.SplitOctonionExteriorAlgebraPeirceBridge

set_option linter.unusedSimpArgs false

/-!
# Hestenes–Krein Bilingual State Bridge

This owner module formalizes the Hestenes–Krein bilingual reformulation of quantum states and observables
on the neutral indefinite metric space $V \oplus V^*$, replacing analytical extensions with exact finite algebraic geometry:

1. **Neutral Krein Metric / Exchange Involution Matrix:**
   $$\eta_W = \kappa_{\rm exch} = \begin{pmatrix} 0 & I_4 \\ I_4 & 0 \end{pmatrix}$$

2. **Krein Bilinear Pairing:**
   $$\langle x, y \rangle_K := x^T \eta_W y$$

3. **Krein Adjoint Operation:**
   $$\boxed{A^\sharp := \eta_W A^T \eta_W}$$

4. **Krein Involutivity & Antiautomorphism:**
   $$\boxed{(A^\sharp)^\sharp = A} \qquad \text{and} \qquad \boxed{(A B)^\sharp = B^\sharp A^\sharp}$$

5. **Hestenes–Krein State Functional:**
   $$\boxed{\omega_\Omega(A) := \langle \Omega, A \Omega \rangle_K}$$
   with exact unit normalization $\omega_\Omega(I) = 1$ for any Krein-normalized vacuum vector $\langle \Omega, \Omega \rangle_K = 1$.

6. **Canonical Split Majorana Vacuum Normalization:**
   $$\boxed{\Omega_0 = \frac{1}{\sqrt{2}} (e_0 + e_4) \implies \langle \Omega_0, \Omega_0 \rangle_K = 1}$$
-/

noncomputable section

namespace InfoGeometry.Lie.HestenesKreinBilingualStateBridge

open Matrix
open InfoGeometry.Lie.SplitOctonionExteriorAlgebraPeirceBridge

abbrev Dim8 := Fin 8
abbrev Mat8 := Matrix Dim8 Dim8 ℝ
abbrev Vec8 := Dim8 → ℝ

/-- The neutral Krein metric matrix $\eta_W$. -/
def kreinMetricMat : Mat8 := exchangeInvolutionMat

theorem kreinMetricMat_sq : kreinMetricMat * kreinMetricMat = 1 :=
  exchangeInvolutionMat_sq

theorem kreinMetricMat_transpose : kreinMetricMatᵀ = kreinMetricMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The Krein bilinear pairing $\langle x, y \rangle_K = x^T \eta_W y$. -/
def kreinPairing (x y : Vec8) : ℝ :=
  dotProduct x (kreinMetricMat *ᵥ y)

/-- Krein adjoint of an endomorphism matrix $A^\sharp = \eta_W A^T \eta_W$. -/
def kreinAdjoint (A : Mat8) : Mat8 :=
  kreinMetricMat * Aᵀ * kreinMetricMat

/-- 🏆 THEOREM 1: Krein Involutivity:
    $(A^\sharp)^\sharp = A$. -/
theorem kreinAdjoint_involutive (A : Mat8) :
    kreinAdjoint (kreinAdjoint A) = A := by
  dsimp [kreinAdjoint]
  have heta_sq : kreinMetricMat * kreinMetricMat = 1 := kreinMetricMat_sq
  have heta_t : kreinMetricMatᵀ = kreinMetricMat := kreinMetricMat_transpose
  have ht : (kreinMetricMat * Aᵀ * kreinMetricMat)ᵀ = kreinMetricMat * A * kreinMetricMat := by
    calc
      (kreinMetricMat * Aᵀ * kreinMetricMat)ᵀ
        = kreinMetricMatᵀ * (kreinMetricMat * Aᵀ)ᵀ := by rw [Matrix.transpose_mul]
      _ = kreinMetricMatᵀ * ((Aᵀ)ᵀ * kreinMetricMatᵀ) := by rw [Matrix.transpose_mul]
      _ = kreinMetricMat * (A * kreinMetricMat) := by rw [heta_t, Matrix.transpose_transpose]
      _ = kreinMetricMat * A * kreinMetricMat := by rw [Matrix.mul_assoc]
  calc
    kreinMetricMat * (kreinMetricMat * Aᵀ * kreinMetricMat)ᵀ * kreinMetricMat
      = kreinMetricMat * (kreinMetricMat * A * kreinMetricMat) * kreinMetricMat := by rw [ht]
    _ = (kreinMetricMat * kreinMetricMat) * A * (kreinMetricMat * kreinMetricMat) := by
      simp only [Matrix.mul_assoc]
    _ = 1 * A * 1 := by rw [heta_sq]
    _ = A := by simp

/-- 🏆 THEOREM 2: Krein Adjoint is an Antiautomorphism:
    $(A B)^\sharp = B^\sharp A^\sharp$. -/
theorem kreinAdjoint_mul (A B : Mat8) :
    kreinAdjoint (A * B) = kreinAdjoint B * kreinAdjoint A := by
  dsimp [kreinAdjoint]
  have heta_sq : kreinMetricMat * kreinMetricMat = 1 := kreinMetricMat_sq
  calc
    kreinMetricMat * (A * B)ᵀ * kreinMetricMat
      = kreinMetricMat * (Bᵀ * Aᵀ) * kreinMetricMat := by
        rw [Matrix.transpose_mul]
    _ = kreinMetricMat * Bᵀ * 1 * Aᵀ * kreinMetricMat := by
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = kreinMetricMat * Bᵀ * (kreinMetricMat * kreinMetricMat) * Aᵀ * kreinMetricMat := by
      rw [← heta_sq]
    _ = (kreinMetricMat * Bᵀ * kreinMetricMat) * (kreinMetricMat * Aᵀ * kreinMetricMat) := by
      simp only [Matrix.mul_assoc]

/-- The Hestenes–Krein state functional $\omega_\Omega(A) = \langle \Omega, A \Omega \rangle_K$. -/
def kreinState (Omega : Vec8) (A : Mat8) : ℝ :=
  kreinPairing Omega (A *ᵥ Omega)

/-- 🏆 THEOREM 3: Linearity of the Krein State Functional:
    $\omega_\Omega(a A + b B) = a \omega_\Omega(A) + b \omega_\Omega(B)$. -/
theorem kreinState_linear (Omega : Vec8) (a b : ℝ) (A B : Mat8) :
    kreinState Omega (a • A + b • B) = a * kreinState Omega A + b * kreinState Omega B := by
  dsimp [kreinState, kreinPairing]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
             dotProduct_add, dotProduct_smul, smul_eq_mul]

/-- 🏆 THEOREM 4: Normalization of the Krein State:
    $\langle \Omega, \Omega \rangle_K = 1 \implies \omega_\Omega(I) = 1$. -/
theorem kreinState_unit (Omega : Vec8) (h_norm : kreinPairing Omega Omega = 1) :
    kreinState Omega 1 = 1 := by
  dsimp [kreinState]
  rw [Matrix.one_mulVec]
  exact h_norm

/-- Canonical normalized split Majorana vacuum vector $\Omega_0 = \frac{1}{\sqrt{2}} (e_0 + e_4)$. -/
def vacuumOmega : Vec8 :=
  ![1 / Real.sqrt 2, 0, 0, 0, 1 / Real.sqrt 2, 0, 0, 0]

/-- 🏆 THEOREM 5: Exact algebraic normalization of the canonical vacuum vector:
    $\langle \Omega_0, \Omega_0 \rangle_K = 1$. -/
theorem vacuumOmega_normalized :
    kreinPairing vacuumOmega vacuumOmega = 1 := by
  dsimp [kreinPairing, vacuumOmega, kreinMetricMat, exchangeInvolutionMat]
  simp [dotProduct, mulVec, Fin.sum_univ_eight]
  have hsq : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : (Real.sqrt 2) ≠ 0 := by positivity
  field_simp
  linarith

end InfoGeometry.Lie.HestenesKreinBilingualStateBridge

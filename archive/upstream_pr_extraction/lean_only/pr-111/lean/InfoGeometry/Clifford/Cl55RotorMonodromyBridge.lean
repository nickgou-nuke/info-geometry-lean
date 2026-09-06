import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Clifford.RotorMonodromy

open Matrix

abbrev Dim32 := Fin 32
abbrev Mat32 := Matrix Dim32 Dim32 ℝ

variable {n : ℕ}
abbrev AlgMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-! ### 1. Realification of Complex Structure via Skew Bivector (i ↦ B) -/

/-- An orthogonal complex structure on $\mathbb{R}^n$:
    $B^2 = -I$ and $B^\top = -B$. -/
structure RealComplexStructure (n : ℕ) where
  B : AlgMat n
  sq_neg_one : B * B = -1
  B_skew : Matrix.transpose B = -B

/-! ### 2. The Discrete Rotor Group Homomorphism ρ_B : ℤ → GL_n(ℝ) -/

/-- One-parameter rotor: $R_B(\theta) = \cos\theta \cdot I + \sin\theta \cdot B$. -/
def rotor (cs : RealComplexStructure n) (theta : ℝ) : AlgMat n :=
  Real.cos theta • 1 + Real.sin theta • cs.B

/-- $R_B(0) = 1$. -/
theorem rotor_zero (cs : RealComplexStructure n) : rotor cs 0 = 1 := by
  unfold rotor
  simp only [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero]

/-- **Theorem (Rotor 1-Parameter Group Law)**:
    $R_B(\theta_1 + \theta_2) = R_B(\theta_1) \cdot R_B(\theta_2)$. -/
theorem rotor_add (cs : RealComplexStructure n) (a b : ℝ) :
    rotor cs (a + b) = rotor cs a * rotor cs b := by
  unfold rotor
  rw [Real.cos_add, Real.sin_add]
  simp only [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
             one_mul, mul_one, cs.sq_neg_one, smul_neg]
  module

/-- Transpose of rotor is its inverse: $R(\theta)^\top = R(-\theta)$. -/
theorem rotor_transpose (cs : RealComplexStructure n) (theta : ℝ) :
    (rotor cs theta)ᵀ = rotor cs (-theta) := by
  unfold rotor
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, cs.B_skew]
  simp only [Real.cos_neg, Real.sin_neg, smul_neg]
  module

/-- **Theorem (Rotor Orthogonality)**:
    $R(\theta)^\top \cdot R(\theta) = 1$. -/
theorem rotor_transpose_mul_self (cs : RealComplexStructure n) (theta : ℝ) :
    (rotor cs theta)ᵀ * rotor cs theta = 1 := by
  rw [rotor_transpose, ← rotor_add]
  have h : -theta + theta = 0 := neg_add_cancel theta
  rw [h, rotor_zero]

/-- The discrete rotor map $\rho_B(m) = R_B(m \cdot \theta_0)$. -/
def discreteRotor (cs : RealComplexStructure n) (theta0 : ℝ) (m : ℤ) : AlgMat n :=
  rotor cs ((m : ℝ) * theta0)

/--
  **MASTER THEOREM (Discrete Rotor Group Law)**:
  $\rho_B(m + k) = \rho_B(m) \cdot \rho_B(k)$.
-/
theorem discreteRotor_add (cs : RealComplexStructure n) (theta0 : ℝ) (m k : ℤ) :
    discreteRotor cs theta0 (m + k) =
    discreteRotor cs theta0 m * discreteRotor cs theta0 k := by
  unfold discreteRotor
  rw [Int.cast_add, add_mul, rotor_add]

/-- Discrete rotor inverse: $\rho_B(-m) \cdot \rho_B(m) = 1$. -/
theorem discreteRotor_inv (cs : RealComplexStructure n) (theta0 : ℝ) (m : ℤ) :
    discreteRotor cs theta0 (-m) * discreteRotor cs theta0 m = 1 := by
  rw [← discreteRotor_add]
  have h : -m + m = 0 := neg_add_cancel m
  rw [h]
  unfold discreteRotor
  simp only [Int.cast_zero, zero_mul, rotor_zero]

/-! ### 3. RoPE Invariant Bilinear Pairing & Relative-Position Invariant -/

/-- Standard Euclidean inner product pairing: $\langle u, v \rangle = u^\top v$. -/
def standardPairing (u v : Fin n → ℝ) : ℝ :=
  dotProduct u v

/--
  **MASTER THEOREM (RoPE Relative-Position Invariant)**:
  For the rotor-invariant pairing, the inner product between queries at position $m$
  and keys at position $k$ depends strictly on the relative position $(k - m)$:
  $$\langle R(m\theta_0) q, R(k\theta_0) v \rangle = \langle q, R((k - m)\theta_0) v \rangle.$$
-/
theorem rope_relative_pairing_invariance
    (cs : RealComplexStructure n) (theta0 : ℝ) (m k : ℤ) (q v : Fin n → ℝ) :
    standardPairing ((discreteRotor cs theta0 m) *ᵥ q)
                    ((discreteRotor cs theta0 k) *ᵥ v) =
    standardPairing q ((discreteRotor cs theta0 (k - m)) *ᵥ v) := by
  unfold standardPairing discreteRotor
  rw [← Matrix.vecMul_transpose]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_vecMul]
  rw [← Matrix.dotProduct_mulVec]
  rw [rotor_transpose, ← rotor_add]
  have h : -((m : ℝ) * theta0) + (k : ℝ) * theta0 = ((k - m : ℤ) : ℝ) * theta0 := by
    push_cast; ring
  rw [h]

/-! ## Master Synthesis -/

/--
🏆 **GRAND SYNTHESIS THEOREM: Rotor Monodromy & Relative-Position Invariant**

Unifies:
1. Rotor 1-parameter group law $R_B(\theta_1 + \theta_2) = R_B(\theta_1) R_B(\theta_2)$.
2. Rotor orthogonality $R_B(\theta)^\top R_B(\theta) = 1$.
3. Discrete group law $\rho_B(m + k) = \rho_B(m) \cdot \rho_B(k)$.
4. Exact relative-position pairing theorem $\langle R_m q, R_k v \rangle = \langle q, R_{k-m} v \rangle$.
-/
theorem grand_rotor_monodromy_synthesis
    (cs : RealComplexStructure n) (theta0 theta1 theta2 : ℝ)
    (m k : ℤ) (q v : Fin n → ℝ) :
    (rotor cs 0 = 1 ∧
     rotor cs (theta1 + theta2) = rotor cs theta1 * rotor cs theta2 ∧
     (rotor cs theta1)ᵀ * rotor cs theta1 = 1) ∧
    (discreteRotor cs theta0 0 = 1 ∧
     discreteRotor cs theta0 (m + k) =
       discreteRotor cs theta0 m * discreteRotor cs theta0 k) ∧
    (standardPairing ((discreteRotor cs theta0 m) *ᵥ q)
                     ((discreteRotor cs theta0 k) *ᵥ v) =
     standardPairing q ((discreteRotor cs theta0 (k - m)) *ᵥ v)) :=
  ⟨⟨rotor_zero cs, rotor_add cs theta1 theta2, rotor_transpose_mul_self cs theta1⟩,
   ⟨by unfold discreteRotor; simp only [Int.cast_zero, zero_mul, rotor_zero],
    discreteRotor_add cs theta0 m k⟩,
   rope_relative_pairing_invariance cs theta0 m k q v⟩

end InfoGeometry.Clifford.RotorMonodromy

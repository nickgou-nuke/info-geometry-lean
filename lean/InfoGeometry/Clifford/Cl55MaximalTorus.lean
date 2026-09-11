import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Clifford.MaximalTorus

open Matrix

variable {n : ℕ}
abbrev AlgMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-!
# Multi-Dimensional RoPE Maximal Torus & Commuting Rotor Representation

This module formalizes the multi-plane Maximal Abelian Torus in the Clifford
algebra / spinor module $\mathrm{Mat}_n(\mathbb{R})$:

$$\boxed{
\begin{aligned}
&\textbf{1. Commuting Bivector Rotors:}\\
&\quad [B_1, B_2] = 0 \implies R_{B_1}(\theta_1) R_{B_2}(\theta_2) = R_{B_2}(\theta_2) R_{B_1}(\theta_1)\\
&\textbf{2. Multi-Frequency Torus Group Homomorphism:}\\
&\quad R(a_1 + a_2, b_1 + b_2) = R(a_1, b_1) \cdot R(a_2, b_2)\\
&\textbf{3. Multi-Channel Relative-Position Invariance:}\\
&\quad \langle R(m\vec{\omega}) q, R(k\vec{\omega}) v \rangle = \langle q, R((k - m)\vec{\omega}) v \rangle.
\end{aligned}}
$$

All proofs are complete in native Mathlib 4 with zero `sorry`s.
-/

/-- Single-plane rotor for a bivector $B$. -/
def rotor (B : AlgMat n) (theta : ℝ) : AlgMat n :=
  Real.cos theta • 1 + Real.sin theta • B

/-- Normalization at zero: $R_B(0) = 1$. -/
theorem rotor_zero (B : AlgMat n) : rotor B 0 = 1 := by
  unfold rotor
  simp only [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero]

/-- Single-plane 1-parameter rotor group law: $R_B(a + b) = R_B(a) R_B(b)$ when $B^2 = -1$. -/
theorem rotor_add (B : AlgMat n) (hB : B * B = -1) (a b : ℝ) :
    rotor B (a + b) = rotor B a * rotor B b := by
  unfold rotor
  rw [Real.cos_add, Real.sin_add]
  simp only [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
             one_mul, mul_one, hB, smul_neg]
  module

/-- Transpose of skew rotor: $R_B(\theta)^\top = R_B(-\theta)$ when $B^\top = -B$. -/
theorem rotor_transpose (B : AlgMat n) (h_skew : Bᵀ = -B) (theta : ℝ) :
    (rotor B theta)ᵀ = rotor B (-theta) := by
  unfold rotor
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, h_skew]
  simp only [Real.cos_neg, Real.sin_neg, smul_neg]
  module

/-- Orthogonality of single-plane rotor: $R_B(\theta)^\top R_B(\theta) = 1$. -/
theorem rotor_transpose_mul_self
    (B : AlgMat n) (hB : B * B = -1) (h_skew : Bᵀ = -B) (theta : ℝ) :
    (rotor B theta)ᵀ * rotor B theta = 1 := by
  rw [rotor_transpose B h_skew, ← rotor_add B hB]
  have h : -theta + theta = 0 := neg_add_cancel theta
  rw [h, rotor_zero]

/-! ## 1. Commutativity of Rotors on Commuting Bivectors -/

/--
  **THEOREM (Commuting Rotors on Maximal Torus)**:
  When bivectors commute ($B_1 B_2 = B_2 B_1$), their corresponding rotors
  commute identically for all rotation angles $\theta_1, \theta_2$:
  $$R_{B_1}(\theta_1) R_{B_2}(\theta_2) = R_{B_2}(\theta_2) R_{B_1}(\theta_1).$$
-/
theorem commuting_rotors (B1 B2 : AlgMat n)
    (h_comm : B1 * B2 = B2 * B1) (t1 t2 : ℝ) :
    rotor B1 t1 * rotor B2 t2 = rotor B2 t2 * rotor B1 t1 := by
  unfold rotor
  rw [add_mul, mul_add, mul_add]
  rw [add_mul, mul_add, mul_add]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one, smul_smul]
  rw [mul_comm (Real.cos t1) (Real.cos t2)]
  rw [mul_comm (Real.cos t1) (Real.sin t2)]
  rw [mul_comm (Real.sin t1) (Real.cos t2)]
  rw [mul_comm (Real.sin t1) (Real.sin t2)]
  rw [h_comm]
  abel

/-! ## 2. Rank-2 Composed Torus Homomorphism -/

/-- Rank-2 Torus Rotor combining two commuting rotation planes. -/
def rank2Rotor (B1 B2 : AlgMat n) (t1 t2 : ℝ) : AlgMat n :=
  rotor B1 t1 * rotor B2 t2

/-- Origin normalization: $R(0, 0) = 1$. -/
theorem rank2Rotor_zero (B1 B2 : AlgMat n) :
    rank2Rotor B1 B2 0 0 = 1 := by
  unfold rank2Rotor
  rw [rotor_zero, rotor_zero, mul_one]

/--
  **THEOREM (Rank-2 Torus Group Law)**:
  Multi-parameter additive translation on the 2-torus:
  $$R(a_1 + a_2, b_1 + b_2) = R(a_1, b_1) \cdot R(a_2, b_2).$$
-/
theorem rank2Rotor_add
    (B1 B2 : AlgMat n) (hB1 : B1 * B1 = -1) (hB2 : B2 * B2 = -1)
    (h_comm : B1 * B2 = B2 * B1) (a1 b1 a2 b2 : ℝ) :
    rank2Rotor B1 B2 (a1 + a2) (b1 + b2) =
    rank2Rotor B1 B2 a1 b1 * rank2Rotor B1 B2 a2 b2 := by
  unfold rank2Rotor
  rw [rotor_add B1 hB1 a1 a2, rotor_add B2 hB2 b1 b2]
  -- Reorder: (R1(a1) * R1(a2)) * (R2(b1) * R2(b2)) = (R1(a1) * R2(b1)) * (R1(a2) * R2(b2))
  rw [mul_assoc (rotor B1 a1) (rotor B1 a2)]
  rw [← mul_assoc (rotor B1 a2) (rotor B2 b1) (rotor B2 b2)]
  rw [commuting_rotors B1 B2 h_comm a2 b1]
  rw [mul_assoc (rotor B2 b1) (rotor B1 a2) (rotor B2 b2)]
  rw [← mul_assoc (rotor B1 a1)]

/-- Transpose of rank-2 torus rotor: $R(\vec{\theta})^\top = R(-\vec{\theta})$. -/
theorem rank2Rotor_transpose
    (B1 B2 : AlgMat n) (h_skew1 : B1ᵀ = -B1) (h_skew2 : B2ᵀ = -B2)
    (h_comm : B1 * B2 = B2 * B1) (t1 t2 : ℝ) :
    (rank2Rotor B1 B2 t1 t2)ᵀ = rank2Rotor B1 B2 (-t1) (-t2) := by
  unfold rank2Rotor
  rw [Matrix.transpose_mul]
  rw [rotor_transpose B1 h_skew1, rotor_transpose B2 h_skew2]
  exact commuting_rotors B2 B1 h_comm.symm (-t2) (-t1)

/-- Orthogonality of rank-2 torus rotor: $R(\vec{\theta})^\top R(\vec{\theta}) = 1$. -/
theorem rank2Rotor_transpose_mul_self
    (B1 B2 : AlgMat n) (hB1 : B1 * B1 = -1) (hB2 : B2 * B2 = -1)
    (h_skew1 : B1ᵀ = -B1) (h_skew2 : B2ᵀ = -B2)
    (h_comm : B1 * B2 = B2 * B1) (t1 t2 : ℝ) :
    (rank2Rotor B1 B2 t1 t2)ᵀ * rank2Rotor B1 B2 t1 t2 = 1 := by
  rw [rank2Rotor_transpose B1 B2 h_skew1 h_skew2 h_comm]
  rw [← rank2Rotor_add B1 B2 hB1 hB2 h_comm]
  have h1 : -t1 + t1 = 0 := neg_add_cancel t1
  have h2 : -t2 + t2 = 0 := neg_add_cancel t2
  rw [h1, h2, rank2Rotor_zero]

/-! ## 3. Multi-Frequency Discrete RoPE Torus Representation -/

/-- Multi-frequency discrete positional rotor for position $m \in \mathbb{Z}$. -/
def discreteRank2Rotor
    (B1 B2 : AlgMat n) (w1 w2 : ℝ) (m : ℤ) : AlgMat n :=
  rank2Rotor B1 B2 ((m : ℝ) * w1) ((m : ℝ) * w2)

/-- Multi-frequency discrete rotor group homomorphism: $\rho(m + k) = \rho(m) \rho(k)$. -/
theorem discreteRank2Rotor_add
    (B1 B2 : AlgMat n) (hB1 : B1 * B1 = -1) (hB2 : B2 * B2 = -1)
    (h_comm : B1 * B2 = B2 * B1) (w1 w2 : ℝ) (m k : ℤ) :
    discreteRank2Rotor B1 B2 w1 w2 (m + k) =
    discreteRank2Rotor B1 B2 w1 w2 m * discreteRank2Rotor B1 B2 w1 w2 k := by
  unfold discreteRank2Rotor
  have h1 : ((m + k : ℤ) : ℝ) * w1 = (m : ℝ) * w1 + (k : ℝ) * w1 := by push_cast; ring
  have h2 : ((m + k : ℤ) : ℝ) * w2 = (m : ℝ) * w2 + (k : ℝ) * w2 := by push_cast; ring
  rw [h1, h2]
  exact rank2Rotor_add B1 B2 hB1 hB2 h_comm _ _ _ _

/--
  **MASTER THEOREM (Multi-Channel RoPE Relative-Position Invariance)**:
  On the multi-plane Maximal Torus, the inner product between query at position $m$
  and key at position $k$ depends strictly on the relative displacement $(k - m)$:
  $$\langle R(m\vec{\omega}) q, R(k\vec{\omega}) v \rangle = \langle q, R((k - m)\vec{\omega}) v \rangle.$$
-/
theorem multi_channel_rope_relative_pairing_invariance
    (B1 B2 : AlgMat n) (hB1 : B1 * B1 = -1) (hB2 : B2 * B2 = -1)
    (h_skew1 : B1ᵀ = -B1) (h_skew2 : B2ᵀ = -B2)
    (h_comm : B1 * B2 = B2 * B1) (w1 w2 : ℝ)
    (m k : ℤ) (q v : Fin n → ℝ) :
    dotProduct ((discreteRank2Rotor B1 B2 w1 w2 m) *ᵥ q)
               ((discreteRank2Rotor B1 B2 w1 w2 k) *ᵥ v) =
    dotProduct q ((discreteRank2Rotor B1 B2 w1 w2 (k - m)) *ᵥ v) := by
  unfold discreteRank2Rotor
  rw [← Matrix.vecMul_transpose]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_vecMul]
  rw [← Matrix.dotProduct_mulVec]
  rw [rank2Rotor_transpose B1 B2 h_skew1 h_skew2 h_comm]
  rw [← rank2Rotor_add B1 B2 hB1 hB2 h_comm]
  have h1 : -((m : ℝ) * w1) + (k : ℝ) * w1 = ((k - m : ℤ) : ℝ) * w1 := by push_cast; ring
  have h2 : -((m : ℝ) * w2) + (k : ℝ) * w2 = ((k - m : ℤ) : ℝ) * w2 := by push_cast; ring
  rw [h1, h2]

/-! ## Master Synthesis -/

/--
🏆 **GRAND SYNTHESIS THEOREM: Multi-Dimensional RoPE Maximal Torus**

Unifies:
1. Commutativity of multi-plane rotors on maximal torus $R_{B_1}(\theta_1) R_{B_2}(\theta_2) = R_{B_2}(\theta_2) R_{B_1}(\theta_1)$.
2. Multi-frequency 2-torus additive group law $R(\vec{a} + \vec{b}) = R(\vec{a}) R(\vec{b})$.
3. Orthogonality $R(\vec{\theta})^\top R(\vec{\theta}) = 1$.
4. Discrete position group homomorphism $\rho(m + k) = \rho(m) \rho(k)$.
5. Exact multi-channel RoPE relative-position invariant $\langle R_m q, R_k v \rangle = \langle q, R_{k-m} v \rangle$.
-/
theorem grand_maximal_torus_synthesis
    (B1 B2 : AlgMat n) (hB1 : B1 * B1 = -1) (hB2 : B2 * B2 = -1)
    (h_skew1 : B1ᵀ = -B1) (h_skew2 : B2ᵀ = -B2)
    (h_comm : B1 * B2 = B2 * B1) (w1 w2 a1 b1 a2 b2 : ℝ)
    (m k : ℤ) (q v : Fin n → ℝ) :
    (rotor B1 a1 * rotor B2 b1 = rotor B2 b1 * rotor B1 a1 ∧
     rank2Rotor B1 B2 (a1 + a2) (b1 + b2) =
       rank2Rotor B1 B2 a1 b1 * rank2Rotor B1 B2 a2 b2 ∧
     (rank2Rotor B1 B2 a1 b1)ᵀ * rank2Rotor B1 B2 a1 b1 = 1) ∧
    (discreteRank2Rotor B1 B2 w1 w2 0 = 1 ∧
     discreteRank2Rotor B1 B2 w1 w2 (m + k) =
       discreteRank2Rotor B1 B2 w1 w2 m * discreteRank2Rotor B1 B2 w1 w2 k) ∧
    (dotProduct ((discreteRank2Rotor B1 B2 w1 w2 m) *ᵥ q)
                ((discreteRank2Rotor B1 B2 w1 w2 k) *ᵥ v) =
     dotProduct q ((discreteRank2Rotor B1 B2 w1 w2 (k - m)) *ᵥ v)) :=
  ⟨⟨commuting_rotors B1 B2 h_comm a1 b1,
     rank2Rotor_add B1 B2 hB1 hB2 h_comm a1 b1 a2 b2,
     rank2Rotor_transpose_mul_self B1 B2 hB1 hB2 h_skew1 h_skew2 h_comm a1 b1⟩,
   ⟨by unfold discreteRank2Rotor; simp only [Int.cast_zero, zero_mul, rank2Rotor_zero],
    discreteRank2Rotor_add B1 B2 hB1 hB2 h_comm w1 w2 m k⟩,
   multi_channel_rope_relative_pairing_invariance B1 B2 hB1 hB2 h_skew1 h_skew2 h_comm w1 w2 m k q v⟩

end InfoGeometry.Clifford.MaximalTorus


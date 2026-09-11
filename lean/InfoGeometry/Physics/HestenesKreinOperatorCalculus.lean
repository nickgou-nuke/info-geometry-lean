import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Hestenes-Krein Operator Calculus

This file establishes the formal geometric translation of complex and
split-complex scalar calculi into internal real operators.

The core result is that the elliptic phase and hyperbolic scaling of
the non-commutative Fourier and Mellin-Laplace transforms arise strictly
from the algebraic properties of real geometric operators $I^2 = -1$
and $K^2 = 1$, avoiding any foundational dependence on an external
imaginary unit.

1. $I^2 = -1 \implies \exp(\theta I) = \cos\theta + I\sin\theta$
2. $K^2 = 1 \implies \exp(tK) = e^t P_+ + e^{-t} P_-$
3. $[I, K] = 0 \implies \exp(\theta I + tK) = \exp(\theta I)\exp(tK)$
-/

noncomputable section

namespace InfoGeometry.Physics.HestenesKreinOperatorCalculus

-- We define an abstract algebra over ℝ with topological/analytic properties
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

local instance : NormedAlgebra ℚ A :=
  NormedAlgebra.restrictScalars ℚ ℝ A

omit [CompleteSpace A] in
private lemma smul_pow_even_of_sq_eq_neg_one
    (G : A) (hSq : G * G = -(1 : A)) (t : ℝ) :
    ∀ n : ℕ,
      (t • G) ^ (2 * n) = (((-1 : ℝ) ^ n) * t ^ (2 * n)) • (1 : A)
  | 0 => by simp
  | n + 1 => by
      have hpow2 : (t • G) ^ 2 = (((-1 : ℝ) * t ^ 2)) • (1 : A) := by
        calc
          (t • G) ^ 2 = (t • G) * (t • G) := by simp [pow_two]
          _ = (t * t) • (G * G) := by
                rw [smul_mul_assoc, mul_smul_comm, smul_smul]
          _ = (t ^ 2) • (-(1 : A)) := by
                simp [hSq, pow_two]
          _ = (((-1 : ℝ) * t ^ 2)) • (1 : A) := by
                simp [mul_comm]
      calc
        (t • G) ^ (2 * (n + 1))
            = (t • G) ^ (2 * n) * (t • G) ^ 2 := by
                rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
        _ = (((( -1 : ℝ) ^ n) * t ^ (2 * n)) • (1 : A)) *
              (((( -1 : ℝ) * t ^ 2)) • (1 : A)) := by
                rw [smul_pow_even_of_sq_eq_neg_one G hSq t n, hpow2]
        _ = (((-1 : ℝ) ^ n) * t ^ (2 * n) *
              (((-1 : ℝ) * t ^ 2))) • (1 : A) := by
              rw [smul_mul_assoc, mul_smul_comm, smul_smul, one_mul]
        _ = (((-1 : ℝ) ^ (n + 1) * t ^ (2 * (n + 1)))) • (1 : A) := by
              congr 1
              have hn :
                  (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ n * (-1 : ℝ) := by
                rw [pow_succ]
              have ht :
                  t ^ (2 * (n + 1)) = t ^ (2 * n) * t ^ 2 := by
                rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
              rw [hn, ht]
              ring

omit [CompleteSpace A] in
private lemma smul_pow_odd_of_sq_eq_neg_one
    (G : A) (hSq : G * G = -(1 : A)) (t : ℝ) (n : ℕ) :
    (t • G) ^ (2 * n + 1) =
      (((-1 : ℝ) ^ n) * t ^ (2 * n + 1)) • G := by
  calc
    (t • G) ^ (2 * n + 1)
        = (t • G) ^ (2 * n) * (t • G) := by rw [pow_succ]
    _ = (((( -1 : ℝ) ^ n) * t ^ (2 * n)) • (1 : A)) * (t • G) := by
          rw [smul_pow_even_of_sq_eq_neg_one G hSq t n]
    _ = ((((-1 : ℝ) ^ n) * t ^ (2 * n + 1))) • G := by
          rw [smul_mul_assoc, one_mul, smul_smul]
          congr 1
          rw [pow_succ]
          ring

omit [CompleteSpace A] in
private lemma smul_pow_even_of_sq_eq_one
    (G : A) (hSq : G * G = (1 : A)) (t : ℝ) :
    ∀ n : ℕ, (t • G) ^ (2 * n) = (t ^ (2 * n)) • (1 : A)
  | 0 => by simp
  | n + 1 => by
      have hpow2 : (t • G) ^ 2 = (t ^ 2) • (1 : A) := by
        rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, hSq]
        simp [pow_two]
      calc
        (t • G) ^ (2 * (n + 1))
            = (t • G) ^ (2 * n) * (t • G) ^ 2 := by
                rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
        _ = ((t ^ (2 * n)) • (1 : A)) * ((t ^ 2) • (1 : A)) := by
              rw [smul_pow_even_of_sq_eq_one G hSq t n, hpow2]
        _ = (t ^ (2 * (n + 1))) • (1 : A) := by
              rw [smul_mul_assoc, mul_smul_comm, smul_smul, one_mul]
              rw [← pow_add]
              simp [show 2 * (n + 1) = 2 * n + 2 by omega]

omit [CompleteSpace A] in
private lemma smul_pow_odd_of_sq_eq_one
    (G : A) (hSq : G * G = (1 : A)) (t : ℝ) (n : ℕ) :
    (t • G) ^ (2 * n + 1) = (t ^ (2 * n + 1)) • G := by
  calc
    (t • G) ^ (2 * n + 1) = (t • G) ^ (2 * n) * (t • G) := by
      rw [pow_succ]
    _ = ((t ^ (2 * n)) • (1 : A)) * (t • G) := by
      rw [smul_pow_even_of_sq_eq_one G hSq t n]
    _ = (t ^ (2 * n + 1)) • G := by
      rw [smul_mul_assoc, one_mul, smul_smul]
      simp [pow_succ]

/-- The Hestenes/Fourier elliptic generator theorem. -/
theorem exp_of_sq_eq_neg_one (I : A) (hI : I ^ 2 = -1) (θ : ℝ) :
    NormedSpace.exp (θ • I) = Real.cos θ • (1 : A) + Real.sin θ • I := by
  have hSq : I * I = -(1 : A) := by simpa [sq] using hI
  rw [NormedSpace.exp_eq_tsum ℝ]
  have hsum :
      HasSum
        (fun n : ℕ => ((Nat.factorial n : ℕ) : ℝ)⁻¹ • (θ • I) ^ n)
        (((Real.cos θ : ℝ) • (1 : A)) + ((Real.sin θ : ℝ) • I)) := by
    refine HasSum.even_add_odd ?_ ?_
    · convert (Real.hasSum_cos θ).smul_const (1 : A) using 1
      ext n x <;>
        rw [smul_pow_even_of_sq_eq_neg_one I hSq θ n] <;>
        simp [div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm]
    · convert (Real.hasSum_sin θ).smul_const I using 1
      ext n x <;>
        rw [smul_pow_odd_of_sq_eq_neg_one I hSq θ n] <;>
        simp [div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm]
  exact hsum.tsum_eq

/-- The Krein/Mellin hyperbolic generator theorem. -/
theorem exp_of_sq_eq_one (K : A) (hK : K ^ 2 = 1) (t : ℝ) :
    NormedSpace.exp (t • K) = Real.cosh t • (1 : A) + Real.sinh t • K := by
  have hSq : K * K = (1 : A) := by simpa [sq] using hK
  rw [NormedSpace.exp_eq_tsum ℝ]
  have hsum :
      HasSum
        (fun n : ℕ => ((Nat.factorial n : ℕ) : ℝ)⁻¹ • (t • K) ^ n)
        (((Real.cosh t : ℝ) • (1 : A)) + ((Real.sinh t : ℝ) • K)) := by
    refine HasSum.even_add_odd ?_ ?_
    · convert (Real.hasSum_cosh t).smul_const (1 : A) using 1
      ext n x <;>
        rw [smul_pow_even_of_sq_eq_one K hSq t n] <;>
        simp [div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm]
    · convert (Real.hasSum_sinh t).smul_const K using 1
      ext n x <;>
        rw [smul_pow_odd_of_sq_eq_one K hSq t n] <;>
        simp [div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm]
  exact hsum.tsum_eq

/-- The mixed loxodromic generator theorem for commuting operators. -/
theorem exp_add_of_commute (I K : A) (h_comm : I * K = K * I) (θ t : ℝ) :
    NormedSpace.exp (θ • I + t • K) = NormedSpace.exp (θ • I) * NormedSpace.exp (t • K) := by
  have h_commute : Commute (θ • I) (t • K) := by
    exact (show Commute I K from h_comm).smul_left θ |>.smul_right t
  exact NormedSpace.exp_add_of_commute h_commute

/-- The square of the mixed generator for anticommuting operators. -/
theorem anticommuting_mixed_square (I K : A)
    (hI : I ^ 2 = -1) (hK : K ^ 2 = 1) (h_anti : I * K = -(K * I)) (θ η : ℝ) :
    (θ • I + η • K) ^ 2 = (η ^ 2 - θ ^ 2) • (1 : A) := by
  have H1 : I * I = -1 := by rw [← sq, hI]
  have H2 : K * K = 1 := by rw [← sq, hK]
  rw [sq, add_mul, mul_add, mul_add]
  rw [smul_mul_smul, smul_mul_smul, smul_mul_smul, smul_mul_smul]
  rw [H1, H2, h_anti]
  simp only [smul_neg]
  module

/-- The hyperbolic exponential theorem for the mixed generator. -/
theorem exp_anticommuting_hyperbolic (I K : A)
    (hI : I ^ 2 = -1) (hK : K ^ 2 = 1) (h_anti : I * K = -(K * I))
    (θ η : ℝ) (hq : θ^2 < η^2) (r : ℝ) (hr : r^2 = η^2 - θ^2) :
    NormedSpace.exp (θ • I + η • K) = Real.cosh r • (1 : A) + (Real.sinh r / r) • (θ • I + η • K) := by
  have hqpos : 0 < η ^ 2 - θ ^ 2 := sub_pos.mpr hq
  have hrne : r ≠ 0 := by
    intro hr0
    apply (ne_of_gt hqpos)
    rw [← hr, hr0]
    simp
  let X : A := θ • I + η • K
  have hXsq : X * X = (r ^ 2) • (1 : A) := by
    dsimp [X]
    calc
      (θ • I + η • K) * (θ • I + η • K) =
          (η ^ 2 - θ ^ 2) • (1 : A) := by
            simpa [pow_two] using
              (anticommuting_mixed_square I K hI hK h_anti θ η)
      _ = (r ^ 2) • (1 : A) := by rw [hr]
  let G : A := r⁻¹ • X
  have hG : G ^ 2 = (1 : A) := by
    dsimp [G]
    rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, hXsq, smul_smul]
    field_simp
    simp
  have hexp := exp_of_sq_eq_one G hG r
  have hscale : r • G = X := by
    dsimp [G]
    rw [smul_smul]
    simp [hrne]
  rw [hscale] at hexp
  have hcoeff : Real.sinh r • G = (Real.sinh r / r) • X := by
    dsimp [G]
    rw [smul_smul]
    congr 1
  rw [hcoeff] at hexp
  simpa [X] using hexp

/-- The elliptic exponential theorem for the mixed generator. -/
theorem exp_anticommuting_elliptic (I K : A)
    (hI : I ^ 2 = -1) (hK : K ^ 2 = 1) (h_anti : I * K = -(K * I))
    (θ η : ℝ) (hq : η^2 < θ^2) (r : ℝ) (hr : r^2 = θ^2 - η^2) :
    NormedSpace.exp (θ • I + η • K) = Real.cos r • (1 : A) + (Real.sin r / r) • (θ • I + η • K) := by
  have hqpos : 0 < θ ^ 2 - η ^ 2 := sub_pos.mpr hq
  have hrne : r ≠ 0 := by
    intro hr0
    apply (ne_of_gt hqpos)
    rw [← hr, hr0]
    simp
  let X : A := θ • I + η • K
  have hXsq : X * X = -(r ^ 2) • (1 : A) := by
    dsimp [X]
    calc
      (θ • I + η • K) * (θ • I + η • K) =
          (η ^ 2 - θ ^ 2) • (1 : A) := by
            simpa [pow_two] using
              (anticommuting_mixed_square I K hI hK h_anti θ η)
      _ = -(θ ^ 2 - η ^ 2) • (1 : A) := by
            congr 1
            ring
      _ = -(r ^ 2) • (1 : A) := by rw [hr]
  let G : A := r⁻¹ • X
  have hG : G ^ 2 = -(1 : A) := by
    dsimp [G]
    rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, hXsq, smul_smul]
    have hinv : r⁻¹ * r⁻¹ * -(r ^ 2) = -1 := by
      calc r⁻¹ * r⁻¹ * -(r ^ 2) = -(r⁻¹ * r⁻¹ * (r * r)) := by ring
        _ = -((r⁻¹ * r) * (r⁻¹ * r)) := by ring
        _ = -(1 * 1) := by
          rw [inv_mul_cancel₀ hrne]
        _ = -1 := by ring
    rw [hinv]
    exact neg_one_smul ℝ (1 : A)
  have hexp := exp_of_sq_eq_neg_one G hG r
  have hscale : r • G = X := by
    dsimp [G]
    rw [smul_smul, mul_inv_cancel₀ hrne, one_smul]
  rw [hscale] at hexp
  have hcoeff : Real.sin r • G = (Real.sin r / r) • X := by
    dsimp [G]
    rw [smul_smul, div_eq_mul_one_div]
    congr 1
    ring
  rw [hcoeff] at hexp
  simpa [X] using hexp

theorem exp_anticommuting_null (I K : A)
    (hI : I ^ 2 = -1) (hK : K ^ 2 = 1) (h_anti : I * K = -(K * I))
    (θ η : ℝ) (hq : η^2 = θ^2) :
    NormedSpace.exp (θ • I + η • K) = (1 : A) + (θ • I + η • K) := by
  have hsq :
      (θ • I + η • K) * (θ • I + η • K) = (0 : A) := by
    have hsq' := anticommuting_mixed_square I K hI hK h_anti θ η
    rw [pow_two, hq] at hsq'
    simpa using hsq'
  rw [NormedSpace.exp_eq_tsum ℝ]
  change
    (∑' n : ℕ, ((Nat.factorial n : ℕ) : ℝ)⁻¹ •
      (θ • I + η • K) ^ n) = _
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.range, pow_zero, pow_one, add_comm]
  · intro n hn
    have h2n : 2 ≤ n := by simpa using hn
    have hpow2 : (θ • I + η • K) ^ 2 = 0 := by
      simpa [pow_two] using hsq
    rw [pow_eq_zero_of_le h2n hpow2, smul_zero]

/-- The hyperbolic formula with the canonical nonnegative square root. -/
theorem exp_anticommuting_hyperbolic_sqrt (I K : A)
    (hI : I ^ 2 = -1) (hK : K ^ 2 = 1)
    (h_anti : I * K = -(K * I))
    (θ η : ℝ) (hq : θ ^ 2 < η ^ 2) :
    NormedSpace.exp (θ • I + η • K) =
      Real.cosh (Real.sqrt (η ^ 2 - θ ^ 2)) • (1 : A) +
        (Real.sinh (Real.sqrt (η ^ 2 - θ ^ 2)) /
          Real.sqrt (η ^ 2 - θ ^ 2)) • (θ • I + η • K) := by
  apply exp_anticommuting_hyperbolic I K hI hK h_anti θ η hq
    (Real.sqrt (η ^ 2 - θ ^ 2))
  exact Real.sq_sqrt (le_of_lt (sub_pos.mpr hq))

/-- The elliptic formula with the canonical nonnegative square root. -/
theorem exp_anticommuting_elliptic_sqrt (I K : A)
    (hI : I ^ 2 = -1) (hK : K ^ 2 = 1)
    (h_anti : I * K = -(K * I))
    (θ η : ℝ) (hq : η ^ 2 < θ ^ 2) :
    NormedSpace.exp (θ • I + η • K) =
      Real.cos (Real.sqrt (θ ^ 2 - η ^ 2)) • (1 : A) +
        (Real.sin (Real.sqrt (θ ^ 2 - η ^ 2)) /
          Real.sqrt (θ ^ 2 - η ^ 2)) • (θ • I + η • K) := by
  apply exp_anticommuting_elliptic I K hI hK h_anti θ η hq
    (Real.sqrt (θ ^ 2 - η ^ 2))
  exact Real.sq_sqrt (le_of_lt (sub_pos.mpr hq))

end InfoGeometry.Physics.HestenesKreinOperatorCalculus

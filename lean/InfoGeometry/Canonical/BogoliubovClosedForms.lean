import InfoGeometry.Canonical.BogoliubovTransport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic

namespace InfoGeometry.Canonical.BogoliubovClosedForms

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Krein

section Basic

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "Kop" => modularComplexI (E := E)

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

private lemma smul_pow_even_of_sq_eq_one
    (G : EndH) (hSq : G * G = (1 : EndH)) (t : ℝ) :
    ∀ n : ℕ, (t • G) ^ (2 * n) = (t ^ (2 * n)) • (1 : EndH)
  | 0 => by simp
  | n + 1 => by
      have hpow2 : (t • G) ^ 2 = (t ^ 2) • (1 : EndH) := by
        rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, hSq]
        simp [pow_two]
      calc
        (t • G) ^ (2 * (n + 1))
            = (t • G) ^ (2 * n) * (t • G) ^ 2 := by
                rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
        _ = ((t ^ (2 * n)) • (1 : EndH)) * ((t ^ 2) • (1 : EndH)) := by
              rw [smul_pow_even_of_sq_eq_one G hSq t n, hpow2]
        _ = (t ^ (2 * (n + 1))) • (1 : EndH) := by
              rw [smul_mul_assoc, mul_smul_comm, smul_smul, one_mul]
              rw [← pow_add]
              simp [show 2 * (n + 1) = 2 * n + 2 by omega]

private lemma smul_pow_odd_of_sq_eq_one
    (G : EndH) (hSq : G * G = (1 : EndH)) (t : ℝ) (n : ℕ) :
    (t • G) ^ (2 * n + 1) = (t ^ (2 * n + 1)) • G := by
  calc
    (t • G) ^ (2 * n + 1)
        = (t • G) ^ (2 * n) * (t • G) := by
            rw [pow_succ]
    _ = ((t ^ (2 * n)) • (1 : EndH)) * (t • G) := by
          rw [smul_pow_even_of_sq_eq_one G hSq t n]
    _ = (t ^ (2 * n + 1)) • G := by
          rw [smul_mul_assoc, one_mul, smul_smul]
          simp [pow_succ]

private lemma smul_pow_even_of_sq_eq_neg_one
    (G : EndH) (hSq : G * G = -(1 : EndH)) (t : ℝ) :
    ∀ n : ℕ, (t • G) ^ (2 * n) = (((-1 : ℝ) ^ n) * t ^ (2 * n)) • (1 : EndH)
  | 0 => by simp
  | n + 1 => by
      have hpow2 : (t • G) ^ 2 = (((-1 : ℝ) * t ^ 2)) • (1 : EndH) := by
        calc
          (t • G) ^ 2 = (t • G) * (t • G) := by simp [pow_two]
          _ = (t * t) • (G * G) := by
                rw [smul_mul_assoc, mul_smul_comm, smul_smul]
          _ = (t ^ 2) • (-(1 : EndH)) := by
                simp [hSq, pow_two]
          _ = (((-1 : ℝ) * t ^ 2)) • (1 : EndH) := by
                simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
      calc
        (t • G) ^ (2 * (n + 1))
            = (t • G) ^ (2 * n) * (t • G) ^ 2 := by
                rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
        _ = (((( -1 : ℝ) ^ n) * t ^ (2 * n)) • (1 : EndH)) *
              (((( -1 : ℝ) * t ^ 2)) • (1 : EndH)) := by
                rw [smul_pow_even_of_sq_eq_neg_one G hSq t n, hpow2]
        _ = ((((-1 : ℝ) ^ n) * t ^ (2 * n) * (((-1 : ℝ) * t ^ 2)))) • (1 : EndH) := by
              rw [smul_mul_assoc, mul_smul_comm, smul_smul, one_mul]
        _ = (((-1 : ℝ) ^ (n + 1) * t ^ (2 * (n + 1)))) • (1 : EndH) := by
              congr 1
              simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
                (show
                  (-1 : ℝ) ^ n * t ^ (2 * n) * ((-1 : ℝ) * t ^ 2)
                    = (-1 : ℝ) ^ (n + 1) * t ^ (2 * (n + 1)) from by
                  calc
                    (-1 : ℝ) ^ n * t ^ (2 * n) * ((-1 : ℝ) * t ^ 2)
                        = (((-1 : ℝ) ^ n) * (-1 : ℝ)) * (t ^ (2 * n) * t ^ 2) := by
                            ring
                    _ = (-1 : ℝ) ^ (n + 1) * t ^ (2 * n + 2) := by
                          have hs : ((-1 : ℝ) ^ n) * (-1 : ℝ) = (-1 : ℝ) ^ (n + 1) := by
                            simpa [pow_succ]
                          have ht : t ^ (2 * n) * t ^ 2 = t ^ (2 * n + 2) := by
                            simpa using (pow_add t (2 * n) 2).symm
                          rw [hs, ht]
                    _ = (-1 : ℝ) ^ (n + 1) * t ^ (2 * (n + 1)) := by
                          congr 2)

private lemma smul_pow_odd_of_sq_eq_neg_one
    (G : EndH) (hSq : G * G = -(1 : EndH)) (t : ℝ) (n : ℕ) :
    (t • G) ^ (2 * n + 1) = (((-1 : ℝ) ^ n) * t ^ (2 * n + 1)) • G := by
  calc
    (t • G) ^ (2 * n + 1)
        = (t • G) ^ (2 * n) * (t • G) := by
            rw [pow_succ]
    _ = (((( -1 : ℝ) ^ n) * t ^ (2 * n)) • (1 : EndH)) * (t • G) := by
          rw [smul_pow_even_of_sq_eq_neg_one G hSq t n]
    _ = ((((-1 : ℝ) ^ n) * t ^ (2 * n + 1))) • G := by
          rw [smul_mul_assoc, one_mul, smul_smul]
          congr 1
          rw [pow_succ]
          ring

/-- Closed form for the exponential of an involution on the doubled carrier. -/
theorem exp_eq_cosh_add_sinh_of_sq_eq_one
    {G : EndH} (hSq : G * G = (1 : EndH)) (t : ℝ) :
    NormedSpace.exp (t • G) = Real.cosh t • (1 : EndH) + Real.sinh t • G := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  have hsum :
      HasSum
        (fun n : ℕ => ((Nat.factorial n : ℕ) : ℝ)⁻¹ • (t • G) ^ n)
        (((Real.cosh t : ℝ) • (1 : EndH)) + ((Real.sinh t : ℝ) • G)) := by
    refine HasSum.even_add_odd ?_ ?_
    · convert (Real.hasSum_cosh t).smul_const (1 : EndH) using 1
      ext n x <;> rw [smul_pow_even_of_sq_eq_one G hSq t n] <;>
        simp [div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm, mul_assoc]
    · convert (Real.hasSum_sinh t).smul_const G using 1
      ext n x <;> rw [smul_pow_odd_of_sq_eq_one G hSq t n] <;>
        simp [div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  simpa using hsum.tsum_eq

/-- Closed form for the exponential of a square-minus-one operator on the doubled carrier. -/
theorem exp_eq_cos_add_sin_of_sq_eq_neg_one
    {G : EndH} (hSq : G * G = -(1 : EndH)) (t : ℝ) :
    NormedSpace.exp (t • G) = Real.cos t • (1 : EndH) + Real.sin t • G := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  have hsum :
      HasSum
        (fun n : ℕ => ((Nat.factorial n : ℕ) : ℝ)⁻¹ • (t • G) ^ n)
        (((Real.cos t : ℝ) • (1 : EndH)) + ((Real.sin t : ℝ) • G)) := by
    refine HasSum.even_add_odd ?_ ?_
    · convert (Real.hasSum_cos t).smul_const (1 : EndH) using 1
      ext n x <;> rw [smul_pow_even_of_sq_eq_neg_one G hSq t n] <;>
        simp [div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm, mul_assoc]
    · convert (Real.hasSum_sin t).smul_const G using 1
      ext n x <;> rw [smul_pow_odd_of_sq_eq_neg_one G hSq t n] <;>
        simp [div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  simpa using hsum.tsum_eq

private lemma modularConjugationJ_sq_mul :
    (modularConjugationJ (E := E) : EndH) * modularConjugationJ (E := E) = (1 : EndH) := by
  change (modularConjugationJ (E := E)).comp (modularConjugationJ (E := E))
      = ContinuousLinearMap.id ℝ H₂
  simpa using modularConjugationJ_sq (E := E)

private lemma modularSignEpsilon_sq_mul :
    (modularSignEpsilon (E := E) : EndH) * modularSignEpsilon (E := E) = (1 : EndH) := by
  change (modularSignEpsilon (E := E)).comp (modularSignEpsilon (E := E))
      = ContinuousLinearMap.id ℝ H₂
  simpa using modularSignEpsilon_sq (E := E)

private lemma modularComplexI_sq_mul :
    (Kop : EndH) * Kop = -(1 : EndH) := by
  change (modularComplexI (E := E)).comp (modularComplexI (E := E))
      = -(ContinuousLinearMap.id ℝ H₂)
  simpa using modularComplexI_sq (E := E)

theorem JBoost_eq_cosh_add_sinh_J
    (t : ℝ) :
    JBoost (E := E) t
      = Real.cosh t • (1 : EndH) + Real.sinh t • modularConjugationJ (E := E) := by
  unfold JBoost
  exact exp_eq_cosh_add_sinh_of_sq_eq_one (E := E) modularConjugationJ_sq_mul t

theorem epsilonBoost_eq_cosh_add_sinh_eps
    (t : ℝ) :
    epsilonBoost (E := E) t
      = Real.cosh t • (1 : EndH) + Real.sinh t • modularSignEpsilon (E := E) := by
  unfold epsilonBoost
  exact exp_eq_cosh_add_sinh_of_sq_eq_one (E := E) modularSignEpsilon_sq_mul t

theorem KRotation_eq_cos_add_sin_K
    (t : ℝ) :
    KRotation (E := E) t
      = Real.cos t • (1 : EndH) + Real.sin t • modularComplexI (E := E) := by
  unfold KRotation
  exact exp_eq_cos_add_sin_of_sq_eq_neg_one (E := E) modularComplexI_sq_mul t

@[simp] theorem JBoost_apply
    (t : ℝ) (ψ : H₂) :
    JBoost (E := E) t ψ = (Real.cosh t) • ψ + (Real.sinh t) • (modularConjugationJ (E := E) ψ) := by
  rw [JBoost_eq_cosh_add_sinh_J (E := E) t]
  simp

@[simp] theorem epsilonBoost_apply
    (t : ℝ) (ψ : H₂) :
    epsilonBoost (E := E) t ψ =
      (Real.cosh t) • ψ + (Real.sinh t) • (modularSignEpsilon (E := E) ψ) := by
  rw [epsilonBoost_eq_cosh_add_sinh_eps (E := E) t]
  simp

@[simp] theorem KRotation_apply
    (t : ℝ) (ψ : H₂) :
    KRotation (E := E) t ψ = (Real.cos t) • ψ + (Real.sin t) • (modularComplexI (E := E) ψ) := by
  rw [KRotation_eq_cos_add_sin_K (E := E) t]
  simp

theorem epsilon_comp_epsilonBoost
    (t : ℝ) :
    (modularSignEpsilon (E := E)).comp (epsilonBoost (E := E) t)
      = (epsilonBoost (E := E) t).comp (modularSignEpsilon (E := E)) := by
  rw [epsilonBoost_eq_cosh_add_sinh_eps (E := E) t]
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;> simp [TomitaTakesaki.modularSignEpsilon]

theorem epsilon_comp_JBoost
    (t : ℝ) :
    (modularSignEpsilon (E := E)).comp (JBoost (E := E) t)
      = (JBoost (E := E) (-t)).comp (modularSignEpsilon (E := E)) := by
  rw [JBoost_eq_cosh_add_sinh_J (E := E) t, JBoost_eq_cosh_add_sinh_J (E := E) (-t)]
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [TomitaTakesaki.modularSignEpsilon, TomitaTakesaki.modularConjugationJ,
      Real.cosh_neg, Real.sinh_neg]

theorem epsilon_comp_KRotation
    (t : ℝ) :
    (modularSignEpsilon (E := E)).comp (KRotation (E := E) t)
      = (KRotation (E := E) (-t)).comp (modularSignEpsilon (E := E)) := by
  rw [KRotation_eq_cos_add_sin_K (E := E) t, KRotation_eq_cos_add_sin_K (E := E) (-t)]
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [TomitaTakesaki.modularSignEpsilon, TomitaTakesaki.modularComplexI,
      Real.cos_neg, Real.sin_neg]




end Basic

end InfoGeometry.Canonical.BogoliubovClosedForms

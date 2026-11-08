import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.BogoliubovClosedForms

open BogoliubovTransport
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Krein

section Basic

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "Kop" => InfoGeometry.Krein.clockAxis (E := E)

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

omit [CompleteSpace E] in
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

omit [CompleteSpace E] in
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

omit [CompleteSpace E] in
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
                simp [mul_comm]
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
              have hn :
                  (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ n * (-1 : ℝ) := by
                rw [pow_succ]
              have ht :
                  t ^ (2 * (n + 1)) = t ^ (2 * n) * t ^ 2 := by
                rw [show 2 * (n + 1) = 2 * n + 2 by omega]
                rw [pow_add]
              rw [hn, ht]
              ring

omit [CompleteSpace E] in
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

omit [CompleteSpace E] in
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
        simp [div_eq_mul_inv, smul_smul, mul_comm]
    · convert (Real.hasSum_sinh t).smul_const G using 1
      ext n x <;> rw [smul_pow_odd_of_sq_eq_one G hSq t n] <;>
        simp [div_eq_mul_inv, smul_smul, mul_comm]
  exact hsum.tsum_eq

omit [CompleteSpace E] in
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
        simp [div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm]
    · convert (Real.hasSum_sin t).smul_const G using 1
      ext n x <;> rw [smul_pow_odd_of_sq_eq_neg_one G hSq t n] <;>
        simp [div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm]
  exact hsum.tsum_eq

private lemma modularConjugationJ_sq_mul :
    (modularConjugationJ (E := E) : EndH) * modularConjugationJ (E := E) = (1 : EndH) := by
  change (modularConjugationJ (E := E)).comp (modularConjugationJ (E := E))
      = ContinuousLinearMap.id ℝ H₂
  exact modularConjugationJ_sq (E := E)

private lemma modularSignEpsilon_sq_mul :
    (modularSignEpsilon (E := E) : EndH) * modularSignEpsilon (E := E) = (1 : EndH) := by
  change (modularSignEpsilon (E := E)).comp (modularSignEpsilon (E := E))
      = ContinuousLinearMap.id ℝ H₂
  exact modularSignEpsilon_sq (E := E)

private lemma modularComplexI_sq_mul :
    (Kop : EndH) * Kop = -(1 : EndH) := by
  change (InfoGeometry.Krein.clockAxis (E := E)).comp (InfoGeometry.Krein.clockAxis (E := E))
      = -(ContinuousLinearMap.id ℝ H₂)
  exact InfoGeometry.Krein.clockAxis_sq (E := E)

theorem JBoost_eq_cosh_add_sinh_J
    (t : ℝ) :
    JBoost (E := E) t
      = Real.cosh t • (1 : EndH) + Real.sinh t • modularConjugationJ (E := E) := by
  unfold JBoost
  exact exp_eq_cosh_add_sinh_of_sq_eq_one (E := E) modularConjugationJ_sq_mul t

theorem JBoost_eq_cosh_add_sinh_modular_j
    (t : ℝ) :
    JBoost (E := E) t
      = Real.cosh t • (1 : EndH) + Real.sinh t • modular_j (E := E) := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_eq_modular_j] using
    JBoost_eq_cosh_add_sinh_J (E := E) t

theorem epsilonBoost_eq_cosh_add_sinh_eps
    (t : ℝ) :
    epsilonBoost (E := E) t
      = Real.cosh t • (1 : EndH) + Real.sinh t • modularSignEpsilon (E := E) := by
  unfold epsilonBoost
  exact exp_eq_cosh_add_sinh_of_sq_eq_one (E := E) modularSignEpsilon_sq_mul t

theorem epsilonBoost_eq_cosh_add_sinh_spectral_epsilon
    (t : ℝ) :
    epsilonBoost (E := E) t
      = Real.cosh t • (1 : EndH) + Real.sinh t • spectral_epsilon (E := E) := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon] using
    epsilonBoost_eq_cosh_add_sinh_eps (E := E) t

theorem KRotation_eq_cos_add_sin_K
    (t : ℝ) :
    KRotation (E := E) t
      = Real.cos t • (1 : EndH) + Real.sin t • InfoGeometry.Krein.clockAxis (E := E) := by
  unfold KRotation
  exact exp_eq_cos_add_sin_of_sq_eq_neg_one (E := E) modularComplexI_sq_mul t

theorem KRotation_eq_cos_add_sin_complex_i
    (t : ℝ) :
    KRotation (E := E) t
      = Real.cos t • (1 : EndH) + Real.sin t • complex_i (E := E) := by
  simpa [InfoGeometry.Krein.clockAxis_eq_complex_i] using
    KRotation_eq_cos_add_sin_K (E := E) t

@[simp] theorem JBoost_apply
    (t : ℝ) (ψ : H₂) :
    JBoost (E := E) t ψ = (Real.cosh t) • ψ + (Real.sinh t) • (modularConjugationJ (E := E) ψ) := by
  rw [JBoost_eq_cosh_add_sinh_J (E := E) t]
  simp

@[simp] theorem JBoost_apply_modular_j
    (t : ℝ) (ψ : H₂) :
    JBoost (E := E) t ψ = (Real.cosh t) • ψ + (Real.sinh t) • (modular_j (E := E) ψ) := by
  simp [InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_eq_modular_j]

@[simp] theorem epsilonBoost_apply
    (t : ℝ) (ψ : H₂) :
    epsilonBoost (E := E) t ψ =
      (Real.cosh t) • ψ + (Real.sinh t) • (modularSignEpsilon (E := E) ψ) := by
  rw [epsilonBoost_eq_cosh_add_sinh_eps (E := E) t]
  simp

@[simp] theorem epsilonBoost_apply_spectral_epsilon
    (t : ℝ) (ψ : H₂) :
    epsilonBoost (E := E) t ψ =
      (Real.cosh t) • ψ + (Real.sinh t) • (spectral_epsilon (E := E) ψ) := by
  simp [InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon]

@[simp] theorem KRotation_apply
    (t : ℝ) (ψ : H₂) :
    KRotation (E := E) t ψ = (Real.cos t) • ψ + (Real.sin t) • (InfoGeometry.Krein.clockAxis (E := E) ψ) := by
  rw [KRotation_eq_cos_add_sin_K (E := E) t]
  simp

@[simp] theorem KRotation_apply_complex_i
    (t : ℝ) (ψ : H₂) :
    KRotation (E := E) t ψ = (Real.cos t) • ψ + (Real.sin t) • (complex_i (E := E) ψ) := by
  simp

/--
Phase-linear operators commute with the exact exponential phase propagator.
The only local coordinate on this transport branch is the exponential time
parameter `t`.
-/
theorem comp_KRotation_eq_KRotation_comp_of_IsPhaseLinear
    (A : EndH)
    (hA : IsPhaseLinear (E := E) A)
    (t : ℝ) :
    A.comp (KRotation (E := E) t) = (KRotation (E := E) t).comp A := by
  apply ContinuousLinearMap.ext
  intro x
  have hA_eval : A (InfoGeometry.Krein.clockAxis (E := E) x) = InfoGeometry.Krein.clockAxis (E := E) (A x) := by
    have h := congrArg (fun T : EndH => T x) hA
    simpa [IsPhaseLinear, ContinuousLinearMap.comp_apply] using h
  have hA_eval' :
      A (WithLp.toLp (2 : ENNReal) (-WithLp.snd x, WithLp.fst x))
        =
      WithLp.toLp (2 : ENNReal) (-WithLp.snd (A x), WithLp.fst (A x)) := by
    simpa [InfoGeometry.Krein.clockAxis] using hA_eval
  simp [ContinuousLinearMap.comp_apply, KRotation_apply, map_add, map_smul, hA_eval']

/--
Phase-antilinear operators intertwine the exact exponential phase propagator
with sign-reversed time.
-/
theorem comp_KRotation_eq_KRotation_neg_comp_of_IsPhaseAntilinear
    (A : EndH)
    (hA : IsPhaseAntilinear (E := E) A)
    (t : ℝ) :
    A.comp (KRotation (E := E) t) = (KRotation (E := E) (-t)).comp A := by
  apply ContinuousLinearMap.ext
  intro x
  have hA_eval :
      A (InfoGeometry.Krein.clockAxis (E := E) x) = -((InfoGeometry.Krein.clockAxis (E := E)) (A x)) := by
    have h := congrArg (fun T : EndH => T x) hA
    simpa [IsPhaseAntilinear, ContinuousLinearMap.comp_apply] using h
  have hA_eval' :
      A (WithLp.toLp (2 : ENNReal) (-WithLp.snd x, WithLp.fst x))
        =
      -WithLp.toLp (2 : ENNReal) (-WithLp.snd (A x), WithLp.fst (A x)) := by
    simpa [InfoGeometry.Krein.clockAxis] using hA_eval
  simp [ContinuousLinearMap.comp_apply, KRotation_apply, map_add, map_smul,
    Real.cos_neg, Real.sin_neg, neg_smul, hA_eval']

/--
The mixed left/right phase propagator pairing collapses exactly to the identity
for the doubled Krein form.
-/
theorem kreinInner_KRotation_neg_left_KRotation_right
    (t : ℝ) (u v : H₂) :
    KreinSpace.kreinInner (H := H₂)
        (KRotation (E := E) (-t) u)
        (KRotation (E := E) t v)
      =
    KreinSpace.kreinInner (H := H₂) u v := by
  have hClock :
      (InfoGeometry.Krein.clockAxis (E := E) : EndH) = (modularComplexI (E := E) : EndH) := by
    calc
      (InfoGeometry.Krein.clockAxis (E := E) : EndH)
          =
        (complex_i (E := E) : EndH) := by
            simp [InfoGeometry.Krein.clockAxis]
      _ = (modularComplexI (E := E) : EndH) := by
            exact (InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i (E := E)).symm
  rw [KRotation_apply, KRotation_apply, Real.cos_neg, Real.sin_neg, neg_smul]
  rw [hClock]
  repeat rw [KreinSpace.kreinInner_add_left, KreinSpace.kreinInner_add_right]
  repeat rw [KreinSpace.kreinInner_smul_left, KreinSpace.kreinInner_smul_right]
  rw [show -(Real.sin t • modularComplexI (E := E) u) = (-Real.sin t) • modularComplexI (E := E) u by simp]
  rw [KreinSpace.kreinInner_smul_left, KreinSpace.kreinInner_add_right]
  repeat rw [KreinSpace.kreinInner_smul_right]
  rw [InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_kreinInner_swap (E := E) u v]
  rw [InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_kreinInner_comp (E := E) u v]
  ring_nf
  have hcossin : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  let g : ℝ := KreinSpace.kreinInner (H := H₂) u v
  change Real.cos t ^ 2 * g + g * Real.sin t ^ 2 = g
  calc
    Real.cos t ^ 2 * g + g * Real.sin t ^ 2 = g * (Real.cos t ^ 2 + Real.sin t ^ 2) := by ring
    _ = g := by rw [hcossin]; ring

theorem epsilon_comp_epsilonBoost
    (t : ℝ) :
    (modularSignEpsilon (E := E)).comp (epsilonBoost (E := E) t)
      = (epsilonBoost (E := E) t).comp (modularSignEpsilon (E := E)) := by
  rw [epsilonBoost_eq_cosh_add_sinh_eps (E := E) t]
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;> simp [InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon]

theorem spectral_epsilon_comp_epsilonBoost
    (t : ℝ) :
    (spectral_epsilon (E := E)).comp (epsilonBoost (E := E) t)
      = (epsilonBoost (E := E) t).comp (spectral_epsilon (E := E)) := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon] using
    epsilon_comp_epsilonBoost (E := E) t

theorem epsilon_comp_JBoost
    (t : ℝ) :
    (modularSignEpsilon (E := E)).comp (JBoost (E := E) t)
      = (JBoost (E := E) (-t)).comp (modularSignEpsilon (E := E)) := by
  rw [JBoost_eq_cosh_add_sinh_J (E := E) t, JBoost_eq_cosh_add_sinh_J (E := E) (-t)]
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon, InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ,
      Real.cosh_neg, Real.sinh_neg]

theorem spectral_epsilon_comp_JBoost
    (t : ℝ) :
    (spectral_epsilon (E := E)).comp (JBoost (E := E) t)
      = (JBoost (E := E) (-t)).comp (spectral_epsilon (E := E)) := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon] using
    epsilon_comp_JBoost (E := E) t

theorem epsilon_comp_KRotation
    (t : ℝ) :
    (modularSignEpsilon (E := E)).comp (KRotation (E := E) t)
      = (KRotation (E := E) (-t)).comp (modularSignEpsilon (E := E)) := by
  rw [KRotation_eq_cos_add_sin_K (E := E) t, KRotation_eq_cos_add_sin_K (E := E) (-t)]
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon,
      Real.cos_neg, Real.sin_neg]

theorem spectral_epsilon_comp_KRotation
    (t : ℝ) :
    (spectral_epsilon (E := E)).comp (KRotation (E := E) t)
      = (KRotation (E := E) (-t)).comp (spectral_epsilon (E := E)) := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon] using
    epsilon_comp_KRotation (E := E) t




end Basic

end InfoGeometry.Canonical.BogoliubovClosedForms

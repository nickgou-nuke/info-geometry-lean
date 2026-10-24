/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveRotorMotion
import InfoGeometry.Canonical.ModularFlowGeneratorDerivative
import InfoGeometry.Algebra.UnipotentReflexivePairFactorization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Real-time motion of the native reflexive rotor

The native ReflexiveRotorMotion import supplies the algebraic identities.
The actual sine/cosine curve and existing conjugationPath are differentiated in
a normed real algebra. No completeness, exponential identification, supplied
analytic law, or star-projection hypothesis is used.
-/
noncomputable section

namespace InfoGeometry.Canonical.ReflexiveRotorRealTime

open ReflexiveNilpotentFlows GrassmannianBundleCyclotomicOrientability
open ModularFlowGeneratorDerivative

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The existing rotor evaluated on the actual real circle. -/
def realRotor (d B : A) (t : ℝ) : A := rotor (Real.cos t) (Real.sin t) d B

theorem realRotor_zero (d B : A) : realRotor d B 0 = 1 := by
  simp [realRotor, rotor, complement]

theorem realRotor_neg (d B : A) (t : ℝ) :
    realRotor d B (-t) = rotor (Real.cos t) (-Real.sin t) d B := by
  simp only [realRotor, Real.cos_neg, Real.sin_neg]

/-- This derivative needs no square-zero or reflexive assumptions. -/
theorem hasDerivAt_realRotor_coefficients (d B : A) (t : ℝ) :
    HasDerivAt (realRotor d B)
      ((-Real.sin t) • support d B + Real.cos t • (d-B)) t := by
  have h := ((hasDerivAt_const t (complement d B)).add
    ((Real.hasDerivAt_cos t).smul_const (support d B))).add
      ((Real.hasDerivAt_sin t).smul_const (d-B))
  have hpath :
      (((fun _ : ℝ => complement d B) + fun s => Real.cos s • support d B) +
        fun s => Real.sin s • (d-B)) = realRotor d B := by
    funext s
    simp only [Pi.add_apply, realRotor, rotor]
  rw [hpath] at h
  simpa only [zero_add] using h

theorem continuous_realRotor (d B : A) : Continuous (realRotor d B) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (hasDerivAt_realRotor_coefficients d B t).continuousAt)

/-- Continuity of the actual native conjugation path, for every ambient element. -/
theorem continuous_rotorOrbit (d B X : A) :
    Continuous (conjugationPath (realRotor d B) (fun t => realRotor d B (-t)) X) := by
  exact ((continuous_realRotor d B).mul continuous_const).mul
    ((continuous_realRotor d B).comp continuous_neg)

variable {d B : A}
variable (hd : d*d=0) (hB : B*B=0) (hr : d*B*d=d) (hs : B*d*B=B)
include hd hB hr hs

/-- The derivative coefficient is left multiplication by the native skew generator. -/
theorem realRotor_generator_left (t : ℝ) :
    (d-B)*realRotor d B t =
      (-Real.sin t) • support d B + Real.cos t • (d-B) := by
  have hJS : (d-B)*support d B = d-B :=
    InfoGeometry.Algebra.UnipotentReflexivePairFactorization.skew_mul_support hd hB hr hs
  have hJJ : (d-B)*(d-B) = -support d B :=
    InfoGeometry.Algebra.UnipotentReflexivePairFactorization.skew_square hd hB
  have hJC : (d-B)*complement d B = 0 := by
    rw [complement, mul_sub, mul_one, hJS, sub_self]
  simp only [realRotor, rotor, mul_add, mul_smul_comm, hJC, hJS, hJJ,
    zero_add, smul_neg, neg_smul]
  abel

theorem realRotor_generator_right (t : ℝ) :
    realRotor d B t * (d-B) =
      (-Real.sin t) • support d B + Real.cos t • (d-B) := by
  have hSJ : support d B*(d-B) = d-B :=
    InfoGeometry.Algebra.UnipotentReflexivePairFactorization.support_mul_skew hd hB hr hs
  have hJJ : (d-B)*(d-B) = -support d B :=
    InfoGeometry.Algebra.UnipotentReflexivePairFactorization.skew_square hd hB
  have hCJ : complement d B*(d-B) = 0 := by
    rw [complement, sub_mul, one_mul, hSJ, sub_self]
  unfold realRotor rotor
  rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, hCJ, hSJ, hJJ]
  simp only [zero_add, smul_neg, neg_smul]
  abel

theorem realRotor_generator_commute (t : ℝ) :
    (d-B)*realRotor d B t = realRotor d B t*(d-B) :=
  (realRotor_generator_left hd hB hr hs t).trans
    (realRotor_generator_right hd hB hr hs t).symm

theorem hasDerivAt_realRotor (t : ℝ) :
    HasDerivAt (realRotor d B) ((d-B)*realRotor d B t) t := by
  rw [realRotor_generator_left hd hB hr hs]
  exact hasDerivAt_realRotor_coefficients d B t

theorem hasDerivAt_reverseRotor (t : ℝ) :
    HasDerivAt (fun s => realRotor d B (-s))
      (-(realRotor d B (-t)*(d-B))) t := by
  have h := (hasDerivAt_realRotor hd hB hr hs (-t)).scomp t (hasDerivAt_neg t)
  simpa only [Function.comp_def, neg_one_smul,
    realRotor_generator_commute hd hB hr hs (-t)] using h

/-- Product differentiation on the existing conjugationPath, with no assumed flow law. -/
theorem hasDerivAt_rotorOrbit (X : A) (t : ℝ) :
    HasDerivAt (conjugationPath (realRotor d B) (fun s => realRotor d B (-s)) X)
      (lieBracket (d-B)
        (conjugationPath (realRotor d B) (fun s => realRotor d B (-s)) X t)) t := by
  have h := hasDerivAt_conjugationPath (realRotor d B)
    (fun s => realRotor d B (-s)) ((d-B)*realRotor d B t)
    (-(realRotor d B (-t)*(d-B))) X t
    (hasDerivAt_realRotor hd hB hr hs t) (hasDerivAt_reverseRotor hd hB hr hs t)
  simpa only [conjugationPath, lieBracket, mul_neg, sub_eq_add_neg, mul_assoc] using h

/-- The real derivative at zero has the negative Q sign. -/
theorem hasDerivAt_plus_zero :
    HasDerivAt (conjugationPath (realRotor d B) (fun t => realRotor d B (-t)) (d*B))
      (-(d+B)) 0 := by
  simpa only [conjugationPath, neg_zero, realRotor_zero, one_mul, mul_one,
    skew_commutator_plus hd hB hr hs] using hasDerivAt_rotorOrbit hd hB hr hs (d*B) 0

/-- Commutators pass through this actual rotor conjugation because J commutes with U. -/
theorem lieBracket_rotorOrbit (X : A) (t : ℝ) :
    lieBracket (d-B)
      (conjugationPath (realRotor d B) (fun s => realRotor d B (-s)) X t) =
    conjugationPath (realRotor d B) (fun s => realRotor d B (-s))
      (lieBracket (d-B) X) t := by
  unfold lieBracket conjugationPath
  calc
    _ = ((d-B)*realRotor d B t)*X*realRotor d B (-t) -
      realRotor d B t*X*(realRotor d B (-t)*(d-B)) := by noncomm_ring
    _ = _ := by
      rw [realRotor_generator_commute hd hB hr hs t,
        ← realRotor_generator_commute hd hB hr hs (-t)]
      simp only [mul_sub, sub_mul, mul_assoc]

/-- The derivative of the actual first derivative is the double commutator. -/
theorem hasDerivAt_deriv_rotorOrbit (X : A) (t : ℝ) :
    HasDerivAt
      (deriv (conjugationPath (realRotor d B) (fun s => realRotor d B (-s)) X))
      (lieBracket (d-B) (lieBracket (d-B)
        (conjugationPath (realRotor d B) (fun s => realRotor d B (-s)) X t))) t := by
  have hfun : deriv (conjugationPath (realRotor d B) (fun s => realRotor d B (-s)) X) =
      fun s => lieBracket (d-B)
        (conjugationPath (realRotor d B) (fun u => realRotor d B (-u)) X s) := by
    funext s
    exact (hasDerivAt_rotorOrbit hd hB hr hs X s).deriv
  rw [hfun]
  have h := hasDerivAt_rotorOrbit hd hB hr hs X t
  have hdiff := (h.const_mul (d-B)).sub (h.mul_const (d-B))
  have hpath :
      ((fun s => (d-B) *
        conjugationPath (realRotor d B) (fun u => realRotor d B (-u)) X s) -
       fun s => conjugationPath (realRotor d B) (fun u => realRotor d B (-u)) X s *
        (d-B)) =
      (fun s => lieBracket (d-B)
        (conjugationPath (realRotor d B) (fun u => realRotor d B (-u)) X s)) := by
    funext s
    simp only [Pi.sub_apply, lieBracket]
  rw [hpath] at hdiff
  exact hdiff

/-- Parity orbit is twice the plus orbit minus its fixed active support. -/
theorem rotorOrbit_parity (t : ℝ) :
    conjugationPath (realRotor d B) (fun s => realRotor d B (-s)) (d*B-B*d) t =
      (2:A)*conjugationPath (realRotor d B) (fun s => realRotor d B (-s)) (d*B) t -
        support d B := by
  have hc : Real.cos t * Real.cos t + Real.sin t * Real.sin t = 1 := by
    simpa only [pow_two] using Real.cos_sq_add_sin_sq t
  have hsum := rotor_projector_sum hd hB hr hs (Real.cos t) (Real.sin t) hc
  change realRotor d B t*(d*B)*rotor (Real.cos t) (-Real.sin t) d B +
    realRotor d B t*(B*d)*rotor (Real.cos t) (-Real.sin t) d B = support d B at hsum
  rw [← realRotor_neg d B t] at hsum
  unfold conjugationPath
  rw [← hsum]
  noncomm_ring

/-- Algebraic polarization on the actual parity orbit. -/
theorem double_commutator_parityOrbit (t : ℝ) :
    lieBracket (d-B) (lieBracket (d-B)
      (conjugationPath (realRotor d B) (fun s => realRotor d B (-s)) (d*B-B*d) t)) =
    -(4:A)*conjugationPath (realRotor d B) (fun s => realRotor d B (-s)) (d*B-B*d) t := by
  rw [lieBracket_rotorOrbit hd hB hr hs, lieBracket_rotorOrbit hd hB hr hs,
    skew_double_commutator_parity hd hB hr hs]
  unfold conjugationPath
  noncomm_ring

/-- The projector oscillator has a support offset; it is not P'' = -4P. -/
theorem double_commutator_plusOrbit (t : ℝ) :
    lieBracket (d-B) (lieBracket (d-B)
      (conjugationPath (realRotor d B) (fun s => realRotor d B (-s)) (d*B) t)) =
    (2:A)*support d B -
      (4:A)*conjugationPath (realRotor d B) (fun s => realRotor d B (-s)) (d*B) t := by
  rw [lieBracket_rotorOrbit hd hB hr hs, lieBracket_rotorOrbit hd hB hr hs,
    skew_commutator_plus hd hB hr hs]
  have hb : lieBracket (d-B) (-(d+B)) = -(2:A)*(d*B-B*d) := by
    calc
      _ = -lieBracket (d-B) (d+B) := by unfold lieBracket; noncomm_ring
      _ = _ := by rw [skew_commutator_sum]; noncomm_ring
  rw [hb]
  calc
    _ = -(2:A)*conjugationPath (realRotor d B) (fun s => realRotor d B (-s))
        (d*B-B*d) t := by unfold conjugationPath; noncomm_ring
    _ = _ := by rw [rotorOrbit_parity hd hB hr hs]; noncomm_ring

/-- Actual second derivative of the parity trajectory. -/
theorem hasDerivAt_deriv_parityOrbit (t : ℝ) :
    HasDerivAt
      (deriv (conjugationPath (realRotor d B) (fun s => realRotor d B (-s)) (d*B-B*d)))
      (-(4:A)*conjugationPath (realRotor d B) (fun s => realRotor d B (-s)) (d*B-B*d) t) t := by
  have h := hasDerivAt_deriv_rotorOrbit hd hB hr hs (d*B-B*d) t
  rw [double_commutator_parityOrbit hd hB hr hs] at h
  exact h

/-- Actual second derivative of the plus-idempotent trajectory. -/
theorem hasDerivAt_deriv_plusOrbit (t : ℝ) :
    HasDerivAt
      (deriv (conjugationPath (realRotor d B) (fun s => realRotor d B (-s)) (d*B)))
      ((2:A)*support d B -
        (4:A)*conjugationPath (realRotor d B) (fun s => realRotor d B (-s)) (d*B) t) t := by
  have h := hasDerivAt_deriv_rotorOrbit hd hB hr hs (d*B) t
  rw [double_commutator_plusOrbit hd hB hr hs] at h
  exact h

end InfoGeometry.Canonical.ReflexiveRotorRealTime

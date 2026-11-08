/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.ChiralPoincareSouriauBridge
import InfoGeometry.Twistor.InfinityTwistor

/-!
# Spinor-helicity identities on the native complex momentum carrier

The bracket is the existing infinity alternating form restricted to its lower
spinor plane. Momenta are the existing `spinorOuter` matrices. The determinant
identity fixes the angle/square sign without assuming a normalization for a
separately defined Lorentz pairing. Nonzero momentum factorizations form one
inverse-scaling orbit. No amplitude or Lorentzian reality condition is assumed.

Reference: Witten, hep-th/0312171v2, equations (2.3)--(2.7).
-/

namespace InfoGeometry.Twistor.WittenSpinorHelicity

open InfoGeometry.Physics.ChiralPoincareSouriauBridge
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.InfinityTwistor

/-- The native infinity form restricted to the lower-spinor plane. -/
def spinorBracket (lambda mu : Spinor2) : ℂ :=
  infinityTwistor (0, lambda) (0, mu)

@[simp] theorem spinorBracket_apply (lambda mu : Spinor2) :
    spinorBracket lambda mu = lambda 0 * mu 1 - lambda 1 * mu 0 := rfl

@[simp] theorem spinorBracket_self (lambda : Spinor2) :
    spinorBracket lambda lambda = 0 := by
  exact infinityTwistor_self (0, lambda)

theorem spinorBracket_swap (lambda mu : Spinor2) :
    spinorBracket mu lambda = -spinorBracket lambda mu := by
  exact infinityTwistor_swap (0, lambda) (0, mu)

theorem spinorBracket_smul (c d : ℂ) (lambda mu : Spinor2) :
    spinorBracket (c • lambda) (d • mu) =
      (c * d) * spinorBracket lambda mu := by
  simp only [spinorBracket_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The two-component Schouten identity is a genuine spinor equality. -/
theorem spinorBracket_schouten (lambda mu nu : Spinor2) :
    spinorBracket lambda mu • nu + spinorBracket mu nu • lambda +
      spinorBracket nu lambda • mu = 0 := by
  funext i
  fin_cases i
  · change (lambda 0 * mu 1 - lambda 1 * mu 0) * nu 0 +
      (mu 0 * nu 1 - mu 1 * nu 0) * lambda 0 +
      (nu 0 * lambda 1 - nu 1 * lambda 0) * mu 0 = 0
    ring
  · change (lambda 0 * mu 1 - lambda 1 * mu 0) * nu 1 +
      (mu 0 * nu 1 - mu 1 * nu 0) * lambda 1 +
      (nu 0 * lambda 1 - nu 1 * lambda 0) * mu 1 = 0
    ring

/-- The Mandelstam determinant for two independent complex null momenta. -/
theorem det_sum_spinorOuter
    (lambda mu lambdaTilde muTilde : Spinor2) :
    (spinorOuter lambda lambdaTilde + spinorOuter mu muTilde).det =
      spinorBracket lambda mu * spinorBracket lambdaTilde muTilde := by
  simp [spinorOuter, Matrix.det_fin_two]
  ring

/-- Both factors scale independently in the existing rank-one matrix. -/
theorem spinorOuter_smul (c d : ℂ) (lambda lambdaTilde : Spinor2) :
    spinorOuter (c • lambda) (d • lambdaTilde) =
      (c * d) • spinorOuter lambda lambdaTilde := by
  ext i j
  simp [spinorOuter, smul_eq_mul]
  ring

/-- Nonzero inverse scalings preserve the momentum itself. -/
theorem spinorOuter_littleGroup (c : ℂ) (hc : c ≠ 0)
    (lambda lambdaTilde : Spinor2) :
    spinorOuter (c • lambda) (c⁻¹ • lambdaTilde) =
      spinorOuter lambda lambdaTilde := by
  rw [spinorOuter_smul, mul_inv_cancel₀ hc, one_smul]

theorem spinor_exists_nonzero_coordinate (lambda : Spinor2)
    (hlambda : lambda ≠ 0) : ∃ i, lambda i ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply hlambda
  funext i
  exact h i

/-- A rank-one momentum vanishes exactly when one spinor factor vanishes. -/
theorem spinorOuter_eq_zero_iff (lambda lambdaTilde : Spinor2) :
    spinorOuter lambda lambdaTilde = 0 ↔ lambda = 0 ∨ lambdaTilde = 0 := by
  constructor
  · intro h
    by_cases hlambda : lambda = 0
    · exact Or.inl hlambda
    · right
      obtain ⟨i, hi⟩ := spinor_exists_nonzero_coordinate lambda hlambda
      funext j
      have hij := congrArg (fun M : M2C => M i j) h
      change lambda i * lambdaTilde j = 0 at hij
      exact (mul_eq_zero.mp hij).resolve_left hi
  · rintro (rfl | rfl) <;> ext i j <;> simp [spinorOuter]

/-- Two nonzero rank-one factorizations differ by inverse scalar factors.
The proof uses a nonzero matrix entry, not a chosen normalization field. -/
theorem exists_littleGroup_scale
    (lambda lambdaTilde mu muTilde : Spinor2)
    (hlambda : lambda ≠ 0) (hlambdaTilde : lambdaTilde ≠ 0)
    (h : spinorOuter lambda lambdaTilde = spinorOuter mu muTilde) :
    ∃ c : ℂ, c ≠ 0 ∧ mu = c • lambda ∧ muTilde = c⁻¹ • lambdaTilde := by
  obtain ⟨i, hi⟩ := spinor_exists_nonzero_coordinate lambda hlambda
  obtain ⟨j, hj⟩ := spinor_exists_nonzero_coordinate lambdaTilde hlambdaTilde
  have hentry (a b : Fin 2) : lambda a * lambdaTilde b = mu a * muTilde b :=
    congrArg (fun M : M2C => M a b) h
  have hprod : mu i * muTilde j ≠ 0 := by
    rw [← hentry i j]
    exact mul_ne_zero hi hj
  have hmi : mu i ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hmtj : muTilde j ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  refine ⟨mu i / lambda i, div_ne_zero hmi hi, ?_, ?_⟩
  · funext a
    change mu a = (mu i / lambda i) * lambda a
    have hcross : mu a * lambda i = mu i * lambda a := by
      apply mul_right_cancel₀ hmtj
      linear_combination -(lambda i) * (hentry a j) +
        (lambda a) * (hentry i j)
    field_simp [hi]
    exact hcross
  · funext b
    change muTilde b = (mu i / lambda i)⁻¹ * lambdaTilde b
    field_simp [hi, hmi]
    linear_combination -(hentry i b)

/-- The inverse-scaling parameter is itself unique when the first spinor is nonzero. -/
theorem littleGroup_scale_unique (lambda mu : Spinor2) (hlambda : lambda ≠ 0)
    {c d : ℂ} (hc : mu = c • lambda) (hd : mu = d • lambda) : c = d := by
  obtain ⟨i, hi⟩ := spinor_exists_nonzero_coordinate lambda hlambda
  apply mul_right_cancel₀ hi
  exact congrArg (fun v : Spinor2 => v i) (hc.symm.trans hd)

/-- The fiber over a nonzero null momentum is one free little-group orbit. -/
theorem existsUnique_littleGroup_scale
    (lambda lambdaTilde mu muTilde : Spinor2)
    (hP : spinorOuter lambda lambdaTilde ≠ 0)
    (h : spinorOuter lambda lambdaTilde = spinorOuter mu muTilde) :
    ∃! c : ℂ, c ≠ 0 ∧ mu = c • lambda ∧ muTilde = c⁻¹ • lambdaTilde := by
  have hnonzero : lambda ≠ 0 ∧ lambdaTilde ≠ 0 := by
    exact not_or.mp (mt (spinorOuter_eq_zero_iff lambda lambdaTilde).mpr hP)
  obtain ⟨c, hc, hmu, hmuTilde⟩ :=
    exists_littleGroup_scale lambda lambdaTilde mu muTilde
      hnonzero.1 hnonzero.2 h
  refine ⟨c, ⟨hc, hmu, hmuTilde⟩, ?_⟩
  intro d hd
  exact littleGroup_scale_unique lambda mu hnonzero.1 hd.2.1 hmu

end InfoGeometry.Twistor.WittenSpinorHelicity

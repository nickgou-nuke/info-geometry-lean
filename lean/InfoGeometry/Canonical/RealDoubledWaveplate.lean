/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.ProjectorEquivariance
import InfoGeometry.Canonical.BogoliubovProjectorTransport
import InfoGeometry.Quantum.GeometricTensorTransport
import InfoGeometry.Quantum.RealMajorana

/-!
# The real doubled waveplate

This file records the finite theorem bridge for the already-owned elliptic
phase flow on `DoubledSpace`.  The flow is the existing `phaseFlow`/`KRotation`
action; no new carrier or compatibility datum is introduced here.

The results are separated by their actual hypotheses: the phase flow has an
inverse and preserves the Hilbert/GNS pairing, its chiral projectors have the
existing transported formulas, and CAR covariance follows for every existing
Majorana datum by applying its CAR law to the isometrically transported modes.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.RealDoubledWaveplate

open InfoGeometry.Krein
open InfoGeometry.Canonical.ProjectorEquivariance
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovClosedForms
open InfoGeometry.Canonical.BogoliubovProjectorTransport
open InfoGeometry.Quantum.RealMajorana
open InfoGeometry.Quantum.GeometricQuantumTensor

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

private theorem phaseAxis_eq_clockAxis :
    HestenesI (E := E) = clockAxis (E := E) := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem phaseFlow_eq_KRotation (θ : ℝ) :
    phaseFlow (E := E) θ = KRotation (E := E) θ := by
  apply ContinuousLinearMap.ext
  intro x
  rw [phaseFlow, phaseAxis_eq_clockAxis (E := E)]
  simp [KRotation_apply]

theorem phaseFlow_add (s t : ℝ) :
    phaseFlow (E := E) (s + t) =
      phaseFlow (E := E) s * phaseFlow (E := E) t := by
  rw [phaseFlow_eq_KRotation (E := E), phaseFlow_eq_KRotation (E := E),
    phaseFlow_eq_KRotation (E := E)]
  exact KRotation_add (E := E) s t

theorem phaseFlow_left_inverse (θ : ℝ) :
    phaseFlow (E := E) (-θ) * phaseFlow (E := E) θ = (1 : EndH) := by
  rw [← phaseFlow_add (E := E), neg_add_cancel, phaseFlow_eq_KRotation,
    KRotation_zero]

theorem phaseFlow_right_inverse (θ : ℝ) :
    phaseFlow (E := E) θ * phaseFlow (E := E) (-θ) = (1 : EndH) := by
  rw [← phaseFlow_add (E := E), add_neg_cancel, phaseFlow_eq_KRotation,
    KRotation_zero]

theorem phaseFlow_preserves_inner (θ : ℝ) (u v : H₂) :
    ⟪phaseFlow (E := E) θ u, phaseFlow (E := E) θ v⟫_ℝ = ⟪u, v⟫_ℝ := by
  rw [phaseFlow_eq_KRotation (E := E)]
  exact KRotation_preserves_inner (E := E) θ u v

/-- The phase flow has the explicit equal-weight real coordinate readout at
45 degrees on the existing doubled carrier. -/
theorem phaseFlow_pi_div_four_to_doubled (x y : E) :
    phaseFlow (E := E) (Real.pi / 4)
        (to_doubled x y : H₂) =
      to_doubled ((Real.sqrt 2 / 2) • x - (Real.sqrt 2 / 2) • y)
        ((Real.sqrt 2 / 2) • y + (Real.sqrt 2 / 2) • x) := by
  rw [phaseFlow_eq_KRotation, KRotation_apply]
  apply DoubledSpace.ext <;>
    simp [to_doubled, clockAxis_apply, Real.cos_pi_div_four,
      Real.sin_pi_div_four] <;>
    module

/- The Hilbert adjoint of the phase flow is its inverse flow. -/
theorem phaseFlow_adjoint (θ : ℝ) :
    ContinuousLinearMap.adjoint (phaseFlow (E := E) θ) =
      phaseFlow (E := E) (-θ) := by
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff
    (A := phaseFlow (E := E) (-θ))
    (B := phaseFlow (E := E) θ)).2 ?_
  intro u v
  have hpres := phaseFlow_preserves_inner (E := E) (-θ) u
    (phaseFlow (E := E) θ v)
  have hcomp : phaseFlow (E := E) (-θ)
      (phaseFlow (E := E) θ v) = v := by
    have h := congrArg (fun T : EndH => T v)
      (phaseFlow_left_inverse (E := E) θ)
    simpa [ContinuousLinearMap.mul_apply] using h
  rw [hcomp] at hpres
  exact hpres

theorem phaseFlow_operator_intertwines_of_phaseLinear
    (A : EndH)
    (hA : A.comp (clockAxis (E := E)) = (clockAxis (E := E)).comp A)
    (θ : ℝ) :
    A.comp (phaseFlow (E := E) θ) =
      (phaseFlow (E := E) θ).comp A := by
  rw [phaseFlow_eq_KRotation (E := E)]
  exact comp_KRotation_eq_KRotation_comp_of_IsPhaseLinear
    (E := E) (A := A) hA θ

theorem phaseFlow_operator_intertwines_of_phaseAntilinear
    (A : EndH)
    (hA : A.comp (clockAxis (E := E)) = -((clockAxis (E := E)).comp A))
    (θ : ℝ) :
    A.comp (phaseFlow (E := E) θ) =
      (phaseFlow (E := E) (-θ)).comp A := by
  simp only [phaseFlow_eq_KRotation]
  exact comp_KRotation_eq_KRotation_neg_comp_of_IsPhaseAntilinear
    (E := E) (A := A) hA θ

/- The corresponding expectation value is invariant under the same phase
flow when the observable is phase-linear. -/
theorem phaseFlow_expectation_intertwines_of_phaseLinear
    (A : EndH)
    (hA : A.comp (clockAxis (E := E)) = (clockAxis (E := E)).comp A)
    (θ : ℝ) (u v : H₂) :
    ⟪phaseFlow (E := E) θ u,
      A (phaseFlow (E := E) θ v)⟫_ℝ = ⟪u, A v⟫_ℝ := by
  have hcomm := phaseFlow_operator_intertwines_of_phaseLinear
    (E := E) A hA θ
  have hAv : A (phaseFlow (E := E) θ v) =
      phaseFlow (E := E) θ (A v) := by
    exact congrArg (fun T : EndH => T v) hcomm
  rw [hAv]
  exact phaseFlow_preserves_inner (E := E) θ u (A v)

theorem phaseFlow_plus_projector_transport (θ : ℝ) :
    (spectralPlusProj (E := E)).comp (phaseFlow (E := E) θ) =
      Real.cos θ • (spectralPlusProj (E := E)) +
        Real.sin θ • ((clockAxis (E := E)).comp (spectralMinusProj (E := E))) := by
  rw [phaseFlow_eq_KRotation (E := E)]
  exact spectralPlusProj_comp_KRotation (E := E) θ

theorem phaseFlow_minus_projector_transport (θ : ℝ) :
    (spectralMinusProj (E := E)).comp (phaseFlow (E := E) θ) =
      Real.cos θ • (spectralMinusProj (E := E)) +
        Real.sin θ • ((clockAxis (E := E)).comp (spectralPlusProj (E := E))) := by
  rw [phaseFlow_eq_KRotation (E := E)]
  exact spectralMinusProj_comp_KRotation (E := E) θ

/-!
The phase flow rotates the grading itself.  This is the conjugation law for
the active convention `R(-θ) ε R(θ)`; it is stronger than the one-sided
projector readbacks above and fixes the sign of the transported off-diagonal
axis.
-/
theorem phaseFlow_conj_spectral_epsilon (θ : ℝ) :
    phaseFlow (E := E) (-θ) * spectral_epsilon (E := E) * phaseFlow (E := E) θ =
      Real.cos (2 * θ) • spectral_epsilon (E := E)
        - Real.sin (2 * θ) • modular_j (E := E) := by
  rw [phaseFlow_eq_KRotation (E := E), phaseFlow_eq_KRotation (E := E)]
  rw [KRotation_eq_cos_add_sin_K (E := E) (-θ),
    KRotation_eq_cos_add_sin_K (E := E) θ]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.neg_apply,
    spectral_epsilon_apply, clockAxis_apply, modular_j_apply]
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq θ
  apply DoubledSpace.ext <;>
    simp [Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul]
    <;> simp only [smul_smul]
    <;> ring_nf
    <;> rw [← htrig]
    <;> module

theorem phaseFlow_conj_spectral_epsilon_reverse (θ : ℝ) :
    phaseFlow (E := E) θ * spectral_epsilon (E := E) * phaseFlow (E := E) (-θ) =
      Real.cos (2 * θ) • spectral_epsilon (E := E)
        + Real.sin (2 * θ) • modular_j (E := E) := by
  have h := phaseFlow_conj_spectral_epsilon (E := E) (-θ)
  have harg : 2 * (-θ) = -(2 * θ) := by ring
  rw [harg, Real.cos_neg, Real.sin_neg] at h
  simp only [neg_neg] at h
  rw [sub_eq_add_neg] at h
  have hneg : -((-Real.sin (2 * θ)) • modular_j (E := E)) =
      Real.sin (2 * θ) • modular_j (E := E) := by
    module
  rw [hneg] at h
  simpa [neg_neg, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

/-- At the geometric 45° angle, active conjugation sends the spectral grading
to the negative doubled swap. -/
theorem phaseFlow_conj_spectral_epsilon_pi_div_four :
    phaseFlow (E := E) (-(Real.pi / 4)) * spectral_epsilon (E := E) *
        phaseFlow (E := E) (Real.pi / 4) =
      -(modular_j (E := E)) := by
  rw [phaseFlow_conj_spectral_epsilon]
  have harg : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
  rw [harg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp
  module

/-- At the geometric 45° angle, reverse active conjugation sends the spectral
grading to the positive doubled swap. -/
theorem phaseFlow_conj_spectral_epsilon_reverse_pi_div_four :
    phaseFlow (E := E) (Real.pi / 4) * spectral_epsilon (E := E) *
        phaseFlow (E := E) (-(Real.pi / 4)) =
      modular_j (E := E) := by
  rw [phaseFlow_conj_spectral_epsilon_reverse]
  have harg : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
  rw [harg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp
  module

theorem phaseFlow_spectral_epsilon_intertwining (θ : ℝ) :
    (spectral_epsilon (E := E)).comp (phaseFlow (E := E) θ) =
      (phaseFlow (E := E) (-θ)).comp (spectral_epsilon (E := E)) := by
  rw [phaseFlow_eq_KRotation (E := E), phaseFlow_eq_KRotation (E := E)]
  exact spectral_epsilon_comp_KRotation (E := E) θ

theorem phaseFlow_kreinMetricOfOperator_invariant
    (A : EndH)
    (hAnti : IsPhaseAntilinear (E := E) A)
    (θ : ℝ) :
    ∀ u v : H₂,
      kreinMetricOfOperator A
          (phaseFlow (E := E) θ u)
          (phaseFlow (E := E) θ v) =
        kreinMetricOfOperator A u v := by
  simp only [phaseFlow_eq_KRotation]
  exact kreinMetricOfOperator_KRotation_eq_of_IsPhaseAntilinear
    (E := E) A hAnti θ

theorem phaseFlow_transportGamma_car
    {M : RealMajoranaDatum (S := H₂)} (θ : ℝ) (u v : H₂) :
    anticommutator (M.gamma (phaseFlow (E := E) θ u))
        (M.gamma (phaseFlow (E := E) θ v)) =
      (2 * inner ℝ u v) • ContinuousLinearMap.id ℝ H₂ := by
  calc
    anticommutator (M.gamma (phaseFlow (E := E) θ u))
        (M.gamma (phaseFlow (E := E) θ v)) =
      (2 * inner ℝ (phaseFlow (E := E) θ u) (phaseFlow (E := E) θ v)) •
        ContinuousLinearMap.id ℝ H₂ := by
          exact M.car _ _
    _ = (2 * inner ℝ u v) • ContinuousLinearMap.id ℝ H₂ := by
      rw [phaseFlow_preserves_inner (E := E) θ u v]

theorem phaseFlow_transportGamma_isMajoranaCAR
    {M : RealMajoranaDatum (S := H₂)} (θ : ℝ) :
    MajoranaCARWitness (S := H₂) (fun u v => inner ℝ u v)
      (fun u => M.gamma (phaseFlow (E := E) θ u)) := by
  intro u v
  exact phaseFlow_transportGamma_car (E := E) (M := M) θ u v

/-!
## Full operator covariance on the endomorphism algebra (plan milestone A4)

The transport `A ↦ phaseFlow (-θ) * A * phaseFlow θ` is defined on the whole
endomorphism algebra: `A` and `B` are arbitrary, need not be diagonalizable,
and need not interact with the phase axis.  None of the transport laws below
carries such an assumption, so no chiral corner of the operator algebra is
erased and the diagonal/commutative specializations used elsewhere are
ordinary specializations, not additional hypotheses.
-/

/-- Pointwise cancellation `φ(θ) ∘ φ(-θ) = id`. -/
theorem phaseFlow_right_inverse_apply (θ : ℝ) (w : H₂) :
    phaseFlow (E := E) θ (phaseFlow (E := E) (-θ) w) = w := by
  have h := congrArg (fun T : EndH => T w)
    (phaseFlow_right_inverse (E := E) θ)
  simpa [ContinuousLinearMap.mul_apply] using h

/-- Pointwise cancellation `φ(-θ) ∘ φ(θ) = id`. -/
theorem phaseFlow_left_inverse_apply (θ : ℝ) (w : H₂) :
    phaseFlow (E := E) (-θ) (phaseFlow (E := E) θ w) = w := by
  have h := congrArg (fun T : EndH => T w)
    (phaseFlow_left_inverse (E := E) θ)
  simpa [ContinuousLinearMap.mul_apply] using h

/-- The phase conjugation, defined on the entire endomorphism algebra. -/
noncomputable def phaseConjugation (θ : ℝ) (A : EndH) : EndH :=
  phaseFlow (E := E) (-θ) * A * phaseFlow (E := E) θ

/-- Multiplication transport: hull covariance holds for arbitrary `A`, `B`. -/
theorem phaseConjugation_mul (θ : ℝ) (A B : EndH) :
    phaseConjugation (E := E) θ (A * B) =
      phaseConjugation (E := E) θ A * phaseConjugation (E := E) θ B := by
  apply ContinuousLinearMap.ext
  intro u
  dsimp only [phaseConjugation]
  simp only [ContinuousLinearMap.mul_apply]
  rw [phaseFlow_right_inverse_apply (E := E) θ]

/-- Additivity transport for arbitrary endomorphisms. -/
theorem phaseConjugation_add (θ : ℝ) (A B : EndH) :
    phaseConjugation (E := E) θ (A + B) =
      phaseConjugation (E := E) θ A + phaseConjugation (E := E) θ B := by
  apply ContinuousLinearMap.ext
  intro u
  dsimp only [phaseConjugation]
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.map_add]

/-- Scalar transport for arbitrary endomorphisms. -/
theorem phaseConjugation_smul (θ : ℝ) (c : ℝ) (A : EndH) :
    phaseConjugation (E := E) θ (c • A) = c • phaseConjugation (E := E) θ A := by
  apply ContinuousLinearMap.ext
  intro u
  dsimp only [phaseConjugation]
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.map_smul]

/-- Negation transport. -/
theorem phaseConjugation_neg (θ : ℝ) (A : EndH) :
    phaseConjugation (E := E) θ (-A) = -(phaseConjugation (E := E) θ A) := by
  rw [← neg_one_smul ℝ A, phaseConjugation_smul]
  exact neg_one_smul ℝ (phaseConjugation (E := E) θ A)

/-- Identity transport. -/
theorem phaseConjugation_id (θ : ℝ) :
    phaseConjugation (E := E) θ (ContinuousLinearMap.id ℝ H₂) =
      ContinuousLinearMap.id ℝ H₂ := by
  apply ContinuousLinearMap.ext
  intro u
  dsimp only [phaseConjugation]
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.id_apply]
  exact phaseFlow_left_inverse_apply (E := E) θ u

/-- Hilbert-adjoint transport: the conjugation is a `*`-preserving map. -/
theorem phaseConjugation_adjoint (θ : ℝ) (A : EndH) :
    ContinuousLinearMap.adjoint (phaseConjugation (E := E) θ A) =
      phaseConjugation (E := E) θ (ContinuousLinearMap.adjoint A) := by
  dsimp only [phaseConjugation]
  have hmul : ∀ f g : EndH, ContinuousLinearMap.adjoint (f * g)
      = ContinuousLinearMap.adjoint g * ContinuousLinearMap.adjoint f := by
    intro f g
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.mul_def]
  rw [hmul, hmul, phaseFlow_adjoint (E := E) θ, phaseFlow_adjoint (E := E) (-θ),
    mul_assoc]
  simp only [neg_neg]

/-- Full bilateral expectation covariance for arbitrary endomorphisms. -/
theorem phaseFlow_expectation_conjugate (θ : ℝ) (A : EndH) (u v : H₂) :
      ⟪u, phaseConjugation (E := E) θ A v⟫_ℝ
    = ⟪phaseFlow (E := E) θ u, A (phaseFlow (E := E) θ v)⟫_ℝ := by
  dsimp only [phaseConjugation]
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
  rw [← ContinuousLinearMap.adjoint_inner_left
    (A := phaseFlow (E := E) (-θ))]
  rw [phaseFlow_adjoint (E := E) (-θ)]
  have hθ : - -θ = θ := neg_neg θ
  rw [hθ]

/-- General-`θ` transport of the modular swap `J` under the phase conjugation. -/
theorem phaseFlow_conj_modular_j (θ : ℝ) :
    phaseFlow (E := E) (-θ) * modular_j (E := E) * phaseFlow (E := E) θ =
      Real.cos (2 * θ) • modular_j (E := E)
        + Real.sin (2 * θ) • spectral_epsilon (E := E) := by
  rw [phaseFlow_eq_KRotation (E := E), phaseFlow_eq_KRotation (E := E)]
  rw [KRotation_eq_cos_add_sin_K (E := E) (-θ),
    KRotation_eq_cos_add_sin_K (E := E) θ]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.neg_apply,
    spectral_epsilon_apply, clockAxis_apply, modular_j_apply]
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq θ
  apply DoubledSpace.ext <;>
    simp [Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul] <;>
    simp only [smul_smul] <;> ring_nf <;> rw [← htrig] <;> module

/-- At 45° the phase conjugation sends the modular swap to the grading. -/
theorem phaseFlow_conj_modular_j_pi_div_four :
    phaseFlow (E := E) (-(Real.pi / 4)) * modular_j (E := E) *
        phaseFlow (E := E) (Real.pi / 4) =
      spectral_epsilon (E := E) := by
  rw [phaseFlow_conj_modular_j]
  have harg : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
  rw [harg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp
  module

/-- General-`θ` exact covariance of the phase axis `HestenesI` itself. -/
theorem phaseFlow_conj_HestenesI (θ : ℝ) :
    phaseFlow (E := E) (-θ) * HestenesI (E := E) * phaseFlow (E := E) θ =
      HestenesI (E := E) := by
  have hcomm :
      (clockAxis (E := E)).comp (phaseFlow (E := E) θ) =
        (phaseFlow (E := E) θ).comp (clockAxis (E := E)) := by
    exact phaseFlow_operator_intertwines_of_phaseLinear
      (E := E) (clockAxis (E := E)) (by simp [IsPhaseLinear]) θ
  have hcomm_mul :
      clockAxis (E := E) * phaseFlow (E := E) θ =
        phaseFlow (E := E) θ * clockAxis (E := E) := by
    simpa [ContinuousLinearMap.mul_def] using hcomm
  rw [phaseAxis_eq_clockAxis (E := E)]
  calc
    phaseFlow (E := E) (-θ) * clockAxis (E := E) * phaseFlow (E := E) θ =
        phaseFlow (E := E) (-θ) *
          (phaseFlow (E := E) θ * clockAxis (E := E)) := by
            rw [mul_assoc, hcomm_mul]
    _ = (phaseFlow (E := E) (-θ) * phaseFlow (E := E) θ) *
        clockAxis (E := E) := by exact (mul_assoc _ _ _).symm
    _ = clockAxis (E := E) := by rw [phaseFlow_left_inverse]; simp

/-- At 45° the conjugated positive `ε`-projector lands on the `J`-grade
    projector: the sectors are exchanged, not preserved. -/
theorem phaseConjugation_spectralPlusProj_pi_div_four :
    phaseConjugation (E := E) (Real.pi / 4) (spectralPlusProj (E := E)) =
      gradeMinusProj (E := E) := by
  rw [show spectralPlusProj (E := E) = (⅟ (2 : ℝ)) •
      (ContinuousLinearMap.id ℝ H₂ + spectral_epsilon (E := E)) from rfl,
    phaseConjugation_smul, phaseConjugation_add, phaseConjugation_id]
  dsimp only [phaseConjugation]
  rw [phaseFlow_conj_spectral_epsilon_pi_div_four]
  simp [gradeMinusProj, sub_eq_add_neg]

/-- At 45° the conjugated negative `ε`-projector lands on the opposite
    `J`-grade projector. -/
theorem phaseConjugation_spectralMinusProj_pi_div_four :
    phaseConjugation (E := E) (Real.pi / 4) (spectralMinusProj (E := E)) =
      gradePlusProj (E := E) := by
  rw [show spectralMinusProj (E := E) = (⅟ (2 : ℝ)) •
      (ContinuousLinearMap.id ℝ H₂ - spectral_epsilon (E := E)) by
        rfl,
    phaseConjugation_smul]
  rw [sub_eq_add_neg, phaseConjugation_add, phaseConjugation_id,
    phaseConjugation_neg]
  dsimp only [phaseConjugation]
  rw [phaseFlow_conj_spectral_epsilon_pi_div_four]
  simp [gradePlusProj, neg_neg]

/-- At 45° the phase axis is a fixed point of its own conjugation. -/
theorem phaseConjugation_HestenesI_pi_div_four :
    phaseConjugation (E := E) (Real.pi / 4) (HestenesI (E := E)) =
      HestenesI (E := E) := by
  rw [show HestenesI (E := E) = modular_j (E := E) * spectral_epsilon (E := E)
    from rfl]
  rw [phaseConjugation_mul (E := E) (Real.pi / 4)]
  dsimp only [phaseConjugation]
  rw [phaseFlow_conj_modular_j_pi_div_four,
      phaseFlow_conj_spectral_epsilon_pi_div_four]
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [HestenesI, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.neg_apply, modular_j_apply, spectral_epsilon_apply]

end InfoGeometry.Canonical.RealDoubledWaveplate

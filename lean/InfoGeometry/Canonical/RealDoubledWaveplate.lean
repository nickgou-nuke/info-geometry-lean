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
  rw [phaseFlow_eq_KRotation (E := E), phaseFlow_eq_KRotation (E := E)]
  exact comp_KRotation_eq_KRotation_neg_comp_of_IsPhaseAntilinear
    (E := E) (A := A) hA θ

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

end InfoGeometry.Canonical.RealDoubledWaveplate

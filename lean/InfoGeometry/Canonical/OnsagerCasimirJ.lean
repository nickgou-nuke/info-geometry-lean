import InfoGeometry.Canonical.ModularTwoStateCorrelation

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OnsagerCasimirJ

Explicit `J`-conjugation reciprocity layer for operatorial two-state
correlations on the doubled carrier.

This file keeps the Onsager/Casimir split fully operatorial:

- `J`-conjugation of observable/perturbation channels,
- metric-sector invariance under `J`-reflection,
- phase-sector sign flip under `J` because `J` anticommutes with `K = Jε`,
- and the resulting left/right reciprocity laws for `J`-paired modular
  generators.

Repository policy boundary:
this file does not instantiate a concrete global Souriau coadjoint-orbit
model, and it does not assert split-source affine current construction.
-/

namespace OnsagerCasimirJ

open InfoGeometry.Canonical.ModularTwoStateCorrelation
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.StateDependentTransport
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Krein

section LightweightTheorems

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "H₂" => DoubledSpace E

/-- `J` preserves the positive doubled-space Hilbert inner product. -/
@[rep_depth krein]
theorem modularConjugationJ_preserves_inner
    (u v : H₂) :
    ⟪modularConjugationJ (E := E) u, modularConjugationJ (E := E) v⟫_ℝ = ⟪u, v⟫_ℝ := by
  repeat rw [WithLp.prod_inner_apply]
  repeat rw [WithLp.ofLp_fst, WithLp.ofLp_snd]
  simp [modular_j, add_comm]

/-- `K = Jε` anticommutes with `J` on the right as well as on the left. -/
@[rep_depth krein]
theorem modularComplexI_comp_modularConjugationJ
    :
    (modularComplexI (E := E)).comp (modularConjugationJ (E := E))
      =
    -((modularConjugationJ (E := E)).comp (modularComplexI (E := E))) := by
  have h := InfoGeometry.Krein.modular_j_complex_i_anticommute (E := E)
  have hFlip :
      (InfoGeometry.Krein.complex_i (E := E)).comp (InfoGeometry.Krein.modular_j (E := E))
        =
      -((InfoGeometry.Krein.modular_j (E := E)).comp (InfoGeometry.Krein.complex_i (E := E))) := by
    have hNeg : -((InfoGeometry.Krein.modular_j (E := E)).comp (InfoGeometry.Krein.complex_i (E := E)))
        =
      (InfoGeometry.Krein.complex_i (E := E)).comp (InfoGeometry.Krein.modular_j (E := E)) := by
      simpa [neg_neg] using congrArg (fun T => -T) h
    exact hNeg.symm
  simpa [modularComplexI_eq_complex_i, modularConjugationJ_eq_modular_j] using hFlip

@[rep_depth krein]
theorem complex_i_comp_modularConjugationJ
    :
    (InfoGeometry.Krein.complex_i (E := E)).comp (modularConjugationJ (E := E))
      =
    -((modularConjugationJ (E := E)).comp (InfoGeometry.Krein.complex_i (E := E))) := by
  simpa [modularComplexI_eq_complex_i] using
    modularComplexI_comp_modularConjugationJ (E := E)

end LightweightTheorems

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- `J`-conjugation of a doubled-space observable/channel. -/
@[rep_depth krein]
noncomputable def JConjugate
    (A : EndH) : EndH :=
  (modularConjugationJ (E := E)).comp (A.comp (modularConjugationJ (E := E)))

/-- `J`-even observables/channels are fixed by `J`-conjugation. -/
@[rep_depth krein]
def IsJInvariant
    (A : EndH) : Prop :=
  JConjugate (E := E) A = A

/-- `J`-odd observables/channels pick up a minus sign under `J`-conjugation. -/
@[rep_depth krein]
def IsJOdd
    (A : EndH) : Prop :=
  JConjugate (E := E) A = -A

omit [CompleteSpace E] in
@[rep_depth krein, simp] theorem JConjugate_apply
    (A : EndH) (u : H₂) :
    JConjugate (E := E) A u =
      modularConjugationJ (E := E) (A (modularConjugationJ (E := E) u)) := by
  simp [JConjugate]

@[rep_depth krein, simp] theorem JConjugate_involutive
    (A : EndH) :
    JConjugate (E := E) (JConjugate (E := E) A) = A := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : WithLp.toLp (2 : ENNReal) (WithLp.fst (A u), WithLp.snd (A u)) = A u := by
    apply DoubledSpace.ext <;> simp
  simpa [JConjugate, ContinuousLinearMap.comp_assoc] using hu

/-- `J` turns `K`-phase twisting into its negative after conjugation. -/
@[rep_depth krein]
theorem JConjugate_channelPhaseAxis_eq_neg_channelPhaseAxis_JConjugate
    (X : PerturbationChannel E) :
    JConjugate (E := E) (channelPhaseAxis (E := E) X)
      =
    -(channelPhaseAxis (E := E) (JConjugate (E := E) X)) := by
  apply ContinuousLinearMap.ext
  intro u
  calc
    JConjugate (E := E) (channelPhaseAxis (E := E) X) u
        =
      modularConjugationJ (E := E)
        ((channelPhaseAxis (E := E) X) ((modularConjugationJ (E := E)) u)) := by
        simp [JConjugate]
    _ = modularConjugationJ (E := E)
          (X ((modularComplexI (E := E)) ((modularConjugationJ (E := E)) u))) := by
        simp [channelPhaseAxis_apply]
    _ = modularConjugationJ (E := E)
          (X (-((modularConjugationJ (E := E)) ((modularComplexI (E := E)) u)))) := by
        rw [show (modularComplexI (E := E)) ((modularConjugationJ (E := E)) u)
              =
            -((modularConjugationJ (E := E)) ((modularComplexI (E := E)) u)) by
          simpa [ContinuousLinearMap.comp_apply] using
            congrArg (fun T : EndH => T u)
              (modularComplexI_comp_modularConjugationJ (E := E))]
    _ = -(modularConjugationJ (E := E)
          (X ((modularConjugationJ (E := E)) ((modularComplexI (E := E)) u)))) := by
        apply DoubledSpace.ext <;> simp
    _ = -((JConjugate (E := E) X) ((modularComplexI (E := E)) u)) := by
        apply DoubledSpace.ext <;> simp [JConjugate]
    _ = -(channelPhaseAxis (E := E) (JConjugate (E := E) X) u) := by
        simp [channelPhaseAxis_apply]

omit [CompleteSpace E] in
/-- Two-state observable correlations are `J`-covariant under channel conjugation. -/
@[rep_depth krein]
theorem twoStateObservableCorrelation_J_conjugate
    (reference comparison : H₂) (A B : EndH) :
    twoStateObservableCorrelation (E := E)
      ((modularConjugationJ (E := E)) reference)
      ((modularConjugationJ (E := E)) comparison) A B
      =
    twoStateObservableCorrelation (E := E) reference comparison
      (JConjugate (E := E) A) (JConjugate (E := E) B) := by
  calc
    twoStateObservableCorrelation (E := E)
        ((modularConjugationJ (E := E)) reference)
        ((modularConjugationJ (E := E)) comparison) A B
        =
      ⟪A ((modularConjugationJ (E := E)) reference),
        B ((modularConjugationJ (E := E)) comparison)⟫_ℝ := rfl
    _ = ⟪(modularConjugationJ (E := E))
            (A ((modularConjugationJ (E := E)) reference)),
          (modularConjugationJ (E := E))
            (B ((modularConjugationJ (E := E)) comparison))⟫_ℝ := by
          rw [(modularConjugationJ_preserves_inner (E := E)
            (A ((modularConjugationJ (E := E)) reference))
            (B ((modularConjugationJ (E := E)) comparison))).symm]
    _ =
      twoStateObservableCorrelation (E := E) reference comparison
        (JConjugate (E := E) A) (JConjugate (E := E) B) := by
          simp [twoStateObservableCorrelation, JConjugate]

/-- Two-state channel correlations are `J`-covariant under channel conjugation. -/
@[rep_depth krein]
theorem twoStateChannelCorrelation_J_conjugate
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    twoStateChannelCorrelation (E := E)
      ((modularConjugationJ (E := E)) reference)
      ((modularConjugationJ (E := E)) comparison) X Y
      =
    twoStateChannelCorrelation (E := E) reference comparison
      (JConjugate (E := E) X) (JConjugate (E := E) Y) := by
  exact twoStateObservableCorrelation_J_conjugate
    (E := E) reference comparison X Y

/-- `J`-invariant channels have metric-sector two-state correlations invariant under `J`-reflection. -/
@[rep_depth krein]
theorem twoStateChannelCorrelation_J_reflect_eq_of_IsJInvariant
    (reference comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : IsJInvariant (E := E) X)
    (hY : IsJInvariant (E := E) Y) :
    twoStateChannelCorrelation (E := E)
      ((modularConjugationJ (E := E)) reference)
      ((modularConjugationJ (E := E)) comparison) X Y
      =
    twoStateChannelCorrelation (E := E) reference comparison X Y := by
  rw [twoStateChannelCorrelation_J_conjugate (E := E) reference comparison X Y, hX, hY]

/-- Under `J`, the `K`-twisted channel correlation picks up the Casimir sign. -/
@[rep_depth krein]
theorem twoStateChannelCorrelation_phase_J_reflect_eq_neg
    (reference comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : IsJInvariant (E := E) X)
    (hY : IsJInvariant (E := E) Y) :
    twoStateChannelCorrelation (E := E)
        ((modularConjugationJ (E := E)) reference)
        ((modularConjugationJ (E := E)) comparison)
        (channelPhaseAxis (E := E) X) Y
      =
    -twoStateChannelCorrelation (E := E)
        reference comparison
        (channelPhaseAxis (E := E) X) Y := by
  rw [twoStateChannelCorrelation_J_conjugate
    (E := E) reference comparison (channelPhaseAxis (E := E) X) Y]
  rw [JConjugate_channelPhaseAxis_eq_neg_channelPhaseAxis_JConjugate (E := E) X, hX, hY]
  simp [twoStateChannelCorrelation]

/-- The right modular generator of a `J`-paired datum is the `J`-conjugate of the left generator. -/
@[rep_depth transport]
theorem stateRelativeModularGenerator_right_eq_JConjugate_left
    (P : JPairedStateGenerators E) (ψ : H₂) :
    stateRelativeModularGenerator (E := E) P.right ψ
      =
    JConjugate (E := E) (stateRelativeModularGenerator (E := E) P.left ψ) := by
  simpa [stateRelativeModularGenerator, JConjugate, ContinuousLinearMap.comp_assoc] using P.J_pairs ψ

/-- Metric-sector reciprocity for the left/right generators of a `J`-paired datum. -/
@[rep_depth transport]
theorem jPairedGeneratorCorrelation_metric
    (P : JPairedStateGenerators E) (ψ : H₂) :
    twoStateObservableCorrelation (E := E)
        ((modularConjugationJ (E := E)) ψ)
        ((modularConjugationJ (E := E)) ψ)
        (stateRelativeModularGenerator (E := E) P.left ψ)
        (stateRelativeModularGenerator (E := E) P.left ψ)
      =
    twoStateObservableCorrelation (E := E)
        ψ ψ
        (stateRelativeModularGenerator (E := E) P.right ψ)
        (stateRelativeModularGenerator (E := E) P.right ψ) := by
  rw [twoStateObservableCorrelation_J_conjugate (E := E) ψ ψ
    (stateRelativeModularGenerator (E := E) P.left ψ)
    (stateRelativeModularGenerator (E := E) P.left ψ)]
  simp [stateRelativeModularGenerator_right_eq_JConjugate_left (E := E) P ψ]

/-- Phase-sector Casimir sign for the left/right generators of a `J`-paired datum. -/
@[rep_depth transport]
theorem jPairedGeneratorCorrelation_phase
    (P : JPairedStateGenerators E) (ψ : H₂)
    (hLeft : IsJInvariant (E := E) (stateRelativeModularGenerator (E := E) P.left ψ)) :
    twoStateChannelCorrelation (E := E)
        ((modularConjugationJ (E := E)) ψ)
        ((modularConjugationJ (E := E)) ψ)
        (channelPhaseAxis (E := E) (stateRelativeModularGenerator (E := E) P.left ψ))
        (stateRelativeModularGenerator (E := E) P.left ψ)
      =
    -twoStateChannelCorrelation (E := E)
        ψ ψ
        (channelPhaseAxis (E := E) (stateRelativeModularGenerator (E := E) P.left ψ))
        (stateRelativeModularGenerator (E := E) P.left ψ) := by
  exact twoStateChannelCorrelation_phase_J_reflect_eq_neg
    (E := E) ψ ψ
    (stateRelativeModularGenerator (E := E) P.left ψ)
    (stateRelativeModularGenerator (E := E) P.left ψ)
    hLeft hLeft

end Core

end OnsagerCasimirJ

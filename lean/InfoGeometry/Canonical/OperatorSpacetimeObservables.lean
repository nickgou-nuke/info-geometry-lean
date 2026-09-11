import InfoGeometry.Canonical.OperatorLightconeCoordinates
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorSpacetimeObservables

Operatorial observable readout for the split atom `{Id, ε, J, K}` on the
doubled carrier, together with light-cone/time-space coordinate identities.

This module introduces no new owner semantics; it packages expectation-level
channels on top of already-owned operators and transport laws.
-/

namespace InfoGeometry.Canonical.OperatorSpacetimeObservables

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.OperatorDictionary
open InfoGeometry.Canonical.OperatorLightconeCoordinates

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "P₊" => spectralPlusProj (E := E)
local notation "P₋" => spectralMinusProj (E := E)
local notation "IdH" => ContinuousLinearMap.id ℝ H₂
local notation "ε" => spectral_epsilon (E := E)
local notation "J" => modular_j (E := E)
local notation "K" => phaseAxisK (E := E)

omit [CompleteSpace E] in
private theorem half_smul_add_half_smul (z : E) :
    ((2 : ℝ)⁻¹) • z + ((2 : ℝ)⁻¹) • z = z := by
  calc
    ((2 : ℝ)⁻¹) • z + ((2 : ℝ)⁻¹) • z
        = (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • z := by
            simpa using (add_smul ((2 : ℝ)⁻¹) ((2 : ℝ)⁻¹) z).symm
    _ = z := by norm_num

/-- Observable channel for the identity operator. -/
@[rep_depth transport]
noncomputable def idObservable (ψ : H₂) : ℝ :=
  kreinExpectation (E := E) ψ IdH

/-- Observable channel for the spectral involution `ε`. -/
@[rep_depth transport]
noncomputable def epsilonObservable (ψ : H₂) : ℝ :=
  kreinExpectation (E := E) ψ ε

/-- Observable channel for the modular involution `J`. -/
@[rep_depth transport]
noncomputable def jObservable (ψ : H₂) : ℝ :=
  kreinExpectation (E := E) ψ J

/-- Observable channel for the phase axis `K = J ∘ ε`. -/
@[rep_depth transport]
noncomputable def kObservable (ψ : H₂) : ℝ :=
  kreinExpectation (E := E) ψ K

/-- The identity observable is exactly the sum of light-cone channels. -/
@[rep_depth transport]
theorem idObservable_eq_lightconePlus_add_lightconeMinus (ψ : H₂) :
    idObservable (E := E) ψ
      = lightconePlusCoordinate (E := E) ψ + lightconeMinusCoordinate (E := E) ψ := by
  simpa [idObservable] using
    (lightconeCoordinate_sum_eq_id_expectation (E := E) ψ).symm

/-- The spectral observable is exactly the light-cone channel difference. -/
@[rep_depth transport]
theorem epsilonObservable_eq_lightconePlus_sub_lightconeMinus (ψ : H₂) :
    epsilonObservable (E := E) ψ
      = lightconePlusCoordinate (E := E) ψ - lightconeMinusCoordinate (E := E) ψ := by
  have hProj :
      P₊ - P₋ = ε := by
    ext u
    · simp [spectralPlusProj, spectralMinusProj, spectral_epsilon_apply, sub_eq_add_neg,
        half_smul_add_half_smul]
    · have hneg :
          -(((2 : ℝ)⁻¹) • WithLp.snd u + ((2 : ℝ)⁻¹) • WithLp.snd u) = -WithLp.snd u := by
          simpa using congrArg Neg.neg (half_smul_add_half_smul (z := WithLp.snd u))
      simpa [spectralPlusProj, spectralMinusProj, spectral_epsilon_apply, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc] using hneg
  calc
    epsilonObservable (E := E) ψ
        = kreinExpectation (E := E) ψ (P₊ - P₋) := by
            simpa [epsilonObservable] using congrArg (fun A : EndH =>
              kreinExpectation (E := E) ψ A) hProj.symm
    _ = lightconePlusCoordinate (E := E) ψ - lightconeMinusCoordinate (E := E) ψ := by
          simp [lightconePlusCoordinate, lightconeMinusCoordinate, kreinExpectation_sub]

/-- Light-cone `+` channel in terms of `{Id, ε}` observables. -/
@[rep_depth transport]
theorem lightconePlus_eq_half_id_add_epsilon (ψ : H₂) :
    lightconePlusCoordinate (E := E) ψ
      = (1 / 2 : ℝ) * (idObservable (E := E) ψ + epsilonObservable (E := E) ψ) := by
  have hsum := idObservable_eq_lightconePlus_add_lightconeMinus (E := E) ψ
  have hdiff := epsilonObservable_eq_lightconePlus_sub_lightconeMinus (E := E) ψ
  have htwox :
      idObservable (E := E) ψ + epsilonObservable (E := E) ψ
        = (2 : ℝ) * lightconePlusCoordinate (E := E) ψ := by
    rw [hsum, hdiff]
    ring
  calc
    lightconePlusCoordinate (E := E) ψ
        = (1 / 2 : ℝ) * ((2 : ℝ) * lightconePlusCoordinate (E := E) ψ) := by ring
    _ = (1 / 2 : ℝ) * (idObservable (E := E) ψ + epsilonObservable (E := E) ψ) := by
          rw [htwox]

/-- Light-cone `-` channel in terms of `{Id, ε}` observables. -/
@[rep_depth transport]
theorem lightconeMinus_eq_half_id_sub_epsilon (ψ : H₂) :
    lightconeMinusCoordinate (E := E) ψ
      = (1 / 2 : ℝ) * (idObservable (E := E) ψ - epsilonObservable (E := E) ψ) := by
  have hsum := idObservable_eq_lightconePlus_add_lightconeMinus (E := E) ψ
  have hdiff := epsilonObservable_eq_lightconePlus_sub_lightconeMinus (E := E) ψ
  have htwox :
      idObservable (E := E) ψ - epsilonObservable (E := E) ψ
        = (2 : ℝ) * lightconeMinusCoordinate (E := E) ψ := by
    rw [hsum, hdiff]
    ring
  calc
    lightconeMinusCoordinate (E := E) ψ
        = (1 / 2 : ℝ) * ((2 : ℝ) * lightconeMinusCoordinate (E := E) ψ) := by ring
    _ = (1 / 2 : ℝ) * (idObservable (E := E) ψ - epsilonObservable (E := E) ψ) := by
          rw [htwox]

/-- Time channel is half of the identity observable. -/
@[rep_depth transport]
theorem timeCoordinate_eq_half_idObservable (ψ : H₂) :
    timeCoordinate (E := E) ψ = (1 / 2 : ℝ) * idObservable (E := E) ψ := by
  unfold timeCoordinate
  rw [idObservable_eq_lightconePlus_add_lightconeMinus (E := E) ψ]

/-- Space channel is half of the spectral observable. -/
@[rep_depth transport]
theorem spaceCoordinate_eq_half_epsilonObservable (ψ : H₂) :
    spaceCoordinate (E := E) ψ = (1 / 2 : ℝ) * epsilonObservable (E := E) ψ := by
  unfold spaceCoordinate
  rw [epsilonObservable_eq_lightconePlus_sub_lightconeMinus (E := E) ψ]

/-- The squared phase-axis expectation channel is `-` the identity channel. -/
@[rep_depth transport]
theorem phaseAxisK_sq_expectation_eq_neg_idObservable (ψ : H₂) :
    kreinExpectation (E := E) ψ ((phaseAxisK (E := E)).comp (phaseAxisK (E := E)))
      = - idObservable (E := E) ψ := by
  rw [phaseAxisK_sq_eq_neg_id (E := E)]
  simp [idObservable]

/-- Rapidity-evolved identity-like observable from light-cone channels. -/
@[rep_depth transport]
noncomputable def rapidityIdObservable (ψ : H₂) (η : ℝ) : ℝ :=
  rapidityPlusCoordinate (E := E) ψ η + rapidityMinusCoordinate (E := E) ψ η

/-- Rapidity-evolved spectral observable from light-cone channels. -/
@[rep_depth transport]
noncomputable def rapidityEpsilonObservable (ψ : H₂) (η : ℝ) : ℝ :=
  rapidityPlusCoordinate (E := E) ψ η - rapidityMinusCoordinate (E := E) ψ η

/-- Rapidity covariance of the `{Id, ε}` observable pair (first row). -/
@[rep_depth transport]
theorem rapidityIdObservable_eq_cosh_id_add_sinh_epsilon (ψ : H₂) (η : ℝ) :
    rapidityIdObservable (E := E) ψ η
      = Real.cosh η * idObservable (E := E) ψ
        + Real.sinh η * epsilonObservable (E := E) ψ := by
  unfold rapidityIdObservable
  calc
    rapidityPlusCoordinate (E := E) ψ η + rapidityMinusCoordinate (E := E) ψ η
        = (2 : ℝ) * rapidityTimeCoordinate (E := E) ψ η := by
            unfold rapidityTimeCoordinate
            ring
    _ =
        (2 : ℝ) *
          (Real.cosh η * timeCoordinate (E := E) ψ
            + Real.sinh η * spaceCoordinate (E := E) ψ) := by
              rw [rapidityTimeCoordinate_eq_cosh_time_add_sinh_space (E := E) ψ η]
    _ = Real.cosh η * idObservable (E := E) ψ
          + Real.sinh η * epsilonObservable (E := E) ψ := by
          rw [timeCoordinate_eq_half_idObservable (E := E) ψ,
            spaceCoordinate_eq_half_epsilonObservable (E := E) ψ]
          ring

/-- Rapidity covariance of the `{Id, ε}` observable pair (second row). -/
@[rep_depth transport]
theorem rapidityEpsilonObservable_eq_sinh_id_add_cosh_epsilon (ψ : H₂) (η : ℝ) :
    rapidityEpsilonObservable (E := E) ψ η
      = Real.sinh η * idObservable (E := E) ψ
        + Real.cosh η * epsilonObservable (E := E) ψ := by
  unfold rapidityEpsilonObservable
  calc
    rapidityPlusCoordinate (E := E) ψ η - rapidityMinusCoordinate (E := E) ψ η
        = (2 : ℝ) * rapiditySpaceCoordinate (E := E) ψ η := by
            unfold rapiditySpaceCoordinate
            ring
    _ =
        (2 : ℝ) *
          (Real.sinh η * timeCoordinate (E := E) ψ
            + Real.cosh η * spaceCoordinate (E := E) ψ) := by
              rw [rapiditySpaceCoordinate_eq_sinh_time_add_cosh_space (E := E) ψ η]
    _ = Real.sinh η * idObservable (E := E) ψ
          + Real.cosh η * epsilonObservable (E := E) ψ := by
          rw [timeCoordinate_eq_half_idObservable (E := E) ψ,
            spaceCoordinate_eq_half_epsilonObservable (E := E) ψ]
          ring

end Core

end InfoGeometry.Canonical.OperatorSpacetimeObservables

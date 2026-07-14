import InfoGeometry.Canonical.BogoliubovProjectorFlux
import InfoGeometry.Canonical.OperatorDictionary
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorLightconeCoordinates

Operatorial light-cone coordinate layer on the doubled carrier.

This file keeps the owner split:
- projectors `P±` remain owned by the Krein/Clifford layers,
- transport remains owned by the Bogoliubov layers,
- this module only packages expectation-level coordinate channels.
-/

namespace OperatorLightconeCoordinates

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovProjectorFlux
open InfoGeometry.Canonical.OperatorDictionary

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "P₊" => spectralPlusProj (E := E)
local notation "P₋" => spectralMinusProj (E := E)

/-- Light-cone `+` coordinate channel from the projector observable `P₊`. -/
@[rep_depth transport]
noncomputable def lightconePlusCoordinate (ψ : H₂) : ℝ :=
  kreinExpectation (E := E) ψ P₊

/-- Light-cone `-` coordinate channel from the projector observable `P₋`. -/
@[rep_depth transport]
noncomputable def lightconeMinusCoordinate (ψ : H₂) : ℝ :=
  kreinExpectation (E := E) ψ P₋

/--
Operator-native alias for the `+` spectral polarization coordinate channel.
This keeps downstream prose independent from manifold-facing terminology.
-/
@[rep_depth transport]
noncomputable abbrev polarizedPlusCoordinate (ψ : H₂) : ℝ :=
  lightconePlusCoordinate (E := E) ψ

/--
Operator-native alias for the `-` spectral polarization coordinate channel.
This keeps downstream prose independent from manifold-facing terminology.
-/
@[rep_depth transport]
noncomputable abbrev polarizedMinusCoordinate (ψ : H₂) : ℝ :=
  lightconeMinusCoordinate (E := E) ψ

/-- Coordinate completeness: `x⁺ + x⁻` equals expectation of the identity channel. -/
@[rep_depth transport]
theorem lightconeCoordinate_sum_eq_id_expectation (ψ : H₂) :
    lightconePlusCoordinate (E := E) ψ + lightconeMinusCoordinate (E := E) ψ
      = kreinExpectation (E := E) ψ (ContinuousLinearMap.id ℝ H₂) := by
  calc
    lightconePlusCoordinate (E := E) ψ + lightconeMinusCoordinate (E := E) ψ
        = kreinExpectation (E := E) ψ P₊ + kreinExpectation (E := E) ψ P₋ := by
            rfl
    _ = kreinExpectation (E := E) ψ (P₊ + P₋) := by
          rw [← kreinExpectation_add (E := E) ψ P₊ P₋]
    _ = kreinExpectation (E := E) ψ (ContinuousLinearMap.id ℝ H₂) := by
          rw [spectralProj_sum (E := E)]

/-- Rapidity-evolved `+` coordinate under the canonical `ε`-boost branch. -/
@[rep_depth transport]
noncomputable def rapidityPlusCoordinate (ψ : H₂) (η : ℝ) : ℝ :=
  kreinExpectation (E := E) ψ (transportedPlusProjector (E := E) (epsilonBoost (E := E) η))

/-- Rapidity-evolved `-` coordinate under the canonical `ε`-boost branch. -/
@[rep_depth transport]
noncomputable def rapidityMinusCoordinate (ψ : H₂) (η : ℝ) : ℝ :=
  kreinExpectation (E := E) ψ (transportedMinusProjector (E := E) (epsilonBoost (E := E) η))

/--
Operator-native alias for the `+` spectral polarization coordinate under
`ε`-boost transport.
-/
@[rep_depth transport]
noncomputable abbrev epsilonBoostPlusCoordinate (ψ : H₂) (η : ℝ) : ℝ :=
  rapidityPlusCoordinate (E := E) ψ η

/--
Operator-native alias for the `-` spectral polarization coordinate under
`ε`-boost transport.
-/
@[rep_depth transport]
noncomputable abbrev epsilonBoostMinusCoordinate (ψ : H₂) (η : ℝ) : ℝ :=
  rapidityMinusCoordinate (E := E) ψ η

/-- Under `ε`-boost rapidity `η`, the `+` light-cone coordinate scales by `exp(η)`. -/
@[rep_depth transport]
theorem rapidityPlusCoordinate_eq_exp_mul_lightconePlus (ψ : H₂) (η : ℝ) :
    rapidityPlusCoordinate (E := E) ψ η
      = Real.exp η * lightconePlusCoordinate (E := E) ψ := by
  simp [rapidityPlusCoordinate, lightconePlusCoordinate]

/-- Under `ε`-boost rapidity `η`, the `-` light-cone coordinate scales by `exp(-η)`. -/
@[rep_depth transport]
theorem rapidityMinusCoordinate_eq_exp_neg_mul_lightconeMinus (ψ : H₂) (η : ℝ) :
    rapidityMinusCoordinate (E := E) ψ η
      = Real.exp (-η) * lightconeMinusCoordinate (E := E) ψ := by
  simp [rapidityMinusCoordinate, lightconeMinusCoordinate]

/-- Rapidity-evolved time-like channel from boosted light-cone coordinates. -/
@[rep_depth transport]
noncomputable def rapidityTimeCoordinate (ψ : H₂) (η : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (rapidityPlusCoordinate (E := E) ψ η + rapidityMinusCoordinate (E := E) ψ η)

/-- Rapidity-evolved space-like channel from boosted light-cone coordinates. -/
@[rep_depth transport]
noncomputable def rapiditySpaceCoordinate (ψ : H₂) (η : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (rapidityPlusCoordinate (E := E) ψ η - rapidityMinusCoordinate (E := E) ψ η)

/--
Operator-native alias for the boosted identity-like polarization channel.
-/
@[rep_depth transport]
noncomputable abbrev epsilonBoostTimeCoordinate (ψ : H₂) (η : ℝ) : ℝ :=
  rapidityTimeCoordinate (E := E) ψ η

/--
Operator-native alias for the boosted grading-like polarization channel.
-/
@[rep_depth transport]
noncomputable abbrev epsilonBoostSpaceCoordinate (ψ : H₂) (η : ℝ) : ℝ :=
  rapiditySpaceCoordinate (E := E) ψ η

/-- Time-like expectation channel from light-cone coordinates: `t = (x⁺ + x⁻)/2`. -/
@[rep_depth transport]
noncomputable def timeCoordinate (ψ : H₂) : ℝ :=
  (1 / 2 : ℝ) * (lightconePlusCoordinate (E := E) ψ + lightconeMinusCoordinate (E := E) ψ)

/-- Space-like expectation channel from light-cone coordinates: `x = (x⁺ - x⁻)/2`. -/
@[rep_depth transport]
noncomputable def spaceCoordinate (ψ : H₂) : ℝ :=
  (1 / 2 : ℝ) * (lightconePlusCoordinate (E := E) ψ - lightconeMinusCoordinate (E := E) ψ)

/-- Inverse light-cone reconstruction: `x⁺ = t + x`. -/
@[rep_depth transport]
theorem lightconePlus_eq_time_add_space (ψ : H₂) :
    lightconePlusCoordinate (E := E) ψ
      = timeCoordinate (E := E) ψ + spaceCoordinate (E := E) ψ := by
  unfold timeCoordinate spaceCoordinate
  ring

/-- Inverse light-cone reconstruction: `x⁻ = t - x`. -/
@[rep_depth transport]
theorem lightconeMinus_eq_time_sub_space (ψ : H₂) :
    lightconeMinusCoordinate (E := E) ψ
      = timeCoordinate (E := E) ψ - spaceCoordinate (E := E) ψ := by
  unfold timeCoordinate spaceCoordinate
  ring

private lemma rapidity_time_linearization
    (η xplus xminus : ℝ) :
    (1 / 2 : ℝ) * (Real.exp η * xplus + Real.exp (-η) * xminus)
      =
    Real.cosh η * ((1 / 2 : ℝ) * (xplus + xminus))
      + Real.sinh η * ((1 / 2 : ℝ) * (xplus - xminus)) := by
  rw [← Real.cosh_add_sinh η, ← Real.cosh_sub_sinh η]
  ring

private lemma rapidity_space_linearization
    (η xplus xminus : ℝ) :
    (1 / 2 : ℝ) * (Real.exp η * xplus - Real.exp (-η) * xminus)
      =
    Real.sinh η * ((1 / 2 : ℝ) * (xplus + xminus))
      + Real.cosh η * ((1 / 2 : ℝ) * (xplus - xminus)) := by
  rw [← Real.cosh_add_sinh η, ← Real.cosh_sub_sinh η]
  ring

/--
Rapidity transport of derived expectation coordinates:
`t(η) = cosh(η) t + sinh(η) x`.
-/
@[rep_depth transport]
theorem rapidityTimeCoordinate_eq_cosh_time_add_sinh_space (ψ : H₂) (η : ℝ) :
    rapidityTimeCoordinate (E := E) ψ η
      =
    Real.cosh η * timeCoordinate (E := E) ψ
      + Real.sinh η * spaceCoordinate (E := E) ψ := by
  rw [rapidityTimeCoordinate, timeCoordinate, spaceCoordinate]
  rw [rapidityPlusCoordinate_eq_exp_mul_lightconePlus (E := E) ψ η]
  rw [rapidityMinusCoordinate_eq_exp_neg_mul_lightconeMinus (E := E) ψ η]
  exact rapidity_time_linearization η
    (lightconePlusCoordinate (E := E) ψ)
    (lightconeMinusCoordinate (E := E) ψ)

/--
Rapidity transport of derived expectation coordinates:
`x(η) = sinh(η) t + cosh(η) x`.
-/
@[rep_depth transport]
theorem rapiditySpaceCoordinate_eq_sinh_time_add_cosh_space (ψ : H₂) (η : ℝ) :
    rapiditySpaceCoordinate (E := E) ψ η
      =
    Real.sinh η * timeCoordinate (E := E) ψ
      + Real.cosh η * spaceCoordinate (E := E) ψ := by
  rw [rapiditySpaceCoordinate, timeCoordinate, spaceCoordinate]
  rw [rapidityPlusCoordinate_eq_exp_mul_lightconePlus (E := E) ψ η]
  rw [rapidityMinusCoordinate_eq_exp_neg_mul_lightconeMinus (E := E) ψ η]
  exact rapidity_space_linearization η
    (lightconePlusCoordinate (E := E) ψ)
    (lightconeMinusCoordinate (E := E) ψ)

end Core

end OperatorLightconeCoordinates

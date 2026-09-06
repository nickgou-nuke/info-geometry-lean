import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport
import InfoGeometry.Dynamics.ModularThermalState

/-!
# Real boundary readouts on a filtered Hestenes--Krein cone

This is the colimit-side replacement for a complex analytic boundary interface.
The two boundary channels are supplied as real-valued finite-stage readouts;
their only continuation law is compatibility with the canonical maps into the
filtered Hestenes carrier.  The result is a genuine finite-stage transport
theorem, not an analytic-continuation assertion.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinColimitRealBoundary

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
open InfoGeometry.Krein

structure RealBoundaryReadout (C : HestenesKreinCone) where
  lowerStage : ∀ n, DoubledSpace (C.Base n) → ℝ
  upperStage : ∀ n, DoubledSpace (C.Base n) → ℝ
  lowerLimit : DoubledSpace C.LimitBase → ℝ
  upperLimit : DoubledSpace C.LimitBase → ℝ
  lower_ι : ∀ n x, lowerStage n x = lowerLimit (C.ι n x)
  upper_ι : ∀ n x, upperStage n x = upperLimit (C.ι n x)

namespace RealBoundaryReadout

variable {C : HestenesKreinCone} (R : RealBoundaryReadout C)

theorem lower_bond (n : ℕ) (x : DoubledSpace (C.Base n)) :
    R.lowerStage (n + 1) (C.bond n x) = R.lowerStage n x := by
  rw [R.lower_ι, R.lower_ι]
  rw [C.ι_bond_apply]

theorem upper_bond (n : ℕ) (x : DoubledSpace (C.Base n)) :
    R.upperStage (n + 1) (C.bond n x) = R.upperStage n x := by
  rw [R.upper_ι, R.upper_ι]
  rw [C.ι_bond_apply]

theorem lower_bondIterate (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    R.lowerStage (n + m)
        (C.toFilteredPhaseCone.bondIterate n m x) =
      R.lowerStage n x := by
  rw [R.lower_ι, R.lower_ι]
  exact congrArg R.lowerLimit
    (C.toFilteredPhaseCone.ι_bondIterate_apply n m x)

theorem upper_bondIterate (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    R.upperStage (n + m)
        (C.toFilteredPhaseCone.bondIterate n m x) =
      R.upperStage n x := by
  rw [R.upper_ι, R.upper_ι]
  exact congrArg R.upperLimit
    (C.toFilteredPhaseCone.ι_bondIterate_apply n m x)

theorem lower_stage_readout (n : ℕ) (x : DoubledSpace (C.Base n)) :
    R.lowerStage n x = R.lowerLimit (C.ι n x) :=
  R.lower_ι n x

theorem upper_stage_readout (n : ℕ) (x : DoubledSpace (C.Base n)) :
    R.upperStage n x = R.upperLimit (C.ι n x) :=
  R.upper_ι n x

/-! ## Native real KMS boundary chains -/

theorem kms_lower_stage_sigma
    {A : Type*} [Monoid A]
    (K : InfoGeometry.Dynamics.HestenesKreinRealKMSBoundaryData A)
    (hK : InfoGeometry.Dynamics.HestenesKreinRealKMSBoundaryLaw K)
    (stage : ∀ n, DoubledSpace (C.Base n) → A)
    (a : A) (t : ℝ) (n : ℕ) (x : DoubledSpace (C.Base n)) :
    K.omega_eval a (K.boundary.lower t (stage n x)) =
      K.omega_eval a
        (InfoGeometry.Dynamics.ModularAutomorphismFamily.sigma
          K.boundary.modular t (stage n x)) := by
  exact InfoGeometry.Dynamics.realKMS_lower_readout K hK t a (stage n x)

theorem kms_upper_stage_sigma
    {A : Type*} [Monoid A]
    (K : InfoGeometry.Dynamics.HestenesKreinRealKMSBoundaryData A)
    (hK : InfoGeometry.Dynamics.HestenesKreinRealKMSBoundaryLaw K)
    (stage : ∀ n, DoubledSpace (C.Base n) → A)
    (a : A) (t : ℝ) (n : ℕ) (x : DoubledSpace (C.Base n)) :
    K.omega_eval a (K.boundary.upper t (stage n x)) =
      K.omega_eval
        (InfoGeometry.Dynamics.ModularAutomorphismFamily.sigma
          K.boundary.modular (t + K.boundary.beta) (stage n x)) a := by
  exact InfoGeometry.Dynamics.realKMS_upper_readout K hK t a (stage n x)

theorem kms_lower_stage_colimit_transport
    {A : Type*} [Monoid A]
    (K : InfoGeometry.Dynamics.HestenesKreinRealKMSBoundaryData A)
    (stage : ∀ n, DoubledSpace (C.Base n) → A)
    (limit : DoubledSpace C.LimitBase → A)
    (hstage : ∀ n x, stage n x = limit (C.ι n x))
    (a : A) (t : ℝ) (n : ℕ) (x : DoubledSpace (C.Base n)) :
    K.omega_eval a (K.boundary.lower t (stage n x)) =
      K.omega_eval a (K.boundary.lower t (limit (C.ι n x))) := by
  rw [hstage n x]

theorem kms_upper_stage_colimit_transport
    {A : Type*} [Monoid A]
    (K : InfoGeometry.Dynamics.HestenesKreinRealKMSBoundaryData A)
    (stage : ∀ n, DoubledSpace (C.Base n) → A)
    (limit : DoubledSpace C.LimitBase → A)
    (hstage : ∀ n x, stage n x = limit (C.ι n x))
    (a : A) (t : ℝ) (n : ℕ) (x : DoubledSpace (C.Base n)) :
    K.omega_eval a (K.boundary.upper t (stage n x)) =
      K.omega_eval a (K.boundary.upper t (limit (C.ι n x))) := by
  rw [hstage n x]

end RealBoundaryReadout


end InfoGeometry.Canonical.HestenesKreinColimitRealBoundary

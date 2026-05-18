import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.KKTClosureSymmetry
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.ObserverDefect

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinSupercharge

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
Local observer slice that preserves the spectral grading orientation.
-/
@[rep_depth transport]
structure ObserverL5 (CIK : CertifiedInverseKernel H₂) where
  localSlice : EndH
  isOrientationFixing :
    localSlice * CIK.toInformationCartanTriple.GammaS =
      CIK.toInformationCartanTriple.GammaS * localSlice

/--
The observer slice lies in the spectral compact Cartan sector because it is
orientation-fixing with respect to the certified grading `Γ_S`.
-/
theorem observerLocalSlice_isSpectralCompact
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) :
    CIK.IsSpectralCompact obs.localSlice := by
  rw [CIK.isSpectralCompact_iff_commute_GammaS]
  simpa using obs.isOrientationFixing

/--
Deviation of the observer slice from the certified Drazin spectral projector.

This is the smallest upstream algebraic datum for comparing observer-induced
residuals with the canonical inverse-kernel lane.
-/
noncomputable def observerProjectorDeviation
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) : EndH :=
  obs.localSlice - CIK.spectralProjector

@[simp] theorem localSlice_eq_spectralProjector_add_observerProjectorDeviation
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) :
    obs.localSlice = CIK.spectralProjector + observerProjectorDeviation CIK obs := by
  unfold observerProjectorDeviation
  abel

/--
Primary observer residual against the geometric dilation lane.
-/
noncomputable def observerOrientationResidual
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) : EndH :=
  DrazinSupercharge.commutator obs.localSlice CIK.dilationGap

/--
Split the observer residual into the canonical spectral-projector commutator and
an observer-deviation commutator.
-/
theorem observerOrientationResidual_eq_commutator_spectralProjector_add_commutator_deviation
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) :
    observerOrientationResidual CIK obs
      = DrazinSupercharge.commutator CIK.spectralProjector CIK.dilationGap
        + DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap := by
  unfold observerOrientationResidual
  rw [localSlice_eq_spectralProjector_add_observerProjectorDeviation (CIK := CIK) (obs := obs)]
  unfold DrazinSupercharge.commutator
  noncomm_ring

/--
Observer-side Cartan split through a chosen axis `sigma` on the geometric lane:
`2 • [L_obs, G] = [L_obs, sigma] + [L_obs, Xi]`, where `Xi := Γ_G - sigma`.

This is the observer analogue of the repo-native
`supercharge_eq_commutator_spectralProjector_sigma_add_commutator_spectralProjector_geometricMismatch`
surface, but it stays on the existing observer residual and uses no new ontology.
-/
theorem two_smul_observerOrientationResidual_eq_commutator_localSlice_sigma_add_commutator_localSlice_geometricMismatch
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (sigma : EndH) :
    (2 : ℝ) • observerOrientationResidual CIK obs
      = DrazinSupercharge.commutator obs.localSlice sigma
        + DrazinSupercharge.commutator obs.localSlice
            (DrazinSupercharge.CertifiedInverseKernel.geometricMismatch CIK sigma) := by
  have hGamma :
      (2 : ℝ) • observerOrientationResidual CIK obs
        = DrazinSupercharge.commutator obs.localSlice CIK.GammaG := by
    unfold observerOrientationResidual DrazinSupercharge.commutator
    rw [CIK.GammaG_eq_two_smul_dilationGap]
    change (2 : ℝ) • (obs.localSlice * CIK.dilationGap - CIK.dilationGap * obs.localSlice) =
      obs.localSlice * ((2 : ℝ) • CIK.dilationGap) - ((2 : ℝ) • CIK.dilationGap) * obs.localSlice
    simp only [two_smul, smul_add, sub_eq_add_neg, add_mul, mul_add, add_assoc]
    abel_nf
  calc
    (2 : ℝ) • observerOrientationResidual CIK obs
        = DrazinSupercharge.commutator obs.localSlice CIK.GammaG := hGamma
    _ = DrazinSupercharge.commutator obs.localSlice sigma
          + DrazinSupercharge.commutator obs.localSlice
              (DrazinSupercharge.CertifiedInverseKernel.geometricMismatch CIK sigma) := by
          rw [DrazinSupercharge.CertifiedInverseKernel.GammaG_eq_sigma_add_geometricMismatch (CIK := CIK) sigma]
          unfold DrazinSupercharge.commutator
          noncomm_ring

/--
Defect-compressed observer residual in the Drazin complementary block.
-/
noncomputable def observerDefectResidual
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) : EndH :=
  CIK.spectralComplementaryProjector *
    observerOrientationResidual CIK obs *
    CIK.spectralComplementaryProjector

/--
Defect-compressed observer residual rewritten through the spectral-projector and
observer-deviation commutator split.
-/
theorem observerDefectResidual_eq_projectorCompression_commutator_split
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) :
    observerDefectResidual CIK obs
      = CIK.spectralComplementaryProjector *
          (DrazinSupercharge.commutator CIK.spectralProjector CIK.dilationGap
            + DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap) *
          CIK.spectralComplementaryProjector := by
  unfold observerDefectResidual
  rw [observerOrientationResidual_eq_commutator_spectralProjector_add_commutator_deviation (CIK := CIK) (obs := obs)]

/--
The canonical spectral-projector commutator seed vanishes after defect-block
compression. The unrestricted observer defect therefore lives entirely in the
observer-deviation lane after `Q₀` compression.
-/
theorem projectorCompression_commutator_spectralProjector_dilationGap_eq_zero
    (CIK : CertifiedInverseKernel H₂) :
    CIK.spectralComplementaryProjector *
        DrazinSupercharge.commutator CIK.spectralProjector CIK.dilationGap *
        CIK.spectralComplementaryProjector
      = 0 := by
  set Q0 : EndH := CIK.spectralComplementaryProjector
  set P : EndH := CIK.spectralProjector
  set D : EndH := CIK.dilationGap
  have hQ0P : Q0 * P = 0 := by
    simpa [Q0, P] using CIK.spectralComplementaryProjector_mul_spectralProjector
  have hPQ0 : P * Q0 = 0 := by
    simpa [Q0, P] using CIK.spectralProjector_mul_spectralComplementaryProjector
  unfold DrazinSupercharge.commutator
  change Q0 * (P * D - D * P) * Q0 = 0
  calc
    Q0 * (P * D - D * P) * Q0
      = (Q0 * P) * D * Q0 - Q0 * D * (P * Q0) := by
          simp [sub_mul, mul_sub, mul_assoc]
    _ = 0 := by simp [hQ0P, hPQ0]

/--
Defect-compressed observer residual is exactly the defect-block compression of
its observer-deviation commutator. This isolates the only uncontrolled owner
term remaining in the unrestricted `observerDefectResidual ≤ Z_D` debt.
-/
theorem observerDefectResidual_eq_projectorCompression_commutator_deviation
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) :
    observerDefectResidual CIK obs
      = CIK.spectralComplementaryProjector *
          DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap *
          CIK.spectralComplementaryProjector := by
  rw [observerDefectResidual_eq_projectorCompression_commutator_split (CIK := CIK) (obs := obs)]
  have hZero := projectorCompression_commutator_spectralProjector_dilationGap_eq_zero (CIK := CIK)
  calc
    CIK.spectralComplementaryProjector *
        (DrazinSupercharge.commutator CIK.spectralProjector CIK.dilationGap
          + DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap) *
        CIK.spectralComplementaryProjector
      = CIK.spectralComplementaryProjector *
          DrazinSupercharge.commutator CIK.spectralProjector CIK.dilationGap *
          CIK.spectralComplementaryProjector
        + CIK.spectralComplementaryProjector *
          DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap *
          CIK.spectralComplementaryProjector := by
            simp [add_mul, mul_add]
    _ = 0 + CIK.spectralComplementaryProjector *
          DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap *
          CIK.spectralComplementaryProjector := by rw [hZero]
    _ = CIK.spectralComplementaryProjector *
          DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap *
          CIK.spectralComplementaryProjector := by simp

/--
Upstream target surface for closing the unrestricted D3 debt.

This is the exact remaining owner obligation after the canonical spectral seed is
shown to vanish under defect compression.
-/
def ObserverDeviationDefectCommutatorBoundedByZD
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) : Prop :=
  ‖CIK.spectralComplementaryProjector *
      DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap *
      CIK.spectralComplementaryProjector‖
    ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖

/--
The unrestricted observer-defect-to-`Z_D` debt reduces exactly to the norm bound
on the defect-compressed observer-deviation commutator.
-/
theorem observerDefectResidualBoundedByZD_of_deviation_bound
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hDevBound : ObserverDeviationDefectCommutatorBoundedByZD CIK obs) :
    ‖observerDefectResidual CIK obs‖ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖ := by
  rw [observerDefectResidual_eq_projectorCompression_commutator_deviation (CIK := CIK) (obs := obs)]
  exact hDevBound

/--
|Constructive `Z_D` control predicate for the remaining observer deviation
|channel.  This is the exact owner-level replacement for bridge-local residual
|budget assumptions.
|-/
def ObserverDeviationControlledByZD
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) : Prop :=
  ‖CIK.spectralComplementaryProjector *
      DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap *
      CIK.spectralComplementaryProjector‖
    ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖

/--
|A constructive witness for `ObserverDeviationControlledByZD`. It carries the
|norm bound as data, allowing downstream theorems to consume a concrete proof
|object instead of a bare `Prop` hypothesis.
|-/
structure ObserverDeviationControl (CIK : CertifiedInverseKernel H₂) (obs : ObserverL5 CIK) where
  bound : ‖CIK.spectralComplementaryProjector *
      DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap *
      CIK.spectralComplementaryProjector‖
    ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖

/-- Convert a constructive `ObserverDeviationControl` into the original `Prop`
|predicate. -/
@[simp]
theorem ObserverDeviationControlledByZD.of_control
    {CIK : CertifiedInverseKernel H₂} {obs : ObserverL5 CIK}
    (c : ObserverDeviationControl CIK obs) :
    ObserverDeviationControlledByZD CIK obs :=
  c.bound

/--
General observer-defect `Z_D` bound from the exact deviation-channel control.

The proof is constructive: the regular spectral-projector commutator is first
eliminated by defect compression, and the remaining term is precisely the
controlled deviation commutator.
-/
@[rep_depth krein]
theorem observerDefectResidual_norm_le_ZD
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hControl : ObserverDeviationControlledByZD CIK obs) :
    ‖observerDefectResidual CIK obs‖ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖ := by
  rw [observerDefectResidual_eq_projectorCompression_commutator_deviation (CIK := CIK) (obs := obs)]
  exact hControl

/--
The owner-level deviation-channel predicate is equivalent to the old residual
norm budget once the exact compressed-deviation identity is used.
-/
theorem observerDeviationControlledByZD_iff_observerDefectResidual_norm_le_ZD
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) :
    ObserverDeviationControlledByZD CIK obs ↔
      ‖observerDefectResidual CIK obs‖ ≤
        ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖ := by
  constructor
  · intro hControl
    exact observerDefectResidual_norm_le_ZD (CIK := CIK) (obs := obs) hControl
  · intro hBound
    unfold ObserverDeviationControlledByZD
    rw [← observerDefectResidual_eq_projectorCompression_commutator_deviation (CIK := CIK) (obs := obs)]
    exact hBound

/--
If the compressed observer-deviation channel itself vanishes, then the `Z_D`
control predicate is constructed without any residual-bound hypothesis.
-/
theorem observerDeviationControlledByZD_of_compressedDeviation_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hZero :
      CIK.spectralComplementaryProjector *
        DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap *
        CIK.spectralComplementaryProjector = 0) :
    ObserverDeviationControlledByZD CIK obs := by
  unfold ObserverDeviationControlledByZD
  rw [hZero]
  calc
    ‖(0 : EndH)‖ = 0 := ContinuousLinearMap.opNorm_zero
    _ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖ :=
      norm_nonneg (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK)

/--
If the compressed observer-deviation channel vanishes, then the observer defect
residual itself vanishes by the exact projector-compression identity.
-/
theorem observerDefectResidual_eq_zero_of_compressedDeviation_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hZero :
      CIK.spectralComplementaryProjector *
        DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap *
        CIK.spectralComplementaryProjector = 0) :
    observerDefectResidual CIK obs = 0 := by
  rw [observerDefectResidual_eq_projectorCompression_commutator_deviation (CIK := CIK) (obs := obs)]
  exact hZero

/--
If the compressed observer-deviation channel vanishes, then the observer defect
residual satisfies the `Z_D` budget constructively: the residual is zero, so
only `0 ≤ ‖Z_D‖` remains.
-/
@[rep_depth krein]
theorem observerDefectResidual_norm_le_ZD_of_compressedDeviation_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hZero :
      CIK.spectralComplementaryProjector *
        DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap *
        CIK.spectralComplementaryProjector = 0) :
    ‖observerDefectResidual CIK obs‖ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖ := by
  have hResidual : observerDefectResidual CIK obs = 0 :=
    observerDefectResidual_eq_zero_of_compressedDeviation_eq_zero (CIK := CIK) (obs := obs) hZero
  rw [hResidual]
  calc
    ‖(0 : EndH)‖ = 0 := ContinuousLinearMap.opNorm_zero
    _ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖ :=
      norm_nonneg (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK)

/--
Zero-Casimir/zero-defect-central collapse:
if the remaining observer deviation channel is controlled by `Z_D` and the
operatorial central defect channel itself is zero, then the observer defect
residual is zero.
-/
@[rep_depth krein]
theorem observerDefectResidual_eq_zero_of_deviationControlledByZD_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hControl : ObserverDeviationControlledByZD CIK obs)
    (hZD :
      InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0) :
    observerDefectResidual CIK obs = 0 := by
  have hBound :
      ‖observerDefectResidual CIK obs‖ ≤
        ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖ :=
    observerDefectResidual_norm_le_ZD (CIK := CIK) (obs := obs) hControl
  rw [hZD, norm_zero] at hBound
  have hNormZero : ‖observerDefectResidual CIK obs‖ = 0 :=
    le_antisymm hBound (norm_nonneg (observerDefectResidual CIK obs))
  exact norm_eq_zero.mp hNormZero

/--
Defect-compressed observer-side Cartan split through a chosen axis `sigma`.
-/
theorem two_smul_observerDefectResidual_eq_projectorCompression_commutator_localSlice_sigma_add_commutator_localSlice_geometricMismatch
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (sigma : EndH) :
    (2 : ℝ) • observerDefectResidual CIK obs
      = CIK.spectralComplementaryProjector *
          (DrazinSupercharge.commutator obs.localSlice sigma
            + DrazinSupercharge.commutator obs.localSlice
                (DrazinSupercharge.CertifiedInverseKernel.geometricMismatch CIK sigma)) *
          CIK.spectralComplementaryProjector := by
  unfold observerDefectResidual
  calc
    (2 : ℝ) •
        (CIK.spectralComplementaryProjector * observerOrientationResidual CIK obs *
          CIK.spectralComplementaryProjector)
      = CIK.spectralComplementaryProjector * ((2 : ℝ) • observerOrientationResidual CIK obs) *
          CIK.spectralComplementaryProjector := by
            simp only [two_smul, add_mul, mul_add]
    _ = CIK.spectralComplementaryProjector *
          (DrazinSupercharge.commutator obs.localSlice sigma
            + DrazinSupercharge.commutator obs.localSlice
                (DrazinSupercharge.CertifiedInverseKernel.geometricMismatch CIK sigma)) *
          CIK.spectralComplementaryProjector := by
            rw [two_smul_observerOrientationResidual_eq_commutator_localSlice_sigma_add_commutator_localSlice_geometricMismatch
              (CIK := CIK) (obs := obs) (sigma := sigma)]

/--
If the observer slice agrees with the certified spectral projector, the observer
orientation residual collapses to the canonical commutator seed.
-/
theorem observerOrientationResidual_eq_commutator_spectralProjector_of_deviation_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hDev : observerProjectorDeviation CIK obs = 0) :
    observerOrientationResidual CIK obs
      = DrazinSupercharge.commutator CIK.spectralProjector CIK.dilationGap := by
  rw [observerOrientationResidual_eq_commutator_spectralProjector_add_commutator_deviation (CIK := CIK) (obs := obs)]
  rw [hDev]
  simp [DrazinSupercharge.commutator]

/--
If the observer slice agrees with the certified spectral projector, the defect
residual is exactly the defect-block compression of the canonical commutator
seed.
-/
theorem observerDefectResidual_eq_projectorCompression_commutator_spectralProjector_of_deviation_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hDev : observerProjectorDeviation CIK obs = 0) :
    observerDefectResidual CIK obs
      = CIK.spectralComplementaryProjector *
          DrazinSupercharge.commutator CIK.spectralProjector CIK.dilationGap *
          CIK.spectralComplementaryProjector := by
  rw [observerDefectResidual_eq_projectorCompression_commutator_split (CIK := CIK) (obs := obs)]
  rw [hDev]
  simp [DrazinSupercharge.commutator, mul_assoc]

/--
If the observer slice agrees with the certified spectral projector, the defect
residual vanishes constructively: the defect-block compression of
`[P_D, G]` is zero because `Q₀ P_D = 0 = P_D Q₀`.
-/
theorem observerDefectResidual_eq_zero_of_deviation_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hDev : observerProjectorDeviation CIK obs = 0) :
    observerDefectResidual CIK obs = 0 := by
  rw [observerDefectResidual_eq_projectorCompression_commutator_spectralProjector_of_deviation_eq_zero
    (CIK := CIK) (obs := obs) hDev]
  unfold DrazinSupercharge.commutator
  have hQ0P : CIK.spectralComplementaryProjector * CIK.spectralProjector = 0 :=
    CIK.spectralComplementaryProjector_mul_spectralProjector
  have hPQ0 : CIK.spectralProjector * CIK.spectralComplementaryProjector = 0 :=
    CIK.spectralProjector_mul_spectralComplementaryProjector
  calc
    CIK.spectralComplementaryProjector *
        (CIK.spectralProjector * CIK.dilationGap - CIK.dilationGap * CIK.spectralProjector) *
        CIK.spectralComplementaryProjector
      = ((CIK.spectralComplementaryProjector * CIK.spectralProjector) * CIK.dilationGap) *
          CIK.spectralComplementaryProjector
        - (CIK.spectralComplementaryProjector * CIK.dilationGap) *
            (CIK.spectralProjector * CIK.spectralComplementaryProjector) := by
            noncomm_ring
    _ = (0 * CIK.dilationGap) * CIK.spectralComplementaryProjector
        - (CIK.spectralComplementaryProjector * CIK.dilationGap) * 0 := by rw [hQ0P, hPQ0]
    _ = 0 := by simp

/--
If the observer slice agrees with the certified spectral projector, the
observer-defect residual satisfies the `Z_D` budget constructively: the
residual itself is zero, so the remaining inequality is just `0 ≤ ‖Z_D‖`.
-/
@[rep_depth krein]
theorem observerDefectResidual_norm_le_ZD_of_deviation_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hDev : observerProjectorDeviation CIK obs = 0) :
    ‖observerDefectResidual CIK obs‖ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖ := by
  have hZero : observerDefectResidual CIK obs = 0 :=
    observerDefectResidual_eq_zero_of_deviation_eq_zero (CIK := CIK) (obs := obs) hDev
  rw [hZero]
  calc
    ‖(0 : EndH)‖ = 0 := ContinuousLinearMap.opNorm_zero
    _ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖ :=
      norm_nonneg (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK)

/--
If the observer slice agrees with the certified spectral projector, the exact
deviation-channel control predicate is constructed directly.
-/
theorem observerDeviationControlledByZD_of_deviation_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hDev : observerProjectorDeviation CIK obs = 0) :
    ObserverDeviationControlledByZD CIK obs := by
  rw [observerDeviationControlledByZD_iff_observerDefectResidual_norm_le_ZD (CIK := CIK) (obs := obs)]
  exact observerDefectResidual_norm_le_ZD_of_deviation_eq_zero (CIK := CIK) (obs := obs) hDev

/--
Defect compression is stable under left/right `Q₀` action.
-/
theorem observerDefectResidual_isDefectSupported
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) :
    CIK.spectralComplementaryProjector * observerDefectResidual CIK obs
      = observerDefectResidual CIK obs
      ∧
    observerDefectResidual CIK obs * CIK.spectralComplementaryProjector
      = observerDefectResidual CIK obs := by
  unfold observerDefectResidual
  constructor
  · calc
      CIK.spectralComplementaryProjector *
          (CIK.spectralComplementaryProjector * observerOrientationResidual CIK obs *
            CIK.spectralComplementaryProjector)
          =
        (CIK.spectralComplementaryProjector * CIK.spectralComplementaryProjector) *
          observerOrientationResidual CIK obs *
          CIK.spectralComplementaryProjector := by
            simp [mul_assoc]
      _ =
        CIK.spectralComplementaryProjector * observerOrientationResidual CIK obs *
          CIK.spectralComplementaryProjector := by
            simp [CIK.spectralComplementaryProjector_idempotent]
  · calc
      (CIK.spectralComplementaryProjector * observerOrientationResidual CIK obs *
          CIK.spectralComplementaryProjector) *
        CIK.spectralComplementaryProjector
          =
        CIK.spectralComplementaryProjector * observerOrientationResidual CIK obs *
          (CIK.spectralComplementaryProjector * CIK.spectralComplementaryProjector) := by
            simp [mul_assoc]
      _ =
        CIK.spectralComplementaryProjector * observerOrientationResidual CIK obs *
          CIK.spectralComplementaryProjector := by
            simp [CIK.spectralComplementaryProjector_idempotent]

/--
Defect residual commutes with the complementary projector.
-/
theorem observerDefectResidual_commutes_complementaryProjector
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) :
    Commute (observerDefectResidual CIK obs) CIK.spectralComplementaryProjector := by
  have h := observerDefectResidual_isDefectSupported (CIK := CIK) (obs := obs)
  calc
    observerDefectResidual CIK obs * CIK.spectralComplementaryProjector
      = observerDefectResidual CIK obs := h.2
    _ = CIK.spectralComplementaryProjector * observerDefectResidual CIK obs := h.1.symm

/--
Aligned observer (zero primary residual) yields zero defect residual.
-/
theorem observerDefectResidual_eq_zero_of_aligned
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hAlign : observerOrientationResidual CIK obs = 0) :
    observerDefectResidual CIK obs = 0 := by
  unfold observerDefectResidual
  simp [hAlign]

/--
Aligned observers satisfy the `Z_D` budget constructively: alignment collapses
observer defect residuals to `0`, and the remaining norm bound is immediate.
-/
@[rep_depth krein]
theorem observerDefectResidual_norm_le_ZD_of_aligned
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hAlign : observerOrientationResidual CIK obs = 0) :
    ‖observerDefectResidual CIK obs‖ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖ := by
  have hZero : observerDefectResidual CIK obs = 0 :=
    observerDefectResidual_eq_zero_of_aligned (CIK := CIK) (obs := obs) hAlign
  rw [hZero]
  calc
    ‖(0 : EndH)‖ = 0 := ContinuousLinearMap.opNorm_zero
    _ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖ :=
      norm_nonneg (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK)

/--
Aligned observers construct the exact deviation-channel control predicate.
-/
theorem observerDeviationControlledByZD_of_aligned
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hAlign : observerOrientationResidual CIK obs = 0) :
    ObserverDeviationControlledByZD CIK obs := by
  rw [observerDeviationControlledByZD_iff_observerDefectResidual_norm_le_ZD (CIK := CIK) (obs := obs)]
  exact observerDefectResidual_norm_le_ZD_of_aligned (CIK := CIK) (obs := obs) hAlign

/--
Scalarized observer strain (pre-thermodynamic cost) via operator norm.
-/
noncomputable def observerOrientationStrain
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) : ℝ :=
  ‖observerDefectResidual CIK obs‖

/--
Zero strain iff zero defect residual.
-/
theorem observerOrientationStrain_eq_zero_iff
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) :
    observerOrientationStrain CIK obs = 0 ↔ observerDefectResidual CIK obs = 0 := by
  show ‖observerDefectResidual CIK obs‖ = 0 ↔ observerDefectResidual CIK obs = 0
  exact norm_eq_zero

/--
If the compressed observer-deviation channel vanishes, then the scalarized
observer strain already vanishes. This lets downstream callers carry the
smaller compressed witness instead of a separate `observerOrientationStrain = 0`
packet.
-/
theorem observerOrientationStrain_eq_zero_of_compressedDeviation_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hZero :
      CIK.spectralComplementaryProjector *
        DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap *
        CIK.spectralComplementaryProjector = 0) :
    observerOrientationStrain CIK obs = 0 := by
  exact
    (observerOrientationStrain_eq_zero_iff (CIK := CIK) (obs := obs)).2
      (observerDefectResidual_eq_zero_of_compressedDeviation_eq_zero
        (CIK := CIK) (obs := obs) hZero)

/--
If the observer slice agrees with the certified spectral projector, then the
scalarized observer strain already vanishes. This exposes the smaller
`observerProjectorDeviation = 0` witness as a direct owner route to the
strain-zero surface.
-/
theorem observerOrientationStrain_eq_zero_of_deviation_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hDev : observerProjectorDeviation CIK obs = 0) :
    observerOrientationStrain CIK obs = 0 := by
  exact
    (observerOrientationStrain_eq_zero_iff (CIK := CIK) (obs := obs)).2
      (observerDefectResidual_eq_zero_of_deviation_eq_zero
        (CIK := CIK) (obs := obs) hDev)

/--
A zero scalarized observer strain already forces the defect residual itself to
vanish.
-/
theorem observerDefectResidual_eq_zero_of_strain_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hStrain : observerOrientationStrain CIK obs = 0) :
    observerDefectResidual CIK obs = 0 := by
  exact (observerOrientationStrain_eq_zero_iff (CIK := CIK) (obs := obs)).mp hStrain

/--
Zero scalarized observer strain yields the observer-defect `Z_D` budget
constructively because the defect residual itself is already zero.
-/
@[rep_depth krein]
theorem observerDefectResidual_norm_le_ZD_of_strain_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hStrain : observerOrientationStrain CIK obs = 0) :
    ‖observerDefectResidual CIK obs‖ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖ := by
  have hZero : observerDefectResidual CIK obs = 0 :=
    observerDefectResidual_eq_zero_of_strain_eq_zero (CIK := CIK) (obs := obs) hStrain
  rw [hZero]
  calc
    ‖(0 : EndH)‖ = 0 := ContinuousLinearMap.opNorm_zero
    _ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖ :=
      norm_nonneg (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK)

/--
Zero scalarized observer strain constructs the exact deviation-channel control
predicate, replacing a bridge-local residual-budget hypothesis by an honest
owner-level theorem.
-/
theorem observerDeviationControlledByZD_of_strain_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hStrain : observerOrientationStrain CIK obs = 0) :
    ObserverDeviationControlledByZD CIK obs := by
  rw [observerDeviationControlledByZD_iff_observerDefectResidual_norm_le_ZD (CIK := CIK) (obs := obs)]
  exact observerDefectResidual_norm_le_ZD_of_strain_eq_zero (CIK := CIK) (obs := obs) hStrain

/--
Under zero central defect, scalarized observer strain is equivalent to the exact
owner-side `Z_D` deviation-control predicate. This lets downstream callers use
whichever witness they already own instead of carrying both packets.
-/
theorem observerOrientationStrain_eq_zero_iff_deviationControlledByZD_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hZD : InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0) :
    observerOrientationStrain CIK obs = 0 ↔ ObserverDeviationControlledByZD CIK obs := by
  constructor
  · intro hStrain
    exact observerDeviationControlledByZD_of_strain_eq_zero (CIK := CIK) (obs := obs) hStrain
  · intro hControl
    have hResidual : observerDefectResidual CIK obs = 0 :=
      observerDefectResidual_eq_zero_of_deviationControlledByZD_of_ZD_eq_zero
        (CIK := CIK) (obs := obs) hControl hZD
    exact (observerOrientationStrain_eq_zero_iff (CIK := CIK) (obs := obs)).2 hResidual

/--
Under zero central defect, exact owner-side `Z_D` deviation control directly
forces zero scalarized observer strain. This is the one-way export of
`observerOrientationStrain_eq_zero_iff_deviationControlledByZD_of_ZD_eq_zero`
for downstream callers that already own the control witness.
-/
theorem observerOrientationStrain_eq_zero_of_deviationControlledByZD_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hZD : InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0)
    (hControl : ObserverDeviationControlledByZD CIK obs) :
    observerOrientationStrain CIK obs = 0 := by
  exact
    (observerOrientationStrain_eq_zero_iff_deviationControlledByZD_of_ZD_eq_zero
      (CIK := CIK) (obs := obs) hZD).2 hControl

end Core

end InfoGeometry.Canonical.ObserverDefect

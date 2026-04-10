import InfoGeometry.Canonical.SuperchargeTransportBridge
import InfoGeometry.Canonical.BogoliubovProjectorFlux
import InfoGeometry.Quantum.SplitTrialityKernel
import Mathlib.Tactic.Abel

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.VortexAnomalyLink

Canonical source/sink boundary package for the doubled-carrier anomaly lane.

This file does not introduce a new boundary ontology. It condenses already-owned
surfaces:

- the spectral plus/minus projectors on the doubled carrier,
- the `J`-mirror exchange between those sectors,
- the projected nilpotent half-charge channels from the split-triality kernel,
- and the transport defect seeds obtained by commuting the connection generator
  with the canonical source/sink projectors.
-/

namespace InfoGeometry.Canonical.VortexAnomalyLink

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Canonical.BogoliubovProjectorTransport
open InfoGeometry.Canonical.BogoliubovProjectorFlux
open InfoGeometry.Quantum
open InfoGeometry.Quantum.RealMajoranaCategory

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "Xc" => cl11DoubledCore E
local notation "EndX" => Xc →ₗ[ℝ] Xc

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Canonical source/sink projector pair on the doubled carrier. -/
@[rep_depth krein]
structure VortexPair where
  source : EndH
  sink : EndH
  source_idem : source.comp source = source
  sink_idem : sink.comp sink = sink
  source_sink_orth : source.comp sink = 0
  sink_source_orth : sink.comp source = 0
  sum_id : source + sink = ContinuousLinearMap.id ℝ H₂
  source_comm_eps :
    source.comp (modularSignEpsilon (E := E)) =
      (modularSignEpsilon (E := E)).comp source
  sink_comm_eps :
    sink.comp (modularSignEpsilon (E := E)) =
      (modularSignEpsilon (E := E)).comp sink
  source_comp_J :
    source.comp (modularConjugationJ (E := E)) =
      (modularConjugationJ (E := E)).comp sink
  sink_comp_J :
    sink.comp (modularConjugationJ (E := E)) =
      (modularConjugationJ (E := E)).comp source

/-- The canonical vortex/antivortex pair is the spectral plus/minus polarization. -/
@[rep_depth krein]
noncomputable def canonicalVortexPair : VortexPair (E := E) where
  source := spectralPlusProj (E := E)
  sink := spectralMinusProj (E := E)
  source_idem := spectralPlusProj_idempotent (E := E)
  sink_idem := spectralMinusProj_idempotent (E := E)
  source_sink_orth := spectralPlusProj_comp_spectralMinusProj (E := E)
  sink_source_orth := spectralMinusProj_comp_spectralPlusProj (E := E)
  sum_id := spectralProj_sum (E := E)
  source_comm_eps := by
    simpa [modularSignEpsilon] using spectralPlusProj_comm_Pi (E := E)
  sink_comm_eps := by
    simpa [modularSignEpsilon] using spectralMinusProj_comm_Pi (E := E)
  source_comp_J := spectralPlusProj_comp_J (E := E)
  sink_comp_J := spectralMinusProj_comp_J (E := E)

@[rep_depth krein]
theorem canonicalVortexPair_source_comm_spectral_epsilon :
    (canonicalVortexPair (E := E)).source.comp (spectral_epsilon (E := E))
      =
    (spectral_epsilon (E := E)).comp (canonicalVortexPair (E := E)).source := by
  simpa [TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon] using
    (canonicalVortexPair (E := E)).source_comm_eps

@[rep_depth krein]
theorem canonicalVortexPair_sink_comm_spectral_epsilon :
    (canonicalVortexPair (E := E)).sink.comp (spectral_epsilon (E := E))
      =
    (spectral_epsilon (E := E)).comp (canonicalVortexPair (E := E)).sink := by
  simpa [TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon] using
    (canonicalVortexPair (E := E)).sink_comm_eps

@[rep_depth krein]
theorem canonicalVortexPair_source_comp_modular_j :
    (canonicalVortexPair (E := E)).source.comp (modular_j (E := E))
      =
    (modular_j (E := E)).comp (canonicalVortexPair (E := E)).sink := by
  simpa [TomitaTakesaki.modularConjugationJ_eq_modular_j] using
    (canonicalVortexPair (E := E)).source_comp_J

@[rep_depth krein]
theorem canonicalVortexPair_sink_comp_modular_j :
    (canonicalVortexPair (E := E)).sink.comp (modular_j (E := E))
      =
    (modular_j (E := E)).comp (canonicalVortexPair (E := E)).source := by
  simpa [TomitaTakesaki.modularConjugationJ_eq_modular_j] using
    (canonicalVortexPair (E := E)).sink_comp_J

/-- Projected nilpotency predicate: the supercharge becomes cohomological only after projection. -/
@[rep_depth krein]
def ProjectedNilpotentOn (Q P : EndX) : Prop :=
  (Q.comp P).comp (Q.comp P) = 0

/-- Canonical boundary source half-charge: the triality supercharge projected to the `+` sector. -/
@[rep_depth krein]
noncomputable abbrev canonicalSourceBoundarySupercharge : EndX :=
  (canonicalSplitTrialityKernel (E := E)).trialitySupercharge.comp
    (canonicalSplitTrialityKernel (E := E)).polarization.Pplus

/-- Canonical boundary sink half-charge: the triality supercharge projected to the `-` sector. -/
@[rep_depth krein]
noncomputable abbrev canonicalSinkBoundarySupercharge : EndX :=
  (canonicalSplitTrialityKernel (E := E)).trialitySupercharge.comp
    (canonicalSplitTrialityKernel (E := E)).polarization.Pminus

@[simp, rep_depth krein]
theorem canonicalSourceBoundarySupercharge_eq_left :
    canonicalSourceBoundarySupercharge (E := E)
      = (canonicalSplitTrialityKernel (E := E)).vectorToLeftSpinor :=
  SplitTrialityKernel.trialitySupercharge_comp_plus_eq_left
    (canonicalSplitTrialityKernel (E := E))

@[simp, rep_depth krein]
theorem canonicalSinkBoundarySupercharge_eq_right :
    canonicalSinkBoundarySupercharge (E := E)
      = (canonicalSplitTrialityKernel (E := E)).vectorToRightSpinor :=
  SplitTrialityKernel.trialitySupercharge_comp_minus_eq_right
    (canonicalSplitTrialityKernel (E := E))

/-- The projected source boundary half-charge is nilpotent. -/
@[simp, rep_depth krein]
theorem canonicalSourceBoundarySupercharge_sq_eq_zero :
    (canonicalSourceBoundarySupercharge (E := E)).comp
        (canonicalSourceBoundarySupercharge (E := E))
      = 0 := by
  rw [canonicalSourceBoundarySupercharge_eq_left (E := E)]
  exact (canonicalSplitTrialityKernel (E := E)).left_nilpotent

/-- The projected sink boundary half-charge is nilpotent. -/
@[simp, rep_depth krein]
theorem canonicalSinkBoundarySupercharge_sq_eq_zero :
    (canonicalSinkBoundarySupercharge (E := E)).comp
        (canonicalSinkBoundarySupercharge (E := E))
      = 0 := by
  rw [canonicalSinkBoundarySupercharge_eq_right (E := E)]
  exact (canonicalSplitTrialityKernel (E := E)).right_nilpotent

@[rep_depth krein]
theorem canonicalSourceBoundarySupercharge_projectedNilpotent :
    ProjectedNilpotentOn
      ((canonicalSplitTrialityKernel (E := E)).trialitySupercharge)
      ((canonicalSplitTrialityKernel (E := E)).polarization.Pplus) := by
  exact canonicalSourceBoundarySupercharge_sq_eq_zero (E := E)

@[rep_depth krein]
theorem canonicalSinkBoundarySupercharge_projectedNilpotent :
    ProjectedNilpotentOn
      ((canonicalSplitTrialityKernel (E := E)).trialitySupercharge)
      ((canonicalSplitTrialityKernel (E := E)).polarization.Pminus) := by
  exact canonicalSinkBoundarySupercharge_sq_eq_zero (E := E)

/-- Source-side transport defect seed: commutator of the connection with the `+` projector. -/
@[rep_depth transport]
noncomputable abbrev sourceVortexSeed
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) : EndH :=
  transportCommutator (E := E) V.connectionGenerator (canonicalVortexPair (E := E)).source

/-- Sink-side transport defect seed: commutator of the connection with the `-` projector. -/
@[rep_depth transport]
noncomputable abbrev sinkVortexSeed
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) : EndH :=
  transportCommutator (E := E) V.connectionGenerator (canonicalVortexPair (E := E)).sink

/-- The source defect seed is exactly the negative positive-projector flux. -/
@[simp, rep_depth transport]
theorem sourceVortexSeed_eq_neg_plusProjectorFlux
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    sourceVortexSeed (E := E) V = -(plusProjectorFlux (E := E) V.connectionGenerator) := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext
  · simp [sourceVortexSeed, plusProjectorFlux, transportCommutator, canonicalVortexPair,
      sub_eq_add_neg]
  · simp [sourceVortexSeed, plusProjectorFlux, transportCommutator, canonicalVortexPair,
      sub_eq_add_neg]

/-- The sink defect seed is exactly the negative negative-projector flux. -/
@[simp, rep_depth transport]
theorem sinkVortexSeed_eq_neg_minusProjectorFlux
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    sinkVortexSeed (E := E) V = -(minusProjectorFlux (E := E) V.connectionGenerator) := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext
  · simp [sinkVortexSeed, minusProjectorFlux, transportCommutator, canonicalVortexPair,
      sub_eq_add_neg]
  · simp [sinkVortexSeed, minusProjectorFlux, transportCommutator, canonicalVortexPair,
      sub_eq_add_neg]

/-- The source and sink defect seeds sum to zero because `P₊ + P₋ = 1`. -/
@[simp, rep_depth transport]
theorem sourceVortexSeed_add_sinkVortexSeed_eq_zero
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    sourceVortexSeed (E := E) V + sinkVortexSeed (E := E) V = 0 := by
  calc
    sourceVortexSeed (E := E) V + sinkVortexSeed (E := E) V
        =
      transportCommutator (E := E) V.connectionGenerator
        ((canonicalVortexPair (E := E)).source + (canonicalVortexPair (E := E)).sink) := by
          apply ContinuousLinearMap.ext
          intro x
          apply DoubledSpace.ext
          · simp [sourceVortexSeed, sinkVortexSeed, transportCommutator, canonicalVortexPair,
              ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp, sub_eq_add_neg]
            abel_nf
          · simp [sourceVortexSeed, sinkVortexSeed, transportCommutator, canonicalVortexPair,
              ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp, sub_eq_add_neg]
            abel_nf
    _ = transportCommutator (E := E) V.connectionGenerator (ContinuousLinearMap.id ℝ H₂) := by
          rw [(canonicalVortexPair (E := E)).sum_id]
    _ = 0 := by
          unfold transportCommutator
          simp

/--
If the connection generator commutes with `J`, the source defect seed is
carried to the sink defect seed by the `J`-mirror.
-/
@[rep_depth transport]
theorem sourceVortexSeed_comp_J_eq_J_comp_sinkVortexSeed_of_commute_modularJ
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (hComm : Commute (modularConjugationJ (E := E)) V.connectionGenerator) :
    (sourceVortexSeed (E := E) V).comp (modularConjugationJ (E := E))
      =
    (modularConjugationJ (E := E)).comp (sinkVortexSeed (E := E) V) := by
  let H : EndH := V.connectionGenerator
  let J : EndH := modularConjugationJ (E := E)
  let Pplus : EndH := (canonicalVortexPair (E := E)).source
  let Pminus : EndH := (canonicalVortexPair (E := E)).sink
  have hHJ : H.comp J = J.comp H := by
    simpa [H, J] using hComm.eq.symm
  have hPJ : Pplus.comp J = J.comp Pminus := (canonicalVortexPair (E := E)).source_comp_J
  calc
    (sourceVortexSeed (E := E) V).comp J
        = (H.comp Pplus - Pplus.comp H).comp J := by
            rfl
    _ = H.comp (Pplus.comp J) - Pplus.comp (H.comp J) := by
          simp [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc]
    _ = H.comp (J.comp Pminus) - Pplus.comp (J.comp H) := by
          rw [hPJ, hHJ]
    _ = (H.comp J).comp Pminus - (Pplus.comp J).comp H := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (J.comp H).comp Pminus - (J.comp Pminus).comp H := by
          rw [hHJ, hPJ]
    _ = J.comp (H.comp Pminus) - J.comp (Pminus.comp H) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = J.comp (H.comp Pminus - Pminus.comp H) := by
          simp [sub_eq_add_neg, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_neg]
    _ = J.comp (sinkVortexSeed (E := E) V) := by
          rfl

/--
If the connection generator commutes with `J`, the sink defect seed is
carried to the source defect seed by the `J`-mirror.
-/
@[rep_depth transport]
theorem sinkVortexSeed_comp_J_eq_J_comp_sourceVortexSeed_of_commute_modularJ
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (hComm : Commute (modularConjugationJ (E := E)) V.connectionGenerator) :
    (sinkVortexSeed (E := E) V).comp (modularConjugationJ (E := E))
      =
    (modularConjugationJ (E := E)).comp (sourceVortexSeed (E := E) V) := by
  let H : EndH := V.connectionGenerator
  let J : EndH := modularConjugationJ (E := E)
  let Pplus : EndH := (canonicalVortexPair (E := E)).source
  let Pminus : EndH := (canonicalVortexPair (E := E)).sink
  have hHJ : H.comp J = J.comp H := by
    simpa [H, J] using hComm.eq.symm
  have hPJ : Pminus.comp J = J.comp Pplus := (canonicalVortexPair (E := E)).sink_comp_J
  calc
    (sinkVortexSeed (E := E) V).comp J
        = (H.comp Pminus - Pminus.comp H).comp J := by
            rfl
    _ = H.comp (Pminus.comp J) - Pminus.comp (H.comp J) := by
          simp [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc]
    _ = H.comp (J.comp Pplus) - Pminus.comp (J.comp H) := by
          rw [hPJ, hHJ]
    _ = (H.comp J).comp Pplus - (Pminus.comp J).comp H := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (J.comp H).comp Pplus - (J.comp Pplus).comp H := by
          rw [hHJ, hPJ]
    _ = J.comp (H.comp Pplus) - J.comp (Pplus.comp H) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = J.comp (H.comp Pplus - Pplus.comp H) := by
          simp [sub_eq_add_neg, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_neg]
    _ = J.comp (sourceVortexSeed (E := E) V) := by
          rfl

end Core

end InfoGeometry.Canonical.VortexAnomalyLink

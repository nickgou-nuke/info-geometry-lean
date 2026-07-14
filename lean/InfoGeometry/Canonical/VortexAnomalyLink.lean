import InfoGeometry.Canonical.SuperchargeTransportBridge
import InfoGeometry.Canonical.BogoliubovProjectorFlux
import InfoGeometry.Canonical.CentralChargeKKTParityBridge
import InfoGeometry.Canonical.SpinorModularBridge
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

namespace VortexAnomalyLink

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Canonical.BogoliubovProjectorTransport
open InfoGeometry.Canonical.BogoliubovProjectorFlux
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Canonical.CentralChargeKKTParityBridge
open InfoGeometry.Canonical.QuasilatticeDirac
open InfoGeometry.Canonical.SpinorModularBridge
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Quantum
open InfoGeometry.Quantum.RealMajoranaCategory
open InfoGeometry.Quantum.BulkBoundary
open InfoGeometry.Quantum.RealMajorana

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
  let H : EndH := V.connectionGenerator
  let Pplus : EndH := (canonicalVortexPair (E := E)).source
  let Pminus : EndH := (canonicalVortexPair (E := E)).sink
  calc
    sourceVortexSeed (E := E) V + sinkVortexSeed (E := E) V
        = transportCommutator (E := E) H (Pplus + Pminus) := by
            simp [sourceVortexSeed, sinkVortexSeed, transportCommutator, H, Pplus, Pminus,
              ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp, sub_eq_add_neg,
              add_assoc, add_left_comm, add_comm]
    _ = transportCommutator (E := E) H (ContinuousLinearMap.id ℝ H₂) := by
          rw [(canonicalVortexPair (E := E)).sum_id]
    _ = 0 := by
          unfold transportCommutator
          simp

/-- Equivalent commutator closure form: the source seed is the negative sink seed. -/
@[simp, rep_depth transport]
theorem sourceVortexSeed_eq_neg_sinkVortexSeed
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    sourceVortexSeed (E := E) V = -(sinkVortexSeed (E := E) V) := by
  have hsum : sourceVortexSeed (E := E) V + sinkVortexSeed (E := E) V = 0 :=
    sourceVortexSeed_add_sinkVortexSeed_eq_zero (E := E) V
  exact eq_neg_of_add_eq_zero_left hsum

/--
Commutator/anticommutator closure on the canonical source/sink split:
the source and sink anticommutator channels add to `2H`.
-/
@[simp, rep_depth transport]
theorem sourceSinkAnticommutator_sum_eq_two_smul_connectionGenerator
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    InfoGeometry.Quantum.RealMajorana.anticommutator
        (S := H₂)
        V.connectionGenerator (canonicalVortexPair (E := E)).source
      +
      InfoGeometry.Quantum.RealMajorana.anticommutator
        (S := H₂)
        V.connectionGenerator (canonicalVortexPair (E := E)).sink
      =
    (2 : ℝ) • V.connectionGenerator := by
  let H : EndH := V.connectionGenerator
  let Pplus : EndH := (canonicalVortexPair (E := E)).source
  let Pminus : EndH := (canonicalVortexPair (E := E)).sink
  calc
    InfoGeometry.Quantum.RealMajorana.anticommutator (S := H₂) H Pplus
        +
        InfoGeometry.Quantum.RealMajorana.anticommutator (S := H₂) H Pminus
      =
        InfoGeometry.Quantum.RealMajorana.anticommutator (S := H₂) H (Pplus + Pminus) := by
          simp [InfoGeometry.Quantum.RealMajorana.anticommutator, H, Pplus, Pminus,
            ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
            add_left_comm, add_comm]
    _ =
        InfoGeometry.Quantum.RealMajorana.anticommutator
          (S := H₂) H (ContinuousLinearMap.id ℝ H₂) := by
            rw [(canonicalVortexPair (E := E)).sum_id]
    _ = H.comp (ContinuousLinearMap.id ℝ H₂) + (ContinuousLinearMap.id ℝ H₂).comp H := by
          rfl
    _ = H + H := by simp
    _ = (2 : ℝ) • H := by simp [two_smul]
    _ = (2 : ℝ) • V.connectionGenerator := rfl

/-- Canonical source-minus-sink projector identity `P₊ - P₋ = ε`. -/
@[simp, rep_depth krein]
theorem canonicalVortexPair_source_sub_sink_eq_spectral_epsilon :
    (canonicalVortexPair (E := E)).source - (canonicalVortexPair (E := E)).sink
      = spectral_epsilon (E := E) := by
  ext u
  · calc
      WithLp.fst (((canonicalVortexPair (E := E)).source - (canonicalVortexPair (E := E)).sink) u)
          = (2⁻¹ : ℝ) • WithLp.fst u + (2⁻¹ : ℝ) • WithLp.fst u := by
              simp [canonicalVortexPair, spectralPlusProj, spectralMinusProj, sub_eq_add_neg]
      _ = ((2⁻¹ : ℝ) + (2⁻¹ : ℝ)) • WithLp.fst u := by
            simp [add_smul]
      _ = (1 : ℝ) • WithLp.fst u := by norm_num
      _ = WithLp.fst ((spectral_epsilon (E := E)) u) := by
            simp [spectral_epsilon_apply]
  · have hsnd :
        ((2 : ℝ)⁻¹) • WithLp.snd u + ((2 : ℝ)⁻¹) • WithLp.snd u = WithLp.snd u := by
        calc
          ((2 : ℝ)⁻¹) • WithLp.snd u + ((2 : ℝ)⁻¹) • WithLp.snd u
              = (((2 : ℝ)⁻¹) + ((2 : ℝ)⁻¹)) • WithLp.snd u := by
                  simp [add_smul]
          _ = (1 : ℝ) • WithLp.snd u := by norm_num
          _ = WithLp.snd u := by simp
    calc
      WithLp.snd (((canonicalVortexPair (E := E)).source - (canonicalVortexPair (E := E)).sink) u)
          = -(((2 : ℝ)⁻¹) • WithLp.snd u + ((2 : ℝ)⁻¹) • WithLp.snd u) := by
              simp [canonicalVortexPair, spectralPlusProj, spectralMinusProj, sub_eq_add_neg,
                add_comm, add_left_comm]
      _ = -WithLp.snd u := by simp [hsnd]
      _ = WithLp.snd ((spectral_epsilon (E := E)) u) := by
            simp [spectral_epsilon_apply]

/--
Commutator closure identity:
the source-minus-sink defect split is exactly the transport commutator against
the grading axis `ε`.
-/
@[simp, rep_depth transport]
theorem sourceVortexSeed_sub_sinkVortexSeed_eq_transportCommutator_spectral_epsilon
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    sourceVortexSeed (E := E) V - sinkVortexSeed (E := E) V
      = transportCommutator (E := E) V.connectionGenerator (spectral_epsilon (E := E)) := by
  let H : EndH := V.connectionGenerator
  let Pplus : EndH := (canonicalVortexPair (E := E)).source
  let Pminus : EndH := (canonicalVortexPair (E := E)).sink
  have h_sub_right (A B : EndH) :
      transportCommutator (E := E) H (A - B)
        = transportCommutator (E := E) H A - transportCommutator (E := E) H B := by
    apply ContinuousLinearMap.ext
    intro x
    simp [transportCommutator, sub_eq_add_neg]
    abel_nf
  calc
    sourceVortexSeed (E := E) V - sinkVortexSeed (E := E) V
      = transportCommutator (E := E) H Pplus - transportCommutator (E := E) H Pminus := by
          rfl
    _ = transportCommutator (E := E) H (Pplus - Pminus) := by
          rw [h_sub_right]
    _ = transportCommutator (E := E) H (spectral_epsilon (E := E)) := by
          rw [canonicalVortexPair_source_sub_sink_eq_spectral_epsilon (E := E)]
    _ = transportCommutator (E := E) V.connectionGenerator (spectral_epsilon (E := E)) := rfl

/--
Anticommutator closure identity:
the source-minus-sink anticommutator split is exactly the anticommutator
against the grading axis `ε`.
-/
@[simp, rep_depth transport]
theorem sourceSinkAnticommutator_sub_eq_anticommutator_spectral_epsilon
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    InfoGeometry.Quantum.RealMajorana.anticommutator
        (S := H₂)
        V.connectionGenerator (canonicalVortexPair (E := E)).source
      -
      InfoGeometry.Quantum.RealMajorana.anticommutator
        (S := H₂)
        V.connectionGenerator (canonicalVortexPair (E := E)).sink
      =
    InfoGeometry.Quantum.RealMajorana.anticommutator
      (S := H₂)
      V.connectionGenerator (spectral_epsilon (E := E)) := by
  let H : EndH := V.connectionGenerator
  let Pplus : EndH := (canonicalVortexPair (E := E)).source
  let Pminus : EndH := (canonicalVortexPair (E := E)).sink
  have h_sub_right (A B : EndH) :
      InfoGeometry.Quantum.RealMajorana.anticommutator
          (S := H₂) H (A - B)
        =
      InfoGeometry.Quantum.RealMajorana.anticommutator
          (S := H₂) H A
        -
      InfoGeometry.Quantum.RealMajorana.anticommutator
          (S := H₂) H B := by
    apply ContinuousLinearMap.ext
    intro x
    simp [InfoGeometry.Quantum.RealMajorana.anticommutator, sub_eq_add_neg]
    abel_nf
  calc
    InfoGeometry.Quantum.RealMajorana.anticommutator (S := H₂) H Pplus
        -
        InfoGeometry.Quantum.RealMajorana.anticommutator (S := H₂) H Pminus
      =
        InfoGeometry.Quantum.RealMajorana.anticommutator (S := H₂) H (Pplus - Pminus) := by
          rw [h_sub_right]
    _ =
        InfoGeometry.Quantum.RealMajorana.anticommutator
          (S := H₂) H (spectral_epsilon (E := E)) := by
            rw [canonicalVortexPair_source_sub_sink_eq_spectral_epsilon (E := E)]
    _ =
        InfoGeometry.Quantum.RealMajorana.anticommutator
          (S := H₂) V.connectionGenerator (spectral_epsilon (E := E)) := rfl

/--
Commutator inversion (source channel):
the grading-axis commutator is exactly twice the source vortex seed.
-/
@[simp, rep_depth transport]
theorem transportCommutator_spectral_epsilon_eq_two_smul_sourceVortexSeed
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    transportCommutator (E := E) V.connectionGenerator (spectral_epsilon (E := E))
      = (2 : ℝ) • sourceVortexSeed (E := E) V := by
  let src : EndH := sourceVortexSeed (E := E) V
  let snk : EndH := sinkVortexSeed (E := E) V
  have hsum : src + snk = 0 := by
    simpa [src, snk] using sourceVortexSeed_add_sinkVortexSeed_eq_zero (E := E) V
  have hsink : snk = -src := by
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hsum)
  calc
    transportCommutator (E := E) V.connectionGenerator (spectral_epsilon (E := E))
      = src - snk := by
          simpa [src, snk] using
            (sourceVortexSeed_sub_sinkVortexSeed_eq_transportCommutator_spectral_epsilon
              (E := E) V).symm
    _ = src + src := by
          simp [sub_eq_add_neg, hsink]
    _ = (2 : ℝ) • src := by
          simp [two_smul]
    _ = (2 : ℝ) • sourceVortexSeed (E := E) V := rfl

/--
Commutator inversion (sink channel):
the grading-axis commutator is exactly minus twice the sink vortex seed.
-/
@[simp, rep_depth transport]
theorem transportCommutator_spectral_epsilon_eq_neg_two_smul_sinkVortexSeed
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    transportCommutator (E := E) V.connectionGenerator (spectral_epsilon (E := E))
      = (-(2 : ℝ)) • sinkVortexSeed (E := E) V := by
  calc
    transportCommutator (E := E) V.connectionGenerator (spectral_epsilon (E := E))
      = (2 : ℝ) • sourceVortexSeed (E := E) V := by
          exact transportCommutator_spectral_epsilon_eq_two_smul_sourceVortexSeed (E := E) V
    _ = (2 : ℝ) • (-(sinkVortexSeed (E := E) V)) := by
          rw [sourceVortexSeed_eq_neg_sinkVortexSeed (E := E) V]
    _ = (-(2 : ℝ)) • sinkVortexSeed (E := E) V := by
          simp [smul_neg]

/--
Source channel reconstruction:
the source vortex seed is half the grading-axis commutator.
-/
@[simp, rep_depth transport]
theorem sourceVortexSeed_eq_half_transportCommutator_spectral_epsilon
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    sourceVortexSeed (E := E) V
      = (2⁻¹ : ℝ) •
          transportCommutator (E := E) V.connectionGenerator (spectral_epsilon (E := E)) := by
  calc
    sourceVortexSeed (E := E) V
      = (2⁻¹ : ℝ) • ((2 : ℝ) • sourceVortexSeed (E := E) V) := by
          simp [smul_smul]
    _ = (2⁻¹ : ℝ) •
          transportCommutator (E := E) V.connectionGenerator (spectral_epsilon (E := E)) := by
          rw [transportCommutator_spectral_epsilon_eq_two_smul_sourceVortexSeed (E := E) V]

/--
Sink channel reconstruction:
the sink vortex seed is minus half the grading-axis commutator.
-/
@[simp, rep_depth transport]
theorem sinkVortexSeed_eq_neg_half_transportCommutator_spectral_epsilon
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    sinkVortexSeed (E := E) V
      = (-(2⁻¹ : ℝ)) •
          transportCommutator (E := E) V.connectionGenerator (spectral_epsilon (E := E)) := by
  have hsink :
      sinkVortexSeed (E := E) V = -(sourceVortexSeed (E := E) V) := by
    exact eq_neg_of_add_eq_zero_left
      (by simpa [add_comm] using sourceVortexSeed_add_sinkVortexSeed_eq_zero (E := E) V)
  calc
    sinkVortexSeed (E := E) V
      = -(sourceVortexSeed (E := E) V) := hsink
    _ = -((2⁻¹ : ℝ) •
          transportCommutator (E := E) V.connectionGenerator (spectral_epsilon (E := E))) := by
          rw [sourceVortexSeed_eq_half_transportCommutator_spectral_epsilon (E := E) V]
    _ = (-(2⁻¹ : ℝ)) •
          transportCommutator (E := E) V.connectionGenerator (spectral_epsilon (E := E)) := by
          simp [neg_smul]

/--
Nonvanishing source-channel defect is equivalent to nonvanishing grading-axis
commutator.
-/
@[rep_depth transport]
theorem sourceVortexSeed_ne_zero_iff_transportCommutator_spectral_epsilon_ne_zero
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    sourceVortexSeed (E := E) V ≠ 0
      ↔ transportCommutator (E := E) V.connectionGenerator (spectral_epsilon (E := E)) ≠ 0 := by
  constructor
  · intro hSource hCommZero
    apply hSource
    rw [sourceVortexSeed_eq_half_transportCommutator_spectral_epsilon (E := E) V]
    simp [hCommZero]
  · intro hComm hSourceZero
    apply hComm
    rw [transportCommutator_spectral_epsilon_eq_two_smul_sourceVortexSeed (E := E) V]
    simp [hSourceZero]

/--
Nonvanishing sink-channel defect is equivalent to nonvanishing grading-axis
commutator.
-/
@[rep_depth transport]
theorem sinkVortexSeed_ne_zero_iff_transportCommutator_spectral_epsilon_ne_zero
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    sinkVortexSeed (E := E) V ≠ 0
      ↔ transportCommutator (E := E) V.connectionGenerator (spectral_epsilon (E := E)) ≠ 0 := by
  constructor
  · intro hSink hCommZero
    apply hSink
    rw [sinkVortexSeed_eq_neg_half_transportCommutator_spectral_epsilon (E := E) V]
    simp [hCommZero]
  · intro hComm hSinkZero
    apply hComm
    rw [transportCommutator_spectral_epsilon_eq_neg_two_smul_sinkVortexSeed (E := E) V]
    simp [hSinkZero]

/--
Anticommutator inversion (source channel):
the source anticommutator channel is `H + (1/2){H, ε}`.
-/
@[simp, rep_depth transport]
theorem sourceAnticommutator_eq_connectionGenerator_add_half_anticommutator_spectral_epsilon
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    InfoGeometry.Quantum.RealMajorana.anticommutator
        (S := H₂)
        V.connectionGenerator (canonicalVortexPair (E := E)).source
      =
    V.connectionGenerator
      + (2⁻¹ : ℝ) •
          InfoGeometry.Quantum.RealMajorana.anticommutator
            (S := H₂)
            V.connectionGenerator (spectral_epsilon (E := E)) := by
  let Aplus : EndH :=
    InfoGeometry.Quantum.RealMajorana.anticommutator
      (S := H₂) V.connectionGenerator (canonicalVortexPair (E := E)).source
  let Aminus : EndH :=
    InfoGeometry.Quantum.RealMajorana.anticommutator
      (S := H₂) V.connectionGenerator (canonicalVortexPair (E := E)).sink
  let Aeps : EndH :=
    InfoGeometry.Quantum.RealMajorana.anticommutator
      (S := H₂) V.connectionGenerator (spectral_epsilon (E := E))
  have hSum : Aplus + Aminus = (2 : ℝ) • V.connectionGenerator := by
    change
      InfoGeometry.Quantum.RealMajorana.anticommutator
          (S := H₂) V.connectionGenerator (canonicalVortexPair (E := E)).source
        +
      InfoGeometry.Quantum.RealMajorana.anticommutator
          (S := H₂) V.connectionGenerator (canonicalVortexPair (E := E)).sink
        =
      (2 : ℝ) • V.connectionGenerator
    exact sourceSinkAnticommutator_sum_eq_two_smul_connectionGenerator (E := E) V
  have hSub : Aplus - Aminus = Aeps := by
    change
      InfoGeometry.Quantum.RealMajorana.anticommutator
          (S := H₂) V.connectionGenerator (canonicalVortexPair (E := E)).source
        -
      InfoGeometry.Quantum.RealMajorana.anticommutator
          (S := H₂) V.connectionGenerator (canonicalVortexPair (E := E)).sink
        =
      InfoGeometry.Quantum.RealMajorana.anticommutator
        (S := H₂) V.connectionGenerator (spectral_epsilon (E := E))
    exact sourceSinkAnticommutator_sub_eq_anticommutator_spectral_epsilon (E := E) V
  calc
    Aplus = (2⁻¹ : ℝ) • (Aplus + Aplus) := by
      calc
        Aplus = (1 : ℝ) • Aplus := by simp
        _ = ((2⁻¹ : ℝ) * (2 : ℝ)) • Aplus := by norm_num
        _ = (2⁻¹ : ℝ) • ((2 : ℝ) • Aplus) := by simp [smul_smul]
        _ = (2⁻¹ : ℝ) • (Aplus + Aplus) := by simp [two_smul]
    _ = (2⁻¹ : ℝ) • ((Aplus + Aminus) + (Aplus - Aminus)) := by
      abel_nf
    _ = (2⁻¹ : ℝ) • ((2 : ℝ) • V.connectionGenerator + Aeps) := by
      rw [hSum, hSub]
    _ = V.connectionGenerator + (2⁻¹ : ℝ) • Aeps := by
      simp [smul_add, smul_smul]
    _ = V.connectionGenerator
          + (2⁻¹ : ℝ) •
              InfoGeometry.Quantum.RealMajorana.anticommutator
                (S := H₂) V.connectionGenerator (spectral_epsilon (E := E)) := by
          rfl

/--
Anticommutator inversion (sink channel):
the sink anticommutator channel is `H - (1/2){H, ε}`.
-/
@[simp, rep_depth transport]
theorem sinkAnticommutator_eq_connectionGenerator_sub_half_anticommutator_spectral_epsilon
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    InfoGeometry.Quantum.RealMajorana.anticommutator
        (S := H₂)
        V.connectionGenerator (canonicalVortexPair (E := E)).sink
      =
    V.connectionGenerator
      - (2⁻¹ : ℝ) •
          InfoGeometry.Quantum.RealMajorana.anticommutator
            (S := H₂)
            V.connectionGenerator (spectral_epsilon (E := E)) := by
  let Aplus : EndH :=
    InfoGeometry.Quantum.RealMajorana.anticommutator
      (S := H₂) V.connectionGenerator (canonicalVortexPair (E := E)).source
  let Aminus : EndH :=
    InfoGeometry.Quantum.RealMajorana.anticommutator
      (S := H₂) V.connectionGenerator (canonicalVortexPair (E := E)).sink
  let Aeps : EndH :=
    InfoGeometry.Quantum.RealMajorana.anticommutator
      (S := H₂) V.connectionGenerator (spectral_epsilon (E := E))
  have hSum : Aplus + Aminus = (2 : ℝ) • V.connectionGenerator := by
    simpa [Aplus, Aminus] using
      sourceSinkAnticommutator_sum_eq_two_smul_connectionGenerator (E := E) V
  have hSub : Aplus - Aminus = Aeps := by
    simpa [Aplus, Aminus, Aeps] using
      sourceSinkAnticommutator_sub_eq_anticommutator_spectral_epsilon (E := E) V
  calc
    Aminus = (2⁻¹ : ℝ) • (Aminus + Aminus) := by
      calc
        Aminus = (1 : ℝ) • Aminus := by simp
        _ = ((2⁻¹ : ℝ) * (2 : ℝ)) • Aminus := by norm_num
        _ = (2⁻¹ : ℝ) • ((2 : ℝ) • Aminus) := by simp [smul_smul]
        _ = (2⁻¹ : ℝ) • (Aminus + Aminus) := by simp [two_smul]
    _ = (2⁻¹ : ℝ) • ((Aplus + Aminus) - (Aplus - Aminus)) := by
      abel_nf
    _ = (2⁻¹ : ℝ) • ((2 : ℝ) • V.connectionGenerator - Aeps) := by
      rw [hSum, hSub]
    _ = V.connectionGenerator - (2⁻¹ : ℝ) • Aeps := by
      simp [smul_sub, smul_smul]
    _ = V.connectionGenerator
          - (2⁻¹ : ℝ) •
              InfoGeometry.Quantum.RealMajorana.anticommutator
                (S := H₂) V.connectionGenerator (spectral_epsilon (E := E)) := by
          rfl

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

section BoundaryLocalization

variable {A B : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [FiniteDimensional ℝ E]
variable [FiniteDimensional ℝ (DoubledSpace E)]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

set_option linter.unusedSectionVars false in
/--
If the singular boundary generator is identified with the canonical source seed,
then nonzero transported central charge forces that source seed to act
nontrivially on a localized boundary-vortex witness.
-/
@[rep_depth transport]
theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0)
    (hSource : S.boundaryGenerator = sourceVortexSeed (E := E) V) :
    ∃ v : H₂,
      IsDanglingZeroMode S v ∧
        sourceVortexSeed (E := E) V v ≠ 0 ∧
        sinkVortexSeed (E := E) V v ≠ 0 := by
  rcases
      exists_danglingZeroMode_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
        (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
        hBoundaryOnZeroModes hCentral with
    ⟨v, hvDangling⟩
  have hSourcev : sourceVortexSeed (E := E) V v ≠ 0 := by
    simpa [hSource] using hvDangling.2
  have hSumv :
      sourceVortexSeed (E := E) V v + sinkVortexSeed (E := E) V v = 0 := by
    simpa [ContinuousLinearMap.add_apply] using
      congrArg (fun T : EndH => T v) (sourceVortexSeed_add_sinkVortexSeed_eq_zero (E := E) V)
  have hSinkv : sinkVortexSeed (E := E) V v ≠ 0 := by
    intro hZero
    have hSumv' := hSumv
    rw [hZero] at hSumv'
    have hSourceZero : sourceVortexSeed (E := E) V v = 0 := by
      simpa using hSumv'
    exact hSourcev hSourceZero
  exact ⟨v, hvDangling, hSourcev, hSinkv⟩

/--
Parity-lifted source-side localized bridge:
nonzero `Z₂` central-charge parity implies nonzero central charge, hence the
same localized source/sink seed existence.
-/
@[rep_depth transport]
theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralChargeParity_ne_zero_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0)
    (hSource : S.boundaryGenerator = sourceVortexSeed (E := E) V) :
    ∃ v : H₂,
      IsDanglingZeroMode S v ∧
        sourceVortexSeed (E := E) V v ≠ 0 ∧
        sinkVortexSeed (E := E) V v ≠ 0 := by
  have hCentral :
      operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 :=
    operatorialCentralCharge_ne_zero_of_operatorialCentralChargeParity_ne_zero
      (A := A) (B := B) (E := E) X hX hParity
  exact
    exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hBoundaryOnZeroModes hCentral hSource

set_option linter.unusedSectionVars false in
/--
Sink-side version of the same bridge when the singular boundary generator is
identified with the canonical sink seed.
-/
@[rep_depth transport]
theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0)
    (hSink : S.boundaryGenerator = sinkVortexSeed (E := E) V) :
    ∃ v : H₂,
      IsDanglingZeroMode S v ∧
        sourceVortexSeed (E := E) V v ≠ 0 ∧
        sinkVortexSeed (E := E) V v ≠ 0 := by
  rcases
      exists_danglingZeroMode_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization
        (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
        hBoundaryOnZeroModes hCentral with
    ⟨v, hvDangling⟩
  have hSinkv : sinkVortexSeed (E := E) V v ≠ 0 := by
    simpa [hSink] using hvDangling.2
  have hSumv :
      sourceVortexSeed (E := E) V v + sinkVortexSeed (E := E) V v = 0 := by
    simpa [ContinuousLinearMap.add_apply] using
      congrArg (fun T : EndH => T v) (sourceVortexSeed_add_sinkVortexSeed_eq_zero (E := E) V)
  have hSourcev : sourceVortexSeed (E := E) V v ≠ 0 := by
    intro hZero
    have hSumv' := hSumv
    rw [hZero] at hSumv'
    have hSinkZero : sinkVortexSeed (E := E) V v = 0 := by
      simpa using hSumv'
    exact hSinkv hSinkZero
  exact ⟨v, hvDangling, hSourcev, hSinkv⟩

/--
Parity-lifted sink-side localized bridge:
nonzero `Z₂` central-charge parity implies nonzero central charge, hence the
same localized source/sink seed existence.
-/
@[rep_depth transport]
theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralChargeParity_ne_zero_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hBoundaryOnZeroModes :
      ∀ v : H₂,
        quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0)
    (hSink : S.boundaryGenerator = sinkVortexSeed (E := E) V) :
    ∃ v : H₂,
      IsDanglingZeroMode S v ∧
        sourceVortexSeed (E := E) V v ≠ 0 ∧
        sinkVortexSeed (E := E) V v ≠ 0 := by
  have hCentral :
      operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 :=
    operatorialCentralCharge_ne_zero_of_operatorialCentralChargeParity_ne_zero
      (A := A) (B := B) (E := E) X hX hParity
  exact
    exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hBoundaryOnZeroModes hCentral hSink

/--
Source-side kernel-separation variant of the localized source/sink seed bridge.
-/
@[rep_depth transport]
theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hSep :
      (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
        = (⊥ : Submodule ℝ H₂))
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0)
    (hSource : S.boundaryGenerator = sourceVortexSeed (E := E) V) :
    ∃ v : H₂,
      IsDanglingZeroMode S v ∧
        sourceVortexSeed (E := E) V v ≠ 0 ∧
        sinkVortexSeed (E := E) V v ≠ 0 := by
  have hBoundaryOnZeroModes :
      ∀ v : H₂,
        quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0 := by
    intro v hv hvne
    have hvA : S.kernel.A v = 0 := by simpa [hA] using hv
    exact boundary_active_on_nonzero_kernel_of_kernel_separation (S := S) hSep v hvA hvne
  exact
    exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hBoundaryOnZeroModes hCentral hSource

/--
Parity-lifted source-side kernel-separation bridge.
-/
@[rep_depth transport]
theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralChargeParity_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hSep :
      (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
        = (⊥ : Submodule ℝ H₂))
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0)
    (hSource : S.boundaryGenerator = sourceVortexSeed (E := E) V) :
    ∃ v : H₂,
      IsDanglingZeroMode S v ∧
        sourceVortexSeed (E := E) V v ≠ 0 ∧
        sinkVortexSeed (E := E) V v ≠ 0 := by
  have hCentral :
      operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 :=
    operatorialCentralCharge_ne_zero_of_operatorialCentralChargeParity_ne_zero
      (A := A) (B := B) (E := E) X hX hParity
  exact
    exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hSep hCentral hSource

/--
Sink-side kernel-separation variant of the localized source/sink seed bridge.
-/
@[rep_depth transport]
theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hSep :
      (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
        = (⊥ : Submodule ℝ H₂))
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0)
    (hSink : S.boundaryGenerator = sinkVortexSeed (E := E) V) :
    ∃ v : H₂,
      IsDanglingZeroMode S v ∧
        sourceVortexSeed (E := E) V v ≠ 0 ∧
        sinkVortexSeed (E := E) V v ≠ 0 := by
  have hBoundaryOnZeroModes :
      ∀ v : H₂,
        quasilatticeDirac V X.F t v = 0 →
          v ≠ 0 → S.boundaryGenerator v ≠ 0 := by
    intro v hv hvne
    have hvA : S.kernel.A v = 0 := by simpa [hA] using hv
    exact boundary_active_on_nonzero_kernel_of_kernel_separation (S := S) hSep v hvA hvne
  exact
    exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hBoundaryOnZeroModes hCentral hSink

/--
Parity-lifted sink-side kernel-separation bridge.
-/
@[rep_depth transport]
theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralChargeParity_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (M : RealMajoranaDatum (S := H₂))
    (P0 : KPolarization (S := H₂) M)
    (S : InfoGeometry.Canonical.SingularBoundaryCorrection H₂)
    (hA : S.kernel.A = quasilatticeDirac V X.F t)
    (hplus : P0.plus = quasilatticeChiralKernelSlicePlus V X t)
    (hminus : P0.minus = quasilatticeChiralKernelSliceMinus V X t)
    (hodd :
      PolarizationOdd (M := M) P0 (quasilatticeDirac V X.F t))
    (hSep :
      (S.kernel.A.toLinearMap.ker ⊓ LinearMap.ker S.boundaryGenerator.toLinearMap)
        = (⊥ : Submodule ℝ H₂))
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0)
    (hSink : S.boundaryGenerator = sinkVortexSeed (E := E) V) :
    ∃ v : H₂,
      IsDanglingZeroMode S v ∧
        sourceVortexSeed (E := E) V v ≠ 0 ∧
        sinkVortexSeed (E := E) V v ≠ 0 := by
  have hCentral :
      operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 :=
    operatorialCentralCharge_ne_zero_of_operatorialCentralChargeParity_ne_zero
      (A := A) (B := B) (E := E) X hX hParity
  exact
    exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization
      (A := A) (B := B) (E := E) V X hX hEven t M P0 S hA hplus hminus hodd
      hSep hCentral hSink

end BoundaryLocalization

end Core

end VortexAnomalyLink

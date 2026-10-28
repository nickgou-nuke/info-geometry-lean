/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl55WittCalibratedHermitian
import InfoGeometry.Canonical.Cl55InfinityChiralCharge
import InfoGeometry.Canonical.FiniteSeedRepresentedAnalyticKMS
import InfoGeometry.Canonical.ComplexOperatorBilingualAnalyticity
import InfoGeometry.Canonical.FiniteSeedRepresentationFaithfulness

/-!
# Concrete chiral source/sink correlations on the represented Gibbs colimit

The Hamiltonian is the calibrated image of the existing native chiral charge.
Its Hermiticity is proved by the CAR representation. The state and flow are the
finite-seed Gibbs family and its completed GNS representation. The same actual
source/sink observables have analytic KMS correlations and a calibrated closed
Cauchy form. No infinity-twistor/modular-operator identification is assumed.
-/

noncomputable section
open scoped ComplexOrder
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55ChiralAnalyticKMS

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55WittCalibratedHermitian
open Cl55InfinitySourceSinkGrading Cl55InfinityChiralCharge
open CuntzMatrixTowerInstantiation FiniteMatrixGibbsFunctional
open FiniteSeedRepresentedAnalyticKMS FiniteSeedRepresentedRealTime
open ComplexOperatorBilingualAnalyticity
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CantorBernoulliCStarMatrixTraceState AlgebraicKMSStateColimit

/-! The finite calibration and native map lemmas are proved before fixing the
constructed Gibbs family.  Concrete proof-valued definitions below specialize
these results without reconstructing the represented carrier's dictionaries. -/

private theorem calibratedComplexRepresentation_injective :
    Function.Injective cl55WittComplexRepresentation := by
  have hInjective : Function.Injective
      (Cl11CuntzCoherentIndexTopologicalBridge.coherentComplexifyClStage 5) := by
    intro A B hAB
    have hComplexify :
        JordanWignerCantorRepresentation.complexifyMatrixAlgHom 5 A =
          JordanWignerCantorRepresentation.complexifyMatrixAlgHom 5 B :=
      (Matrix.reindexAlgEquiv ℝ ℂ
        (Cl11CuntzCoherentIndexTopologicalBridge.coherentIdxEquivFinPowTwo 5)).injective hAB
    ext i j
    have hEntry := congrArg (fun M => M i j) hComplexify
    have hEntry : Complex.ofReal (A i j) = Complex.ofReal (B i j) := by
      simpa [JordanWignerCantorRepresentation.complexifyMatrixAlgHom,
        RingHom.mapMatrix_apply] using hEntry
    exact Complex.ofReal_injective hEntry
  exact hInjective.comp
    InfoGeometry.Clifford.Cl55WittCalibratedRepresentation.cl55WittRepresentation_injective

section NativeObservable

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

private theorem nativeMappedObservable_injective
    (f : MatrixStage 5 →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (hf : Function.Injective f) :
    Function.Injective (fun X : Cl55 => f (cl55WittComplexRepresentation X)) :=
  hf.comp calibratedComplexRepresentation_injective

private theorem nativeMappedObservable_ne_zero
    (f : MatrixStage 5 →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω))
    (hf : Function.Injective f) (X : Cl55) (hX : X ≠ 0) :
    f (cl55WittComplexRepresentation X) ≠ 0 := by
  intro hx
  apply hX
  apply nativeMappedObservable_injective Stage sys ω f hf
  simpa only [map_zero] using hx

end NativeObservable

private abbrev matrixStageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun n => (inferInstance : CStarAlgebra (CStarMatrixStage n))
private abbrev matrixStageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun n => (inferInstance : PartialOrder (CStarMatrixStage n))
private abbrev matrixStageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun n => (inferInstance : StarOrderedRing (CStarMatrixStage n))
attribute [local instance] matrixStageCStarFamily matrixStageOrderFamily matrixStageStarOrderFamily

def chiralHamiltonian : MatrixStage 5 :=
  cl55WittComplexRepresentation chiralCharge55

theorem chiralHamiltonian_isHermitian : chiralHamiltonian.IsHermitian :=
  cl55WittComplexRepresentation_chiralCharge55_isHermitian

abbrev ChiralCarrier (β : ℝ) := Carrier chiralHamiltonian chiralHamiltonian_isHermitian β

/-- Each native observable enters the actual represented C⋆ closure through
the calibrated coherent matrix stage and the established stage representation. -/
def chiralObservable (β : ℝ) (X : Cl55) :=
  seedStageHom chiralHamiltonian chiralHamiltonian_isHermitian β
    (cl55WittComplexRepresentation X)

/-- Faithfulness of the same finite observables in the completed representation,
as an inferred specialization of the proved native-map theorem. -/
def chiralObservable_injective (β : ℝ) :=
  nativeMappedObservable_injective CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates chiralHamiltonian chiralHamiltonian_isHermitian β)
    (seedStageHom chiralHamiltonian chiralHamiltonian_isHermitian β)
    (FiniteSeedRepresentationFaithfulness.seedStageHom_injective
      chiralHamiltonian chiralHamiltonian_isHermitian β)

/-- The native nonzero source word remains nonzero in the completed algebra. -/
def chiralSource_ne_zero (β : ℝ) (i : Fin 5) (hi : i ≠ 4) :=
  nativeMappedObservable_ne_zero CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates chiralHamiltonian chiralHamiltonian_isHermitian β)
    (seedStageHom chiralHamiltonian chiralHamiltonian_isHermitian β)
    (FiniteSeedRepresentationFaithfulness.seedStageHom_injective
      chiralHamiltonian chiralHamiltonian_isHermitian β)
    (sourcePair55 i) (sourcePair55_ne_zero i hi)

/-- The native nonzero sink word remains nonzero in the completed algebra. -/
def chiralSink_ne_zero (β : ℝ) (i : Fin 5) (hi : i ≠ 4) :=
  nativeMappedObservable_ne_zero CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates chiralHamiltonian chiralHamiltonian_isHermitian β)
    (seedStageHom chiralHamiltonian chiralHamiltonian_isHermitian β)
    (FiniteSeedRepresentationFaithfulness.seedStageHom_injective
      chiralHamiltonian chiralHamiltonian_isHermitian β)
    (sinkPair55 i) (sinkPair55_ne_zero i hi)

def chiralCorrelation (β : ℝ) (v : ℕ) (X Y : Cl55) (z : ℂ) : ℂ :=
  seedCorrelation chiralHamiltonian chiralHamiltonian_isHermitian β v
    (chiralObservable β X) (chiralObservable β Y) z

/-- Entire analyticity, specialized from the actual finite-seed correlation. -/
def chiralCorrelation_analyticAt (β : ℝ) (v : ℕ) (X Y : Cl55) (z : ℂ) :=
  seedCorrelation_analyticAt chiralHamiltonian chiralHamiltonian_isHermitian β v
    (chiralObservable β X) (chiralObservable β Y) z

/-- KMS upper boundary with the actual source and sink words. -/
def source_sink_KMS_boundary (β : ℝ) (v : ℕ) (i j : Fin 5) (t : ℝ) :=
  seedCorrelation_upper_boundary chiralHamiltonian chiralHamiltonian_isHermitian β v
    (chiralObservable β (sourcePair55 i)) (chiralObservable β (sinkPair55 j)) t

/-- The closed form is calibrated to these same operator correlations. -/
def source_sink_cauchyForm_closed
    (β : ℝ) (v : ℕ) (i j : Fin 5) (z : ℂ) :=
  calibratedForm_closed_of_analyticAt
    (chiralCorrelation_analyticAt β v (sourcePair55 i) (sinkPair55 j) z)

def chiralKMSState (β : ℝ) (hβ : 0 < β) (v : ℕ) :
    InfoGeometry.Geometry.IsKMSState
      (fun t => (seedRealTimeAut chiralHamiltonian chiralHamiltonian_isHermitian β t).toAlgEquiv)
      β :=
  finiteSeedKMSState chiralHamiltonian chiralHamiltonian_isHermitian β hβ v

theorem source_zero_chiral_expectation (β : ℝ) :
    gibbsFunctional chiralHamiltonian chiralHamiltonian_isHermitian β
      (cl55WittComplexRepresentation (sourcePair55 0)) = 0 := by
  have hc := congrArg cl55WittComplexRepresentation
    sourcePair55_mode_zero_charge_pos_one
  simp only [map_sub, map_mul] at hc
  change chiralHamiltonian * cl55WittComplexRepresentation (sourcePair55 0) -
      cl55WittComplexRepresentation (sourcePair55 0) * chiralHamiltonian =
    cl55WittComplexRepresentation (sourcePair55 0) at hc
  have h := gibbsFunctional_commutator_zero chiralHamiltonian
    chiralHamiltonian_isHermitian β (cl55WittComplexRepresentation (sourcePair55 0))
  rw [hc] at h
  exact h

theorem sink_zero_chiral_expectation (β : ℝ) :
    gibbsFunctional chiralHamiltonian chiralHamiltonian_isHermitian β
      (cl55WittComplexRepresentation (sinkPair55 0)) = 0 := by
  have hc := congrArg cl55WittComplexRepresentation
    sinkPair55_mode_zero_charge_neg_one
  simp only [map_sub, map_mul, map_neg] at hc
  change chiralHamiltonian * cl55WittComplexRepresentation (sinkPair55 0) -
      cl55WittComplexRepresentation (sinkPair55 0) * chiralHamiltonian =
    -cl55WittComplexRepresentation (sinkPair55 0) at hc
  have h := gibbsFunctional_commutator_zero chiralHamiltonian
    chiralHamiltonian_isHermitian β (cl55WittComplexRepresentation (sinkPair55 0))
  rw [hc, map_neg, neg_eq_zero] at h
  exact h

end InfoGeometry.Canonical.Cl55ChiralAnalyticKMS

import InfoGeometry.Canonical.RelativeModularPolarizedBridge
import InfoGeometry.Canonical.KKTGeneralizedMetricBridge
import InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge
import InfoGeometry.Canonical.GeneralizedMetricCore
import InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.PhaseSpacePolarizedBridge

Adjacency bridge from the corrected neutral phase-space owner to the existing
polarized relative-modular carrier package.

This file stays narrow:

- a chosen real duality equivalence `ρ : H ≃ₗ[ℝ] H*` pulls polarized doubled
  lifts back to owner-side phase-space lifts,
- the phase-space `±` projectors fix those pulled-back lifts exactly,
- and the forward doubled realization recovers the original polarized lifts.

No recomposition data is introduced here.
-/

namespace InfoGeometry.Canonical.PhaseSpacePolarizedBridge

open InfoGeometry.Canonical.RelativeModularPolarizedBridge
open InfoGeometry.Canonical.KKTGeneralizedMetricBridge
open InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge
open InfoGeometry.Canonical.GeneralizedMetricCore
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
open InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric
open InfoGeometry.Krein
open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Krein.SplitQuadraticSheets

section Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α : Type*} [Fintype α] [Nonempty α]
variable {betaPlus : Type*} [Fintype betaPlus] [Nonempty betaPlus]
variable {betaMinus : Type*} [Fintype betaMinus] [Nonempty betaMinus]

/-- Owner-side phase-space lift of a polarized `+`-sector point. -/
@[rep_depth krein]
noncomputable def PlusRestrictedRelativeModularData.phaseLift
    (R : PlusRestrictedRelativeModularData H α betaPlus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaPlus) : PhaseSpaceCarrier H :=
  fromDoubledCopyRho (E := H) ρ (R.lift b)

/-- Owner-side phase-space lift of a polarized `-`-sector point. -/
@[rep_depth krein]
noncomputable def MinusRestrictedRelativeModularData.phaseLift
    (R : MinusRestrictedRelativeModularData H α betaMinus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaMinus) : PhaseSpaceCarrier H :=
  fromDoubledCopyRho (E := H) ρ (R.lift b)

@[rep_depth krein, simp] theorem PlusRestrictedRelativeModularData.realize_phaseLift
    (R : PlusRestrictedRelativeModularData H α betaPlus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaPlus) :
    toDoubledCopyRho (E := H) ρ (PlusRestrictedRelativeModularData.phaseLift R ρ b) = R.lift b := by
  apply DoubledSpace.ext <;>
    simp [PlusRestrictedRelativeModularData.phaseLift, fromDoubledCopyRho_apply,
      toDoubledCopyRho_apply]

@[rep_depth krein, simp] theorem MinusRestrictedRelativeModularData.realize_phaseLift
    (R : MinusRestrictedRelativeModularData H α betaMinus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaMinus) :
    toDoubledCopyRho (E := H) ρ (MinusRestrictedRelativeModularData.phaseLift R ρ b) = R.lift b := by
  apply DoubledSpace.ext <;>
    simp [MinusRestrictedRelativeModularData.phaseLift, fromDoubledCopyRho_apply,
      toDoubledCopyRho_apply]

@[rep_depth krein, simp] theorem PlusRestrictedRelativeModularData.phaseLift_fixed_by_phasePlusProjector
    (R : PlusRestrictedRelativeModularData H α betaPlus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaPlus) :
    phasePlusProjector (E := H) (PlusRestrictedRelativeModularData.phaseLift R ρ b)
      = PlusRestrictedRelativeModularData.phaseLift R ρ b := by
  have hsnd : WithLp.snd (R.lift b) = 0 := by
    exact (mem_plusSheet_iff_snd_eq_zero (E := H) (R.lift b)).mp (R.lift_mem b)
  rw [PlusRestrictedRelativeModularData.phaseLift, fromDoubledCopyRho_apply, hsnd]
  ext
  · simp [phasePlusProjector_apply, phaseEpsilon_apply]
    calc
      (2 : ℝ)⁻¹ • WithLp.fst (R.lift b) + (2 : ℝ)⁻¹ • WithLp.fst (R.lift b)
          = (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • WithLp.fst (R.lift b) := by
              simpa using
                (add_smul ((2 : ℝ)⁻¹) ((2 : ℝ)⁻¹) (WithLp.fst (R.lift b))).symm
      _ = WithLp.fst (R.lift b) := by
            norm_num
  ·
    simp [phasePlusProjector_apply, phaseEpsilon_apply]

@[rep_depth krein, simp] theorem PlusRestrictedRelativeModularData.realize_phaseLift_fixed_by_generalizedMetric_plusProjector
    (R : PlusRestrictedRelativeModularData H α betaPlus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaPlus) :
    GeneralizedMetricSeed.plusProjector
        (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
        (R.lift b) = R.lift b := by
  have hfix :
      phasePlusProjector (E := H) (PlusRestrictedRelativeModularData.phaseLift R ρ b)
        = PlusRestrictedRelativeModularData.phaseLift R ρ b := by
        simpa using PlusRestrictedRelativeModularData.phaseLift_fixed_by_phasePlusProjector R ρ b
  have htransport :=
    congrArg
      (fun F : PhaseSpaceCarrier H →ₗ[ℝ] DoubledSpace H =>
        F (PlusRestrictedRelativeModularData.phaseLift R ρ b))
      (toDoubledCopyRho_comp_phasePlusProjector_eq_generalizedMetric_plusProjector (H := H) ρ)
  have hforward :
      GeneralizedMetricSeed.plusProjector
          (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
          (toDoubledCopyRho (E := H) ρ
            (PlusRestrictedRelativeModularData.phaseLift R ρ b))
        =
        toDoubledCopyRho (E := H) ρ
          (PlusRestrictedRelativeModularData.phaseLift R ρ b) := by
    have htransport' :
        toDoubledCopyRho (E := H) ρ
            (phasePlusProjector (E := H) (PlusRestrictedRelativeModularData.phaseLift R ρ b))
          =
        spectralPlusProj (E := H)
          (toDoubledCopyRho (E := H) ρ
            (PlusRestrictedRelativeModularData.phaseLift R ρ b)) := by
      simpa [LinearMap.comp_apply] using htransport
    have htransport'' :
        toDoubledCopyRho (E := H) ρ
            (PlusRestrictedRelativeModularData.phaseLift R ρ b)
          =
        spectralPlusProj (E := H)
          (toDoubledCopyRho (E := H) ρ
            (PlusRestrictedRelativeModularData.phaseLift R ρ b)) := by
      simpa [hfix] using htransport'
    calc
      GeneralizedMetricSeed.plusProjector
          (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
          (toDoubledCopyRho (E := H) ρ
            (PlusRestrictedRelativeModularData.phaseLift R ρ b))
          = spectralPlusProj (E := H)
              (toDoubledCopyRho (E := H) ρ
                (PlusRestrictedRelativeModularData.phaseLift R ρ b)) := by
              exact
                congrArg
                  (fun F : DoubledSpace H →L[ℝ] DoubledSpace H =>
                    F (toDoubledCopyRho (E := H) ρ
                      (PlusRestrictedRelativeModularData.phaseLift R ρ b)))
                  (tomitaGeneralizedMetricSeed_plusProjector_eq_spectralPlusProj (H := H))
      _ = toDoubledCopyRho (E := H) ρ
            (PlusRestrictedRelativeModularData.phaseLift R ρ b) := by
              exact htransport''.symm
  simp [PlusRestrictedRelativeModularData.realize_phaseLift (R := R) (ρ := ρ) (b := b)] at hforward
  simpa using hforward

@[rep_depth krein, simp] theorem PlusRestrictedRelativeModularData.realize_phaseLift_fixed_by_realizedPlusProjector
    (G : InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric.GeneralizedMetricDatum H)
    (R : PlusRestrictedRelativeModularData H α betaPlus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaPlus)
    (hfix : G.plusProjector (PlusRestrictedRelativeModularData.phaseLift R ρ b)
      = PlusRestrictedRelativeModularData.phaseLift R ρ b) :
    (InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.realizedPlusProjector
      (G := G) ρ : Module.End ℝ (DoubledSpace H)) (R.lift b) = R.lift b := by
  have htransport :=
    congrArg
      (fun F : PhaseSpaceCarrier H →ₗ[ℝ] DoubledSpace H =>
        F (PlusRestrictedRelativeModularData.phaseLift R ρ b))
      (InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.toDoubledCopyRho_comp_plusProjector_eq_realized
        (G := G) ρ)
  have hreal :
      (InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.realizedPlusProjector
        (G := G) ρ : Module.End ℝ (DoubledSpace H))
        (toDoubledCopyRho (E := H) ρ
          (PlusRestrictedRelativeModularData.phaseLift R ρ b))
        =
      toDoubledCopyRho (E := H) ρ
          (PlusRestrictedRelativeModularData.phaseLift R ρ b) := by
    have htransport' :
        toDoubledCopyRho (E := H) ρ
            (G.plusProjector (PlusRestrictedRelativeModularData.phaseLift R ρ b))
          =
        (InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.realizedPlusProjector
          (G := G) ρ : Module.End ℝ (DoubledSpace H))
          (toDoubledCopyRho (E := H) ρ
            (PlusRestrictedRelativeModularData.phaseLift R ρ b)) := by
      simpa [LinearMap.comp_apply] using htransport
    simpa [hfix] using htransport'.symm
  simpa [PlusRestrictedRelativeModularData.realize_phaseLift (R := R) (ρ := ρ) (b := b)] using hreal

@[rep_depth krein, simp] theorem MinusRestrictedRelativeModularData.phaseLift_fixed_by_phaseMinusProjector
    (R : MinusRestrictedRelativeModularData H α betaMinus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaMinus) :
    phaseMinusProjector (E := H) (MinusRestrictedRelativeModularData.phaseLift R ρ b)
      = MinusRestrictedRelativeModularData.phaseLift R ρ b := by
  have hfst : WithLp.fst (R.lift b) = 0 := by
    exact (mem_minusSheet_iff_fst_eq_zero (E := H) (R.lift b)).mp (R.lift_mem b)
  rw [MinusRestrictedRelativeModularData.phaseLift, fromDoubledCopyRho_apply, hfst]
  ext
  · simp [phaseMinusProjector_apply, phaseEpsilon_apply]
  ·
    simp [phaseMinusProjector_apply, phaseEpsilon_apply]
    ring_nf

@[rep_depth krein, simp] theorem MinusRestrictedRelativeModularData.realize_phaseLift_fixed_by_generalizedMetric_minusProjector
    (R : MinusRestrictedRelativeModularData H α betaMinus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaMinus) :
    GeneralizedMetricSeed.minusProjector
        (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
        (R.lift b) = R.lift b := by
  have hfix :
      phaseMinusProjector (E := H) (MinusRestrictedRelativeModularData.phaseLift R ρ b)
        = MinusRestrictedRelativeModularData.phaseLift R ρ b := by
        simpa using MinusRestrictedRelativeModularData.phaseLift_fixed_by_phaseMinusProjector R ρ b
  have htransport :=
    congrArg
      (fun F : PhaseSpaceCarrier H →ₗ[ℝ] DoubledSpace H =>
        F (MinusRestrictedRelativeModularData.phaseLift R ρ b))
      (toDoubledCopyRho_comp_phaseMinusProjector_eq_generalizedMetric_minusProjector (H := H) ρ)
  have hforward :
      GeneralizedMetricSeed.minusProjector
          (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
          (toDoubledCopyRho (E := H) ρ
            (MinusRestrictedRelativeModularData.phaseLift R ρ b))
        =
        toDoubledCopyRho (E := H) ρ
          (MinusRestrictedRelativeModularData.phaseLift R ρ b) := by
    have htransport' :
        toDoubledCopyRho (E := H) ρ
            (phaseMinusProjector (E := H) (MinusRestrictedRelativeModularData.phaseLift R ρ b))
          =
        spectralMinusProj (E := H)
          (toDoubledCopyRho (E := H) ρ
            (MinusRestrictedRelativeModularData.phaseLift R ρ b)) := by
      simpa [LinearMap.comp_apply] using htransport
    have htransport'' :
        toDoubledCopyRho (E := H) ρ
            (MinusRestrictedRelativeModularData.phaseLift R ρ b)
          =
        spectralMinusProj (E := H)
          (toDoubledCopyRho (E := H) ρ
            (MinusRestrictedRelativeModularData.phaseLift R ρ b)) := by
      simpa [hfix] using htransport'
    calc
      GeneralizedMetricSeed.minusProjector
          (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
          (toDoubledCopyRho (E := H) ρ
            (MinusRestrictedRelativeModularData.phaseLift R ρ b))
          = spectralMinusProj (E := H)
              (toDoubledCopyRho (E := H) ρ
                (MinusRestrictedRelativeModularData.phaseLift R ρ b)) := by
              exact
                congrArg
                  (fun F : DoubledSpace H →L[ℝ] DoubledSpace H =>
                    F (toDoubledCopyRho (E := H) ρ
                      (MinusRestrictedRelativeModularData.phaseLift R ρ b)))
                  (tomitaGeneralizedMetricSeed_minusProjector_eq_spectralMinusProj (H := H))
      _ = toDoubledCopyRho (E := H) ρ
            (MinusRestrictedRelativeModularData.phaseLift R ρ b) := by
              exact htransport''.symm
  simp [MinusRestrictedRelativeModularData.realize_phaseLift (R := R) (ρ := ρ) (b := b)] at hforward
  simpa using hforward

@[rep_depth krein, simp] theorem MinusRestrictedRelativeModularData.realize_phaseLift_fixed_by_realizedMinusProjector
    (G : InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric.GeneralizedMetricDatum H)
    (R : MinusRestrictedRelativeModularData H α betaMinus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaMinus)
    (hfix : G.minusProjector (MinusRestrictedRelativeModularData.phaseLift R ρ b)
      = MinusRestrictedRelativeModularData.phaseLift R ρ b) :
    (InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.realizedMinusProjector
      (G := G) ρ : Module.End ℝ (DoubledSpace H)) (R.lift b) = R.lift b := by
  have htransport :=
    congrArg
      (fun F : PhaseSpaceCarrier H →ₗ[ℝ] DoubledSpace H =>
        F (MinusRestrictedRelativeModularData.phaseLift R ρ b))
      (InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.toDoubledCopyRho_comp_minusProjector_eq_realized
        (G := G) ρ)
  have hreal :
      (InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.realizedMinusProjector
        (G := G) ρ : Module.End ℝ (DoubledSpace H))
        (toDoubledCopyRho (E := H) ρ
          (MinusRestrictedRelativeModularData.phaseLift R ρ b))
        =
      toDoubledCopyRho (E := H) ρ
          (MinusRestrictedRelativeModularData.phaseLift R ρ b) := by
    have htransport' :
        toDoubledCopyRho (E := H) ρ
            (G.minusProjector (MinusRestrictedRelativeModularData.phaseLift R ρ b))
          =
        (InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.realizedMinusProjector
          (G := G) ρ : Module.End ℝ (DoubledSpace H))
          (toDoubledCopyRho (E := H) ρ
            (MinusRestrictedRelativeModularData.phaseLift R ρ b)) := by
      simpa [LinearMap.comp_apply] using htransport
    simpa [hfix] using htransport'.symm
  simpa [MinusRestrictedRelativeModularData.realize_phaseLift (R := R) (ρ := ρ) (b := b)] using hreal

@[rep_depth krein, simp] theorem PolarizedRelativeModularPair.plus_realize_phaseLift
    (R : PolarizedRelativeModularPair H α betaPlus betaMinus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaPlus) :
    toDoubledCopyRho (E := H) ρ
      (PlusRestrictedRelativeModularData.phaseLift R.plus ρ b) = R.plus.lift b := by
  simpa using PlusRestrictedRelativeModularData.realize_phaseLift R.plus ρ b

@[rep_depth krein, simp] theorem PolarizedRelativeModularPair.minus_realize_phaseLift
    (R : PolarizedRelativeModularPair H α betaPlus betaMinus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaMinus) :
    toDoubledCopyRho (E := H) ρ
      (MinusRestrictedRelativeModularData.phaseLift R.minus ρ b) = R.minus.lift b := by
  simpa using MinusRestrictedRelativeModularData.realize_phaseLift R.minus ρ b

@[rep_depth krein, simp] theorem PolarizedRelativeModularPair.plus_phaseLift_fixed_by_phasePlusProjector
    (R : PolarizedRelativeModularPair H α betaPlus betaMinus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaPlus) :
    phasePlusProjector (E := H) (PlusRestrictedRelativeModularData.phaseLift R.plus ρ b)
      = PlusRestrictedRelativeModularData.phaseLift R.plus ρ b := by
  simpa using PlusRestrictedRelativeModularData.phaseLift_fixed_by_phasePlusProjector R.plus ρ b

@[rep_depth krein, simp] theorem PolarizedRelativeModularPair.minus_phaseLift_fixed_by_phaseMinusProjector
    (R : PolarizedRelativeModularPair H α betaPlus betaMinus)
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) (b : betaMinus) :
    phaseMinusProjector (E := H) (MinusRestrictedRelativeModularData.phaseLift R.minus ρ b)
      = MinusRestrictedRelativeModularData.phaseLift R.minus ρ b := by
  simpa using MinusRestrictedRelativeModularData.phaseLift_fixed_by_phaseMinusProjector R.minus ρ b

section CountJunction

variable {nPlus : Nat} [Nonempty (Fin nPlus)]
variable {nMinus : Nat} [Nonempty (Fin nMinus)]
variable [MeasurableSpace (Fin nPlus)] [MeasurableSingletonClass (Fin nPlus)] [Countable (Fin nPlus)]
variable [MeasurableSpace (Fin nMinus)] [MeasurableSingletonClass (Fin nMinus)] [Countable (Fin nMinus)]

/-- Junction closure (`+` wing): the same polarized count index carries both the
phase-space fixed-point statement and the projective-count Hamiltonian identity. -/
@[rep_depth krein, capstone] theorem
    PlusRestrictedRelativeModularData.phaseSpace_projectiveCount_junction_of_countRays
    (R : PlusRestrictedRelativeModularData H α (Fin nPlus))
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H)
    (counts ref : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts nPlus)
    (hcounts : ∀ i : Fin nPlus, 0 < counts i)
    (href : ∀ i : Fin nPlus, 0 < ref i)
    (hsource : R.data.localSource =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay counts hcounts)
    (htarget : R.data.localTarget =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay ref href)
    (i : Fin nPlus) :
    GeneralizedMetricSeed.plusProjector
        (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
        (R.lift i) = R.lift i
      ∧
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nPlus) R.data.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nPlus) R.data.localSource) i
      = InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
          counts ref hcounts href i := by
  refine ⟨?_, ?_⟩
  · exact PlusRestrictedRelativeModularData.realize_phaseLift_fixed_by_generalizedMetric_plusProjector
      (R := R) (ρ := ρ) (b := i)
  · exact
      PlusRestrictedRelativeModularData.local_projectiveLogGenerator_eq_projectiveCountHamiltonianProfile_of_countRays
        (R := R) (counts := counts) (ref := ref)
        (hcounts := hcounts) (href := href)
        (hsource := hsource) (htarget := htarget) i

/-- Junction closure (`-` wing): the same polarized count index carries both the
phase-space fixed-point statement and the projective-count Hamiltonian identity. -/
@[rep_depth krein, capstone] theorem
    MinusRestrictedRelativeModularData.phaseSpace_projectiveCount_junction_of_countRays
    (R : MinusRestrictedRelativeModularData H α (Fin nMinus))
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H)
    (counts ref : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts nMinus)
    (hcounts : ∀ i : Fin nMinus, 0 < counts i)
    (href : ∀ i : Fin nMinus, 0 < ref i)
    (hsource : R.data.localSource =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay counts hcounts)
    (htarget : R.data.localTarget =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay ref href)
    (i : Fin nMinus) :
    GeneralizedMetricSeed.minusProjector
        (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
        (R.lift i) = R.lift i
      ∧
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nMinus) R.data.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nMinus) R.data.localSource) i
      = InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
          counts ref hcounts href i := by
  refine ⟨?_, ?_⟩
  · exact MinusRestrictedRelativeModularData.realize_phaseLift_fixed_by_generalizedMetric_minusProjector
      (R := R) (ρ := ρ) (b := i)
  · exact
      MinusRestrictedRelativeModularData.local_projectiveLogGenerator_eq_projectiveCountHamiltonianProfile_of_countRays
        (R := R) (counts := counts) (ref := ref)
        (hcounts := hcounts) (href := href)
        (hsource := hsource) (htarget := htarget) i

/--
Count/phase-space weld on the shared polarized carrier:
for a single polarized pair, the plus/minus phase-space fixed-point statements
and the plus/minus count/projective Hamiltonian identities are discharged
simultaneously.
-/
@[rep_depth krein, capstone] theorem
    PolarizedRelativeModularPair.phaseSpace_projectiveCount_weld_of_countRays
    (R : PolarizedRelativeModularPair H α (Fin nPlus) (Fin nMinus))
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H)
    (countsPlus refPlus : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts nPlus)
    (hcountsPlus : ∀ i : Fin nPlus, 0 < countsPlus i)
    (hrefPlus : ∀ i : Fin nPlus, 0 < refPlus i)
    (hplusSource : R.plus.data.localSource =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay countsPlus hcountsPlus)
    (hplusTarget : R.plus.data.localTarget =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay refPlus hrefPlus)
    (countsMinus refMinus : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts nMinus)
    (hcountsMinus : ∀ i : Fin nMinus, 0 < countsMinus i)
    (hrefMinus : ∀ i : Fin nMinus, 0 < refMinus i)
    (hminusSource : R.minus.data.localSource =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay countsMinus hcountsMinus)
    (hminusTarget : R.minus.data.localTarget =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay refMinus hrefMinus)
    (iPlus : Fin nPlus) (iMinus : Fin nMinus) :
    GeneralizedMetricSeed.plusProjector
        (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
        (R.plus.lift iPlus) = R.plus.lift iPlus
      ∧
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nPlus) R.plus.data.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nPlus) R.plus.data.localSource) iPlus
      = InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
          countsPlus refPlus hcountsPlus hrefPlus iPlus
      ∧
    GeneralizedMetricSeed.minusProjector
        (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
        (R.minus.lift iMinus) = R.minus.lift iMinus
      ∧
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nMinus) R.minus.data.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nMinus) R.minus.data.localSource) iMinus
      = InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
          countsMinus refMinus hcountsMinus hrefMinus iMinus := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      (PlusRestrictedRelativeModularData.phaseSpace_projectiveCount_junction_of_countRays
        (R := R.plus) (ρ := ρ)
        (counts := countsPlus) (ref := refPlus)
        (hcounts := hcountsPlus) (href := hrefPlus)
        (hsource := hplusSource) (htarget := hplusTarget) (i := iPlus)).1
  · exact
      (PlusRestrictedRelativeModularData.phaseSpace_projectiveCount_junction_of_countRays
        (R := R.plus) (ρ := ρ)
        (counts := countsPlus) (ref := refPlus)
        (hcounts := hcountsPlus) (href := hrefPlus)
        (hsource := hplusSource) (htarget := hplusTarget) (i := iPlus)).2
  · exact
      (MinusRestrictedRelativeModularData.phaseSpace_projectiveCount_junction_of_countRays
        (R := R.minus) (ρ := ρ)
        (counts := countsMinus) (ref := refMinus)
        (hcounts := hcountsMinus) (href := hrefMinus)
        (hsource := hminusSource) (htarget := hminusTarget) (i := iMinus)).1
  · exact
      (MinusRestrictedRelativeModularData.phaseSpace_projectiveCount_junction_of_countRays
        (R := R.minus) (ρ := ρ)
        (counts := countsMinus) (ref := refMinus)
        (hcounts := hcountsMinus) (href := hrefMinus)
        (hsource := hminusSource) (htarget := hminusTarget) (i := iMinus)).2

end CountJunction

end Core

end InfoGeometry.Canonical.PhaseSpacePolarizedBridge

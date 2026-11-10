/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ArchitecturalBlueprintD59
import InfoGeometry.OperatorAlgebra.PeirceSpine.ConnesGaugeConfinementD61
import InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmologyPeirce
import InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformationPeirce
import InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornHistoryQuantitativeRecovery
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceHistoryRecoveryError
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCoarseGrainedDynamics
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixPeirceOperatorGeometryD62
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixBlackHolePeirceD63
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixChiralTraceD64
import InfoGeometry.OperatorAlgebra.PeirceSpine.OrderOneMatrixWitnessD65
import InfoGeometry.Optics.OperatorDerivationForms
import InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes

/-!
# Cross-owner causal order for the Peirce operator archetypes

This file orders proved results from the generic-ring, sector, and matrix
owners.  Edges record theorem-input dependencies; no edge asserts a physical
interpretation or identifies the finite-matrix and arbitrary-ring carriers.
The corresponding theorems remain in their owner modules and are imported
here rather than recopied.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ArchetypeCausalSynthesis

open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.MetaCompiler
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum
open scoped ComplexOrder MatrixOrder

/-! Concrete finite-matrix inputs used to anchor the D63 causal edges.  The
cut is the existing tilted star projection, and the amplitudes are the
existing non-diagonal matrix witness; generic archetypes remain available in
their owner module. -/

abbrev D63CausalMatrix := Matrix (Fin 2) (Fin 2) ℂ

noncomputable def d63CausalCut : BlackHoleInformation.BH63IdempotentCut D63CausalMatrix :=
  ⟨d63TiltedProjection,
    d63_tilted_projection_is_star_projection.isIdempotentElem.eq⟩

noncomputable def d63CausalPageInput : BlackHoleInformation.BH63PageDefectInput D63CausalMatrix :=
  ⟨d63CausalCut, d63TiltedAmplitude, star d63TiltedAmplitude⟩

noncomputable def d63CausalBulkInput : BlackHoleInformation.BH63BulkInvarianceInput D63CausalMatrix :=
  ⟨d63CausalCut, d63TiltedAmplitude, star d63TiltedAmplitude,
    d63TiltedAmplitude, star d63TiltedAmplitude⟩

noncomputable def d63CausalMirrorInput : BlackHoleInformation.BH63MirrorSandwichInput D63CausalMatrix :=
  ⟨d63CausalCut, d63TiltedAmplitude, star d63TiltedAmplitude⟩

noncomputable def d63CausalShearInput : BlackHoleInformation.BH63ShearInput D63CausalMatrix :=
  ⟨d63CausalCut, d63TiltedAmplitude, star d63TiltedAmplitude⟩

noncomputable def d63CausalShearRecoveryInput : BlackHoleInformation.BH63ShearInput D63CausalMatrix ×
    D63CausalMatrix :=
  (d63CausalShearInput, d63TiltedAmplitude)

/-! D62 operator claims below use the repository's non-diagonal finite
matrix carrier, while leaving the two amplitudes arbitrary.  This makes the
causal edges proof-bearing without pretending that a finite matrix instance
proves a field-theoretic anomaly statement. -/

noncomputable def d62CausalCut :
    InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.ACIdempotentCut
      D63CausalMatrix :=
  ⟨d63TiltedProjection,
    d63_tilted_projection_is_star_projection.isIdempotentElem.eq⟩

noncomputable def d61CausalCut :
    InfoGeometry.OperatorAlgebra.PeirceSpine.D59IdempotentCut D63CausalMatrix :=
  ⟨d63TiltedProjection,
    d63_tilted_projection_is_star_projection.isIdempotentElem.eq⟩

noncomputable def d62CausalOperatorInput (A C : D63CausalMatrix) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.ACOperatorInput
      D63CausalMatrix := ⟨d62CausalCut, A, C⟩

/-! The finite pinching and full-history owners provide genuine matrix-level
archetypes for the recovery branch. -/

structure FinitePinchingArchetypeInput (n : ℕ) where
  cut : Matrix (Fin n) (Fin n) ℂ
  operator : Matrix (Fin n) (Fin n) ℂ
  amplifiedOperator : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ
  cutIdempotent : cut * cut = cut
  cutSelfAdjoint : star cut = cut
  amplifiedPositive : amplifiedOperator.PosSemidef

theorem d63_finite_pinching_input_has_nonzero_cut_and_operator :
    ∃ input : FinitePinchingArchetypeInput 2,
      input.cut ≠ 0 ∧ input.operator ≠ 0 ∧ input.amplifiedOperator ≠ 0 := by
  let input : FinitePinchingArchetypeInput 2 :=
    { cut := d63TiltedProjection
      operator := d63TiltedAmplitude
      amplifiedOperator := 1
      cutIdempotent := d63_tilted_projection_is_star_projection.isIdempotentElem.eq
      cutSelfAdjoint := d63_tilted_projection_is_star_projection.isSelfAdjoint
      amplifiedPositive := Matrix.PosSemidef.one }
  refine ⟨input, ?_, ?_, ?_⟩
  · intro h
    have h00 := congrArg (fun M : D63CausalMatrix => M 0 0) h
    norm_num [input, d63TiltedProjection] at h00
  · intro h
    have h00 := congrArg (fun M : D63CausalMatrix => M 0 0) h
    norm_num [input, d63TiltedAmplitude] at h00
  · intro h
    have h00 := congrArg
      (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ => M (0, 0) (0, 0)) h
    norm_num [input] at h00

def finitePinchingChannelArchetype (n : ℕ) :
    TypedArchetype (FinitePinchingArchetypeInput n) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.ArchetypeCausalSynthesis.finitePinchingChannelArchetype
  phase := 63
  claim := fun input =>
    InfoGeometry.Quantum.Choi.krausMap
        (InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel.pinchingKraus
          input.cut) input.operator =
        InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade input.cut input.operator ∧
    Matrix.trace (InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade
      input.cut input.operator) = Matrix.trace input.operator ∧
    (InfoGeometry.Quantum.KrausAmplification.amplification (r := Fin 2)
      (InfoGeometry.Modular.Choi.krausChannel
        (InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel.pinchingKraus
          input.cut)) input.amplifiedOperator).PosSemidef
  evidence := fun input =>
    ⟨InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel.pinchingKraus_eq_even
        input.cut input.operator input.cutSelfAdjoint,
      InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel.pinching_trace
        input.cut input.operator input.cutIdempotent input.cutSelfAdjoint,
      InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel.pinching_completely_positive
        input.cut input.amplifiedOperator input.amplifiedPositive⟩

structure PinchedHistoryArchetypeInput (n : ℕ) where
  cut : Matrix (Fin n) (Fin n) ℂ
  amplitude : Matrix (Fin n) (Fin n) ℂ
  cutIdempotent : cut * cut = cut
  cutSelfAdjoint : star cut = cut
  cutNonzero : cut ≠ 0
  cutNotOne : cut ≠ 1
  residualPositive : (1 - InfoGeometry.OperatorAlgebra.PeirceSpine.genV
    cut amplitude (star amplitude)).PosSemidef

theorem d63_pinched_history_input_has_nonzero_amplitude :
    ∃ input : PinchedHistoryArchetypeInput 2, input.amplitude ≠ 0 := by
  let A := InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.d63InteriorPageAmplitude
  have hResidual : (1 - InfoGeometry.OperatorAlgebra.PeirceSpine.genV
      d63TiltedProjection A (star A)).PosSemidef := by
    rw [show A = InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.d63InteriorPageAmplitude by rfl]
    rw [InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.d63_interior_page_metric_value]
    have hdiag : (Matrix.diagonal (fun _ : Fin 2 => (3 / 4 : ℂ))).PosSemidef :=
      Matrix.PosSemidef.diagonal (fun _ => by positivity)
    convert hdiag using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.diagonal_apply, Matrix.one_apply]
  let input : PinchedHistoryArchetypeInput 2 :=
    { cut := d63TiltedProjection
      amplitude := A
      cutIdempotent := d63_tilted_projection_is_star_projection.isIdempotentElem.eq
      cutSelfAdjoint := d63_tilted_projection_is_star_projection.isSelfAdjoint
      cutNonzero := by
        intro h
        have h00 := congrArg (fun M : D63CausalMatrix => M 0 0) h
        norm_num [d63TiltedProjection] at h00
      cutNotOne := by
        intro h
        have h01 := congrArg (fun M : D63CausalMatrix => M 0 1) h
        norm_num [d63TiltedProjection] at h01
      residualPositive := hResidual }
  refine ⟨input, ?_⟩
  · intro h
    have h00 := congrArg
      (fun M : D63CausalMatrix => M 0 0) h
    norm_num [input, A,
      InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.d63InteriorPageAmplitude] at h00

def residualKrausCompletionArchetype (n : ℕ) :
    TypedArchetype (PinchedHistoryArchetypeInput n) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.ArchetypeCausalSynthesis.residualKrausCompletionArchetype
  phase := 63
  claim := fun input =>
    ∃ W : Matrix (Fin n) (Fin n) ℂ,
      InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade input.cut W = W ∧
      star W * W = 1 - InfoGeometry.OperatorAlgebra.PeirceSpine.genV
        input.cut input.amplitude (star input.amplitude) ∧
      ∀ X : Matrix (Fin n) (Fin n) ℂ,
        Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
          (InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.cornerKrausWithResidual
            input.cut input.amplitude W) X) = Matrix.trace X
  evidence := fun input => by
    obtain ⟨W, hW, hResidual⟩ :=
      InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceChannelDynamics.exists_even_residual
        input.cut input.amplitude input.cutIdempotent input.residualPositive
    exact ⟨W, hW, hResidual, fun X =>
      InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.cornerKrausWithResidual_trace
        input.cut input.amplitude W X input.cutSelfAdjoint hResidual⟩

def pinchedHistoryCollisionArchetype (n : ℕ) :
    TypedArchetype (PinchedHistoryArchetypeInput n) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.ArchetypeCausalSynthesis.pinchedHistoryCollisionArchetype
  phase := 63
  claim := fun input =>
    ∃ W : Matrix (Fin n) (Fin n) ℂ,
      InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade input.cut W = W ∧
      ∃ ρ σ : Matrix (Fin n) (Fin n) ℂ,
        ρ.PosSemidef ∧ σ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧
        ρ ≠ σ ∧ ∀ k,
          InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade input.cut
            (InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCoarseGrainedDynamics.evolve
              input.cut input.amplitude W k ρ) =
          InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade input.cut
            (InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCoarseGrainedDynamics.evolve
              input.cut input.amplitude W k σ)
  evidence := fun input => by
    obtain ⟨W, hW, _, _⟩ := (residualKrausCompletionArchetype n).evidence input
    obtain ⟨ρ, σ, hρ, hσ, hτρ, hτσ, hne, hcollision⟩ :=
      InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCoarseGrainedDynamics.exists_densities_colliding_after_evolution
        input.cut input.amplitude W
        input.cutIdempotent input.cutSelfAdjoint hW input.cutNonzero input.cutNotOne
    exact ⟨W, hW, ρ, σ, hρ, hσ, hτρ, hτσ, hne, hcollision⟩

def sharpHistoryMinimaxArchetype (n : ℕ) :
    TypedArchetype (PinchedHistoryArchetypeInput n) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.ArchetypeCausalSynthesis.sharpHistoryMinimaxArchetype
  phase := 63
  claim := fun input =>
    ∃ W : Matrix (Fin n) (Fin n) ℂ,
      InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade input.cut W = W ∧
      ∃ ρ σ : Matrix (Fin n) (Fin n) ℂ,
        ρ.PosSemidef ∧ σ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧
        ρ ≠ σ ∧
        (∀ k,
          InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade input.cut
            (InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCoarseGrainedDynamics.evolve
              input.cut input.amplitude W k ρ) =
          InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade input.cut
            (InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCoarseGrainedDynamics.evolve
              input.cut input.amplitude W k σ)) ∧
        ∃ ε : ℝ, 0 < ε ∧
          ∀ decode : (ℕ → Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ,
            ε ≤ max
              (InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.matrixTraceNormSq
                (ρ - decode (fun k =>
                  InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade input.cut
                    (InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCoarseGrainedDynamics.evolve
                      input.cut input.amplitude W k ρ))))
              (InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.matrixTraceNormSq
                (σ - decode (fun k =>
                  InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade input.cut
                    (InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCoarseGrainedDynamics.evolve
                      input.cut input.amplitude W k σ))))
  evidence := fun input => by
    obtain ⟨W, hW, _, _⟩ := (residualKrausCompletionArchetype n).evidence input
    obtain ⟨ρ, σ, hρ, hσ, hτρ, hτσ, hne, hsame, ε, hε, hbound⟩ :=
      InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceHistoryRecoveryError.exists_density_pair_with_uniform_history_error
        input.cut input.amplitude W
        input.cutIdempotent input.cutSelfAdjoint hW input.cutNonzero input.cutNotOne
    exact ⟨W, hW, ρ, σ, hρ, hσ, hτρ, hτσ, hne, hsame, ε, hε, hbound⟩

structure ReplacementMinimaxInput (m : ℕ) where
  rho : Matrix (Fin m) (Fin m) ℂ
  sigma : Matrix (Fin m) (Fin m) ℂ
  observationOne : Matrix (Fin m) (Fin m) ℂ
  observationTwo : Matrix (Fin m) (Fin m) ℂ
  rhoPositive : rho.PosSemidef
  sigmaPositive : sigma.PosSemidef
  rhoTrace : Matrix.trace rho = 1
  sigmaTrace : Matrix.trace sigma = 1
  observationOneTrace : Matrix.trace observationOne = 1
  observationTwoTrace : Matrix.trace observationTwo = 1

theorem replacement_minimax_one_dimensional_inputs_are_scalar_identity
    (input : ReplacementMinimaxInput 1) :
    input.rho = 1 ∧ input.sigma = 1 ∧
      input.observationOne = 1 ∧ input.observationTwo = 1 := by
  have hscalar (M : Matrix (Fin 1) (Fin 1) ℂ) (hM : Matrix.trace M = 1) : M = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simpa [Matrix.trace] using hM
  exact ⟨hscalar input.rho input.rhoTrace,
    hscalar input.sigma input.sigmaTrace,
    hscalar input.observationOne input.observationOneTrace,
    hscalar input.observationTwo input.observationTwoTrace⟩

/-- A replacement channel attains the exact two-state minimax midpoint bound.
This is an owner-backed finite-dimensional matrix archetype. -/
def replacementMinimaxArchetype (m : ℕ) :
    TypedArchetype (ReplacementMinimaxInput m) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.ArchetypeCausalSynthesis.replacementMinimaxArchetype
  phase := 63
  claim := fun input =>
    ∃ E : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ,
      (∀ X, Matrix.trace (E X) = Matrix.trace X) ∧
      (∀ (r : ℕ) (X : Matrix (Fin r × Fin m) (Fin r × Fin m) ℂ),
        X.PosSemidef →
          (InfoGeometry.Quantum.KrausAmplification.amplification (r := Fin r) E X).PosSemidef) ∧
      max
          (InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.matrixTraceNormSq
            (input.rho - E input.observationOne))
          (InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.matrixTraceNormSq
            (input.sigma - E input.observationTwo)) =
        InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.matrixTraceNormSq
          (input.rho - input.sigma) / 4
  evidence := fun input =>
    InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceHistoryRecoveryError.density_midpoint_cptp_attains_bound
      input.rho input.sigma input.rhoPositive input.sigmaPositive input.rhoTrace input.sigmaTrace
      input.observationOne input.observationTwo input.observationOneTrace input.observationTwoTrace

#register_archetype replacementMinimaxArchetype
#audit_archetype replacementMinimaxArchetype

#register_archetype finitePinchingChannelArchetype
#audit_archetype finitePinchingChannelArchetype
#register_archetype residualKrausCompletionArchetype
#audit_archetype residualKrausCompletionArchetype
#register_archetype pinchedHistoryCollisionArchetype
#audit_archetype pinchedHistoryCollisionArchetype
#register_archetype sharpHistoryMinimaxArchetype
#audit_archetype sharpHistoryMinimaxArchetype

/-- Proof-input strata for the operator archetypes distributed across the
Peirce-spine owners. -/
inductive Node where
  | idempotentCut
  | evenCoordinate
  | connesOneForm
  | curvatureConfinement
  | logisticDefect
  | cyclicTraceLaws
  | cubicCommutator
  | cubicTraceCancellation
  | quarticDefectAction
  | quarticFlowInvariant
  | operatorSquareDefect
  | nestedDoubleCommutator
  | sectorData
  | chargeDifference
  | sectorTraceBalance
  | balancedChargeTrace
  | starProjection
  | selfAdjointOperator
  | matrixGramIdentity
  | matrixGramPositivity
  | matrixGramKernel
  | positiveMatrixInput
  | matrixMirrorKrausForm
  | matrixMirrorCompletePositivity
  | matrixMirrorUpperCornerWitness
  | matrixMirrorNonInjectivity
  | matrixShearNonunitarityWitness
  | pageDefect
  | finiteMetricContractionBound
  | normalizedProjectionTrace
  | finitePageDensity
  | residualKrausCompletion
  | tracePreservingPageEvolution
  | finiteInteriorPageDefect
  | finitePinchingChannel
  | pinchedHistoryCollision
  | twoPointTraceBound
  | replacementChannel
  | sharpHistoryMinimax
  | bulkInvariance
  | mirrorSandwich
  | reversibleShear
  | shearStateRecovery
  | matrixSheetGram
  | matrixSheetPositivityAndTrace
  | matrixPageDefect
  | finiteOperatorCut
  | finiteCutInnerDerivation
  | finiteYukawaOperator
  | finiteConnesCommutator
  | continuousFrechetDerivation
  | continuousLeibnizLaw
  | derivationCommutatorClosure
  | genericChiralMassSquareTrace
  | matrixTraceFunctional
  | matrixChiralTraceSpecialization
  | matrixChiralTraceAmplitudeInvariance
  | nondiagonalMatrixCutWitness
  | nondiagonalMatrixAmplitudeWitness
  | matrixOrderZeroCorners
  | matrixTwoWaveOperator
  | matrixOrderOneObstruction
  | orderZeroDoesNotImplyOrderOne
  | opticsFrechetDerivationCarrier
  | opticsInnerFrechetDerivation
  | opticsFrechetCommutatorClosure
  | opticsFrechetCurvatureLeibniz
  deriving DecidableEq, Repr

/-- Direct dependencies used by the owner theorem proofs. -/
def Node.edge : Node → Node → Prop
  | .idempotentCut, .connesOneForm =>
      ∀ A C a b : D63CausalMatrix,
        InfoGeometry.OperatorAlgebra.PeirceSpine.d61ConnesLeibnizArchetype.claim
          ⟨d63TiltedProjection, A, C, a, b⟩
  | .evenCoordinate, .connesOneForm =>
      ∀ A C X : D63CausalMatrix,
        InfoGeometry.OperatorAlgebra.PeirceSpine.d61OneFormParityArchetype.claim
          ⟨d61CausalCut, A, C, X⟩
  | .connesOneForm, .curvatureConfinement =>
      (∀ A C X : D63CausalMatrix,
        InfoGeometry.OperatorAlgebra.PeirceSpine.d61CurvatureConfinementArchetype.claim
          ⟨d61CausalCut, A, C, X⟩) ∧
      (∀ input : InfoGeometry.OperatorAlgebra.PeirceSpine.D59OneFormCurvatureInput
          D63CausalMatrix,
        InfoGeometry.OperatorAlgebra.PeirceSpine.d59OneFormCurvatureArchetype.claim input)
  | .idempotentCut, .logisticDefect =>
      ∀ A C : D63CausalMatrix,
        InfoGeometry.OperatorAlgebra.PeirceSpine.d59LogisticDefectArchetype.claim
          ⟨⟨d63TiltedProjection,
            d63_tilted_projection_is_star_projection.isIdempotentElem.eq⟩, A, C⟩
  | .idempotentCut, .cubicCommutator =>
      ∀ A C : D63CausalMatrix,
        InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acCubicCommutatorArchetype.claim
          (d62CausalOperatorInput A C)
  | .cubicCommutator, .cubicTraceCancellation =>
      ∀ (τ : D63CausalMatrix → ℂ),
        (∀ X Y, τ (X - Y) = τ X - τ Y) →
        (∀ X Y, τ (X * Y) = τ (Y * X)) →
        ∀ X Y : D63CausalMatrix, τ (comm X Y) = 0
  | .cyclicTraceLaws, .cubicTraceCancellation =>
      ∀ (τ : D63CausalMatrix → ℂ),
        (∀ X Y, τ (X - Y) = τ X - τ Y) →
        (∀ X Y, τ (X * Y) = τ (Y * X)) →
        ∀ X Y : D63CausalMatrix, τ (comm X Y) = 0
  | .idempotentCut, .quarticDefectAction =>
      ∀ A C : D63CausalMatrix,
        InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acQuarticDecompositionArchetype.claim
          (d62CausalOperatorInput A C)
  | .quarticDefectAction, .quarticFlowInvariant =>
      ∀ A C : D63CausalMatrix,
        InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acQuarticFlowArchetype.claim
          (d62CausalOperatorInput A C)
  | .idempotentCut, .operatorSquareDefect =>
      ∀ A C : D63CausalMatrix,
        InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acSquareDefectArchetype.claim
          (d62CausalOperatorInput A C)
  | .idempotentCut, .nestedDoubleCommutator =>
      ∀ A C : D63CausalMatrix,
        InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acDoubleCommutatorArchetype.claim
          (d62CausalOperatorInput A C)
  | .sectorData, .chargeDifference =>
      ∀ (input : InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.ACChargeBalanceInput D63CausalMatrix ℂ),
        InfoGeometry.OperatorAlgebra.PeirceSpine.chargeQ6
            input.colorSector input.weakSectorTwo input.scalarSector -
          InfoGeometry.OperatorAlgebra.PeirceSpine.chargeY6
            input.colorSector input.weakSectorOne input.weakSectorTwo input.scalarSector =
          (3 : ℤ) • InfoGeometry.OperatorAlgebra.PeirceSpine.quatChiralInv
            input.weakSectorOne input.weakSectorTwo
  | .chargeDifference, .balancedChargeTrace =>
      ∀ (input : InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.ACChargeBalanceInput D63CausalMatrix ℂ),
        InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acBalancedChargeTraceArchetype.claim input
  | .sectorTraceBalance, .balancedChargeTrace =>
      ∀ (input : InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.ACChargeBalanceInput D63CausalMatrix ℂ),
        InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acBalancedChargeTraceArchetype.claim input
  | .starProjection, .matrixGramIdentity =>
      ∀ (input : InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixD62GramInput (Fin 2)),
        InfoGeometry.OperatorAlgebra.PeirceSpine.matrixD62GramArchetype.claim input
  | .selfAdjointOperator, .matrixGramIdentity =>
      ∀ (input : InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixD62GramInput (Fin 2)),
        InfoGeometry.OperatorAlgebra.PeirceSpine.matrixD62GramArchetype.claim input
  | .matrixGramIdentity, .matrixGramPositivity =>
      ∀ (input : InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixD62GramInput (Fin 2)),
        InfoGeometry.OperatorAlgebra.PeirceSpine.matrixD62GramArchetype.claim input
  | .matrixGramIdentity, .matrixGramKernel =>
      ∀ (input : InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixD62GramInput (Fin 2)),
        InfoGeometry.OperatorAlgebra.PeirceSpine.matrixD62GramArchetype.claim input
  | .positiveMatrixInput, .matrixMirrorCompletePositivity =>
      ∀ (input : InfoGeometry.OperatorAlgebra.PeirceSpine.D63MatrixMirrorCPInput
        (Fin 2) (Fin 2)),
        InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixMirrorCPArchetype.claim input
  | .matrixMirrorKrausForm, .matrixMirrorCompletePositivity =>
      ∀ (input : InfoGeometry.OperatorAlgebra.PeirceSpine.D63MatrixMirrorCPInput
        (Fin 2) (Fin 2)),
        InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixMirrorCPArchetype.claim input
  | .matrixMirrorUpperCornerWitness, .matrixMirrorNonInjectivity =>
      InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixMirrorNoninjectiveArchetype.claim ()
  | .reversibleShear, .matrixShearNonunitarityWitness =>
      InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixShearInvertibleNonunitaryArchetype.claim ()
  | .reversibleShear, .shearStateRecovery =>
      BlackHoleInformation.bh63ShearConjugationRecoveryArchetype.claim
        d63CausalShearRecoveryInput
  | .idempotentCut, .pageDefect =>
      BlackHoleInformation.bh63PageDefectArchetype.claim d63CausalPageInput
  | .idempotentCut, .bulkInvariance =>
      BlackHoleInformation.bh63BulkInvarianceArchetype.claim d63CausalBulkInput
  | .idempotentCut, .mirrorSandwich =>
      BlackHoleInformation.bh63MirrorSandwichArchetype.claim d63CausalMirrorInput
  | .idempotentCut, .reversibleShear =>
      BlackHoleInformation.bh63ShearReversibilityArchetype.claim d63CausalShearInput
  | .starProjection, .matrixSheetGram =>
      InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixSheetArchetype.claim
        ⟨InfoGeometry.OperatorAlgebra.PeirceSpine.d63TiltedProjection,
          InfoGeometry.OperatorAlgebra.PeirceSpine.d63TiltedAmplitude,
          InfoGeometry.OperatorAlgebra.PeirceSpine.d63_tilted_projection_is_star_projection⟩
  | .matrixSheetGram, .matrixSheetPositivityAndTrace =>
      InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixSheetArchetype.claim
        ⟨InfoGeometry.OperatorAlgebra.PeirceSpine.d63TiltedProjection,
          InfoGeometry.OperatorAlgebra.PeirceSpine.d63TiltedAmplitude,
          InfoGeometry.OperatorAlgebra.PeirceSpine.d63_tilted_projection_is_star_projection⟩
  | .pageDefect, .matrixPageDefect =>
      InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixPageDefectArchetype.claim
        ⟨InfoGeometry.OperatorAlgebra.PeirceSpine.d63TiltedProjection,
          InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.d63InteriorPageAmplitude,
          InfoGeometry.OperatorAlgebra.PeirceSpine.d63_tilted_projection_is_star_projection⟩
  | .starProjection, .matrixPageDefect =>
      InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixPageDefectArchetype.claim
        ⟨InfoGeometry.OperatorAlgebra.PeirceSpine.d63TiltedProjection,
          InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.d63InteriorPageAmplitude,
          InfoGeometry.OperatorAlgebra.PeirceSpine.d63_tilted_projection_is_star_projection⟩
  | .finiteMetricContractionBound, .finitePageDensity =>
      finitePageDensityClaim d63InteriorFinitePageInput
  | .normalizedProjectionTrace, .finitePageDensity =>
      finitePageDensityClaim d63InteriorFinitePageInput
  | .starProjection, .finitePageDensity =>
      finitePageDensityClaim d63InteriorFinitePageInput
  | .finiteMetricContractionBound, .residualKrausCompletion =>
      finitePageChannelEvolutionClaim d63InteriorFinitePageInput
  | .finitePageDensity, .tracePreservingPageEvolution =>
      finitePageChannelEvolutionClaim d63InteriorFinitePageInput
  | .residualKrausCompletion, .tracePreservingPageEvolution =>
      finitePageChannelEvolutionClaim d63InteriorFinitePageInput
  | .finitePageDensity, .finiteInteriorPageDefect =>
      finitePageDensityClaim d63InteriorFinitePageInput
  | .tracePreservingPageEvolution, .finiteInteriorPageDefect =>
      finitePageChannelEvolutionClaim d63InteriorFinitePageInput
  | .starProjection, .finitePinchingChannel =>
      ∀ (n : ℕ) (input : FinitePinchingArchetypeInput n),
        (finitePinchingChannelArchetype n).claim input
  | .residualKrausCompletion, .pinchedHistoryCollision =>
      ∀ (input : PinchedHistoryArchetypeInput 2),
        (pinchedHistoryCollisionArchetype 2).claim input
  | .pinchedHistoryCollision, .sharpHistoryMinimax =>
      ∀ (input : PinchedHistoryArchetypeInput 2),
        (sharpHistoryMinimaxArchetype 2).claim input
  | .twoPointTraceBound, .sharpHistoryMinimax =>
      ∀ (X Y Z : D63CausalMatrix),
        InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.matrixTraceNormSq (X - Y) / 4 ≤
          max (InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.matrixTraceNormSq (X - Z))
            (InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.matrixTraceNormSq (Y - Z))
  | .replacementChannel, .sharpHistoryMinimax =>
      ∀ (m : ℕ) (input : ReplacementMinimaxInput m),
        (replacementMinimaxArchetype m).claim input
  | .finiteOperatorCut, .finiteCutInnerDerivation =>
      ∀ (n : ℕ) (P : InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.PeirceCut n)
        (X Y : SouriauOnsagerBKM.FiniteOperatorAlgebra n),
        (InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.cutLeibnizArchetype n).claim
          ⟨P, X, Y⟩
  | .finiteOperatorCut, .finiteYukawaOperator =>
      ∀ (n : ℕ) (P : InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.PeirceCut n)
        (A C : SouriauOnsagerBKM.FiniteOperatorAlgebra n),
        ∃ D : FrechetOperatorDerivation ℝ (SouriauOnsagerBKM.FiniteOperatorAlgebra n),
          ∀ X, D X = InfoGeometry.OperatorAlgebra.PeirceSpine.comm
            (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi
              (P : SouriauOnsagerBKM.FiniteOperatorAlgebra n) A C) X
  | .finiteYukawaOperator, .finiteConnesCommutator =>
      ∀ (n : ℕ) (P : InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.PeirceCut n)
        (A C X Y : SouriauOnsagerBKM.FiniteOperatorAlgebra n),
        (InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.yukawaOneFormArchetype n).claim
          ⟨P, (A, (C, (X, Y)))⟩
  | .finiteYukawaOperator, .continuousFrechetDerivation =>
      ∀ {n : ℕ}
        (P : InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.PeirceCut n)
        (A C : SouriauOnsagerBKM.FiniteOperatorAlgebra n),
        ∃ D : FrechetOperatorDerivation ℝ
            (SouriauOnsagerBKM.FiniteOperatorAlgebra n),
          (∀ X, D X = InfoGeometry.OperatorAlgebra.PeirceSpine.comm
            (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi
              (P : SouriauOnsagerBKM.FiniteOperatorAlgebra n) A C) X) ∧
          (∀ X Y, D (X * Y) = D X * Y + X * D Y)
  | .finiteCutInnerDerivation, .continuousLeibnizLaw =>
      ∀ {n : ℕ}
        (P : InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.PeirceCut n)
        (X Y : SouriauOnsagerBKM.FiniteOperatorAlgebra n),
        InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.cutDerivation P
          (X * Y) =
          InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.cutDerivation P X * Y +
            X * InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.cutDerivation P Y
  | .continuousFrechetDerivation, .continuousLeibnizLaw =>
      ∀ {n : ℕ}
        (D : FrechetOperatorDerivation ℝ
          (SouriauOnsagerBKM.FiniteOperatorAlgebra n)) X Y,
        D (X * Y) = D X * Y + X * D Y
  | .continuousLeibnizLaw, .derivationCommutatorClosure =>
      ∀ {n : ℕ}
        (D E : FrechetOperatorDerivation ℝ
          (SouriauOnsagerBKM.FiniteOperatorAlgebra n)) X Y,
        FrechetOperatorDerivation.commutator D E (X * Y) =
          FrechetOperatorDerivation.commutator D E X * Y +
            X * FrechetOperatorDerivation.commutator D E Y
  | .idempotentCut, .genericChiralMassSquareTrace =>
      ∀ {P : D63CausalMatrix}, P * P = P →
        ∀ τ : D63CausalMatrix → ℂ,
          (∀ X Y, τ (X + Y) = τ X + τ Y) →
          (∀ X Y, τ (X - Y) = τ X - τ Y) →
          (∀ X Y, τ (X * Y) = τ (Y * X)) →
          ∀ A C : D63CausalMatrix,
            τ (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P *
              (InfoGeometry.OperatorAlgebra.PeirceSpine.peirceMassDirac P A C *
                InfoGeometry.OperatorAlgebra.PeirceSpine.peirceMassDirac P A C)) =
              τ P - τ (1 - P)
  | .cyclicTraceLaws, .genericChiralMassSquareTrace =>
      ∀ {P : D63CausalMatrix}, P * P = P →
        ∀ τ : D63CausalMatrix → ℂ,
          (∀ X Y, τ (X + Y) = τ X + τ Y) →
          (∀ X Y, τ (X - Y) = τ X - τ Y) →
          (∀ X Y, τ (X * Y) = τ (Y * X)) →
          ∀ A C : D63CausalMatrix,
            τ (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P *
              (InfoGeometry.OperatorAlgebra.PeirceSpine.peirceMassDirac P A C *
                InfoGeometry.OperatorAlgebra.PeirceSpine.peirceMassDirac P A C)) =
              τ P - τ (1 - P)
  | .genericChiralMassSquareTrace, .matrixChiralTraceSpecialization =>
      ∀ (input : InfoGeometry.OperatorAlgebra.PeirceSpine.D64MatrixTraceInput (Fin 2)),
        InfoGeometry.OperatorAlgebra.PeirceSpine.d64MatrixChiralTraceArchetype.claim input
  | .starProjection, .matrixChiralTraceSpecialization =>
      ∀ (input : InfoGeometry.OperatorAlgebra.PeirceSpine.D64MatrixTraceInput (Fin 2)),
        InfoGeometry.OperatorAlgebra.PeirceSpine.d64MatrixChiralTraceArchetype.claim input
  | .matrixTraceFunctional, .matrixChiralTraceSpecialization =>
      ∀ (input : InfoGeometry.OperatorAlgebra.PeirceSpine.D64MatrixTraceInput (Fin 2)),
        InfoGeometry.OperatorAlgebra.PeirceSpine.d64MatrixChiralTraceArchetype.claim input
  | .matrixChiralTraceSpecialization, .matrixChiralTraceAmplitudeInvariance =>
      ∀ {p A C A' C' : Matrix (Fin 2) (Fin 2) ℂ},
        IsStarProjection p →
        Matrix.trace (InfoGeometry.OperatorAlgebra.PeirceSpine.invS p *
          (InfoGeometry.OperatorAlgebra.PeirceSpine.peirceMassDirac p A C *
            InfoGeometry.OperatorAlgebra.PeirceSpine.peirceMassDirac p A C)) =
        Matrix.trace (InfoGeometry.OperatorAlgebra.PeirceSpine.invS p *
          (InfoGeometry.OperatorAlgebra.PeirceSpine.peirceMassDirac p A' C' *
            InfoGeometry.OperatorAlgebra.PeirceSpine.peirceMassDirac p A' C'))
  | .nondiagonalMatrixCutWitness, .matrixOrderZeroCorners =>
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        InfoGeometry.OperatorAlgebra.PeirceSpine.d65LeftCorner
        InfoGeometry.OperatorAlgebra.PeirceSpine.d65RightCorner = 0
  | .nondiagonalMatrixCutWitness, .matrixTwoWaveOperator =>
      InfoGeometry.OperatorAlgebra.PeirceSpine.d65TwoWaveDirac =
        InfoGeometry.OperatorAlgebra.PeirceSpine.d65Forward +
          InfoGeometry.OperatorAlgebra.PeirceSpine.d65Backward
  | .nondiagonalMatrixAmplitudeWitness, .matrixTwoWaveOperator =>
      InfoGeometry.OperatorAlgebra.PeirceSpine.d65ForwardWaveNonzeroArchetype.claim ()
  | .matrixTwoWaveOperator, .matrixOrderOneObstruction =>
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm
          InfoGeometry.OperatorAlgebra.PeirceSpine.d65TwoWaveDirac
          InfoGeometry.OperatorAlgebra.PeirceSpine.d65LeftCorner)
        InfoGeometry.OperatorAlgebra.PeirceSpine.d65RightCorner ≠ 0
  | .matrixOrderZeroCorners, .orderZeroDoesNotImplyOrderOne =>
      InfoGeometry.OperatorAlgebra.PeirceSpine.d65OrderZeroOrderOneCounterexampleArchetype.claim ()
  | .matrixOrderOneObstruction, .orderZeroDoesNotImplyOrderOne =>
      InfoGeometry.OperatorAlgebra.PeirceSpine.d65OrderZeroOrderOneCounterexampleArchetype.claim ()
  | .opticsFrechetDerivationCarrier, .opticsInnerFrechetDerivation =>
      ∀ (D : FrechetOperatorDerivation ℝ
          (SouriauOnsagerBKM.FiniteOperatorAlgebra 2)) x y,
        D (x * y) = D x * y + x * D y
  | .opticsFrechetDerivationCarrier, .opticsFrechetCommutatorClosure =>
      ∀ (D E : FrechetOperatorDerivation ℝ
          (SouriauOnsagerBKM.FiniteOperatorAlgebra 2)) x y,
        FrechetOperatorDerivation.commutator D E (x * y) =
          FrechetOperatorDerivation.commutator D E x * y +
            x * FrechetOperatorDerivation.commutator D E y
  | .opticsInnerFrechetDerivation, .opticsFrechetCurvatureLeibniz =>
      ∀ (D : FrechetOperatorDerivation ℝ
          (SouriauOnsagerBKM.FiniteOperatorAlgebra 2))
        (C : InfoGeometry.Optics.OperatorValuedConnection.Connection
          (Point := Fin 2) (Tangent := Fin 2)
          (Value := SouriauOnsagerBKM.FiniteOperatorAlgebra 2))
        (p X Y : Fin 2),
        D (InfoGeometry.Optics.OperatorValuedConnection.curvature C p X Y) =
          D (C.derivative p X Y) +
            ((D (C.form p X) * C.form p Y + C.form p X * D (C.form p Y)) -
              (D (C.form p Y) * C.form p X + C.form p Y * D (C.form p X)))
  | _, _ => False

/-- A rank certifies that every direct dependency strictly advances in the
causal order. -/
def Node.rank : Node → Nat
  | .idempotentCut => 0
  | .evenCoordinate => 0
  | .cyclicTraceLaws => 0
  | .sectorData => 0
  | .sectorTraceBalance => 0
  | .starProjection => 0
  | .selfAdjointOperator => 0
  | .connesOneForm => 1
  | .logisticDefect => 1
  | .cubicCommutator => 1
  | .quarticDefectAction => 1
  | .quarticFlowInvariant => 2
  | .operatorSquareDefect => 1
  | .nestedDoubleCommutator => 1
  | .chargeDifference => 1
  | .matrixGramIdentity => 1
  | .pageDefect => 1
  | .finiteMetricContractionBound => 0
  | .normalizedProjectionTrace => 0
  | .finitePageDensity => 1
  | .residualKrausCompletion => 1
  | .tracePreservingPageEvolution => 2
  | .finiteInteriorPageDefect => 3
  | .finitePinchingChannel => 1
  | .pinchedHistoryCollision => 2
  | .twoPointTraceBound => 0
  | .replacementChannel => 0
  | .sharpHistoryMinimax => 3
  | .bulkInvariance => 1
  | .mirrorSandwich => 1
  | .reversibleShear => 1
  | .shearStateRecovery => 2
  | .matrixSheetGram => 1
  | .curvatureConfinement => 2
  | .cubicTraceCancellation => 2
  | .balancedChargeTrace => 2
  | .matrixGramPositivity => 2
  | .matrixGramKernel => 2
  | .positiveMatrixInput => 0
  | .matrixMirrorKrausForm => 1
  | .matrixMirrorCompletePositivity => 2
  | .matrixMirrorUpperCornerWitness => 0
  | .matrixMirrorNonInjectivity => 1
  | .matrixShearNonunitarityWitness => 2
  | .matrixSheetPositivityAndTrace => 2
  | .matrixPageDefect => 2
  | .finiteOperatorCut => 0
  | .finiteCutInnerDerivation => 1
  | .finiteYukawaOperator => 1
  | .finiteConnesCommutator => 2
  | .continuousFrechetDerivation => 2
  | .continuousLeibnizLaw => 3
  | .derivationCommutatorClosure => 4
  | .genericChiralMassSquareTrace => 1
  | .matrixTraceFunctional => 0
  | .matrixChiralTraceSpecialization => 2
  | .matrixChiralTraceAmplitudeInvariance => 3
  | .nondiagonalMatrixCutWitness => 0
  | .nondiagonalMatrixAmplitudeWitness => 0
  | .matrixOrderZeroCorners => 1
  | .matrixTwoWaveOperator => 1
  | .matrixOrderOneObstruction => 2
  | .orderZeroDoesNotImplyOrderOne => 3
  | .opticsFrechetDerivationCarrier => 0
  | .opticsInnerFrechetDerivation => 1
  | .opticsFrechetCommutatorClosure => 1
  | .opticsFrechetCurvatureLeibniz => 2

set_option maxHeartbeats 1000000 in
theorem Node.edge_rank_strict {a b : Node} (h : a.edge b) : a.rank < b.rank := by
  cases a <;> cases b <;> simp only [edge] at h <;>
    (try contradiction) <;> simp only [rank] <;> norm_num

/-- Reflexive-transitive closure of the direct theorem-dependency edges. -/
inductive Reachable : Node → Node → Prop where
  | refl (a : Node) : Reachable a a
  | edge {a b : Node} : a.edge b → Reachable a b
  | trans {a b c : Node} : Reachable a b → Reachable b c → Reachable a c

def causalLE (a b : Node) : Prop := Reachable a b

theorem reachable_rank_strict_of_ne {a b : Node}
    (h : Reachable a b) (hne : a ≠ b) : a.rank < b.rank := by
  induction h with
  | @refl x => exact (hne rfl).elim
  | edge h => exact Node.edge_rank_strict h
  | @trans x y z hxy hyz ihxy ihyz =>
      by_cases hxyEq : x = y
      · subst y
        exact ihyz hne
      · by_cases hyzEq : y = z
        · subst z
          exact ihxy hne
        · exact lt_trans (ihxy hxyEq) (ihyz hyzEq)

theorem causalLE_refl (a : Node) : causalLE a a := Reachable.refl a

theorem causalLE_trans {a b c : Node}
    (hab : causalLE a b) (hbc : causalLE b c) : causalLE a c :=
  Reachable.trans hab hbc

theorem causalLE_antisymm {a b : Node}
    (hab : causalLE a b) (hba : causalLE b a) : a = b := by
  by_cases hEq : a = b
  · exact hEq
  · exact (lt_asymm (reachable_rank_strict_of_ne hab hEq)
      (reachable_rank_strict_of_ne hba (Ne.symm hEq))).elim

instance : PartialOrder Node where
  le := causalLE
  le_refl := causalLE_refl
  le_trans := fun _ _ _ hab hbc => causalLE_trans hab hbc
  le_antisymm := fun _ _ hab hba => causalLE_antisymm hab hba

theorem edge_causalLE {a b : Node} (h : a.edge b) : causalLE a b :=
  Reachable.edge h

/-! ## Cross-owner dependency paths -/

theorem cut_to_curvature : causalLE .idempotentCut .curvatureConfinement := by
  have hOneForm : Node.edge .idempotentCut .connesOneForm := by
    intro A C a b
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.d61ConnesLeibnizArchetype.evidence
      ⟨d63TiltedProjection, A, C, a, b⟩
  have hCurvature : Node.edge .connesOneForm .curvatureConfinement := by
    constructor
    · intro A C X
      exact InfoGeometry.OperatorAlgebra.PeirceSpine.d61CurvatureConfinementArchetype.evidence
        ⟨d61CausalCut, A, C, X⟩
    · intro input
      exact InfoGeometry.MetaCompiler.TypedArchetype.discharge
        InfoGeometry.OperatorAlgebra.PeirceSpine.d59OneFormCurvatureArchetype input
  exact causalLE_trans
    (edge_causalLE (a := .idempotentCut) (b := .connesOneForm) hOneForm)
    (edge_causalLE (a := .connesOneForm) (b := .curvatureConfinement) hCurvature)

theorem even_coordinate_to_connes_one_form :
    causalLE .evenCoordinate .connesOneForm := by
  have hParity : Node.edge .evenCoordinate .connesOneForm := by
    intro A C X
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.d61OneFormParityArchetype.evidence
      ⟨d61CausalCut, A, C, X⟩
  exact edge_causalLE hParity

theorem cubic_to_trace_cancellation : causalLE .cubicCommutator .cubicTraceCancellation :=
  edge_causalLE (by
    intro τ hSub hCyc X Y
    unfold comm
    rw [hSub, hCyc X Y, sub_self])

theorem d62_cubic_and_quartic_archetypes_causal_order :
    causalLE .idempotentCut .logisticDefect ∧
    causalLE .idempotentCut .cubicCommutator ∧
    causalLE .cyclicTraceLaws .cubicTraceCancellation ∧
    causalLE .idempotentCut .quarticDefectAction ∧
    causalLE .quarticDefectAction .quarticFlowInvariant ∧
    causalLE .idempotentCut .operatorSquareDefect ∧
    causalLE .idempotentCut .nestedDoubleCommutator := by
  have hLogistic : Node.edge .idempotentCut .logisticDefect := by
    intro A C
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.d59LogisticDefectArchetype.evidence
      ⟨⟨d63TiltedProjection,
        d63_tilted_projection_is_star_projection.isIdempotentElem.eq⟩, A, C⟩
  have hCubic : Node.edge .idempotentCut .cubicCommutator := by
    intro A C
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acCubicCommutatorArchetype.evidence
      (d62CausalOperatorInput A C)
  have hQuartic : Node.edge .idempotentCut .quarticDefectAction := by
    intro A C
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acQuarticDecompositionArchetype.evidence
      (d62CausalOperatorInput A C)
  have hFlow : Node.edge .quarticDefectAction .quarticFlowInvariant := by
    intro A C
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acQuarticFlowArchetype.evidence
      (d62CausalOperatorInput A C)
  have hSquare : Node.edge .idempotentCut .operatorSquareDefect := by
    intro A C
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acSquareDefectArchetype.evidence
      (d62CausalOperatorInput A C)
  have hDouble : Node.edge .idempotentCut .nestedDoubleCommutator := by
    intro A C
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acDoubleCommutatorArchetype.evidence
      (d62CausalOperatorInput A C)
  have hTrace : Node.edge .cyclicTraceLaws .cubicTraceCancellation := by
    intro τ hSub hCyc X Y
    unfold comm
    rw [hSub, hCyc X Y, sub_self]
  exact ⟨edge_causalLE (a := .idempotentCut) (b := .logisticDefect) hLogistic,
    edge_causalLE (a := .idempotentCut) (b := .cubicCommutator) hCubic,
    edge_causalLE (a := .cyclicTraceLaws) (b := .cubicTraceCancellation) hTrace,
    edge_causalLE (a := .idempotentCut) (b := .quarticDefectAction) hQuartic,
    edge_causalLE (a := .quarticDefectAction) (b := .quarticFlowInvariant) hFlow,
    edge_causalLE (a := .idempotentCut) (b := .operatorSquareDefect) hSquare,
    edge_causalLE (a := .idempotentCut) (b := .nestedDoubleCommutator) hDouble⟩

/-- D62's quartic action identity precedes invariance under the owner-defined
commutator flow; the square and nested-commutator identities are parallel
consequences of the same idempotent-cut input. -/
theorem d62_operator_flow_and_square_causal_order :
    causalLE .quarticDefectAction .quarticFlowInvariant ∧
    causalLE .idempotentCut .operatorSquareDefect ∧
    causalLE .idempotentCut .nestedDoubleCommutator := by
  rcases d62_cubic_and_quartic_archetypes_causal_order with
    ⟨_, _, _, _, hFlow, hSquare, hDouble⟩
  exact ⟨hFlow, hSquare, hDouble⟩

theorem sector_data_to_balanced_trace :
    causalLE .sectorData .balancedChargeTrace := by
  have hDifference : Node.edge .sectorData .chargeDifference := by
    intro data
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.charge_difference_from_sector_data
      (P_O2 := data.colorSector) (P_H1 := data.weakSectorOne)
      (P_H2 := data.weakSectorTwo) (P_C := data.scalarSector)
  have hBalanced : Node.edge .chargeDifference .balancedChargeTrace := by
    intro data
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acBalancedChargeTraceArchetype.evidence data
  exact causalLE_trans
    (edge_causalLE (a := .sectorData) (b := .chargeDifference) hDifference)
    (edge_causalLE (a := .chargeDifference) (b := .balancedChargeTrace) hBalanced)

theorem matrix_gram_to_kernel : causalLE .matrixGramIdentity .matrixGramKernel := by
  apply edge_causalLE
  intro input
  exact InfoGeometry.OperatorAlgebra.PeirceSpine.matrixD62GramArchetype.evidence input

/-- The quantitative recovery branch combines the collision, trace-metric
bound and replacement-channel inputs; the bound is stated on the actual
full complex matrix carrier. -/
theorem pinching_history_minimax_causal_branch {n : Type*}
    [Fintype n] [DecidableEq n] (X Y Z : Matrix n n ℂ) :
    causalLE .starProjection .finitePinchingChannel ∧
    causalLE .residualKrausCompletion .pinchedHistoryCollision ∧
    causalLE .pinchedHistoryCollision .sharpHistoryMinimax ∧
    causalLE .twoPointTraceBound .sharpHistoryMinimax ∧
    causalLE .replacementChannel .sharpHistoryMinimax ∧
    InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.matrixTraceNormSq (X - Y) / 4 ≤
      max (InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.matrixTraceNormSq (X - Z))
        (InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.matrixTraceNormSq (Y - Z)) := by
  have hPinching : Node.edge .starProjection .finitePinchingChannel := by
    intro k input
    exact (finitePinchingChannelArchetype k).evidence input
  have hCollision : Node.edge .residualKrausCompletion .pinchedHistoryCollision := by
    intro input
    exact (pinchedHistoryCollisionArchetype 2).evidence input
  have hSharp : Node.edge .pinchedHistoryCollision .sharpHistoryMinimax := by
    intro input
    exact (sharpHistoryMinimaxArchetype 2).evidence input
  have hTwoPoint : Node.edge .twoPointTraceBound .sharpHistoryMinimax := by
    intro U V W
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceHistoryRecoveryError.two_point_error_lower_bound
      U V W
  have hReplacement : Node.edge .replacementChannel .sharpHistoryMinimax := by
    intro m input
    exact (replacementMinimaxArchetype m).evidence input
  refine ⟨edge_causalLE (a := .starProjection) (b := .finitePinchingChannel) hPinching,
    edge_causalLE (a := .residualKrausCompletion) (b := .pinchedHistoryCollision) hCollision,
    edge_causalLE (a := .pinchedHistoryCollision) (b := .sharpHistoryMinimax) hSharp,
    edge_causalLE (a := .twoPointTraceBound) (b := .sharpHistoryMinimax) hTwoPoint,
    edge_causalLE (a := .replacementChannel) (b := .sharpHistoryMinimax) hReplacement, ?_⟩
  exact InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceHistoryRecoveryError.two_point_error_lower_bound
    X Y Z

theorem mirror_kraus_form_to_complete_positivity :
    causalLE .matrixMirrorKrausForm .matrixMirrorCompletePositivity := by
  apply edge_causalLE
  intro input
  exact InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixMirrorCPArchetype.evidence input

theorem d63_noninjectivity_and_nonunitarity_boundaries :
    causalLE .matrixMirrorUpperCornerWitness .matrixMirrorNonInjectivity ∧
    causalLE .reversibleShear .matrixShearNonunitarityWitness :=
  ⟨edge_causalLE
      (InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixMirrorNoninjectiveArchetype.evidence ()),
    edge_causalLE
      (InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixShearInvertibleNonunitaryArchetype.evidence ())⟩

/-- The D63 matrix sheet theorem, bulk invariance, and mirror-sandwich result
occupy causal branches from their actual star-projection and Peirce-cut inputs. -/
theorem d63_matrix_trace_bulk_and_mirror_causal_branches :
    causalLE .starProjection .matrixSheetPositivityAndTrace ∧
    causalLE .idempotentCut .bulkInvariance ∧
    causalLE .idempotentCut .mirrorSandwich := by
  exact ⟨causalLE_trans
      (edge_causalLE (a := .starProjection) (b := .matrixSheetGram)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixSheetArchetype.evidence
          ⟨InfoGeometry.OperatorAlgebra.PeirceSpine.d63TiltedProjection,
            InfoGeometry.OperatorAlgebra.PeirceSpine.d63TiltedAmplitude,
            InfoGeometry.OperatorAlgebra.PeirceSpine.d63_tilted_projection_is_star_projection⟩))
      (edge_causalLE (a := .matrixSheetGram)
        (b := .matrixSheetPositivityAndTrace)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixSheetArchetype.evidence
          ⟨InfoGeometry.OperatorAlgebra.PeirceSpine.d63TiltedProjection,
            InfoGeometry.OperatorAlgebra.PeirceSpine.d63TiltedAmplitude,
            InfoGeometry.OperatorAlgebra.PeirceSpine.d63_tilted_projection_is_star_projection⟩)),
    edge_causalLE (a := .idempotentCut) (b := .bulkInvariance)
      (BlackHoleInformation.bh63BulkInvarianceArchetype.evidence d63CausalBulkInput),
    edge_causalLE (a := .idempotentCut) (b := .mirrorSandwich)
      (BlackHoleInformation.bh63MirrorSandwichArchetype.evidence d63CausalMirrorInput)⟩

/-- Concrete D63 causal branch for the generic-ring Page, bulk, mirror, and
shear archetypes.  The archetypes themselves remain universally quantified in
their owner; this theorem supplies the existing non-diagonal `Fin 2` matrix
instance and proves each edge from that archetype's evidence. -/
theorem d63_concrete_operator_archetypes_causal_order :
    causalLE .idempotentCut .pageDefect ∧
    causalLE .idempotentCut .bulkInvariance ∧
    causalLE .idempotentCut .mirrorSandwich ∧
    causalLE .idempotentCut .reversibleShear ∧
    causalLE .reversibleShear .shearStateRecovery := by
  exact ⟨
    edge_causalLE (a := .idempotentCut) (b := .pageDefect)
      (BlackHoleInformation.bh63PageDefectArchetype.evidence d63CausalPageInput),
    edge_causalLE (a := .idempotentCut) (b := .bulkInvariance)
      (BlackHoleInformation.bh63BulkInvarianceArchetype.evidence d63CausalBulkInput),
    edge_causalLE (a := .idempotentCut) (b := .mirrorSandwich)
      (BlackHoleInformation.bh63MirrorSandwichArchetype.evidence d63CausalMirrorInput),
    edge_causalLE (a := .idempotentCut) (b := .reversibleShear)
      (BlackHoleInformation.bh63ShearReversibilityArchetype.evidence d63CausalShearInput),
    edge_causalLE
      (BlackHoleInformation.bh63ShearConjugationRecoveryArchetype.evidence
        d63CausalShearRecoveryInput)⟩

/-- The concrete non-diagonal finite-matrix Page-state archetype sits downstream
of the Peirce defect and star-projection nodes. Its final clause is the full
registered archetype claim for this fixed noncommuting matrix input. -/
theorem d63_matrix_page_defect_causal_order :
    causalLE .pageDefect .matrixPageDefect ∧
    causalLE .starProjection .matrixPageDefect ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixPageDefectArchetype.claim
      ⟨InfoGeometry.OperatorAlgebra.PeirceSpine.d63TiltedProjection,
        InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.d63InteriorPageAmplitude,
        InfoGeometry.OperatorAlgebra.PeirceSpine.d63_tilted_projection_is_star_projection⟩ := by
  let input : InfoGeometry.OperatorAlgebra.PeirceSpine.D63MatrixPageInput (Fin 2) :=
    ⟨InfoGeometry.OperatorAlgebra.PeirceSpine.d63TiltedProjection,
      InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.d63InteriorPageAmplitude,
      InfoGeometry.OperatorAlgebra.PeirceSpine.d63_tilted_projection_is_star_projection⟩
  exact ⟨edge_causalLE
      (InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixPageDefectArchetype.evidence input),
    edge_causalLE
      (InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixPageDefectArchetype.evidence input),
    InfoGeometry.MetaCompiler.TypedArchetype.discharge
      InfoGeometry.OperatorAlgebra.PeirceSpine.d63MatrixPageDefectArchetype input⟩

/-- The finite density-matrix and channel evolution archetypes are ordered by
their actual hypotheses: a positive metric complement plus a normalized
star-projection yields the state, while the residual Kraus completion and
state together yield trace-preserving density evolution. -/
theorem d63_finite_page_channel_causal_order {n : Type*}
    [Fintype n] [DecidableEq n] :
    causalLE .finiteMetricContractionBound .finitePageDensity ∧
    causalLE .normalizedProjectionTrace .finitePageDensity ∧
    causalLE .starProjection .finitePageDensity ∧
    causalLE .finiteMetricContractionBound .residualKrausCompletion ∧
    causalLE .finitePageDensity .tracePreservingPageEvolution ∧
    causalLE .residualKrausCompletion .tracePreservingPageEvolution ∧
    (∀ input : InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.FinitePageAdmissibleInput n,
      InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.finitePageDensityClaim input) ∧
    (∀ input : InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.FinitePageAdmissibleInput n,
      InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.finitePageChannelEvolutionClaim input) := by
  have hDensity := finitePageDensityClaim_proved d63InteriorFinitePageInput
  have hEvolution := finitePageChannelEvolutionClaim_proved d63InteriorFinitePageInput
  exact ⟨edge_causalLE (a := .finiteMetricContractionBound) (b := .finitePageDensity) hDensity,
    edge_causalLE (a := .normalizedProjectionTrace) (b := .finitePageDensity) hDensity,
    edge_causalLE (a := .starProjection) (b := .finitePageDensity) hDensity,
    edge_causalLE (a := .finiteMetricContractionBound) (b := .residualKrausCompletion) hEvolution,
    edge_causalLE (a := .finitePageDensity) (b := .tracePreservingPageEvolution) hEvolution,
    edge_causalLE (a := .residualKrausCompletion) (b := .tracePreservingPageEvolution) hEvolution,
    fun input => TypedArchetype.discharge
      InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.finitePageDensityArchetype
      input,
    fun input => TypedArchetype.discharge
      InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.finitePageChannelEvolutionArchetype
      input⟩

/-- The finite Page-state and channel branch has a concrete noncommuting
matrix instance. This closes the admissibility-to-output path for an actual
two-by-two operator input, rather than leaving the universal archetypes
potentially empty. -/
theorem d63_finite_page_archetypes_have_concrete_instance :
    causalLE .finiteMetricContractionBound .finitePageDensity ∧
    causalLE .finitePageDensity .tracePreservingPageEvolution ∧
    causalLE .finitePageDensity .finiteInteriorPageDefect ∧
    causalLE .tracePreservingPageEvolution .finiteInteriorPageDefect ∧
    ∃ input : FinitePageAdmissibleInput (Fin 2),
      finitePageDensityClaim input ∧
      finitePageChannelEvolutionClaim input ∧
      input.val.projection * input.val.amplitude ≠
        input.val.amplitude * input.val.projection := by
  have hDensityEdge : Node.edge .finitePageDensity .finiteInteriorPageDefect :=
    finitePageDensityClaim_proved d63InteriorFinitePageInput
  have hEvolutionEdge : Node.edge .tracePreservingPageEvolution
      .finiteInteriorPageDefect :=
    finitePageChannelEvolutionClaim_proved d63InteriorFinitePageInput
  refine ⟨edge_causalLE (a := .finiteMetricContractionBound) (b := .finitePageDensity)
      (finitePageDensityClaim_proved d63InteriorFinitePageInput),
    edge_causalLE (a := .finitePageDensity) (b := .tracePreservingPageEvolution)
      (finitePageChannelEvolutionClaim_proved d63InteriorFinitePageInput),
    edge_causalLE (a := .finitePageDensity) (b := .finiteInteriorPageDefect) hDensityEdge,
    edge_causalLE (a := .tracePreservingPageEvolution) (b := .finiteInteriorPageDefect)
      hEvolutionEdge, ?_⟩
  refine ⟨d63ConcreteFinitePageInput, ?_, ?_, ?_⟩
  · exact finitePageDensityClaim_proved _
  · exact finitePageChannelEvolutionClaim_proved _
  · change d63TiltedProjection * d63TiltedAmplitude ≠
      d63TiltedAmplitude * d63TiltedProjection
    exact d63_tilted_cut_amplitude_noncommute

theorem d63_interior_page_defect_archetype_proved :
    causalLE .finitePageDensity .finiteInteriorPageDefect ∧
    causalLE .tracePreservingPageEvolution .finiteInteriorPageDefect ∧
    d63InteriorPageDefectArchetype.claim () := by
  have hDensityEdge : Node.edge .finitePageDensity .finiteInteriorPageDefect :=
    finitePageDensityClaim_proved d63InteriorFinitePageInput
  have hEvolutionEdge : Node.edge .tracePreservingPageEvolution
      .finiteInteriorPageDefect :=
    finitePageChannelEvolutionClaim_proved d63InteriorFinitePageInput
  exact ⟨edge_causalLE (a := .finitePageDensity) (b := .finiteInteriorPageDefect) hDensityEdge,
    edge_causalLE (a := .tracePreservingPageEvolution) (b := .finiteInteriorPageDefect) hEvolutionEdge,
    TypedArchetype.discharge d63InteriorPageDefectArchetype ()⟩

theorem d63_shear_recovery_follows_from_invertibility :
    causalLE .reversibleShear .shearStateRecovery :=
  edge_causalLE
    (BlackHoleInformation.bh63ShearConjugationRecoveryArchetype.evidence
      d63CausalShearRecoveryInput)

/-- The finite Yukawa one-form has a concrete continuous Fréchet–Leibniz
derivation on its own matrix-operator carrier. This is a carrier-level bridge:
the witness is the inner commutator, not a nonlinear Fréchet derivative. -/
theorem finite_yukawa_frechet_derivation_bridge {n : ℕ}
    (P : InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.PeirceCut n)
    (A C : SouriauOnsagerBKM.FiniteOperatorAlgebra n) :
    causalLE .finiteYukawaOperator .continuousFrechetDerivation ∧
    ∃ D : FrechetOperatorDerivation ℝ
        (SouriauOnsagerBKM.FiniteOperatorAlgebra n),
      (∀ X,
        D X = InfoGeometry.OperatorAlgebra.PeirceSpine.comm
          (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi
            (P : SouriauOnsagerBKM.FiniteOperatorAlgebra n) A C) X) ∧
      (∀ X Y, D (X * Y) = D X * Y + X * D Y) := by
  have hEdge : Node.edge .finiteYukawaOperator .continuousFrechetDerivation := by
    intro k Q U V
    refine ⟨InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.yukawaOneFormDerivation
      Q U V, ?_, ?_⟩
    · intro X
      exact InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.yukawaOneFormDerivation_apply
        Q U V X
    · intro X Y
      exact InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.yukawaOneFormDerivation_leibniz
        Q U V X Y
  refine ⟨edge_causalLE (a := .finiteYukawaOperator)
      (b := .continuousFrechetDerivation) hEdge, ?_⟩
  refine ⟨InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.yukawaOneFormDerivation
    P A C, ?_, ?_⟩
  · intro X
    exact InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.yukawaOneFormDerivation_apply
      P A C X
  · intro X Y
    exact InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.yukawaOneFormDerivation_leibniz
      P A C X Y

theorem finite_yukawa_to_continuous_leibniz {n : ℕ}
    (P : InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.PeirceCut n)
    (A C : SouriauOnsagerBKM.FiniteOperatorAlgebra n) :
    causalLE .finiteYukawaOperator .continuousFrechetDerivation ∧
    ∃ D : FrechetOperatorDerivation ℝ (SouriauOnsagerBKM.FiniteOperatorAlgebra n),
      (∀ X, D X = InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi
          (P : SouriauOnsagerBKM.FiniteOperatorAlgebra n) A C) X) ∧
      (∀ X Y, D (X * Y) = D X * Y + X * D Y) :=
  finite_yukawa_frechet_derivation_bridge P A C

/-- The idempotent cut's inner derivation satisfies the noncommutative
Leibniz law on every finite operator carrier. -/
theorem finite_cut_inner_derivation_leibniz_causal {n : ℕ}
    (P : InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.PeirceCut n)
    (X Y : SouriauOnsagerBKM.FiniteOperatorAlgebra n) :
    causalLE .finiteCutInnerDerivation .continuousLeibnizLaw ∧
    InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.cutDerivation P (X * Y) =
      InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.cutDerivation P X * Y +
        X * InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.cutDerivation P Y := by
  have hEdge : Node.edge .finiteCutInnerDerivation .continuousLeibnizLaw := by
    intro k Q U V
    exact InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.cutDerivation_leibniz
      Q U V
  exact ⟨edge_causalLE hEdge,
    InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.cutDerivation_leibniz P X Y⟩

/-- Data for the concrete finite-operator Yukawa derivation bridge. -/
structure FiniteYukawaFrechetInput (n : ℕ) where
  cut : InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.PeirceCut n
  forwardAmplitude : SouriauOnsagerBKM.FiniteOperatorAlgebra n
  backwardAmplitude : SouriauOnsagerBKM.FiniteOperatorAlgebra n

/-- Proof-carrying archetype witnessing that the finite Yukawa commutator is
a continuous Fréchet–Leibniz derivation on its native operator carrier. -/
def finiteYukawaFrechetDerivationArchetype (n : ℕ) :
    TypedArchetype (FiniteYukawaFrechetInput n) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.ArchetypeCausalSynthesis.finiteYukawaFrechetDerivationArchetype
  phase := 63
  claim := fun input =>
    ∃ D : FrechetOperatorDerivation ℝ (SouriauOnsagerBKM.FiniteOperatorAlgebra n),
      (∀ X, D X = InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi
          (input.cut : SouriauOnsagerBKM.FiniteOperatorAlgebra n)
          input.forwardAmplitude input.backwardAmplitude) X) ∧
      (∀ X Y, D (X * Y) = D X * Y + X * D Y)
  evidence := fun input =>
    (finite_yukawa_frechet_derivation_bridge input.cut
      input.forwardAmplitude input.backwardAmplitude).2

#register_archetype finiteYukawaFrechetDerivationArchetype
#audit_archetype finiteYukawaFrechetDerivationArchetype

/-! The generic derivation archetype above has a concrete inhabitant on the
repository's tilted matrix projection, transported to the continuous
operator carrier.  This also records that the example is genuinely
noncommutative at the cut/amplitude level. -/

open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators

noncomputable def d63FrechetOperatorCut :
    InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.PeirceCut 2 := by
  let P := CblinfunMatrix.matrixOp d63TiltedProjection
  have hP : P * P = P := by
    apply CblinfunMatrix.matrixOfOp_injective
    change CblinfunMatrix.matrixOfOp (P.comp P) =
      CblinfunMatrix.matrixOfOp P
    rw [CblinfunMatrix.matrixOfOp_comp]
    simpa only [P, CblinfunMatrix.matrixOfOp_matrixOp] using
      d63_tilted_projection_is_star_projection.isIdempotentElem.eq
  exact ⟨P, hP⟩

noncomputable def d63FrechetYukawaInput : FiniteYukawaFrechetInput 2 :=
  ⟨d63FrechetOperatorCut,
    CblinfunMatrix.matrixOp d63TiltedAmplitude,
    CblinfunMatrix.matrixOp (star d63TiltedAmplitude)⟩

/-- The concrete tilted projection/amplitude supports the existing continuous
Fréchet–Leibniz archetype, and its cut and amplitude do not commute. -/
theorem d63_tilted_frechet_yukawa_archetype_and_noncommutativity :
    (finiteYukawaFrechetDerivationArchetype 2).claim d63FrechetYukawaInput ∧
    ((d63FrechetOperatorCut : SouriauOnsagerBKM.FiniteOperatorAlgebra 2) *
        d63FrechetYukawaInput.forwardAmplitude ≠
      d63FrechetYukawaInput.forwardAmplitude *
        (d63FrechetOperatorCut : SouriauOnsagerBKM.FiniteOperatorAlgebra 2)) := by
  constructor
  · exact TypedArchetype.discharge
      (finiteYukawaFrechetDerivationArchetype 2) d63FrechetYukawaInput
  · intro h
    have hm := congrArg
      (CblinfunMatrix.matrixOfOp :
        SouriauOnsagerBKM.FiniteOperatorAlgebra 2 → D63CausalMatrix) h
    change CblinfunMatrix.matrixOfOp
        ((CblinfunMatrix.matrixOp d63TiltedProjection).comp
          (CblinfunMatrix.matrixOp d63TiltedAmplitude)) =
      CblinfunMatrix.matrixOfOp
        ((CblinfunMatrix.matrixOp d63TiltedAmplitude).comp
          (CblinfunMatrix.matrixOp d63TiltedProjection)) at hm
    simp only [CblinfunMatrix.matrixOfOp_comp,
      CblinfunMatrix.matrixOfOp_matrixOp] at hm
    exact d63_tilted_cut_amplitude_noncommute hm

theorem frechet_leibniz_to_derivation_commutator :
    causalLE .continuousLeibnizLaw .derivationCommutatorClosure :=
  edge_causalLE (by
    intro n D E X Y
    exact FrechetOperatorDerivation.commutator_leibniz D E X Y)

theorem d64_generic_trace_archetype_edges :
    causalLE .idempotentCut .genericChiralMassSquareTrace ∧
    causalLE .cyclicTraceLaws .genericChiralMassSquareTrace := by
  have hCut : Node.edge .idempotentCut .genericChiralMassSquareTrace := by
    intro P hP τ hAdd hSub hCyc A C
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.peirce_cyclic_trace_mass_square
      hP τ hAdd hSub hCyc A C
  have hTrace : Node.edge .cyclicTraceLaws .genericChiralMassSquareTrace := by
    intro P hP τ hAdd hSub hCyc A C
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.peirce_cyclic_trace_mass_square
      hP τ hAdd hSub hCyc A C
  exact ⟨edge_causalLE hCut, edge_causalLE hTrace⟩

theorem generic_trace_to_matrix_specialization :
    causalLE .genericChiralMassSquareTrace .matrixChiralTraceSpecialization := by
  have hEdge : Node.edge .genericChiralMassSquareTrace .matrixChiralTraceSpecialization := by
    intro input
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.d64MatrixChiralTraceArchetype.evidence
      input
  exact edge_causalLE hEdge

theorem matrix_trace_specialization_to_amplitude_invariance :
    causalLE .matrixChiralTraceSpecialization .matrixChiralTraceAmplitudeInvariance := by
  have hEdge : Node.edge .matrixChiralTraceSpecialization
      .matrixChiralTraceAmplitudeInvariance := by
    intro p A C A' C' hp
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.d64_matrix_chiral_trace_independent_of_amplitudes
      hp
  exact edge_causalLE hEdge

theorem d65_matrix_cut_to_order_zero_and_one :
    causalLE .nondiagonalMatrixCutWitness .matrixOrderZeroCorners ∧
    causalLE .nondiagonalMatrixAmplitudeWitness .matrixTwoWaveOperator ∧
    causalLE .nondiagonalMatrixCutWitness .matrixTwoWaveOperator ∧
    causalLE .matrixTwoWaveOperator .matrixOrderOneObstruction := by
  exact ⟨
    edge_causalLE InfoGeometry.OperatorAlgebra.PeirceSpine.d65_order_zero_corners_commute,
    edge_causalLE (InfoGeometry.OperatorAlgebra.PeirceSpine.d65ForwardWaveNonzeroArchetype.evidence ()),
    edge_causalLE (by rfl),
    edge_causalLE InfoGeometry.OperatorAlgebra.PeirceSpine.d65_order_one_obstruction_nonzero⟩

theorem d65_order_zero_and_obstruction_synthesis :
    causalLE .matrixOrderZeroCorners .orderZeroDoesNotImplyOrderOne ∧
    causalLE .matrixOrderOneObstruction .orderZeroDoesNotImplyOrderOne :=
  ⟨edge_causalLE
      (InfoGeometry.OperatorAlgebra.PeirceSpine.d65OrderZeroOrderOneCounterexampleArchetype.evidence ()),
    edge_causalLE
      (InfoGeometry.OperatorAlgebra.PeirceSpine.d65OrderZeroOrderOneCounterexampleArchetype.evidence ())⟩

/-! ## Fréchet–Leibniz owner path

These vertices refer to the analytic operator-derivation carrier in `Optics`,
not to a nonlinear map's Fréchet derivative.  The finite Peirce-cut instance
is a separate specialization in `Canonical`; the dependency edges below only
record constructions whose proofs use the indicated owner declarations.
-/

theorem optics_frechet_derivation_causal_laws :
    causalLE .opticsFrechetDerivationCarrier .opticsInnerFrechetDerivation ∧
    causalLE .opticsFrechetDerivationCarrier .opticsFrechetCommutatorClosure ∧
    causalLE .opticsInnerFrechetDerivation .opticsFrechetCurvatureLeibniz := by
  have hInner : Node.edge .opticsFrechetDerivationCarrier
      .opticsInnerFrechetDerivation := by
    intro D x y
    exact D.leibniz x y
  have hClosure : Node.edge .opticsFrechetDerivationCarrier
      .opticsFrechetCommutatorClosure := by
    intro D E x y
    exact FrechetOperatorDerivation.commutator_leibniz D E x y
  have hCurvature : Node.edge .opticsInnerFrechetDerivation
      .opticsFrechetCurvatureLeibniz := by
    intro D C p X Y
    exact FrechetOperatorDerivation.map_curvature D C p X Y
  exact ⟨edge_causalLE hInner, edge_causalLE hClosure, edge_causalLE hCurvature⟩

/-! ## Proof-carrying Fréchet–Leibniz archetype

This archetype is over the repository's continuous operator-derivation carrier.
Its claim is the noncommutative product rule for the commutator derivation;
it is not a claim about differentiating a nonlinear map. -/

/-- Inputs for closure of continuous operator derivations under commutator. -/
structure FrechetCommutatorInput
    (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] where
  left : FrechetOperatorDerivation 𝕜 A
  right : FrechetOperatorDerivation 𝕜 A
  first : A
  second : A

/-- The commutator of continuous operator derivations again satisfies the
noncommutative Leibniz rule. The proof reuses the analytic operator owner. -/
def frechetCommutatorLeibnizArchetype
    (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] :
    TypedArchetype (FrechetCommutatorInput 𝕜 A) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.ArchetypeCausalSynthesis.frechetCommutatorLeibnizArchetype
  phase := 63
  claim := fun input =>
    FrechetOperatorDerivation.commutator input.left input.right
        (input.first * input.second) =
      FrechetOperatorDerivation.commutator input.left input.right input.first *
          input.second +
        input.first * FrechetOperatorDerivation.commutator
          input.left input.right input.second
  evidence := fun input =>
    FrechetOperatorDerivation.commutator_leibniz
      input.left input.right input.first input.second

#register_archetype frechetCommutatorLeibnizArchetype
#audit_archetype frechetCommutatorLeibnizArchetype

theorem frechet_commutator_archetype_follows_from_leibniz_stage
    {n : ℕ}
    (D E : FrechetOperatorDerivation ℝ (SouriauOnsagerBKM.FiniteOperatorAlgebra n))
    (x y : SouriauOnsagerBKM.FiniteOperatorAlgebra n) :
    causalLE .continuousLeibnizLaw .derivationCommutatorClosure ∧
      FrechetOperatorDerivation.commutator D E (x * y) =
        FrechetOperatorDerivation.commutator D E x * y +
          x * FrechetOperatorDerivation.commutator D E y := by
  have hEdge : Node.edge .continuousLeibnizLaw .derivationCommutatorClosure := by
    intro k F G u v
    exact FrechetOperatorDerivation.commutator_leibniz F G u v
  exact ⟨edge_causalLE hEdge,
    TypedArchetype.discharge
      (frechetCommutatorLeibnizArchetype ℝ
        (SouriauOnsagerBKM.FiniteOperatorAlgebra n))
      ⟨D, E, x, y⟩⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine.ArchetypeCausalSynthesis

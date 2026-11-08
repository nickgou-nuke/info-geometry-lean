import InfoGeometry.Canonical.MadelungMetriplecticTomitaFrame
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.TraceFormula.DeterminantBondNative
import InfoGeometry.TraceFormula.PrimonColimitGNSRepresentation
import InfoGeometry.Clifford.CliffordBitWordEquivalence
import InfoGeometry.Arithmetic.AmariCayleyQuantumBridge

/-!
# Finite carrier lift for the Madelung--metriplectic frame

This file owns only the finite-to-colimit transport of the observable action.
The Madelung, metriplectic, KAN, and modular laws remain in their respective
owner files; this bridge records how a finite matrix carrier is represented in
the algebraic UHF colimit.
-/

noncomputable section

namespace InfoGeometry.Canonical.MadelungMetriplecticColimitBridge

open InfoGeometry.Algebra.PrimonColimitAlgebra
open InfoGeometry.Canonical.MadelungMetriplecticTomitaFrame
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Physics
open InfoGeometry.TraceFormula.DeterminantBondNative
open InfoGeometry.TraceFormula.PrimonColimitGNSRepresentation
open InfoGeometry.Algebra.CliffordBitWordEquivalence
open InfoGeometry.Clifford.Cl11TensorTowerLimit

/-! ## Carrier isomorphism -/

/-- The finite trace-bimodule carrier and the Primon matrix stage are the same
    real matrix space after choosing the bitword index type. -/
noncomputable def traceOperatorSpaceMatrixStageEquiv (n : ℕ) :
    TraceOperatorSpace (BitWord n) ≃ₗ[ℝ] MatrixStage n :=
  LinearEquiv.refl ℝ (MatrixStage n)

@[simp] theorem traceOperatorSpaceMatrixStageEquiv_apply
    (n : ℕ) (X : TraceOperatorSpace (BitWord n)) :
    traceOperatorSpaceMatrixStageEquiv n X = X := by
  rfl

theorem tracePairing_native_eq_rawTrace
    (n : ℕ) (X Y : TraceOperatorSpace (BitWord n)) :
    rawTrace n
        (traceOperatorSpaceMatrixStageEquiv n X *
          traceOperatorSpaceMatrixStageEquiv n Y) =
      tracePairingNative X Y := by
  rfl

/-- The finite Onsager trace pairing has the normalized colimit readout. -/
theorem tracePairing_colimit_stage_readout
    (n : ℕ) (X Y : TraceOperatorSpace (BitWord n)) :
    tauInfinity
        (toColimit n
          (traceOperatorSpaceMatrixStageEquiv n X *
            traceOperatorSpaceMatrixStageEquiv n Y)) =
      (1 / (2 ^ n : ℝ)) * tracePairingNative X Y := by
  rw [tauInfinity_stage]
  unfold normalizedTrace rawTrace
  rfl

theorem fermi_covariance_tracePairing_colimit_readout (θ : ℝ) :
    let C : TraceOperatorSpace (BitWord 1) :=
        (InfoGeometry.Algebra.CliffordBitWordEquivalence.bitWordStageEquivFin 1).symm
        (InfoGeometry.Krein.FiniteCovarianceMajoranaBlock.covarianceProjection
          (InfoGeometry.Clifford.ThermodynamicZetaGeometry.occupation .FD θ))
    tauInfinity (toColimit 1 (C * C)) =
      (1 / (2 ^ 1 : ℝ)) * tracePairingNative C C := by
  dsimp
  exact tracePairing_colimit_stage_readout 1 _ _

/-! The stage successor is identified through the native bitword index
    equivalence and the Kronecker identity factor. -/

theorem matrixStage_bond_reindex_kronecker
    (n : ℕ) (M : MatrixStage n) :
    matrixBond n M =
      Matrix.reindex
        (InfoGeometry.TraceFormula.DeterminantBondNative.bitWordSuccEquiv n).symm
        (InfoGeometry.TraceFormula.DeterminantBondNative.bitWordSuccEquiv n).symm
        (Matrix.kronecker M (1 : Matrix Bool Bool ℝ)) := by
  change matrixBondFun n M = _
  exact matrixBondFun_eq_reindex_kronecker n M

/-! ## Finite carrier action -/

@[simp] theorem finiteCarrier_action_apply
    (n : ℕ) (a x : MatrixStage n) :
    finiteLeftAction n a x = a * x := by
  rfl

theorem finiteCarrier_action_bond
    (n : ℕ) (a x : MatrixStage n) :
    finiteLeftAction (n + 1) (matrixBond n a) (matrixBond n x) =
      matrixBond n (finiteLeftAction n a x) := by
  simp [finiteLeftAction, map_mul]

/-! ## Colimit lift -/

def liftedLeftAction (a : PrimonUHFAlgebra) :
    PrimonUHFAlgebra →+ PrimonUHFAlgebra :=
  colimitLeftAction a

@[simp] theorem liftedLeftAction_apply
    (a x : PrimonUHFAlgebra) :
    liftedLeftAction a x = a * x := by
  rfl

theorem liftedLeftAction_stage
    (n : ℕ) (a x : MatrixStage n) :
    liftedLeftAction (toColimit n a) (toColimit n x) =
      toColimit n (finiteLeftAction n a x) := by
  simp [liftedLeftAction, finiteLeftAction]

theorem liftedLeftAction_bond
    (n : ℕ) (a x : MatrixStage n) :
    liftedLeftAction (toColimit (n + 1) (matrixBond n a))
      (toColimit (n + 1) (matrixBond n x)) =
    liftedLeftAction (toColimit n a) (toColimit n x) := by
  exact colimitLeftAction_bond n a x

/-! ## The packaged finite-to-colimit carrier datum -/

structure CarrierLift where
  stage : ℕ
  observable : MatrixStage stage

def CarrierLift.colimit (C : CarrierLift) : PrimonUHFAlgebra :=
  toColimit C.stage C.observable

theorem CarrierLift.colimit_action (C : CarrierLift) :
    liftedLeftAction C.colimit C.colimit =
      toColimit C.stage (C.observable * C.observable) := by
  simp [CarrierLift.colimit, liftedLeftAction]

/-! ## Frame lanes transported to the colimit -/

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure FrameCarrierLift where
  stage : ℕ
  frame : Frame (n := BitWord stage) (E := E)

def FrameCarrierLift.matrix (C : FrameCarrierLift (E := E))
    (X : TraceOperatorSpace (BitWord C.stage)) : MatrixStage C.stage :=
  traceOperatorSpaceMatrixStageEquiv C.stage X

def FrameCarrierLift.hamiltonian (C : FrameCarrierLift (E := E)) :
    PrimonUHFAlgebra :=
  toColimit C.stage (C.matrix C.frame.H)

def FrameCarrierLift.metric (C : FrameCarrierLift (E := E)) :
    PrimonUHFAlgebra :=
  toColimit C.stage (C.matrix C.frame.S)

def FrameCarrierLift.observable (C : FrameCarrierLift (E := E)) :
    PrimonUHFAlgebra :=
  toColimit C.stage (C.matrix C.frame.X)

def FrameCarrierLift.generator (C : FrameCarrierLift (E := E)) :
    PrimonUHFAlgebra :=
  toColimit C.stage (C.matrix (finiteGenerator C.frame))

def FrameCarrierLift.weightedGenerator (C : FrameCarrierLift (E := E)) (γ : ℝ) :
    PrimonUHFAlgebra :=
  toColimit C.stage (C.matrix (finiteWeightedGenerator C.frame γ))

theorem FrameCarrierLift.hamiltonian_action
    (C : FrameCarrierLift (E := E)) (Y : TraceOperatorSpace (BitWord C.stage)) :
    liftedLeftAction C.hamiltonian (toColimit C.stage (C.matrix Y)) =
      toColimit C.stage (C.matrix (C.frame.H * Y)) := by
  simp [FrameCarrierLift.hamiltonian, FrameCarrierLift.matrix,
    liftedLeftAction]

theorem FrameCarrierLift.metric_action
    (C : FrameCarrierLift (E := E)) (Y : TraceOperatorSpace (BitWord C.stage)) :
    liftedLeftAction C.metric (toColimit C.stage (C.matrix Y)) =
      toColimit C.stage (C.matrix (C.frame.S * Y)) := by
  simp [FrameCarrierLift.metric, FrameCarrierLift.matrix,
    liftedLeftAction]

theorem FrameCarrierLift.observable_action
    (C : FrameCarrierLift (E := E)) (Y : TraceOperatorSpace (BitWord C.stage)) :
    liftedLeftAction C.observable (toColimit C.stage (C.matrix Y)) =
      toColimit C.stage (C.matrix (C.frame.X * Y)) := by
  simp [FrameCarrierLift.observable, FrameCarrierLift.matrix,
    liftedLeftAction]

theorem FrameCarrierLift.generator_action
    (C : FrameCarrierLift (E := E)) (Y : TraceOperatorSpace (BitWord C.stage)) :
    liftedLeftAction C.generator (toColimit C.stage (C.matrix Y)) =
      toColimit C.stage (C.matrix (finiteGenerator C.frame * Y)) := by
  simp [FrameCarrierLift.generator, FrameCarrierLift.matrix,
    liftedLeftAction]

theorem FrameCarrierLift.weightedGenerator_action
    (C : FrameCarrierLift (E := E)) (γ : ℝ)
    (Y : TraceOperatorSpace (BitWord C.stage)) :
    liftedLeftAction (C.weightedGenerator γ)
      (toColimit C.stage (C.matrix Y)) =
      toColimit C.stage
        (C.matrix (weightedMetriplecticGenerator γ C.frame.H C.frame.S
          C.frame.X * Y)) := by
  simp [FrameCarrierLift.weightedGenerator, FrameCarrierLift.matrix,
    finiteWeightedGenerator, liftedLeftAction]

/-! The finite trace-bimodule and the colimit action are two readouts of the
same weighted noncommutative driver.  This packet deliberately keeps the
pairing statement on the finite stage and the multiplication statement on
the colimit; no analytic limit or scalar diagonalization is involved. -/
theorem FrameCarrierLift.weighted_metriplectic_packet
    (C : FrameCarrierLift (E := E)) (γ : ℝ)
    (Y : TraceOperatorSpace (BitWord C.stage)) :
    tracePairingNative (finiteWeightedGenerator C.frame γ) Y =
        - tracePairingNative C.frame.X
            (conservativeDriver C.frame.H Y) +
          γ * tracePairingNative C.frame.X
            (dissipativeDriver C.frame.S Y) ∧
      liftedLeftAction (C.weightedGenerator γ)
        (toColimit C.stage (C.matrix Y)) =
        toColimit C.stage
          (C.matrix (weightedMetriplecticGenerator γ C.frame.H
            C.frame.S C.frame.X * Y)) := by
  constructor
  · exact finiteWeightedGenerator_tracePairing_decomposition C.frame γ Y
  · exact C.weightedGenerator_action γ Y

theorem FrameCarrierLift.hamiltonian_commonCarrier
    (C : FrameCarrierLift (E := E)) :
    cliffordBitWordColimitEquiv
        (ofStage C.stage
          ((clStageEquiv C.stage).symm (C.matrix C.frame.H))) =
      C.hamiltonian := by
  rw [cliffordBitWordColimitEquiv_ofStage_symm]
  rfl

theorem FrameCarrierLift.metric_commonCarrier
    (C : FrameCarrierLift (E := E)) :
    cliffordBitWordColimitEquiv
        (ofStage C.stage
          ((clStageEquiv C.stage).symm (C.matrix C.frame.S))) =
      C.metric := by
  rw [cliffordBitWordColimitEquiv_ofStage_symm]
  rfl

theorem FrameCarrierLift.observable_commonCarrier
    (C : FrameCarrierLift (E := E)) :
    cliffordBitWordColimitEquiv
        (ofStage C.stage
          ((clStageEquiv C.stage).symm (C.matrix C.frame.X))) =
      C.observable := by
  rw [cliffordBitWordColimitEquiv_ofStage_symm]
  rfl

theorem FrameCarrierLift.generator_commonCarrier
    (C : FrameCarrierLift (E := E)) :
    cliffordBitWordColimitEquiv
        (ofStage C.stage
          ((clStageEquiv C.stage).symm
            (C.matrix (finiteGenerator C.frame)))) =
      C.generator := by
  rw [cliffordBitWordColimitEquiv_ofStage_symm]
  rfl

end InfoGeometry.Canonical.MadelungMetriplecticColimitBridge

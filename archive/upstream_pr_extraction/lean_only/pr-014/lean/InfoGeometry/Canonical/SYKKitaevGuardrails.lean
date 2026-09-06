import InfoGeometry.Canonical.FirstQuantizationProbability
import InfoGeometry.Canonical.MajoranaKitaevSpinorBridge
import InfoGeometry.Canonical.RNDeterminantConnesChainBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SYKKitaevGuardrails

Scope guardrails for SYK-vs-Kitaev language and a strict four-step modular lane:

1. `Δ`: relative modular operator owner,
2. `K = -log Δ`: derived Hamiltonian operator lane,
3. scalar readout: normalized relative modular Hamiltonian expectation,
4. cocycle chain law: multiplicative primary dynamics.
-/

namespace InfoGeometry.Canonical.SYKKitaevGuardrails

open InfoGeometry.Canonical.FirstQuantizationProbability
open InfoGeometry.Canonical.MajoranaKitaevSpinorBridge
open InfoGeometry.Canonical.RNDeterminantConnesChainBridge
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativeModularOperator
open InfoGeometry.Canonical.RelativeModularHamiltonian
open InfoGeometry.Quantum.KitaevChain
open InfoGeometry.Quantum.BulkBoundary
open InfoGeometry.Quantum.RealMajorana

section Bands

variable {S : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
variable [FiniteDimensional ℝ S]

/-- Scope band for SYK/Kitaev statements in this repository. -/
inductive ScopeBand where
  | repo_theorem
  | formalizable_next_owner_target
  | external_interpretation
deriving DecidableEq, Repr

/-- Minimal two-copy SYK-like protocol interface (owner target, not yet canonical owner). -/
@[rep_depth transport]
structure TwoCopySYKLikeProtocol where
  leftHamiltonian : S →L[ℝ] S
  rightHamiltonian : S →L[ℝ] S
  crossCoupling : S →L[ℝ] S
  couplingStrength : ℝ

/-- Existence marker for a typed two-copy SYK-like protocol lane. -/
def HasTwoCopySYKLikeProtocol : Prop :=
  Nonempty (TwoCopySYKLikeProtocol (S := S))

/-- Classification guardrail for traversable-wormhole language. -/
noncomputable def traversableClaimBand : ScopeBand :=
  by
    classical
    exact if h : HasTwoCopySYKLikeProtocol (S := S)
      then ScopeBand.formalizable_next_owner_target
      else ScopeBand.external_interpretation

omit [CompleteSpace S] [FiniteDimensional ℝ S] in
@[rep_depth transport]
theorem traversableClaimBand_eq_external_of_noProtocol
    (hNo : ¬HasTwoCopySYKLikeProtocol (S := S)) :
    traversableClaimBand (S := S) = ScopeBand.external_interpretation := by
  classical
  unfold traversableClaimBand
  simp [hNo]

omit [CompleteSpace S] [FiniteDimensional ℝ S] in
@[rep_depth transport]
theorem traversableClaimBand_eq_formalizable_of_protocol
    (hYes : HasTwoCopySYKLikeProtocol (S := S)) :
    traversableClaimBand (S := S) = ScopeBand.formalizable_next_owner_target := by
  classical
  unfold traversableClaimBand
  simp [hYes]

end Bands

section KitaevOwnedSurface

variable {S : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
variable [FiniteDimensional ℝ S]

/-- Repo-owned Kitaev/Majorana boundary lane hypotheses. -/
@[rep_depth krein]
def KitaevRepoHypotheses
    (M : RealMajoranaDatum (S := S))
    (localOp : KitaevCell → S →L[ℝ] S)
    (chain : List KitaevCell) : Prop :=
  topologicalIndexZ2 chain = 1
    ∧ (∀ c : KitaevCell,
        ParticleHoleSymmetric (M := M) (P0 := M.chiralityPolarization) (localOp c))
    ∧ SimplifiedBoundaryModel (M := M) (P0 := M.chiralityPolarization) localOp chain

omit [FiniteDimensional ℝ S] in
@[rep_depth krein]
theorem exists_weylBoundarySpinorPair_of_kitaevRepoHypotheses
    (M : RealMajoranaDatum (S := S))
    (localOp : KitaevCell → S →L[ℝ] S)
    (chain : List KitaevCell)
    (hRepo : KitaevRepoHypotheses (S := S) M localOp chain) :
    Nonempty (WeylBoundarySpinorPair
      (S := S) M (globalChainOperatorFromOpenChain (S := S) localOp chain)) := by
  rcases hRepo with ⟨hTopo, hPHS, hSimple⟩
  exact ⟨weylBoundarySpinorPair_of_simplifiedBoundaryModel
    (S := S) M localOp chain hTopo hPHS hSimple⟩

@[rep_depth krein]
theorem exists_nontrivial_regularization_pair_of_kitaevRepoHypotheses
    (M : RealMajoranaDatum (S := S))
    (localOp : KitaevCell → S →L[ℝ] S)
    (chain : List KitaevCell)
    (hRepo : KitaevRepoHypotheses (S := S) M localOp chain) :
    ∃ (Q_MP Q_D : S →L[ℝ] S) (k : ℕ),
      IsMoorePenroseInverse
        (globalChainOperatorFromOpenChain (S := S) localOp chain) Q_MP ∧
      IsDrazinInverse
        (globalChainOperatorFromOpenChain (S := S) localOp chain) Q_D k ∧
      MoorePenrose.IsMoorePenroseInverse.rightProjector
          (globalChainOperatorFromOpenChain (S := S) localOp chain) Q_MP
          ≠ (1 : S →L[ℝ] S) ∧
      MoorePenrose.IsMoorePenroseInverse.leftProjector
          (globalChainOperatorFromOpenChain (S := S) localOp chain) Q_MP
          ≠ (1 : S →L[ℝ] S) ∧
      Drazin.IsDrazinInverse.projection
          (globalChainOperatorFromOpenChain (S := S) localOp chain) Q_D
          ≠ (1 : S →L[ℝ] S) := by
  rcases hRepo with ⟨hTopo, hPHS, hSimple⟩
  exact exists_nontrivial_regularization_pair_of_simplifiedBoundaryModel
    (S := S) M localOp chain hTopo hPHS hSimple

end KitaevOwnedSurface

section FourStepLane

variable {n : ℕ} [Nonempty (Fin n)]

/--
Four-step modular lane package:
`Δ` owner -> `K = -log Δ` operator -> scalar readout -> cocycle chain law.
-/
@[rep_depth thermo, capstone]
theorem fourStep_modular_lane_package
    (q q0 q1 : PositiveRay (Fin n)) :
    let _Delta := relativeModularOperator (n := n) q q0
    let K := relativeModularHamiltonianOperator (n := n) q q0
    let scalarReadout := relativeModularHamiltonianReadout (n := n) q q0
    K = quantizedSurprisalOperator (n := n) q q0
      ∧ scalarReadout = (n : ℝ)⁻¹ * relativeModularVolumePotential (n := n) q q0
      ∧ relativeModularOperator (n := n) q q1
          = relativeModularOperator (n := n) q q0
              * relativeModularOperator (n := n) q0 q1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact relativeModularHamiltonianOperator_eq_quantizedSurprisalOperator (n := n) q q0
  · exact relativeModularHamiltonianReadout_eq_inv_card_mul_relativeModularVolumePotential
      (n := n) q q0
  · exact relativeModularOperator_state_chain (n := n) q q0 q1

end FourStepLane

end InfoGeometry.Canonical.SYKKitaevGuardrails

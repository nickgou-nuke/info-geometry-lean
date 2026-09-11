import InfoGeometry.LLM.TransformerPhysicsEngine
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.LLM.RouterFreeEnergyBridge
import InfoGeometry.LLM.KreinAttentionEnergy
import InfoGeometry.LLM.KMSSoftmaxBridge
import InfoGeometry.Meta.Architecture

open scoped BigOperators InnerProductSpace

namespace InfoGeometry.LLM.HypothesisScaffold70

open InfoGeometry.Canonical.MoE
open InfoGeometry.LLM.AllTopThermodynamicTransformer
open InfoGeometry.LLM.KreinAttentionEnergy
open InfoGeometry.LLM.KMSSoftmaxBridge
open InfoGeometry.LLM.RouterFreeEnergyBridge
open InfoGeometry.LLM.TransformerPhysicsEngine

/-- Lifecycle tag for Chapter 70 hypotheses. -/
inductive H70Status where
  | spec
  | unproven
  | testable
  deriving DecidableEq, Repr

/-- Authority/evidence tier for Chapter 70 claims. -/
inductive H70Authority where
  | externalFact
  | repoTheorem
  | analogy
  | speculative
  deriving DecidableEq, Repr

/-- Minimal metadata carrier for hypothesis tracking. -/
structure H70Claim where
  id : String
  label : String
  status : H70Status
  authority : H70Authority

/-- Chapter 70 registry (formal hooks only; no proof commitments here). -/
def registry : List H70Claim :=
  [
    { id := "H70-003", label := "Router free-energy/Massieu bridge", status := H70Status.testable, authority := H70Authority.repoTheorem }
  , { id := "H70-004", label := "Per-layer scale/shape split", status := H70Status.testable, authority := H70Authority.repoTheorem }
  , { id := "H70-005", label := "Stack-level defect quarantine", status := H70Status.testable, authority := H70Authority.repoTheorem }
  , { id := "H70-007", label := "Krein attention inner product surface", status := H70Status.testable, authority := H70Authority.repoTheorem }
  , { id := "H70-008", label := "Softmax/KMS finite normalization bridge", status := H70Status.testable, authority := H70Authority.repoTheorem }
  , { id := "H70-010", label := "Horizon inversion gate", status := H70Status.spec, authority := H70Authority.speculative }
  ]

section KreinInterface

/-- Testable hook for H70-007 (split-signature/Krein attention energy surface). -/
@[rep_depth krein]
theorem h70_krein_energy_surface
    (q k : ℝ × ℝ) :
    kreinInteractionEnergy q k = -(q.1 * k.1 - q.2 * k.2) := by
  exact kreinInteractionEnergy_eq_neg_splitB11 q k

end KreinInterface

section KMSSoftmaxInterface

variable {Tok V : Type*}
variable [NormedAddCommGroup V]
variable {n : Nat} [Nonempty (Fin n)]

/-- Testable hook for H70-008 (finite KMS-compatible normalization bridge). -/
@[rep_depth thermo]
theorem h70_kms_softmax_normalization
    (β : ℝ) (x : Tok → V) (i : Tok) :
    (∑ e : ExpertIdx n, softmaxWeight n β x i e = 1)
      ∧
    (∑ e : ExpertIdx n, kmsWeight n β x i e = 1) := by
  refine ⟨?_, ?_⟩
  · exact softmaxWeight_sum_one (n := n) (β := β) (x := x) (i := i)
  · exact kmsWeight_sum_one (n := n) (β := β) (x := x) (i := i)

end KMSSoftmaxInterface

section ThermoInterface

variable {Tok V : Type*}
variable [NormedAddCommGroup V]
variable {n : Nat} [Nonempty (Fin n)]

/-- Testable hook for H70-003 (thermodynamic bridge). -/
@[rep_depth thermo]
theorem h70_router_free_energy_bridge
    (β : ℝ) (x : Tok → V) (i : Tok) (hβ : β ≠ 0) :
    β * routerFreeEnergy n β x i = -routerMassieu n β x i := by
  exact
    router_free_energy_identity_per_step
      (n := n) (β := β) (x := x) (i := i) hβ

end ThermoInterface

section TransportInterfaces

variable {Tok V : Type*}
variable [Fintype Tok] [DecidableEq Tok]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : Nat} [Nonempty (Fin n)]

section OmitTransportRouterVars

omit [Fintype Tok] [DecidableEq Tok] [Nonempty (Fin n)]

/-- Testable hook for H70-004 (scale/shape split per layer). -/
@[rep_depth transport]
theorem h70_scale_shape_split
    (L : ReusedAllTopLayer V n)
    (β : ℝ) (x : Tok → V) (i : Tok) :
    L.runToken β x i = L.base.run (x i) + normalizedMixture L.routedMoE β x i := by
  exact
    scale_shape_split_preserved_per_layer
      (L := L) (β := β) (x := x) (i := i)

/-- Testable hook for H70-005 (defect quarantine under stack composition). -/
@[rep_depth transport]
theorem h70_defect_quarantine
    (layers : List (DecoderLayer V))
    (β : ℝ) (x : Tok → V) :
    runLayerStack (Tok := Tok) (V := V) (n := n)
      (layers.map (WeightReuse.withZeroMoE (V := V) (n := n))) β x
      =
    runDecoderStackPointwise (Tok := Tok) (V := V) layers x := by
  exact
    defect_quarantine_preserved_under_stack
      (Tok := Tok) (V := V) (n := n) (layers := layers) (β := β) (x := x)

end OmitTransportRouterVars

section OmitTransportSurfaceVars

omit [Fintype Tok] [DecidableEq Tok]

/-- Capstone package: all currently testable Chapter 70 hooks bundled together. -/
@[rep_depth transport, capstone]
theorem h70_test_surface
    (L : ReusedAllTopLayer V n)
    (layers : List (DecoderLayer V))
    (β : ℝ) (x : Tok → V) (i : Tok) (hβ : β ≠ 0) :
    (β * routerFreeEnergy n β x i = -routerMassieu n β x i)
      ∧
    (L.runToken β x i = L.base.run (x i) + normalizedMixture L.routedMoE β x i)
      ∧
    (runLayerStack (Tok := Tok) (V := V) (n := n)
      (layers.map (WeightReuse.withZeroMoE (V := V) (n := n))) β x
      =
    runDecoderStackPointwise (Tok := Tok) (V := V) layers x) := by
  refine ⟨?_, ?_, ?_⟩
  · exact h70_router_free_energy_bridge (n := n) (β := β) (x := x) (i := i) hβ
  · exact h70_scale_shape_split (L := L) (β := β) (x := x) (i := i)
  · exact h70_defect_quarantine (Tok := Tok) (V := V) (n := n) (layers := layers) (β := β) (x := x)

end OmitTransportSurfaceVars

end TransportInterfaces

end InfoGeometry.LLM.HypothesisScaffold70

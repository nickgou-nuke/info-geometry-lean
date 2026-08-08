import InfoGeometry.LLM.AllTopThermodynamicTransformer
import InfoGeometry.LLM.RouterFreeEnergyBridge
import InfoGeometry.Meta.Architecture

open scoped BigOperators InnerProductSpace

namespace InfoGeometry.LLM.TransformerPhysicsEngine

open InfoGeometry.Canonical.MoE
open InfoGeometry.LLM.AllTopThermodynamicTransformer
open InfoGeometry.LLM.RouterFreeEnergyBridge

section ThermoInvariant

variable {Tok V : Type*}
variable [NormedAddCommGroup V]
variable {n : Nat} [Nonempty (Fin n)]

/--
Token-local thermodynamic identity on the routed expert slice:
`β F = -ψ` (free energy / Massieu relation).
-/
@[rep_depth thermo]
theorem router_free_energy_identity_per_step
    (β : ℝ) (x : Tok → V) (i : Tok) (hβ : β ≠ 0) :
    β * routerFreeEnergy n β x i = -routerMassieu n β x i := by
  exact
    beta_mul_routerFreeEnergy_eq_neg_routerMassieu
      (n := n) (β := β) (x := x) (i := i) hβ

end ThermoInvariant

section EngineInvariants

variable {Tok V : Type*}
variable [Fintype Tok] [DecidableEq Tok]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : Nat} [Nonempty (Fin n)]

section OmitEngineRouterVars

omit [Fintype Tok] [DecidableEq Tok] [Nonempty (Fin n)]

/--
Per-layer scale/shape split in the all-top engine:
the token update decomposes into base transport plus normalized routed mixture.
-/
@[rep_depth transport]
theorem scale_shape_split_preserved_per_layer
    (L : ReusedAllTopLayer V n)
    (β : ℝ) (x : Tok → V) (i : Tok) :
    L.runToken β x i = L.base.run (x i) + normalizedMixture L.routedMoE β x i := by
  exact
    ReusedAllTopLayer.runToken_eq_base_plus_normalizedMixture
      (L := L) (β := β) (x := x) (i := i)

/--
Stack-level defect quarantine in exact-reuse mode:
attaching zero routed branches preserves the base decoder stack pointwise.
-/
@[rep_depth transport]
theorem defect_quarantine_preserved_under_stack
    (layers : List (DecoderLayer V))
    (β : ℝ) (x : Tok → V) :
    runLayerStack (Tok := Tok) (V := V) (n := n)
      (layers.map (WeightReuse.withZeroMoE (V := V) (n := n))) β x
      =
    runDecoderStackPointwise (Tok := Tok) (V := V) layers x := by
  exact
    WeightReuse.runLayerStack_map_withZeroMoE_eq_pointwise
      (Tok := Tok) (V := V) (n := n) (layers := layers) (β := β) (x := x)

end OmitEngineRouterVars

section OmitEngineCapstoneVars

omit [Fintype Tok] [DecidableEq Tok]

/--
Capstone engine property:
the all-top transformer lane satisfies per-layer scale/shape split,
token-local thermodynamic free-energy identity, and stack-level defect quarantine.
-/
@[rep_depth transport, capstone]
theorem transformer_engine_realizes_information_physics
    (L : ReusedAllTopLayer V n)
    (layers : List (DecoderLayer V))
    (β : ℝ) (x : Tok → V) (i : Tok) (hβ : β ≠ 0) :
    (L.runToken β x i = L.base.run (x i) + normalizedMixture L.routedMoE β x i)
      ∧
    (β * routerFreeEnergy n β x i = -routerMassieu n β x i)
      ∧
    (runLayerStack (Tok := Tok) (V := V) (n := n)
      (layers.map (WeightReuse.withZeroMoE (V := V) (n := n))) β x
      =
    runDecoderStackPointwise (Tok := Tok) (V := V) layers x) := by
  refine ⟨?_, ?_, ?_⟩
  · exact scale_shape_split_preserved_per_layer (L := L) (β := β) (x := x) (i := i)
  · exact TransformerPhysicsEngine.router_free_energy_identity_per_step
      (n := n) (β := β) (x := x) (i := i) hβ
  · exact defect_quarantine_preserved_under_stack
      (Tok := Tok) (V := V) (n := n) (layers := layers) (β := β) (x := x)

end OmitEngineCapstoneVars

end EngineInvariants

end InfoGeometry.LLM.TransformerPhysicsEngine

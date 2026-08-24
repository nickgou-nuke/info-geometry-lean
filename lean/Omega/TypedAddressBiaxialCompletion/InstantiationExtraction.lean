import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

universe u

/-- Minimal observer-spacetime interface used by the typed-address instantiation wrapper. -/
structure ObserverSpacetimeInterface (State : Type u) where
  timeProjection : State → ℝ

/-- Minimal resource interface providing the scalarized resource quasidistance. -/
structure ResourceQuasidistanceInterface (State : Type u) where
  resourceQuasidistance : State → State → ℝ

/-- Chapter-local admissible instantiation package for the rough spacetime extraction wrapper. -/
structure AdmissiblePhysicalInstantiation where
  State : Type u
  observerSpacetime : ObserverSpacetimeInterface State
  causalPreorder : State → State → Prop
  resourceQuasidistance : ResourceQuasidistanceInterface State
  obstruction : State → State → Prop

/-- The extracted rough spacetime quadruple `(≼, τ, d_res, Ω)`. -/
structure RoughSpacetimeQuadruple (State : Type u) where
  causalPreorder : State → State → Prop
  timeProjection : State → ℝ
  resourceQuasidistance : State → State → ℝ
  obstruction : State → State → Prop

/-- The canonical rough spacetime quadruple extracted from an admissible physical instantiation. -/
def extractRoughSpacetimeQuadruple (I : AdmissiblePhysicalInstantiation) :
    RoughSpacetimeQuadruple I.State where
  causalPreorder := I.causalPreorder
  timeProjection := I.observerSpacetime.timeProjection
  resourceQuasidistance := I.resourceQuasidistance.resourceQuasidistance
  obstruction := I.obstruction

/-- Paper-facing wrapper: every admissible typed-address physical instantiation canonically
induces the rough spacetime quadruple whose four components are read off from the
observer-spacetime, causal-compatibility, resource-quasidistance, and obstruction interfaces.
    prop:typed-address-biaxial-completion-instantiation-extraction -/
theorem paper_typed_address_biaxial_completion_instantiation_extraction
    (I : AdmissiblePhysicalInstantiation) :
    ∃ G : RoughSpacetimeQuadruple I.State,
      G.causalPreorder = I.causalPreorder ∧
      G.timeProjection = I.observerSpacetime.timeProjection ∧
      G.resourceQuasidistance = I.resourceQuasidistance.resourceQuasidistance ∧
      G.obstruction = I.obstruction := by
  refine ⟨extractRoughSpacetimeQuadruple I, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl⟩

end Omega.TypedAddressBiaxialCompletion

import InfoGeometry.Topology.D4StarQuotientFactorization
import InfoGeometry.Topology.ContinuousModularFlowQuotientDescent

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical
open InfoGeometry.Topology.ContinuousQuotientDescent

/-! Concrete observational quotient instance for the D₄ star. -/

def starQuotientFlow : ContinuousFlow D4StarQuotient where
  flow := fun _ q => q
  zero_law := by intro q; rfl
  add_law := by intro s t q; rfl
  continuous := by intro t; exact continuous_id

def starObservationalQuotient :
    QuotientData D4StarQuotient Bool starQuotientFlow where
  proj := quotientToBool
  isQuotient := d4StarQuotientHomeomorphBool.isQuotientMap
  invariant := by
    intro t x y h
    exact h

theorem starObservationalQuotient_descended_eq_id
    (t : ℤ) (b : Bool) :
    descended starObservationalQuotient t b = b := by
  obtain ⟨q, rfl⟩ := d4StarQuotientHomeomorphBool.surjective b
  simpa [starObservationalQuotient, starQuotientFlow] using
    (descended_commutes starObservationalQuotient t q)

theorem starObservationalQuotient_descended_continuous
    (t : ℤ) :
    Continuous (descended starObservationalQuotient t) := by
  exact continuous_descended starObservationalQuotient t

noncomputable def starObservationalQuotient_descended_homeomorph
    (t : ℤ) : Bool ≃ₜ Bool :=
  descended_homeomorph starObservationalQuotient t

end InfoGeometry.Topology.PauliJungD4Star

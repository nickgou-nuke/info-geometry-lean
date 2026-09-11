import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotientFunctoriality

/-!
# Topological readout of symbolic-latent path homotopy quotients

This file exposes the native quotient map and endpoint map as continuous
functions.  It does not add any new quotient relation or homotopy claim.
-/

namespace InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotientTopological

variable {X : Type} [TopologicalSpace X]

/-- The quotient projection from paths to homotopy classes as a continuous map. -/
theorem continuous_symbolicLatentPathHomotopyQuotientMap :
    Continuous (symbolicLatentPathHomotopyQuotientMap (X := X)) := by
  exact @continuous_quotient_mk' (SymbolicLatentPath X) _
    (symbolicLatentPathHomotopySetoid (X := X))

/-- The endpoint readout of the homotopy quotient as a continuous map. -/
theorem continuous_symbolicLatentPathHomotopyEndpointMap :
    Continuous (symbolicLatentPathHomotopyEndpointMap (X := X)) := by
  exact Continuous.quotient_lift
    ((continuous_eval_const (0 : SymbolicPathDomain) :
      Continuous (fun γ : SymbolicLatentPath X => γ 0)).prodMk
      (continuous_eval_const (1 : SymbolicPathDomain) :
        Continuous (fun γ : SymbolicLatentPath X => γ 1))) (by
    intro γ₀ γ₁ h
    exact h.same_endpoints)

/-- The homotopy quotient projection as a topological map. -/
def symbolicLatentPathHomotopyQuotientContinuousMap :
    SymbolicLatentPath X → SymbolicLatentPathHomotopyQuotient (X := X) :=
  symbolicLatentPathHomotopyQuotientMap (X := X)

@[simp] theorem symbolicLatentPathHomotopyQuotientContinuousMap_apply
    (γ : SymbolicLatentPath X) :
    symbolicLatentPathHomotopyQuotientContinuousMap (X := X) γ =
      symbolicLatentPathHomotopyQuotientMap (X := X) γ :=
  rfl

/-- The endpoint readout of the quotient as a topological map. -/
def symbolicLatentPathHomotopyEndpointContinuousMap :
    SymbolicLatentPathHomotopyQuotient (X := X) → X × X :=
  symbolicLatentPathHomotopyEndpointMap (X := X)

@[simp] theorem symbolicLatentPathHomotopyEndpointContinuousMap_apply
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    symbolicLatentPathHomotopyEndpointContinuousMap (X := X) q =
      symbolicLatentPathHomotopyEndpointMap (X := X) q :=
  rfl

theorem continuous_symbolicLatentPathHomotopyQuotientContinuousMap :
    Continuous (symbolicLatentPathHomotopyQuotientContinuousMap (X := X)) := by
  simpa [symbolicLatentPathHomotopyQuotientContinuousMap] using
    continuous_symbolicLatentPathHomotopyQuotientMap (X := X)

theorem continuous_symbolicLatentPathHomotopyEndpointContinuousMap :
    Continuous (symbolicLatentPathHomotopyEndpointContinuousMap (X := X)) := by
  simpa [symbolicLatentPathHomotopyEndpointContinuousMap] using
    continuous_symbolicLatentPathHomotopyEndpointMap (X := X)

theorem symbolicLatentPathHomotopyEndpointContinuousMap_mk
    (γ : SymbolicLatentPath X) :
    symbolicLatentPathHomotopyEndpointContinuousMap (X := X)
        (symbolicLatentPathHomotopyQuotientMap (X := X) γ) =
      γ.endpoints := by
  rfl

end InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotientTopological

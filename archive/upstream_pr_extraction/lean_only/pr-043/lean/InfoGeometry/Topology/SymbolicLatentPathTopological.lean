import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathEndpoints

/-!
# Topological readout of symbolic-latent paths

This file exposes the native path evaluation and endpoint maps as ordinary
continuous maps.  It does not add any new path structure or quotient claim.
-/

namespace InfoGeometry.Topology.SymbolicLatentPathTopological

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- Evaluation of a symbolic-latent path at a fixed parameter. -/
def symbolicLatentPathParameterEvaluation
    (t : SymbolicPathDomain) : SymbolicLatentPath X → X :=
  fun γ => γ t

@[simp] theorem symbolicLatentPathParameterEvaluation_apply
    (t : SymbolicPathDomain) (γ : SymbolicLatentPath X) :
    symbolicLatentPathParameterEvaluation (X := X) t γ = γ t :=
  rfl

theorem continuous_symbolicLatentPathParameterEvaluation
    (t : SymbolicPathDomain) :
    Continuous (symbolicLatentPathParameterEvaluation (X := X) t) := by
  simpa [symbolicLatentPathParameterEvaluation] using
    (ContinuousEvalConst.continuous_eval_const (X := X) t)

/-- The start evaluation of a symbolic-latent path as a continuous map. -/
def symbolicLatentPathStartEvaluation : SymbolicLatentPath X → X :=
  symbolicLatentPathParameterEvaluation (X := X) (0 : SymbolicPathDomain)

@[simp] theorem symbolicLatentPathStartEvaluation_apply
    (γ : SymbolicLatentPath X) :
    symbolicLatentPathStartEvaluation (X := X) γ = γ.start :=
  rfl

theorem continuous_symbolicLatentPathStartEvaluation :
    Continuous (symbolicLatentPathStartEvaluation (X := X)) := by
  simpa [symbolicLatentPathStartEvaluation] using
    continuous_symbolicLatentPathParameterEvaluation (X := X) (0 : SymbolicPathDomain)

/-- The finish evaluation of a symbolic-latent path as a continuous map. -/
def symbolicLatentPathFinishEvaluation : SymbolicLatentPath X → X :=
  symbolicLatentPathParameterEvaluation (X := X) (1 : SymbolicPathDomain)

@[simp] theorem symbolicLatentPathFinishEvaluation_apply
    (γ : SymbolicLatentPath X) :
    symbolicLatentPathFinishEvaluation (X := X) γ = γ.finish :=
  rfl

theorem continuous_symbolicLatentPathFinishEvaluation :
    Continuous (symbolicLatentPathFinishEvaluation (X := X)) := by
  simpa [symbolicLatentPathFinishEvaluation] using
    continuous_symbolicLatentPathParameterEvaluation (X := X) (1 : SymbolicPathDomain)

/-- The endpoint evaluation of a symbolic-latent path as a continuous map. -/
def symbolicLatentPathEndpointsEvaluation : SymbolicLatentPath X → X × X :=
  fun γ => (γ.start, γ.finish)

@[simp] theorem symbolicLatentPathEndpointsEvaluation_apply
    (γ : SymbolicLatentPath X) :
    symbolicLatentPathEndpointsEvaluation (X := X) γ = γ.endpoints :=
  rfl

theorem continuous_symbolicLatentPathEndpointsEvaluation :
    Continuous (symbolicLatentPathEndpointsEvaluation (X := X)) := by
  change Continuous (fun γ : SymbolicLatentPath X =>
    (symbolicLatentPathStartEvaluation γ,
      symbolicLatentPathFinishEvaluation γ))
  exact Continuous.prodMk
    (continuous_symbolicLatentPathStartEvaluation (X := X))
    (continuous_symbolicLatentPathFinishEvaluation (X := X))

theorem symbolicLatentPathEndpointsEvaluation_fst
    (γ : SymbolicLatentPath X) :
    (symbolicLatentPathEndpointsEvaluation (X := X) γ).1 = γ.start :=
  rfl

theorem symbolicLatentPathEndpointsEvaluation_snd
    (γ : SymbolicLatentPath X) :
    (symbolicLatentPathEndpointsEvaluation (X := X) γ).2 = γ.finish :=
  rfl

end

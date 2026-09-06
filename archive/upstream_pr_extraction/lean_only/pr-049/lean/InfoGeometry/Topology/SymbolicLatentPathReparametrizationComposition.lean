import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathReparametrizationQuotient

namespace InfoGeometry.Topology

/-!
# Composition of endpoint-fixing path reparametrizations

The order is chosen so that `compose R S` is the parameter map induced by
first reparametrizing by `S` and then by `R`.
-/

def composeSymbolicLatentPathReparametrization
    (R S : SymbolicLatentPathReparametrization) :
    SymbolicLatentPathReparametrization :=
  ⟨S.parameter.comp R.parameter, by
    constructor
    · change S.parameter (R.parameter 0) = 0
      rw [R.at_zero, S.at_zero]
    · change S.parameter (R.parameter 1) = 1
      rw [R.at_one, S.at_one]⟩

theorem reparametrizeSymbolicLatentPath_comp
    {X : Type*} [TopologicalSpace X]
    (R S : SymbolicLatentPathReparametrization)
    (γ : SymbolicLatentPath X) :
    reparametrizeSymbolicLatentPath R
        (reparametrizeSymbolicLatentPath S γ) =
      reparametrizeSymbolicLatentPath
        (composeSymbolicLatentPathReparametrization R S) γ := by
  ext t
  rfl

theorem reparametrizeSymbolicLatentPathHomotopyQuotient_comp
    {X : Type*} [TopologicalSpace X]
    (R S : SymbolicLatentPathReparametrization)
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    reparametrizeSymbolicLatentPathHomotopyQuotient R
        (reparametrizeSymbolicLatentPathHomotopyQuotient S q) =
      reparametrizeSymbolicLatentPathHomotopyQuotient
        (composeSymbolicLatentPathReparametrization R S) q := by
  refine Quotient.inductionOn q ?_
  intro γ
  change reparametrizeSymbolicLatentPathHomotopyQuotient R
      (symbolicLatentPathHomotopyQuotientMap
        (reparametrizeSymbolicLatentPath S γ)) =
    reparametrizeSymbolicLatentPathHomotopyQuotient
      (composeSymbolicLatentPathReparametrization R S)
      (symbolicLatentPathHomotopyQuotientMap γ)
  rw [reparametrizeSymbolicLatentPathHomotopyQuotient_mk,
    reparametrizeSymbolicLatentPathHomotopyQuotient_mk]
  exact congrArg symbolicLatentPathHomotopyQuotientMap
    (reparametrizeSymbolicLatentPath_comp R S γ)

end InfoGeometry.Topology

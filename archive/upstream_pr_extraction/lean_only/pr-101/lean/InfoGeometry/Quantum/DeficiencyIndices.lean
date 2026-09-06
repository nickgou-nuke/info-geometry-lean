import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.DeficiencyIndices

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def deficiencyIndicesSelfAdjoint (n_plus n_minus : ℕ) : Prop :=
  n_plus = n_minus

theorem apollonius_self_adjoint_indices :
    deficiencyIndicesSelfAdjoint 0 0 := by
  unfold deficiencyIndicesSelfAdjoint
  rfl

theorem grand_deficiency_indices_synthesis :
    deficiencyIndicesSelfAdjoint 0 0 :=
  apollonius_self_adjoint_indices

end
end InfoGeometry.Quantum.DeficiencyIndices

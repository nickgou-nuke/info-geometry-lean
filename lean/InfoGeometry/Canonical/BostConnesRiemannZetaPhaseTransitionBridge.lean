import Mathlib.NumberTheory.LSeries.RiemannZeta
import InfoGeometry.Arithmetic.BostConnesCriticality

namespace InfoGeometry.Canonical

noncomputable def bostConnesZetaPartitionFunction (β : ℂ) : ℂ :=
  riemannZeta β

theorem bostConnesZetaPartitionFunction_eq_zeta (β : ℂ) :
    bostConnesZetaPartitionFunction β = riemannZeta β := rfl

theorem bostConnesZetaPartitionFunction_residue_one :
    Filter.Tendsto
      (fun s => (s - 1) * bostConnesZetaPartitionFunction s)
      (nhdsWithin 1 {1}ᶜ) (nhds 1) := by
  simpa [bostConnesZetaPartitionFunction] using riemannZeta_residue_one

theorem bostConnes_critical_diagonal_not_summable :
    ¬ Summable (InfoGeometry.Arithmetic.BostConnesCriticality.bc_eigenvalues 1) :=
  InfoGeometry.Arithmetic.BostConnesCriticality.operator_not_trace_class_at_critical

theorem bostConnes_zeta_critical_readout :
    bostConnesZetaPartitionFunction (1 : ℂ) = riemannZeta 1 ∧
      ¬ Summable
        (InfoGeometry.Arithmetic.BostConnesCriticality.bc_eigenvalues 1) := by
  exact ⟨bostConnesZetaPartitionFunction_eq_zeta 1,
    bostConnes_critical_diagonal_not_summable⟩

end InfoGeometry.Canonical

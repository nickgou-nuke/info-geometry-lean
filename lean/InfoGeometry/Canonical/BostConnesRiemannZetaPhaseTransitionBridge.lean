import Mathlib.NumberTheory.LSeries.RiemannZeta
import InfoGeometry.Arithmetic.BostConnesCriticality

/-!
# Bost--Connes zeta readout and the critical obstruction

This owner records the theorem-safe part of the usual partition-function
dictionary.  The zeta readout is definitional, while the critical statement
is expressed as failure of summability of the diagonal eigenvalue model at
`β = 1`.  No pointwise value `ζ 1` is used as a proxy for a pole.
-/

namespace InfoGeometry.Canonical

noncomputable def bostConnesZetaPartitionFunction (β : ℂ) : ℂ :=
  riemannZeta β

theorem bostConnesZetaPartitionFunction_eq_zeta (β : ℂ) :
    bostConnesZetaPartitionFunction β = riemannZeta β := rfl

def hagedornInverseTemperature : ℝ := 1

theorem hagedornInverseTemperature_eq_one :
    hagedornInverseTemperature = 1 := rfl

theorem bostConnes_critical_diagonal_not_summable :
    ¬ Summable (InfoGeometry.Arithmetic.BostConnesCriticality.bc_eigenvalues 1) :=
  InfoGeometry.Arithmetic.BostConnesCriticality.operator_not_trace_class_at_critical

theorem bostConnes_zeta_critical_readout :
    bostConnesZetaPartitionFunction (1 : ℂ) = riemannZeta 1 ∧
      hagedornInverseTemperature = 1 ∧
      ¬ Summable
        (InfoGeometry.Arithmetic.BostConnesCriticality.bc_eigenvalues 1) := by
  exact ⟨bostConnesZetaPartitionFunction_eq_zeta 1,
    hagedornInverseTemperature_eq_one,
    bostConnes_critical_diagonal_not_summable⟩

end InfoGeometry.Canonical

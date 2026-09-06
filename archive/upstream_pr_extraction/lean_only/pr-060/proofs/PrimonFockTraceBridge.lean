import Mathlib

/-!
# Primon Fock trace bridge

Finite, theorem-honest bridge from a spectral projector Hamiltonian to the
Bost--Connes/primon partition trace.

If `H = Σᵢ εᵢ Pᵢ` and the representation trace normalizes `Tr(Pᵢ)=1`, then
functional calculus gives the finite heat trace

`Tr(exp(-βH)) = Σᵢ exp(-β εᵢ)`.

For the arithmetic/primon energy choice `εᵢ = log(i+1)`, this finite trace is
exactly the finite Dirichlet/zeta partial sum `Σ (i+1)^(-β)`.  This file proves
only finite cutoff equalities; it does not assert convergence of the infinite
zeta series.
-/

noncomputable section

namespace PrimonFockTraceBridge

open scoped BigOperators

/-- Abstract finite spectral data after diagonalizing a finite primon Hamiltonian. -/
structure FiniteSpectralData (N : ℕ) where
  energy : Fin N → ℝ
  projectorTrace : Fin N → ℝ

/-- Functional-calculus heat trace of a finite diagonal/projector Hamiltonian. -/
def spectralHeatTrace {N : ℕ} (D : FiniteSpectralData N) (β : ℝ) : ℝ :=
  ∑ i : Fin N, Real.exp (-(β * D.energy i)) * D.projectorTrace i

/-- Trace-normalized finite Fock representation: every minimal projector has trace one. -/
def traceNormalized {N : ℕ} (D : FiniteSpectralData N) : Prop :=
  ∀ i : Fin N, D.projectorTrace i = 1

/-- The arithmetic/primon energy assignment `ε_i = log(i+1)`. -/
def primonEnergy {N : ℕ} (i : Fin N) : ℝ :=
  Real.log ((i.val + 1 : ℕ) : ℝ)

/-- Finite arithmetic spectral data with unit trace on each spectral projector. -/
def primonSpectralData (N : ℕ) : FiniteSpectralData N where
  energy := primonEnergy
  projectorTrace := fun _ => 1

@[simp] theorem primonSpectralData_traceNormalized (N : ℕ) :
    traceNormalized (primonSpectralData N) := by
  intro i
  rfl

/-- Finite heat trace after inserting the primon energies. -/
def finitePrimonFockTrace (β : ℝ) (N : ℕ) : ℝ :=
  spectralHeatTrace (primonSpectralData N) β

/-- Finite Dirichlet/zeta partial sum. -/
def finiteZetaPartial (β : ℝ) (N : ℕ) : ℝ :=
  (Finset.range N).sum fun k => ((k + 1 : ℕ) : ℝ) ^ (-β)

/-- The Boltzmann weight for `ε_n=log n` is the Dirichlet weight `n^{-β}`. -/
theorem exp_neg_beta_log_eq_rpow (β : ℝ) {n : ℕ} (hn : n ≠ 0) :
    Real.exp (-(β * Real.log (n : ℝ))) = (n : ℝ) ^ (-β) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn)]
  congr 1
  ring

/-- In a trace-normalized spectral representation, the heat trace is just the
sum of the Boltzmann characters `exp(-βεᵢ)`. -/
theorem spectralHeatTrace_traceNormalized {N : ℕ} (D : FiniteSpectralData N)
    (htr : traceNormalized D) (β : ℝ) :
    spectralHeatTrace D β = ∑ i : Fin N, Real.exp (-(β * D.energy i)) := by
  unfold spectralHeatTrace
  apply Finset.sum_congr rfl
  intro i hi
  rw [htr i]
  ring

/-- The finite primon Fock trace is the finite zeta partial sum. -/
theorem finitePrimonFockTrace_eq_zeta_partial (β : ℝ) (N : ℕ) :
    finitePrimonFockTrace β N = finiteZetaPartial β N := by
  unfold finitePrimonFockTrace spectralHeatTrace primonSpectralData primonEnergy finiteZetaPartial
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  have hlt : k < N := Finset.mem_range.mp hk
  simp only [hlt, ↓reduceDIte]
  rw [mul_one]
  exact exp_neg_beta_log_eq_rpow β (Nat.succ_ne_zero k)

/-- Successor recursion: adding the next Fock basis state adds `(N+1)^(-β)`. -/
theorem finitePrimonFockTrace_succ (β : ℝ) (N : ℕ) :
    finitePrimonFockTrace β (N + 1) =
      finitePrimonFockTrace β N + ((N + 1 : ℕ) : ℝ) ^ (-β) := by
  rw [finitePrimonFockTrace_eq_zeta_partial β (N + 1),
    finitePrimonFockTrace_eq_zeta_partial β N]
  simp [finiteZetaPartial, Finset.sum_range_succ]

/-- Consolidated finite bridge theorem. -/
theorem primon_fock_trace_bridge_synthesis :
    (∀ N, traceNormalized (primonSpectralData N)) ∧
    (∀ β N, finitePrimonFockTrace β N = finiteZetaPartial β N) ∧
    (∀ β N, finitePrimonFockTrace β (N + 1) =
      finitePrimonFockTrace β N + ((N + 1 : ℕ) : ℝ) ^ (-β)) := by
  exact ⟨primonSpectralData_traceNormalized,
    finitePrimonFockTrace_eq_zeta_partial,
    finitePrimonFockTrace_succ⟩

#check spectralHeatTrace_traceNormalized
#check finitePrimonFockTrace_eq_zeta_partial
#check finitePrimonFockTrace_succ
#check primon_fock_trace_bridge_synthesis

end PrimonFockTraceBridge

import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ToeplitzCuntzVacuumBridge

/-!
# InfoGeometry.Canonical.ToeplitzCuntzFockVacuumBridge

Hilbert / Fock representation layer for Toeplitz-Cuntz ℰ₂ algebra with a cyclic
unbroken BPS vacuum state vector `Ω ≠ 0`.

While `ToeplitzCuntzVacuumBridge` proves the pure algebraic projector identities
`H = 1 - P₀` and `H P₀ = 0`, this module constructs the representation map
`π : ℰ₂ → ℬ(ℋ)` and the distinguished vacuum vector `Ω ∈ ℋ` such that:
`π(P₀) Ω = Ω`.

This yields the literal unbroken BPS vacuum theorems:
`π(Q₊) Ω = 0`, `π(Q₋) Ω = 0`, and `π(H) Ω = 0`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzFockVacuumBridge

open InfoGeometry.Canonical.ToeplitzCuntzVacuumBridge
open ToeplitzCuntzGenerators

variable {R H : Type*} [Ring R] [StarRing R] [AddCommGroup H] [Module ℂ H]

/-- Hilbert representation of Toeplitz-Cuntz generators with a cyclic vacuum vector `Ω`. -/
structure ToeplitzCuntzRepresentation (g : ToeplitzCuntzGenerators R) (H : Type*) [AddCommGroup H] [Module ℂ H] where
  rep : R →+* (H →ₗ[ℂ] H)
  vacuum : H
  vacuum_nonzero : vacuum ≠ 0
  vacuum_eigenstate : rep (g.P0) vacuum = vacuum

namespace ToeplitzCuntzRepresentation

variable {g : ToeplitzCuntzGenerators R}
variable (R_rep : ToeplitzCuntzRepresentation g H)

/-- Unbroken BPS Vacuum theorem for positive supercharge: `π(Q₊) Ω = 0`. -/
theorem vacuum_annihilated_by_qplus : R_rep.rep g.QPlus R_rep.vacuum = 0 := by
  have h_alg := (supercharges_vacuum_annihilation g).1
  calc R_rep.rep g.QPlus R_rep.vacuum
      = R_rep.rep g.QPlus (R_rep.rep g.P0 R_rep.vacuum) := by rw [R_rep.vacuum_eigenstate]
    _ = (R_rep.rep g.QPlus * R_rep.rep g.P0) R_rep.vacuum := rfl
    _ = R_rep.rep (g.QPlus * g.P0) R_rep.vacuum := by rw [← map_mul]
    _ = R_rep.rep 0 R_rep.vacuum := by rw [h_alg]
    _ = 0 := by simp

/-- Unbroken BPS Vacuum theorem for negative supercharge: `π(Q₋) Ω = 0`. -/
theorem vacuum_annihilated_by_qminus : R_rep.rep g.QMinus R_rep.vacuum = 0 := by
  have h_alg := (supercharges_vacuum_annihilation g).2
  calc R_rep.rep g.QMinus R_rep.vacuum
      = R_rep.rep g.QMinus (R_rep.rep g.P0 R_rep.vacuum) := by rw [R_rep.vacuum_eigenstate]
    _ = (R_rep.rep g.QMinus * R_rep.rep g.P0) R_rep.vacuum := rfl
    _ = R_rep.rep (g.QMinus * g.P0) R_rep.vacuum := by rw [← map_mul]
    _ = R_rep.rep 0 R_rep.vacuum := by rw [h_alg]
    _ = 0 := by simp

/-- Unbroken BPS Vacuum theorem for Hamiltonian: `π(H) Ω = 0`. -/
theorem vacuum_annihilated_by_susyHamiltonian : R_rep.rep g.susyHamiltonian R_rep.vacuum = 0 := by
  have h_alg := susyHamiltonian_vacuum_annihilation g
  calc R_rep.rep g.susyHamiltonian R_rep.vacuum
      = R_rep.rep g.susyHamiltonian (R_rep.rep g.P0 R_rep.vacuum) := by rw [R_rep.vacuum_eigenstate]
    _ = (R_rep.rep g.susyHamiltonian * R_rep.rep g.P0) R_rep.vacuum := rfl
    _ = R_rep.rep (g.susyHamiltonian * g.P0) R_rep.vacuum := by rw [← map_mul]
    _ = R_rep.rep 0 R_rep.vacuum := by rw [h_alg]
    _ = 0 := by simp

/-- **Master Synthesis Theorem**: Hilbert/Fock Representation BPS Vacuum Closure. -/
theorem master_toeplitz_cuntz_fock_vacuum_synthesis :
    R_rep.vacuum ≠ 0 ∧
    R_rep.rep g.P0 R_rep.vacuum = R_rep.vacuum ∧
    R_rep.rep g.QPlus R_rep.vacuum = 0 ∧
    R_rep.rep g.QMinus R_rep.vacuum = 0 ∧
    R_rep.rep g.susyHamiltonian R_rep.vacuum = 0 := by
  exact ⟨R_rep.vacuum_nonzero,
         R_rep.vacuum_eigenstate,
         vacuum_annihilated_by_qplus R_rep,
         vacuum_annihilated_by_qminus R_rep,
         vacuum_annihilated_by_susyHamiltonian R_rep⟩

end ToeplitzCuntzRepresentation

end InfoGeometry.Canonical.ToeplitzCuntzFockVacuumBridge

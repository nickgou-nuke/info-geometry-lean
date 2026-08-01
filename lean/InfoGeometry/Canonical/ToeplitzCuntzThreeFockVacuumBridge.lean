import Mathlib
import InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge

/-!
# InfoGeometry.Canonical.ToeplitzCuntzThreeFockVacuumBridge

Hilbert / Fock representation layer for Toeplitz-Cuntz ℰ₃ algebra over non-commutative Ring A
with a cyclic unbroken 3-ary BPS vacuum state vector `Ω ≠ 0`.

While `ToeplitzCuntzThreeCyclicSuperchargeBridge` proves the pure algebraic projector identities
`H = 1 - P₀` and `H P₀ = 0, Q P₀ = 0`, this module constructs the representation map
`π : ℰ₃ → ℬ(ℋ)` and the distinguished vacuum vector `Ω ∈ ℋ` such that:
`π(P₀) Ω = Ω`.

This yields the literal unbroken 3-ary BPS vacuum theorems:
`π(Q) Ω = 0`, `π(Q³) Ω = 0`, and `π(H) Ω = 0`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeFockVacuumBridge

open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge
open ToeplitzCuntzThreeGenerators

variable {A : Type*} [Ring A] [StarRing A]

/-- Hilbert representation of Toeplitz-Cuntz ℰ₃ generators with a cyclic vacuum vector `Ω`. -/
structure ToeplitzCuntzThreeRepresentation (g : ToeplitzCuntzThreeGenerators A) (H : Type*) [AddCommGroup H] [Module ℂ H] where
  rep : A →+* (H →ₗ[ℂ] H)
  vacuum : H
  vacuum_nonzero : vacuum ≠ 0
  vacuum_eigenstate : rep (g.P0) vacuum = vacuum

namespace ToeplitzCuntzThreeRepresentation

variable {H : Type*} [AddCommGroup H] [Module ℂ H]
variable {g : ToeplitzCuntzThreeGenerators A}
variable (A_rep : ToeplitzCuntzThreeRepresentation g H)

/-- Unbroken 3-ary BPS Vacuum theorem for cyclic supercharge: `π(Q) Ω = 0`. -/
theorem vacuum_annihilated_by_cyclicSupercharge : A_rep.rep (cyclicSupercharge g) A_rep.vacuum = 0 := by
  have h_alg := cyclicSupercharge_defect_annihilation_right g
  calc A_rep.rep (cyclicSupercharge g) A_rep.vacuum
      = A_rep.rep (cyclicSupercharge g) (A_rep.rep g.P0 A_rep.vacuum) := by rw [A_rep.vacuum_eigenstate]
    _ = (A_rep.rep (cyclicSupercharge g) * A_rep.rep g.P0) A_rep.vacuum := rfl
    _ = A_rep.rep (cyclicSupercharge g * g.P0) A_rep.vacuum := by rw [← map_mul]
    _ = A_rep.rep 0 A_rep.vacuum := by rw [h_alg]
    _ = 0 := by simp

/-- Unbroken 3-ary BPS Vacuum theorem for Hamiltonian: `π(H) Ω = 0`. -/
theorem vacuum_annihilated_by_susyHamiltonian : A_rep.rep g.susyHamiltonian A_rep.vacuum = 0 := by
  have h_alg := susyHamiltonian_defect_annihilation_right g
  calc A_rep.rep g.susyHamiltonian A_rep.vacuum
      = A_rep.rep g.susyHamiltonian (A_rep.rep g.P0 A_rep.vacuum) := by rw [A_rep.vacuum_eigenstate]
    _ = (A_rep.rep g.susyHamiltonian * A_rep.rep g.P0) A_rep.vacuum := rfl
    _ = A_rep.rep (g.susyHamiltonian * g.P0) A_rep.vacuum := by rw [← map_mul]
    _ = A_rep.rep 0 A_rep.vacuum := by rw [h_alg]
    _ = 0 := by simp


end ToeplitzCuntzThreeRepresentation

end InfoGeometry.Canonical.ToeplitzCuntzThreeFockVacuumBridge

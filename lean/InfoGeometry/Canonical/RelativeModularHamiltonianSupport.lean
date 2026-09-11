import InfoGeometry.Canonical.RelativeModularHamiltonian
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RelativeModularCommutingLift
import InfoGeometry.Canonical.RelativeModularSingularization
import InfoGeometry.Meta.Architecture

open scoped BigOperators

/-!
# Relative Modular Hamiltonian Support

Support-restricted finite owner lane for `K := -log Δ`.

This file does **not** claim unbounded functional calculus. It packages the
finite support/domain surrogate:

- choose a support projector `P_s`,
- keep diagonal Hamiltonian entries on `s`,
- force zero off-support.

This gives a strict bridge between the fully positive finite lane and the
future unbounded/support-aware modular Hamiltonian interface.
-/

namespace InfoGeometry.Canonical.RelativeModularHamiltonianSupport

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.RelativeModularHamiltonian
open InfoGeometry.Canonical.RelativeModularCommutingLift
open InfoGeometry.Canonical.RelativeModularSingularization
open InfoGeometry.MaxEnt.JaynesInfoStatMech.ThermalDiagonal

section Finite

variable {n : ℕ} [Nonempty (Fin n)]

/--
Support-restricted finite relative modular Hamiltonian:
keep the diagonal `K` entries on `s`, set zero off-support.
-/
@[rep_depth operator]
noncomputable def supportRestrictedModularHamiltonianOperator
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) : FinMat n :=
  diagMatrix (fun i =>
    if i ∈ s then relativeModularHamiltonianOperator (n := n) q q0 i i else 0)

@[simp] theorem supportRestrictedModularHamiltonianOperator_diag
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) (i : Fin n) :
    supportRestrictedModularHamiltonianOperator (n := n) s q q0 i i
      = if i ∈ s then relativeModularHamiltonianOperator (n := n) q q0 i i else 0 := by
  simp [supportRestrictedModularHamiltonianOperator, diagMatrix]

@[simp] theorem supportRestrictedModularHamiltonianOperator_offdiag
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) {i j : Fin n} (hij : i ≠ j) :
    supportRestrictedModularHamiltonianOperator (n := n) s q q0 i j = 0 := by
  simp [supportRestrictedModularHamiltonianOperator, diagMatrix, hij]

@[rep_depth operator]
theorem supportRestrictedModularHamiltonianOperator_eq_supportProjector_mul
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    supportRestrictedModularHamiltonianOperator (n := n) s q q0
      = supportProjector (n := n) s * relativeModularHamiltonianOperator (n := n) q q0 := by
  rw [relativeModularHamiltonianOperator_eq_diag_relativeModularPotential (n := n) q q0]
  unfold supportRestrictedModularHamiltonianOperator supportProjector diagMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr
  funext i
  by_cases hi : i ∈ s <;>
    simp only [hi, if_true, if_false, one_mul, zero_mul,
      relativeModularHamiltonianOperator_diag]

@[rep_depth operator]
theorem supportRestrictedModularHamiltonianOperator_eq_mul_supportProjector
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    supportRestrictedModularHamiltonianOperator (n := n) s q q0
      = relativeModularHamiltonianOperator (n := n) q q0 * supportProjector (n := n) s := by
  rw [relativeModularHamiltonianOperator_eq_diag_relativeModularPotential (n := n) q q0]
  unfold supportRestrictedModularHamiltonianOperator supportProjector diagMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr
  funext i
  by_cases hi : i ∈ s <;>
    simp only [hi, if_true, if_false, mul_one, mul_zero,
      relativeModularHamiltonianOperator_diag]

@[rep_depth operator]
theorem supportProjector_mul_supportRestrictedModularHamiltonianOperator
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    supportProjector (n := n) s * supportRestrictedModularHamiltonianOperator (n := n) s q q0
      = supportRestrictedModularHamiltonianOperator (n := n) s q q0 := by
  unfold supportProjector supportRestrictedModularHamiltonianOperator diagMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr
  funext i
  by_cases hi : i ∈ s <;> simp [hi]

@[rep_depth operator]
theorem supportRestrictedModularHamiltonianOperator_mul_supportProjector
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    supportRestrictedModularHamiltonianOperator (n := n) s q q0 * supportProjector (n := n) s
      = supportRestrictedModularHamiltonianOperator (n := n) s q q0 := by
  unfold supportProjector supportRestrictedModularHamiltonianOperator diagMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr
  funext i
  by_cases hi : i ∈ s <;> simp [hi]

/-- On full support we recover the finite owner `K(q,q₀)`. -/
@[simp, rep_depth operator]
theorem supportRestrictedModularHamiltonianOperator_univ
    (q q0 : PositiveRay (Fin n)) :
    supportRestrictedModularHamiltonianOperator (n := n) (Finset.univ) q q0
      = relativeModularHamiltonianOperator (n := n) q q0 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [supportRestrictedModularHamiltonianOperator_diag]
  · rw [supportRestrictedModularHamiltonianOperator_offdiag (hij := hij)]
    symm
    exact relativeModularHamiltonianOperator_offdiag (n := n) q q0 (hij := hij)

/-- On empty support the support-restricted Hamiltonian is zero. -/
@[simp, rep_depth operator]
theorem supportRestrictedModularHamiltonianOperator_empty
    (q q0 : PositiveRay (Fin n)) :
    supportRestrictedModularHamiltonianOperator (n := n) (∅) q q0 = 0 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [supportRestrictedModularHamiltonianOperator_diag]
  · rw [supportRestrictedModularHamiltonianOperator_offdiag (hij := hij)]
    simp

/--
Support-restricted additive cocycle on the finite commuting lane.
-/
@[rep_depth operator]
theorem supportRestrictedModularHamiltonianOperator_cocycle
    (s : Finset (Fin n)) (q q0 q1 : PositiveRay (Fin n)) :
    supportRestrictedModularHamiltonianOperator (n := n) s q q1
      = supportRestrictedModularHamiltonianOperator (n := n) s q q0
          + supportRestrictedModularHamiltonianOperator (n := n) s q0 q1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ s
    · simp [supportRestrictedModularHamiltonianOperator_diag, hi, Matrix.add_apply]
      simpa using
        (relativeModularHamiltonianOperator_diag_cocycle (n := n) q q0 q1 i)
    · simp [supportRestrictedModularHamiltonianOperator_diag, hi, Matrix.add_apply]
  · rw [supportRestrictedModularHamiltonianOperator_offdiag (hij := hij)]
    rw [Matrix.add_apply]
    rw [supportRestrictedModularHamiltonianOperator_offdiag (hij := hij)]
    rw [supportRestrictedModularHamiltonianOperator_offdiag (hij := hij)]
    ring

/--
Capstone package for the support-restricted finite Hamiltonian lane:
left/right support compression plus additive cocycle.
-/
@[rep_depth operator, capstone]
theorem supportRestricted_finite_hamiltonian_lane_package
    (s : Finset (Fin n)) (q q0 q1 : PositiveRay (Fin n)) :
    (supportRestrictedModularHamiltonianOperator (n := n) s q q0
      = supportProjector (n := n) s * relativeModularHamiltonianOperator (n := n) q q0)
      ∧ (supportRestrictedModularHamiltonianOperator (n := n) s q q0
          = relativeModularHamiltonianOperator (n := n) q q0 * supportProjector (n := n) s)
      ∧ (supportRestrictedModularHamiltonianOperator (n := n) s q q1
          = supportRestrictedModularHamiltonianOperator (n := n) s q q0
              + supportRestrictedModularHamiltonianOperator (n := n) s q0 q1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact supportRestrictedModularHamiltonianOperator_eq_supportProjector_mul
      (n := n) s q q0
  · exact supportRestrictedModularHamiltonianOperator_eq_mul_supportProjector
      (n := n) s q q0
  · exact supportRestrictedModularHamiltonianOperator_cocycle (n := n) s q q0 q1

end Finite

end InfoGeometry.Canonical.RelativeModularHamiltonianSupport

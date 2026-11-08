import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

open Complex

namespace NambuGorkovParticleHoleBridge

/-- Pauli X matrix in Nambu space (Particle-Hole exchange). -/
def tauX : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i ≠ j then 1 else 0

/-- Matrix complex conjugation. -/
def matrixConj (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => star (M i j)

/-- Particle-Hole Conjugation operation: C M C⁻¹ = τ_x M* τ_x. -/
def particleHoleConj (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  tauX * matrixConj M * tauX

/-- 1D Kitaev Chain BdG Hamiltonian in momentum space.
    ξ_k : Real kinetic/chemical potential energy (even in k: ξ_{-k} = ξ_k).
    Δ_k : Complex p-wave pairing potential (odd in k: Δ_{-k} = -Δ_k). -/
def kitaevH (ξ_k : ℝ) (Δ_k : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(ξ_k : ℂ), Δ_k; star Δ_k, -(ξ_k : ℂ)]

/-- Helper lemma to explicitly evaluate the particle-hole conjugation. -/
lemma particleHoleConj_apply (M : Matrix (Fin 2) (Fin 2) ℂ) :
    particleHoleConj M = !![star (M 1 1), star (M 1 0); star (M 0 1), star (M 0 0)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [particleHoleConj, tauX, matrixConj, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Theorem**: Class D Particle-Hole Symmetry in Momentum Space.
    Machine-certifies that for the p-wave BdG Hamiltonian,
    the Particle-Hole operator C = τ_x K transforms H(k) to -H(-k).
    Since ξ(-k) = ξ(k) and Δ(-k) = -Δ(k), H(-k) = kitaevH ξ_k (-Δ_k). -/
theorem bdg_class_D_particle_hole_symmetry (ξ_k : ℝ) (Δ_k : ℂ) :
    particleHoleConj (kitaevH ξ_k Δ_k) = - kitaevH ξ_k (-Δ_k) := by
  rw [particleHoleConj_apply]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [kitaevH]
  · simp [kitaevH]
  · simp [kitaevH]
  · simp [kitaevH]

/-- **Theorem**: Particle-Hole Operator squares to +1 (Class D signature).
    Machine-certifies that applying particleHoleConj twice is the identity,
    meaning C² = +1 (defining Altland-Zirnbauer Class D). -/
theorem particle_hole_operator_sq_eq_one (M : Matrix (Fin 2) (Fin 2) ℂ) :
    particleHoleConj (particleHoleConj M) = M := by
  rw [particleHoleConj_apply, particleHoleConj_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end NambuGorkovParticleHoleBridge

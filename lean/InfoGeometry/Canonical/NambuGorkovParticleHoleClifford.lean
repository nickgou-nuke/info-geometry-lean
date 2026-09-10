import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Matrix

noncomputable section

namespace InfoGeometry.Canonical.NambuGorkovParticleHoleClifford

/-!
# Nambu-Gor'kov BdG Particle-Hole Charge Conjugation & Class BDI Symmetry

This module formalizes the Nambu-Gor'kov particle-hole charge conjugation operator
$\mathcal{C} = \tau_x K$ for the Bogoliubov-de Gennes (BdG) Hamiltonian, proving:
1. Class BDI Particle-Hole Involutivity: $\mathcal{C}^2 = \tau_x^2 = I_2$
2. Particle-Hole Anti-Commutation: $\tau_x \tau_z \tau_x = - \tau_z$
3. Self-Adjointness of diagonal mass: $\tau_z^* = \tau_z$
4. BdG Particle-Hole Anti-Symmetry Constraint:
   $$\tau_x (h \tau_z)^* \tau_x = - (h \tau_z)^*$$
-/

abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Nambu-Gor'kov particle-hole operator Pauli τ_x matrix: [0 1; 1 0]. -/
def tauX : Mat2C := !![0, 1; 1, 0]

/-- Pauli τ_z matrix: [1 0; 0 -1]. -/
def tauZ : Mat2C := !![1, 0; 0, -1]

/-- **Theorem**: Particle-Hole Operator Involutivity C² = (τ_x)² = I₂.
    Class BDI topology requires C² = +1. -/
theorem particle_hole_square_eq_one : tauX * tauX = 1 := by
  dsimp [tauX]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

/-- **Theorem**: Particle-Hole Anti-Commutation with τ_z: τ_x τ_z τ_x = - τ_z. -/
theorem particle_hole_tau_z_anticomm : tauX * tauZ * tauX = - tauZ := by
  dsimp [tauX, tauZ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

/-- **Theorem**: Self-adjointness of τ_z: τ_z* = τ_z. -/
theorem tauZ_self_adjoint : tauZ.conjTranspose = tauZ := by
  dsimp [tauZ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTranspose_apply]

/-- **Theorem**: BdG Particle-Hole Anti-Symmetry Constraint for h τ_z.
    τ_x (h • τ_z)* τ_x = - (h • τ_z)*. -/
theorem nambu_bdg_particle_hole_symmetry (h : ℂ) :
    tauX * (h • tauZ).conjTranspose * tauX = - (h • tauZ).conjTranspose := by
  rw [conjTranspose_smul, tauZ_self_adjoint]
  calc tauX * (star h • tauZ) * tauX
    _ = star h • (tauX * tauZ * tauX) := by simp only [Matrix.smul_mul, Matrix.mul_smul]
    _ = star h • (- tauZ) := by rw [particle_hole_tau_z_anticomm]
    _ = - (star h • tauZ) := by simp only [smul_neg]

end InfoGeometry.Canonical.NambuGorkovParticleHoleClifford

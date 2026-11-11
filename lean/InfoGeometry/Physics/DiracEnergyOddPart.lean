/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.EnergySignInvolution
import InfoGeometry.Physics.DiracRestChiralTwoSectorBridge

/-!
# The energy-odd part of the one-direction Dirac alpha observable

The carrier is the existing full `4 × 4` complex Dirac matrix algebra, viewed
as a real algebra. Its Hamiltonian square and alpha anticommutator discharge
the hypotheses of the generic energy-involution owner. The concrete residual
is `alpha1 - (c*p/E²) • H`; the physical velocity residual is `c` times this
operator. Its square is the longitudinal factor `(m²*c⁴/E²) • 1`.

Only a finite momentum fiber is treated. The labels positive and negative
energy additionally require the positive choice of `E`; the algebraic results
allow either nonzero choice. No spacetime horizon, trajectory, three-dimensional
transverse family, or physical mass-generation conclusion is asserted.
-/

noncomputable section

namespace InfoGeometry.Physics.DiracRest

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.EnergySign
open InfoGeometry.Clifford.DiracPauliGamma

private theorem complex_smul_eq_real_smul (r : ℝ) (M : DiracMatrix) :
    (r : ℂ) • M = r • M := by
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

/-- The established dispersion identity expressed using the native real action. -/
theorem diracHamiltonian1D_sq_real (p m c : ℝ) :
    diracHamiltonian1D p m c * diracHamiltonian1D p m c =
      (c ^ 2 * p ^ 2 + m ^ 2 * c ^ 4) • (1 : DiracMatrix) := by
  rw [diracHamiltonian1D_sq]
  exact complex_smul_eq_real_smul _ _

/-- The concrete alpha anticommutator, with the real scalar action required by
the representation-independent energy-involution owner. -/
theorem diracAlpha1_hamiltonian_anticommutator_real (p m c : ℝ) :
    diracAlpha1 * diracHamiltonian1D p m c +
        diracHamiltonian1D p m c * diracAlpha1 =
      (2 * (c * p)) • (1 : DiracMatrix) := by
  calc
    diracAlpha1 * diracHamiltonian1D p m c +
        diracHamiltonian1D p m c * diracAlpha1 =
        (2 * c * p : ℂ) • (1 : DiracMatrix) := by
      rw [add_comm, diracHamiltonian_alpha1_anticommutator]
    _ = ((2 * (c * p) : ℝ) : ℂ) • (1 : DiracMatrix) := by
      congr 1
      push_cast <;> ring
    _ = (2 * (c * p)) • (1 : DiracMatrix) := complex_smul_eq_real_smul _ _

/-- The actual normalized involution of the existing Dirac Hamiltonian. Its
square-one field is derived from the proved dispersion polynomial. -/
def diracEnergyInvolution1D (p m c E : ℝ) (hE : E ≠ 0)
    (hdisp : E ^ 2 = c ^ 2 * p ^ 2 + m ^ 2 * c ^ 4) :
    ChiralInvolution DiracMatrix :=
  energySignInvolution (diracHamiltonian1D p m c) E hE
    (by rw [diracHamiltonian1D_sq_real, hdisp])

/-- The longitudinal dimensionless trembling operator in a momentum fiber. -/
def diracTrembling1D (p m c E : ℝ) : DiracMatrix :=
  energyResidual (diracHamiltonian1D p m c) diracAlpha1 E (c * p)

/-- The actual residual anticommutes with the concrete Hamiltonian. -/
theorem diracTrembling1D_anticommutes (p m c E : ℝ) (hE : E ≠ 0)
    (hdisp : E ^ 2 = c ^ 2 * p ^ 2 + m ^ 2 * c ^ 4) :
    diracTrembling1D p m c E * diracHamiltonian1D p m c =
      -(diracHamiltonian1D p m c * diracTrembling1D p m c E) := by
  exact energyResidual_anticommutes (diracHamiltonian1D p m c) diracAlpha1
    E (c * p) hE (by rw [diracHamiltonian1D_sq_real, hdisp])
    (diracAlpha1_hamiltonian_anticommutator_real p m c)

/-- The trembling operator has zero compression within either derived energy
sector. The projectors are constructed from `H/E`, not identified with chirality. -/
theorem diracTrembling1D_diagonal_corners_zero (p m c E : ℝ) (hE : E ≠ 0)
    (hdisp : E ^ 2 = c ^ 2 * p ^ 2 + m ^ 2 * c ^ 4) :
    let C := diracEnergyInvolution1D p m c E hE hdisp
    C.Pleft * diracTrembling1D p m c E * C.Pleft = 0 ∧
      C.Pright * diracTrembling1D p m c E * C.Pright = 0 := by
  exact energyResidual_diagonal_corners_zero
    (diracHamiltonian1D p m c) diracAlpha1 E (c * p) hE
    (by rw [diracHamiltonian1D_sq_real, hdisp])
    (diracAlpha1_hamiltonian_anticommutator_real p m c)

/-- The two inter-energy corners recover the full concrete residual. -/
theorem diracTrembling1D_off_diagonal_decomposition (p m c E : ℝ) (hE : E ≠ 0)
    (hdisp : E ^ 2 = c ^ 2 * p ^ 2 + m ^ 2 * c ^ 4) :
    let C := diracEnergyInvolution1D p m c E hE hdisp
    diracTrembling1D p m c E =
      C.Pleft * diracTrembling1D p m c E * C.Pright +
        C.Pright * diracTrembling1D p m c E * C.Pleft := by
  exact energyResidual_off_diagonal_decomposition
    (diracHamiltonian1D p m c) diracAlpha1 E (c * p) hE
    (by rw [diracHamiltonian1D_sq_real, hdisp])
    (diracAlpha1_hamiltonian_anticommutator_real p m c)

/-- The longitudinal residual square is the exact mass-to-energy factor. -/
theorem diracTrembling1D_sq (p m c E : ℝ) (hE : E ≠ 0)
    (hdisp : E ^ 2 = c ^ 2 * p ^ 2 + m ^ 2 * c ^ 4) :
    diracTrembling1D p m c E * diracTrembling1D p m c E =
      (m ^ 2 * c ^ 4 / E ^ 2) • (1 : DiracMatrix) := by
  have hcoeff : 1 - (c * p / E) ^ 2 = m ^ 2 * c ^ 4 / E ^ 2 := by
    field_simp [hE]
    nlinarith [hdisp]
  calc
    diracTrembling1D p m c E * diracTrembling1D p m c E =
        (1 - (c * p / E) ^ 2) • (1 : DiracMatrix) :=
      energyResidual_sq (diracHamiltonian1D p m c) diracAlpha1 E (c * p) hE
        (by rw [diracHamiltonian1D_sq_real, hdisp]) diracAlpha1_sq
        (diracAlpha1_hamiltonian_anticommutator_real p m c)
    _ = (m ^ 2 * c ^ 4 / E ^ 2) • (1 : DiracMatrix) := by rw [hcoeff]

/-- At zero mass the full Hamiltonian is explicitly proportional to alpha1. -/
theorem diracHamiltonian1D_massless (p c : ℝ) :
    diracHamiltonian1D p 0 c = (c * p) • diracAlpha1 := by
  calc
    diracHamiltonian1D p 0 c = ((c * p : ℝ) : ℂ) • diracAlpha1 := by
      simp [diracHamiltonian1D]
    _ = (c * p) • diracAlpha1 := complex_smul_eq_real_smul _ _

/-- Massless longitudinal trembling vanishes by the explicit Hamiltonian
formula and the nonzero energy relation, without inferring zero from a
square-zero operator. -/
theorem diracTrembling1D_massless_eq_zero (p c E : ℝ) (hE : E ≠ 0)
    (hdisp : E ^ 2 = c ^ 2 * p ^ 2) :
    diracTrembling1D p 0 c E = 0 := by
  change diracAlpha1 - (c * p / E ^ 2) • diracHamiltonian1D p 0 c = 0
  rw [diracHamiltonian1D_massless, smul_smul]
  have hcp : (c * p) ^ 2 = E ^ 2 := by nlinarith [hdisp]
  have hcoeff : (c * p / E ^ 2) * (c * p) = 1 := by
    calc
      (c * p / E ^ 2) * (c * p) = (c * p) ^ 2 / E ^ 2 := by ring
      _ = 1 := by rw [hcp, div_self (pow_ne_zero 2 hE)]
  rw [hcoeff, one_smul, sub_self]

end InfoGeometry.Physics.DiracRest

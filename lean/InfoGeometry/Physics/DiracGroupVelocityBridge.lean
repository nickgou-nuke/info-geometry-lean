/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.DiracEnergyOddPart
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Energy-branch derivatives and compressed Dirac velocity

The Hamiltonian, velocity observable, energy involution, and projectors are
the existing full `4 × 4` complex matrix owners. The positive energy branch
is the square root of their proved dispersion polynomial. Its derivative
and the derivative of its negative agree with the two projector-compressed
velocity coefficients.

The algebraic compression theorem allows either nonzero choice of energy
satisfying the square relation. The derivative theorem chooses the positive
square root and assumes a positive radicand at the selected momentum. This
also excludes the massless crossing where the absolute-value branch need
not be differentiable.

This is a finite momentum-fiber statement with genuine one-variable
derivatives. It constructs no wavepacket, Fourier evolution, spatial
position operator, or dispersion estimate for a differential equation.
-/

noncomputable section

namespace InfoGeometry.Physics.DiracRest

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.EnergySign
open InfoGeometry.Clifford.DiracPauliGamma

/-- The positive branch of the existing Hamiltonian's dispersion polynomial. -/
def diracPositiveEnergy1D (p m c : ℝ) : ℝ :=
  Real.sqrt (c ^ 2 * p ^ 2 + m ^ 2 * c ^ 4)

/-- The branch square is the coefficient already proved for the native
matrix Hamiltonian, including at zero energy. -/
theorem diracPositiveEnergy1D_sq (p m c : ℝ) :
    diracPositiveEnergy1D p m c ^ 2 = c ^ 2 * p ^ 2 + m ^ 2 * c ^ 4 := by
  unfold diracPositiveEnergy1D
  apply Real.sq_sqrt
  positivity

/-- A positive dispersion polynomial gives a strictly positive energy. -/
theorem diracPositiveEnergy1D_pos (p m c : ℝ)
    (hgap : 0 < c ^ 2 * p ^ 2 + m ^ 2 * c ^ 4) :
    0 < diracPositiveEnergy1D p m c :=
  Real.sqrt_pos.mpr hgap

/-- Actual differentiation of the positive energy branch at a gapped momentum. -/
theorem hasDerivAt_diracPositiveEnergy1D (p m c : ℝ)
    (hgap : 0 < c ^ 2 * p ^ 2 + m ^ 2 * c ^ 4) :
    HasDerivAt (fun q : ℝ => diracPositiveEnergy1D q m c)
      (c ^ 2 * p / diracPositiveEnergy1D p m c) p := by
  have hpoly :
      HasDerivAt (fun q : ℝ => c ^ 2 * q ^ 2 + m ^ 2 * c ^ 4)
        (2 * c ^ 2 * p) p := by
    convert (hasDerivAt_add_const_iff (m ^ 2 * c ^ 4)).mpr
      (HasDerivAt.const_mul (c ^ 2) (HasDerivAt.pow (hasDerivAt_id p) 2))
      using 1 <;> ring
  have hroot :
      HasDerivAt (fun q : ℝ => diracPositiveEnergy1D q m c)
        ((2 * c ^ 2 * p) / (2 * diracPositiveEnergy1D p m c)) p :=
    HasDerivAt.sqrt hpoly (ne_of_gt hgap)
  have hE : diracPositiveEnergy1D p m c ≠ 0 :=
    ne_of_gt (diracPositiveEnergy1D_pos p m c hgap)
  have hcoeff :
      (2 * c ^ 2 * p) / (2 * diracPositiveEnergy1D p m c) =
        c ^ 2 * p / diracPositiveEnergy1D p m c := by
    field_simp [hE] <;> ring
  rwa [hcoeff] at hroot

/-- The opposite energy branch has the opposite derivative. -/
theorem hasDerivAt_diracNegativeEnergy1D (p m c : ℝ)
    (hgap : 0 < c ^ 2 * p ^ 2 + m ^ 2 * c ^ 4) :
    HasDerivAt (fun q : ℝ => -diracPositiveEnergy1D q m c)
      (-(c ^ 2 * p / diracPositiveEnergy1D p m c)) p :=
  HasDerivAt.neg (hasDerivAt_diracPositiveEnergy1D p m c hgap)

/-- The native velocity compressed to either derived energy sector is its
scalar branch coefficient times that native projector. No commutativity of
the matrix algebra or identification with a chirality projector is used. -/
theorem diracVelocity1D_compressed_energy_sectors
    (p m c E : ℝ) (hE : E ≠ 0)
    (hdisp : E ^ 2 = c ^ 2 * p ^ 2 + m ^ 2 * c ^ 4) :
    let C := diracEnergyInvolution1D p m c E hE hdisp
    C.Pleft * diracVelocity1D c * C.Pleft =
        (c ^ 2 * p / E) • C.Pleft ∧
      C.Pright * diracVelocity1D c * C.Pright =
        (-(c ^ 2 * p / E)) • C.Pright := by
  let C := diracEnergyInvolution1D p m c E hE hdisp
  have hres :
      diracTrembling1D p m c E =
        diracAlpha1 - (c * p / E) • C.chi := by
    exact energyResidual_eq_normalizedResidual
      (diracHamiltonian1D p m c) diracAlpha1 E (c * p) hE
      (by rw [diracHamiltonian1D_sq_real, hdisp])
  have hcorners :
      C.Pleft * diracTrembling1D p m c E * C.Pleft = 0 ∧
        C.Pright * diracTrembling1D p m c E * C.Pright = 0 :=
    diracTrembling1D_diagonal_corners_zero p m c E hE hdisp
  have hleft : C.Pleft * diracAlpha1 * C.Pleft =
      (c * p / E) • C.Pleft := by
    apply sub_eq_zero.mp
    simpa only [hres, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
      C.Pleft_mul_chi, C.Pleft_idem] using hcorners.1
  have hright : C.Pright * diracAlpha1 * C.Pright =
      (-(c * p / E)) • C.Pright := by
    apply sub_eq_zero.mp
    simpa only [hres, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
      C.Pright_mul_chi, neg_mul, C.Pright_idem, smul_neg, neg_smul]
      using hcorners.2
  have hvelocity : diracVelocity1D c = c • diracAlpha1 := by
    ext i j
    simp only [diracVelocity1D, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  change
    C.Pleft * diracVelocity1D c * C.Pleft =
        (c ^ 2 * p / E) • C.Pleft ∧
      C.Pright * diracVelocity1D c * C.Pright =
        (-(c ^ 2 * p / E)) • C.Pright
  constructor
  · rw [hvelocity, mul_smul_comm, smul_mul_assoc, hleft, smul_smul]
    congr 1
    ring
  · rw [hvelocity, mul_smul_comm, smul_mul_assoc, hright, smul_smul]
    congr 1
    ring

/-- The two native velocity compressions equal the derivatives of the
positive and negative dispersion branches at the chosen momentum. -/
theorem diracVelocity1D_compressed_eq_energy_derivatives
    (p m c : ℝ) (hgap : 0 < c ^ 2 * p ^ 2 + m ^ 2 * c ^ 4) :
    let E := diracPositiveEnergy1D p m c
    let C := diracEnergyInvolution1D p m c E
      (ne_of_gt (diracPositiveEnergy1D_pos p m c hgap))
      (diracPositiveEnergy1D_sq p m c)
    C.Pleft * diracVelocity1D c * C.Pleft =
        deriv (fun q : ℝ => diracPositiveEnergy1D q m c) p • C.Pleft ∧
      C.Pright * diracVelocity1D c * C.Pright =
        deriv (fun q : ℝ => -diracPositiveEnergy1D q m c) p • C.Pright := by
  dsimp only
  rw [(hasDerivAt_diracPositiveEnergy1D p m c hgap).deriv,
    (hasDerivAt_diracNegativeEnergy1D p m c hgap).deriv]
  exact diracVelocity1D_compressed_energy_sectors p m c
    (diracPositiveEnergy1D p m c)
    (ne_of_gt (diracPositiveEnergy1D_pos p m c hgap))
    (diracPositiveEnergy1D_sq p m c)

end InfoGeometry.Physics.DiracRest

end

import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import InfoGeometry.Section8

/-!
# Section 9: Quaternion Curvature and Riemann Curvature

This file formalizes the finite algebraic core of the curvature section.

It does not claim a full manifold-level derivation of the spin connection from
tetrads.  Instead it proves the compile-checked algebra used by the section:

* quaternion curvature is the Section 8 gauge-curvature formula;
* spin curvature is `d_mu omega_nu - d_nu omega_mu + [omega_mu, omega_nu]`;
* Riemann curvature is the Christoffel curvature formula at fixed indices;
* all three curvatures vanish in the flat zero-connection case;
* spin curvature and Riemann curvature are antisymmetric in `mu,nu`;
* commutators and Lorentz generators are traceless;
* the linear spin-to-quaternion and Riemann-to-spin curvature readouts send zero
  curvature to zero.
-/

noncomputable section

namespace Section9

open Matrix

abbrev Quat := Section8.Quat

/-! ## 9.1 Pauli matrices and Lorentz generators -/

def I2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, 1]

def s1 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 1; 1, 0]

def s2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), -Complex.I; Complex.I, 0]

def s3 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, -1]

def sigma : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => I2
  | 1 => s1
  | 2 => s2
  | 3 => s3

/-- Lorentz generators `sigma_ab = (i/2) [sigma_a, sigma_b]`. -/
def sigma_ab (a b : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.I / 2) • (sigma a * sigma b - sigma b * sigma a)

/-- The trace of each Lorentz generator vanishes because it is a commutator. -/
theorem sigma_ab_traceless (a b : Fin 4) :
    (∑ i : Fin 2, sigma_ab a b i i) = (0 : ℂ) := by
  unfold sigma_ab
  fin_cases a <;> fin_cases b <;>
    simp [sigma, I2, s1, s2, s3, Fin.sum_univ_two] <;> ring_nf

/-! ## 9.1 Quaternion curvature -/

/-- Quaternion curvature `Omega_{mu nu} = d_mu Omega_nu - d_nu Omega_mu + [Omega_mu,Omega_nu]`. -/
abbrev quaternionCurvature :=
  Section8.Quat.quaternionCurvature

theorem quaternionCurvature_flat :
    quaternionCurvature 0 0 0 0 = (0 : Quat) :=
  Section8.Quat.quaternionCurvature_flat

theorem quaternionCurvature_swap
    (dMuOmegaNu dNuOmegaMu OmegaMu OmegaNu : Quat) :
    quaternionCurvature dNuOmegaMu dMuOmegaNu OmegaNu OmegaMu =
      -quaternionCurvature dMuOmegaNu dNuOmegaMu OmegaMu OmegaNu := by
  ext <;> simp [quaternionCurvature, Section8.Quat.quaternionCurvature] <;> ring_nf

/-! ## 9.2 Spin curvature -/

/-- Matrix commutator. -/
def commutator (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  A * B - B * A

/-- Spin curvature `F = d_mu omega_nu - d_nu omega_mu + [omega_mu, omega_nu]`. -/
def spinCurvature
    (dMuOmegaNu dNuOmegaMu omegaMu omegaNu : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  dMuOmegaNu - dNuOmegaMu + commutator omegaMu omegaNu

theorem spinCurvature_flat :
    spinCurvature 0 0 0 0 = (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinCurvature, commutator]

theorem spinCurvature_swap
    (dMuOmegaNu dNuOmegaMu omegaMu omegaNu : Matrix (Fin 2) (Fin 2) ℂ) :
    spinCurvature dNuOmegaMu dMuOmegaNu omegaNu omegaMu =
      -spinCurvature dMuOmegaNu dNuOmegaMu omegaMu omegaNu := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinCurvature, commutator, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf

/-- Commutators in the 2-spinor matrix algebra are traceless. -/
theorem commutator_traceless (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ i : Fin 2, commutator A B i i) = 0 := by
  simp [commutator, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf

/-! ## 9.3 Riemann curvature at fixed indices -/

/--
Riemann curvature coefficient at fixed `rho,sigma,mu,nu`, with the contracted
Christoffel products supplied as functions of the dummy index `lambda`.
-/
def riemannCurvature
    (dMuGammaNuSigma dNuGammaMuSigma : ℂ)
    (GammaMuLambda GammaNuSigma GammaNuLambda GammaMuSigma : Fin 4 → ℂ) : ℂ :=
  dMuGammaNuSigma - dNuGammaMuSigma +
    (∑ l : Fin 4, GammaMuLambda l * GammaNuSigma l) -
    (∑ l : Fin 4, GammaNuLambda l * GammaMuSigma l)

theorem riemannCurvature_flat :
    riemannCurvature 0 0 0 0 0 0 = 0 := by
  simp [riemannCurvature]

theorem riemannCurvature_swap
    (dMuGammaNuSigma dNuGammaMuSigma : ℂ)
    (GammaMuLambda GammaNuSigma GammaNuLambda GammaMuSigma : Fin 4 → ℂ) :
    riemannCurvature dNuGammaMuSigma dMuGammaNuSigma
        GammaNuLambda GammaMuSigma GammaMuLambda GammaNuSigma =
      -riemannCurvature dMuGammaNuSigma dNuGammaMuSigma
        GammaMuLambda GammaNuSigma GammaNuLambda GammaMuSigma := by
  simp [riemannCurvature]
  ring

/-! ## 9.4 Curvature bridges -/

/--
Linear spin-to-quaternion curvature readout:
`Omega = (i/4) sum_a sigma_a F sigma_a`.
-/
def quaternionCurvatureFromSpin (F : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.I / 4) • (∑ a : Fin 4, sigma a * F * sigma a)

theorem quaternionCurvatureFromSpin_zero :
    quaternionCurvatureFromSpin 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quaternionCurvatureFromSpin]

/--
Linear Riemann-to-spin curvature readout:
`F = (1/2) sum_{a,b} R_ab sigma_ab`.
-/
def spinCurvatureFromRiemann (R : Fin 4 → Fin 4 → ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (∑ a : Fin 4, ∑ b : Fin 4, R a b • sigma_ab a b)

theorem spinCurvatureFromRiemann_zero :
    spinCurvatureFromRiemann 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinCurvatureFromRiemann]

theorem quaternion_spin_riemann_flat_chain :
    quaternionCurvatureFromSpin (spinCurvatureFromRiemann 0) = 0 :=
  by rw [spinCurvatureFromRiemann_zero, quaternionCurvatureFromSpin_zero]

theorem section9_capstone :
    (∀ a b : Fin 4, (∑ i : Fin 2, sigma_ab a b i i) = (0 : ℂ)) ∧
    quaternionCurvature 0 0 0 0 = (0 : Quat) ∧
    spinCurvature 0 0 0 0 = (0 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    riemannCurvature 0 0 0 0 0 0 = 0 ∧
    (∀ A B : Matrix (Fin 2) (Fin 2) ℂ, (∑ i : Fin 2, commutator A B i i) = 0) ∧
    quaternionCurvatureFromSpin (spinCurvatureFromRiemann 0) = 0 := by
  exact ⟨sigma_ab_traceless, quaternionCurvature_flat, spinCurvature_flat,
    riemannCurvature_flat, commutator_traceless, quaternion_spin_riemann_flat_chain⟩

end Section9

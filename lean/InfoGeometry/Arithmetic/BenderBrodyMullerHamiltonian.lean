import Mathlib

/-!
# Bender--Brody--Müller Hamiltonian socket

Finite/theorem-safe algebraic interfaces for
Carl M. Bender, Dorje C. Brody, Markus P. Müller,
"Hamiltonian for the zeros of the Riemann zeta function",
arXiv:1608.03679v4.

The paper proposes a non-Hermitian operator
`H = Δ⁻¹ (xp + px) Δ` whose boundary condition `ψ_z(0)=0` selects zeta zeros,
and discusses PT symmetry, pseudo-Hermiticity, and self-adjointness as analytic
obligations.

This Lean module proves only closed algebraic fragments:

* the coordinate conversion `E = i(2z-1)` and `z = (1-iE)/2` is inverse;
* if a boundary value is `-ζ(z)` and the boundary condition sets it to zero,
  then the corresponding zeta value is zero;
* a similarity transform transfers eigenvectors from the Berry--Keating block to
  the BBM Hamiltonian whenever the inverse/left-inverse laws are supplied;
* PT/pseudo-Hermitian/self-adjoint/RH consequences are recorded only as socket
  data, never as proved analytic theorems.
-/

noncomputable section

open Complex

namespace InfoGeometry.Arithmetic.BenderBrodyMullerHamiltonian

/-! ## Spectral coordinate algebra -/

/-- BBM energy coordinate attached to a zeta coordinate `z`: `E = i(2z - 1)`. -/
def bbmEnergy (z : ℂ) : ℂ :=
  Complex.I * (2 * z - 1)

/-- Inverse coordinate used in the paper: `z = (1 - iE) / 2`. -/
def bbmZeroCoordinate (E : ℂ) : ℂ :=
  (1 - Complex.I * E) / 2

/-- The BBM energy/zero coordinate conversion recovers `z`. -/
theorem bbmZeroCoordinate_energy (z : ℂ) :
    bbmZeroCoordinate (bbmEnergy z) = z := by
  simp [bbmZeroCoordinate, bbmEnergy]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- The BBM energy/zero coordinate conversion recovers `E`. -/
theorem bbmEnergy_zeroCoordinate (E : ℂ) :
    bbmEnergy (bbmZeroCoordinate E) = E := by
  simp [bbmZeroCoordinate, bbmEnergy]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- Critical-line zeros (`z = 1/2 + it`) correspond to real BBM energy `-2t`. -/
theorem bbmEnergy_on_critical_line (t : ℝ) :
    bbmEnergy ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = (-2 * t : ℂ) := by
  simp [bbmEnergy]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- If the BBM energy coordinate is real `E`, its zero coordinate lies on `1/2 - iE/2`. -/
theorem bbmZeroCoordinate_real_energy (E : ℝ) :
    bbmZeroCoordinate (E : ℂ) = (1 / 2 : ℂ) - Complex.I * ((E / 2 : ℝ) : ℂ) := by
  simp [bbmZeroCoordinate]
  ring_nf

/-! ## Boundary condition to zeta-zero algebra -/

/--
Pure boundary algebra: if the boundary value is `-ζ(z)` and the boundary
condition forces it to vanish, then the zeta value vanishes.
-/
theorem zeta_zero_of_boundary_zero {A : Type*} [AddGroup A]
    {psiAtZero zetaAtZero : A}
    (h_eval : psiAtZero = -zetaAtZero) (h_boundary : psiAtZero = 0) :
    zetaAtZero = 0 := by
  rw [h_eval] at h_boundary
  exact neg_eq_zero.mp h_boundary

/-- Data packet for the BBM boundary-value selection mechanism. -/
structure BoundaryZetaPacket (ZeroLabel BoundaryValue : Type*) [AddGroup BoundaryValue] where
  psiAtZero : ZeroLabel → BoundaryValue
  zetaAt : ZeroLabel → BoundaryValue
  psiAtZero_eq_neg_zeta : ∀ z : ZeroLabel, psiAtZero z = -zetaAt z

namespace BoundaryZetaPacket

variable {ZeroLabel BoundaryValue : Type*} [AddGroup BoundaryValue]
variable (P : BoundaryZetaPacket ZeroLabel BoundaryValue)

/-- Re-export of the boundary-to-zero implication for a supplied zero label. -/
theorem zetaAt_eq_zero_of_boundary {z : ZeroLabel} (h_boundary : P.psiAtZero z = 0) :
    P.zetaAt z = 0 :=
  zeta_zero_of_boundary_zero (P.psiAtZero_eq_neg_zeta z) h_boundary

end BoundaryZetaPacket

/-! ## Similarity transform eigenvector transfer -/

/--
A linear BBM similarity packet abstracting `H = Δ⁻¹ (xp + px) Δ`.

`delta_left_inverse` is the theorem-level substitute for the analytic domain
statement that `Δ⁻¹Δ` acts as the identity on the chosen functions.
-/
structure BBMSimilarityPacket (R V : Type*) [Semiring R] [AddCommMonoid V] [Module R V] where
  delta : V →ₗ[R] V
  deltaInv : V →ₗ[R] V
  berryKeating : V →ₗ[R] V
  hamiltonian : V →ₗ[R] V
  hamiltonian_eq : hamiltonian = deltaInv.comp (berryKeating.comp delta)
  delta_left_inverse : ∀ v : V, deltaInv (delta v) = v

namespace BBMSimilarityPacket

variable {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
variable (P : BBMSimilarityPacket R V)

/-- The Hamiltonian acts by the advertised similarity transform. -/
theorem hamiltonian_apply (v : V) :
    P.hamiltonian v = P.deltaInv (P.berryKeating (P.delta v)) := by
  rw [P.hamiltonian_eq]
  rfl

/--
Eigenvector transfer through the similarity transform: if `Δ ψ` is a
Berry--Keating eigenvector with eigenvalue `E`, then `ψ` is a BBM-Hamiltonian
eigenvector with the same eigenvalue.
-/
theorem eigen_of_delta_eigen {E : R} {psi : V}
    (hBK : P.berryKeating (P.delta psi) = E • P.delta psi) :
    P.hamiltonian psi = E • psi := by
  calc
    P.hamiltonian psi = P.deltaInv (P.berryKeating (P.delta psi)) := P.hamiltonian_apply psi
    _ = P.deltaInv (E • P.delta psi) := by rw [hBK]
    _ = E • P.deltaInv (P.delta psi) := by simp
    _ = E • psi := by rw [P.delta_left_inverse psi]

end BBMSimilarityPacket

/-! ## Analytic obligation socket -/

/--
Socket for the analytic BBM obligations.  These fields are hypotheses/targets,
not constructed proofs in this finite module.
-/
structure BBMAnalyticSocket where
  domainChosen : Prop
  deltaInverseOnDomain : Prop
  boundaryConditionSelectsNontrivialZeros : Prop
  momentumSymmetricOnMetricDomain : Prop
  pseudoHermitianMetricPositive : Prop
  selfAdjointClosure : Prop
  rhConsequence : Prop
  selfAdjointClosure_implies_rh : selfAdjointClosure → rhConsequence

end InfoGeometry.Arithmetic.BenderBrodyMullerHamiltonian

import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

/-!
# arXiv:1608.03679 finite Hamiltonian algebra packet

Paper: Carl M. Bender, Dorje C. Brody, and Markus P. Müller,
*Hamiltonian for the zeros of the Riemann zeta function*,
arXiv:1608.03679v4.

This module formalizes the theorem-safe algebraic backbone of the paper:

* the spectral parameter conversion `E = i(2z-1)` and
  `z = (1-iE)/2`;
* the boundary readout `ψ_z(0) = -ζ(z)`, so the boundary condition
  `ψ_z(0)=0` is equivalent to `ζ(z)=0`;
* the finite algebraic direction from real `E` to the critical-line real part;
* the commuting classical shadow `xp + px = 2xp` of the Berry--Keating
  Hamiltonian.

#### BUCKET 1: CLOSED FINITE THEOREMS

All declarations below are kernel-checked algebraic theorems over `ℂ` or a
generic semiring.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

`boundaryCondition_iff_zeta_zero` depends on the explicit premise
`ψ_z(0) = -ζ(z)`. It does not define an analytic zeta function.

#### BUCKET 3: OPEN CLOSURE DEBT

No domain theorem, self-adjointness theorem, pseudo-Hermitian metric theorem,
completeness theorem, or Riemann-hypothesis implication is proved here. The
paper itself treats those analytic operator-theoretic points as the hard
closure problem.
-/

namespace InfoGeometry.Arithmetic.Arxiv160803679BenderHamiltonian

open Complex

noncomputable section

/-! ## Spectral parameter algebra -/

/-- The paper's Hamiltonian eigenvalue relation `E = i(2z-1)`. -/
def benderEigenvalueRelation (z E : ℂ) : Prop :=
  E = Complex.I * (2 * z - 1)

/-- The inverse readout `z = (1-iE)/2` attached to the Bender Hamiltonian. -/
def benderSpectralZ (E : ℂ) : ℂ :=
  (1 - Complex.I * E) / 2

/-- If `E = i(2z-1)`, then the inverse readout returns `z`. -/
theorem benderSpectralZ_of_eigenvalueRelation {z E : ℂ}
    (h : benderEigenvalueRelation z E) :
    benderSpectralZ E = z := by
  unfold benderEigenvalueRelation benderSpectralZ at *
  rw [h]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Reconstructing `E` from the inverse readout gives back the same `E`. -/
theorem eigenvalueRelation_benderSpectralZ (E : ℂ) :
    benderEigenvalueRelation (benderSpectralZ E) E := by
  unfold benderEigenvalueRelation benderSpectralZ
  ring_nf
  rw [Complex.I_sq]
  ring

/--
Real Hamiltonian eigenvalues land on the critical-line real part under the
paper's spectral conversion.
-/
theorem criticalLine_realPart_of_real_eigenvalue {z E : ℂ} {t : ℝ}
    (hE : E = (t : ℂ))
    (h : benderEigenvalueRelation z E) :
    z.re = (1 / 2 : ℝ) := by
  have hz : z = benderSpectralZ E :=
    (benderSpectralZ_of_eigenvalueRelation h).symm
  rw [hz, hE]
  simp [benderSpectralZ]

/--
Conversely, a point explicitly parameterized as `z = 1/2 + i t` has real
Hamiltonian eigenvalue `E = -2t`.
-/
theorem eigenvalueRelation_of_criticalLine_param (t : ℝ) :
    benderEigenvalueRelation
      ((1 / 2 : ℂ) + Complex.I * (t : ℂ))
      ((-2 * t : ℝ) : ℂ) := by
  unfold benderEigenvalueRelation
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-! ## Boundary condition readout -/

/-- Abstract boundary predicate for a supplied wavefunction-at-zero readout. -/
def boundaryCondition (psiAtZero : ℂ → ℂ) (z : ℂ) : Prop :=
  psiAtZero z = 0

/--
The paper's boundary readout: if `ψ_z(0) = -ζ(z)`, then the boundary condition
is exactly the abstract zeta-zero condition.
-/
theorem boundaryCondition_iff_zeta_zero
    (psiAtZero zeta : ℂ → ℂ) {z : ℂ}
    (hBoundaryReadout : psiAtZero z = -zeta z) :
    boundaryCondition psiAtZero z ↔ zeta z = 0 := by
  constructor
  · intro hBoundary
    unfold boundaryCondition at hBoundary
    have hneg : -zeta z = 0 := by
      rw [← hBoundaryReadout]
      exact hBoundary
    exact neg_eq_zero.mp hneg
  · intro hzeta
    unfold boundaryCondition
    rw [hBoundaryReadout, hzeta, neg_zero]

/--
Combining the boundary readout with the spectral relation: a boundary
eigenstate whose readout is `-ζ(z)` is a zeta-zero eigenstate.
-/
theorem zeta_zero_of_boundary_eigenstate
    (psiAtZero zeta : ℂ → ℂ) {z E : ℂ}
    (_hEigen : benderEigenvalueRelation z E)
    (hBoundaryReadout : psiAtZero z = -zeta z)
    (hBoundary : boundaryCondition psiAtZero z) :
    zeta z = 0 :=
  (boundaryCondition_iff_zeta_zero psiAtZero zeta hBoundaryReadout).mp hBoundary

/-! ## Classical Berry--Keating shadow -/

/--
If the classical variables commute, the symmetric Berry--Keating expression
`xp+px` collapses to `2xp`.
-/
theorem berryKeating_commuting_shadow {R : Type*} [Semiring R]
    {x p : R} (hcomm : p * x = x * p) :
    x * p + p * x = (2 : R) * (x * p) := by
  rw [hcomm]
  rw [two_mul]

end

end InfoGeometry.Arithmetic.Arxiv160803679BenderHamiltonian

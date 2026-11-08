import InfoGeometry.Physics.TwoSectorSpectralOscillation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.DiracPauliGamma
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

noncomputable section

open InfoGeometry.Physics.TwoSector
open InfoGeometry.Clifford.DiracPauliGamma

namespace InfoGeometry.Physics.DiracRest

/-!
# Dirac Rest Frame Weyl Chiral Mixing to Two-Sector Oscillation Bridge

This module formalizes the rest-frame ($p=0$) Dirac Hamiltonian in the Weyl (chiral) basis:
$$H_D = \begin{pmatrix} 0 & m c^2 \\ m c^2 & 0 \end{pmatrix} = m c^2 \sigma_x$$
as an instance of `TwoSectorSpectralOscillation` with $E_0 = 0$ and $\Delta = m c^2$.

## Epistemic Clarifications & Boundaries:
1. **Mass-Induced Chirality Mixing**:
   The Dirac mass term couples the left and right Weyl spinor components:
   $\mathcal{L}_{\text{mass}} = -m (\psi_L^\dagger \psi_R + \psi_R^\dagger \psi_L)$.
   At $p=0$, this generates an off-diagonal two-sector Hamiltonian with coupling $\Delta = mc^2$.
2. **Dirac Zitterbewegung vs Chirality Mixing**:
   Standard Dirac Zitterbewegung (the rapid oscillation of the velocity operator $v(t) = c \alpha(t)$)
   arises from the quantum interference between positive- and negative-energy sectors $E_\pm = \pm \sqrt{p^2 c^2 + m^2 c^4}$.
   At rest ($p=0$), the energy splitting between positive and negative energy states is precisely $2mc^2$.
   The chiral two-state Hamiltonian has the same gap scale, but its transition probability is not by itself
   a derivation of the Dirac velocity-operator oscillation: chirality ($L/R$) and energy sign ($E_\pm$)
   are distinct physical gradings.

The results here are kernel-checked; this module introduces no custom axioms or proof holes.
-/

/-- Dirac rest-frame Hamiltonian in the Weyl basis: $H_D(m, c) = \begin{pmatrix} 0 & m c^2 \\ m c^2 & 0 \end{pmatrix}$. -/
def diracRestHamiltonian (m c : ℝ) : InfoGeometry.Algebra.FiniteSpin.Mat2R :=
  twoSectorHamiltonian 0 (m * c ^ 2)

/-- **THE REST-FRAME DIRAC MASS GAP THEOREM**:
    The physical energy separation between positive and negative rest-energy states is $\Delta E = 2 |m| c^2$. -/
theorem dirac_rest_mass_gap (m c : ℝ) :
    |(0 + m * c ^ 2) - (0 - m * c ^ 2)| = 2 * |m| * c ^ 2 := by
  have h_gap := physical_spectral_gap 0 (m * c ^ 2)
  have h_abs : |m * c ^ 2| = |m| * c ^ 2 := by
    rw [abs_mul, abs_sq]
  rw [h_gap, h_abs, mul_assoc]

/-- The Weyl-sector transition probability has the elementary double-angle
form at coupling `m c²`. Its phase scale is set by twice that coupling; this
identity alone does not identify the transition with Dirac Zitterbewegung. -/
theorem dirac_rest_chiral_transition_double_angle (m c t : ℝ) :
    transitionProb (m * c ^ 2) t =
    (1 - Real.cos (2 * (m * c ^ 2) * t)) / 2 :=
  transition_double_angle (m * c ^ 2) t

theorem diracRestHamiltonian_secular_roots (m c E : ℝ) :
    Matrix.det (diracRestHamiltonian m c - E • (1 : InfoGeometry.Algebra.FiniteSpin.Mat2R)) =
      (E - (-(m * c ^ 2))) * (E - (m * c ^ 2)) := by
  have hdet := secular_roots 0 (m * c ^ 2) E
  simp only [zero_sub, zero_add] at hdet
  simpa [diracRestHamiltonian] using hdet

/-! ### Concrete Dirac velocity commutator

The two-sector rest Hamiltonian above is expressed in the Weyl/chiral basis.
For the standard Dirac velocity observable, use the Pauli--Dirac gamma
representation instead: in one spatial direction `α₁ = γ⁰γ¹` and
`H(p) = c p α₁ + m c² γ⁰`.  The commutator below is the finite-dimensional
algebraic carrier behind positive/negative-energy mixing.  It does not assert
a measured oscillation or a nuclear detector signal.
-/

/-- The first Dirac alpha matrix in the Pauli--Dirac representation. -/
def diracAlpha1 : DiracMatrix := gamma0 * gamma1

/-- One-dimensional free Dirac Hamiltonian in the Pauli--Dirac representation. -/
def diracHamiltonian1D (p m c : ℝ) : DiracMatrix :=
  (c * p : ℂ) • diracAlpha1 + (m * c ^ 2 : ℂ) • gamma0

/-- The physical velocity observable `c α₁` in this finite representation. -/
def diracVelocity1D (c : ℝ) : DiracMatrix := (c : ℂ) • diracAlpha1

/-- The Pauli--Dirac alpha matrix squares to the identity. -/
theorem diracAlpha1_sq : diracAlpha1 * diracAlpha1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracAlpha1, gamma0, gamma1] <;> ring

/-- The one-dimensional free Dirac Hamiltonian squares to its relativistic
dispersion polynomial times the identity. This proves the algebraic energy
shell in this representation; it does not supply a state or a measurement. -/
theorem diracHamiltonian1D_sq (p m c : ℝ) :
    diracHamiltonian1D p m c * diracHamiltonian1D p m c =
      ((c ^ 2 * p ^ 2 + m ^ 2 * c ^ 4 : ℝ) : ℂ) • (1 : DiracMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracHamiltonian1D, diracAlpha1, gamma0, gamma1] <;> ring

/-- The Hamiltonian--velocity commutator is independent of momentum and is
the mass term coupling the two energy sectors:
`H(p)(c α₁) - (c α₁)H(p) = 2 m c³ γ¹`.

This is an algebraic commutator identity; time evolution is a separate step. -/
theorem diracHamiltonian_velocity_commutator (p m c : ℝ) :
    diracHamiltonian1D p m c * diracVelocity1D c -
        diracVelocity1D c * diracHamiltonian1D p m c =
      (2 * m * c ^ 3 : ℂ) • gamma1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracHamiltonian1D, diracVelocity1D, diracAlpha1,
      gamma0, gamma1] <;> ring

/-- Matrix commutator `[A,B] = AB - BA` in the Dirac representation. -/
def diracCommutator (A B : DiracMatrix) : DiracMatrix := A * B - B * A

/-- The second Heisenberg derivative in units `ℏ = 1`, namely
`-[H,[H,O]]`. The negative sign comes from applying the generator
`O ↦ i[H,O]` twice. -/
def diracHeisenbergSecondDerivative (H O : DiracMatrix) : DiracMatrix :=
  -diracCommutator H (diracCommutator H O)

/-- At rest, the standard Dirac velocity operator satisfies the exact
harmonic double-commutator equation with angular frequency scale `2mc²`
(`ℏ = 1`):
`-[H,[H,v]] = -(2mc²)² v`.

This is the finite-dimensional operator identity underlying the textbook
rest-frame Zitterbewegung frequency. It does not assert a state, expectation
value, or detector response. -/
theorem diracRest_velocity_heisenberg_harmonicity (m c : ℝ) :
    diracHeisenbergSecondDerivative
        (diracHamiltonian1D 0 m c) (diracVelocity1D c) =
      -((2 * m * c ^ 2 : ℂ) ^ 2) • diracVelocity1D c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracHeisenbergSecondDerivative, diracCommutator,
      diracHamiltonian1D, diracVelocity1D, diracAlpha1,
      gamma0, gamma1] <;> ring

end InfoGeometry.Physics.DiracRest

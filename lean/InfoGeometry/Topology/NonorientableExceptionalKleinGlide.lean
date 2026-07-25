import Mathlib.Tactic

/-!
# Non-orientable exceptional points in a Klein Brillouin zone

Finite algebraic layer for arXiv:2504.11983v1,
"Non-orientable Exceptional Points in Twisted Boundary Systems".

This module proves only exact identities for the two-band model used in the
paper:

* the momentum-space glide `(kx, ky) ↦ (-kx, ky + π)` preserves the coefficients
  in Eqs. (3)--(4), and hence the Hamiltonian `H = dx σx + dy σy`;
* the two-band square law `H² = (dx² + dy²) I`;
* at an explicit discriminant-zero point, the Hamiltonian is square-zero.

Numerical device modeling, Berry-phase plots, and global topology are left as
separate evidence layers rather than theorem claims here.
-/

noncomputable section

open Matrix Complex

namespace InfoGeometry.Topology.NonorientableExceptionalKleinGlide

/-- Complex `2 × 2` matrices for the finite two-band model. -/
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Coefficient `d_x(k) = cos k_x + i α` from Eq. (3). -/
def dx (α kx : ℝ) : ℂ :=
  (Real.cos kx : ℂ) + Complex.I * (α : ℂ)

/-- Coefficient `d_y(k)` from Eq. (4). -/
def dy (γ β kx ky : ℝ) : ℂ :=
  (-(Real.sin kx) * ((1 - γ) * Real.sin ky + γ * Real.cos ky) - (1 / 2 : ℝ) : ℂ) +
    Complex.I * (β : ℂ)

/-- Two-band non-Hermitian Bloch Hamiltonian `H = d_x σ_x + d_y σ_y`. -/
def kleinHamiltonian (α β γ kx ky : ℝ) : Mat2C :=
  ![![0, dx α kx - Complex.I * dy γ β kx ky],
    ![dx α kx + Complex.I * dy γ β kx ky, 0]]

/-- The exceptional-point discriminant for the two-band model. -/
def epDiscriminant (α β γ kx ky : ℝ) : ℂ :=
  dx α kx ^ 2 + dy γ β kx ky ^ 2

/-- The glide leaves `d_x` invariant. -/
theorem dx_glide (α kx : ℝ) :
    dx α (-kx) = dx α kx := by
  simp [dx, Real.cos_neg]

/-- The glide leaves `d_y` invariant. -/
theorem dy_glide (γ β kx ky : ℝ) :
    dy γ β (-kx) (ky + Real.pi) = dy γ β kx ky := by
  simp [dy, Real.sin_neg, Real.sin_add, Real.cos_add]
  ring

/-- Exact momentum-space glide symmetry of the two-band Hamiltonian. -/
theorem kleinHamiltonian_glide (α β γ kx ky : ℝ) :
    kleinHamiltonian α β γ (-kx) (ky + Real.pi) = kleinHamiltonian α β γ kx ky := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kleinHamiltonian, dx_glide, dy_glide]

/-- The two-band square law: `H² = (d_x² + d_y²) I`. -/
theorem kleinHamiltonian_sq (α β γ kx ky : ℝ) :
    kleinHamiltonian α β γ kx ky * kleinHamiltonian α β γ kx ky =
      epDiscriminant α β γ kx ky • (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kleinHamiltonian, epDiscriminant, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring_nf; try rw [Complex.I_sq]; ring_nf

/-- At discriminant zero the two-band Hamiltonian is square-zero. -/
theorem kleinHamiltonian_sq_zero_of_discriminant_zero {α β γ kx ky : ℝ}
    (h : epDiscriminant α β γ kx ky = 0) :
    kleinHamiltonian α β γ kx ky * kleinHamiltonian α β γ kx ky = 0 := by
  rw [kleinHamiltonian_sq, h]
  simp

/-- A finite braid/orientation packet for an EP transported through a Klein glide. -/
structure KleinGlideBraidPacket (B : Type*) [Group B] where
  clockwise : B
  counterclockwise : B
  glideRelation : counterclockwise = clockwise⁻¹

namespace KleinGlideBraidPacket

variable {B : Type*} [Group B]

/-- The glide swaps orientation by inverting the braid charge. -/
theorem counterclockwise_eq_inverse (P : KleinGlideBraidPacket B) :
    P.counterclockwise = P.clockwise⁻¹ :=
  P.glideRelation

/-- If a braid charge is not self-inverse, the two loop orientations are inequivalent. -/
theorem orientations_inequivalent_of_not_self_inverse (P : KleinGlideBraidPacket B)
    (h : P.clockwise⁻¹ ≠ P.clockwise) : P.counterclockwise ≠ P.clockwise := by
  rw [P.glideRelation]
  exact h

end KleinGlideBraidPacket

end InfoGeometry.Topology.NonorientableExceptionalKleinGlide

end noncomputable section

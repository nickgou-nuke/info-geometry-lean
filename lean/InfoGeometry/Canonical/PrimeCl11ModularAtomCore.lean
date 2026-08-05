import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.HodgeDiracLaplacianBridge

/-!
# InfoGeometry.Canonical.PrimeCl11ModularAtomCore

Mathlib-based local algebra for the `Cl(1,1)` prime atom.

This file proves the elementary Clifford/Majorana parity facts directly.

No Lee--Yang theorem.
No Hurwitz limit theorem.
No Clifford wavelet convergence claim.
No RH-level witness.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeCl11ModularAtomCore

open InfoGeometry.Canonical.HodgeDiracLaplacianBridge

variable {A : Type*} [Ring A]

/--
A local `Cl(1,1)` atom.

`c² = +1`, `d² = -1`, and `c d = - d c`.
-/
@[rep_depth operator]
structure Cl11Atom (A : Type*) [Ring A] where
  c : A
  d : A
  c_sq : c * c = 1
  d_sq : d * d = -1
  anticomm : c * d + d * c = 0

namespace Cl11Atom

variable (atom : Cl11Atom A)

/-- Local Möbius/Witten parity: the pseudoscalar `c d`. -/
@[rep_depth operator]
def mobiusParity : A :=
  atom.c * atom.d

/-- From `c d + d c = 0`, derive `d c = - c d`. -/
@[rep_depth operator]
theorem d_mul_c_eq_neg_c_mul_d :
    atom.d * atom.c = - (atom.c * atom.d) := by
  have h : atom.d * atom.c + atom.c * atom.d = 0 := by
    simpa [add_comm] using atom.anticomm
  exact eq_neg_of_add_eq_zero_left h

/--
The local Möbius/Witten parity is an involution:

`(c d)² = 1`.
-/
@[rep_depth operator]
theorem mobiusParity_sq_eq_one :
    atom.mobiusParity * atom.mobiusParity = 1 := by
  have hdc : atom.d * atom.c = - (atom.c * atom.d) :=
    atom.d_mul_c_eq_neg_c_mul_d
  unfold mobiusParity
  calc
    (atom.c * atom.d) * (atom.c * atom.d)
        = atom.c * (atom.d * atom.c) * atom.d := by
            noncomm_ring
    _ = atom.c * (-(atom.c * atom.d)) * atom.d := by
            rw [hdc]
    _ = - ((atom.c * atom.c) * (atom.d * atom.d)) := by
            noncomm_ring
    _ = - (1 * (-1)) := by
            rw [atom.c_sq, atom.d_sq]
    _ = 1 := by simp

/-- Left multiplication by local Möbius parity is its own inverse. -/
@[rep_depth operator]
theorem mobiusParity_left_involutive (x : A) :
    atom.mobiusParity * (atom.mobiusParity * x) = x := by
  calc
    atom.mobiusParity * (atom.mobiusParity * x)
        = (atom.mobiusParity * atom.mobiusParity) * x := by
            rw [mul_assoc]
    _ = 1 * x := by
            rw [atom.mobiusParity_sq_eq_one]
    _ = x := by simp

/-- Right multiplication by local Möbius parity is its own inverse. -/
@[rep_depth operator]
theorem mobiusParity_right_involutive (x : A) :
    (x * atom.mobiusParity) * atom.mobiusParity = x := by
  calc
    (x * atom.mobiusParity) * atom.mobiusParity
        = x * (atom.mobiusParity * atom.mobiusParity) := by
            rw [mul_assoc]
    _ = x * 1 := by
            rw [atom.mobiusParity_sq_eq_one]
    _ = x := by simp

/-! ## Hodge--Dirac readout of the local prime atom -/

/-- The `c` generator is odd for the local Möbius/Witten parity axis. -/
@[rep_depth operator]
theorem c_anticommutes_mobiusParity :
    atom.c * atom.mobiusParity = -(atom.mobiusParity * atom.c) := by
  have hdc : atom.d * atom.c = - (atom.c * atom.d) :=
    atom.d_mul_c_eq_neg_c_mul_d
  have hpc : (atom.c * atom.d) * atom.c = -atom.d := by
    calc
      (atom.c * atom.d) * atom.c = atom.c * (atom.d * atom.c) := by
        rw [mul_assoc]
      _ = atom.c * (-(atom.c * atom.d)) := by
        rw [hdc]
      _ = -((atom.c * atom.c) * atom.d) := by
        noncomm_ring
      _ = -(1 * atom.d) := by
        rw [atom.c_sq]
      _ = -atom.d := by
        simp
  unfold mobiusParity
  calc
    atom.c * (atom.c * atom.d) = (atom.c * atom.c) * atom.d := by
      rw [mul_assoc]
    _ = 1 * atom.d := by
      rw [atom.c_sq]
    _ = atom.d := by
      simp
    _ = -((atom.c * atom.d) * atom.c) := by
      rw [hpc]
      simp

/-- The `d` generator is odd for the local Möbius/Witten parity axis. -/
@[rep_depth operator]
theorem d_anticommutes_mobiusParity :
    atom.d * atom.mobiusParity = -(atom.mobiusParity * atom.d) := by
  have hdc : atom.d * atom.c = - (atom.c * atom.d) :=
    atom.d_mul_c_eq_neg_c_mul_d
  unfold mobiusParity
  calc
    atom.d * (atom.c * atom.d) = (atom.d * atom.c) * atom.d := by
      rw [mul_assoc]
    _ = (-(atom.c * atom.d)) * atom.d := by
      rw [hdc]
    _ = -((atom.c * atom.d) * atom.d) := by
      simp

/-- Hodge--Dirac carrier obtained by reading `c` as the odd Dirac generator. -/
@[rep_depth operator]
def hodgeDiracCarrierFromC : HodgeDiracLaplacianCarrier A :=
  (atom.mobiusParity, atom.c, atom.c * atom.c, atom.mobiusParity)

/-- Hodge--Dirac carrier obtained by reading `d` as the odd Dirac generator. -/
@[rep_depth operator]
def hodgeDiracCarrierFromD : HodgeDiracLaplacianCarrier A :=
  (atom.mobiusParity, atom.d, atom.d * atom.d, atom.mobiusParity)

/-- Carrier-level readback: `c` anticommutes with the supplied parity/Hodge axis. -/
@[rep_depth operator]
theorem hodgeDiracCarrierFromC_chiral :
    IsDiracHodgeChiral atom.hodgeDiracCarrierFromC :=
  atom.c_anticommutes_mobiusParity

/-- Carrier-level readback: `d` anticommutes with the supplied parity/Hodge axis. -/
@[rep_depth operator]
theorem hodgeDiracCarrierFromD_chiral :
    IsDiracHodgeChiral atom.hodgeDiracCarrierFromD :=
  atom.d_anticommutes_mobiusParity

/-- Carrier-level readback: the `c`-Laplacian is the square of the `c` Dirac operator. -/
@[rep_depth operator]
theorem hodgeDiracCarrierFromC_laplacian_from_dirac :
    IsLaplacianFromDirac atom.hodgeDiracCarrierFromC :=
  rfl

/-- Carrier-level readback: the `d`-Laplacian is the square of the `d` Dirac operator. -/
@[rep_depth operator]
theorem hodgeDiracCarrierFromD_laplacian_from_dirac :
    IsLaplacianFromDirac atom.hodgeDiracCarrierFromD :=
  rfl

/-- The `c`-Dirac square is even for the local Möbius/Witten parity axis. -/
@[rep_depth operator]
theorem c_laplacian_commutes_mobiusParity :
    (atom.c * atom.c) * atom.mobiusParity =
      atom.mobiusParity * (atom.c * atom.c) := by
  simpa [hodgeDiracCarrierFromC] using
    laplacian_commutes_hodge_of_dirac_closure
      atom.hodgeDiracCarrierFromC
      atom.hodgeDiracCarrierFromC_chiral
      atom.hodgeDiracCarrierFromC_laplacian_from_dirac

/-- The `d`-Dirac square is even for the local Möbius/Witten parity axis. -/
@[rep_depth operator]
theorem d_laplacian_commutes_mobiusParity :
    (atom.d * atom.d) * atom.mobiusParity =
      atom.mobiusParity * (atom.d * atom.d) := by
  simpa [hodgeDiracCarrierFromD] using
    laplacian_commutes_hodge_of_dirac_closure
      atom.hodgeDiracCarrierFromD
      atom.hodgeDiracCarrierFromD_chiral
      atom.hodgeDiracCarrierFromD_laplacian_from_dirac

end Cl11Atom


/-! ## Reciprocal-zero algebra -/

/--
If a nonvanishing factor `R` multiplies `Z`, then zeros of `R * Z`
are zeros of `Z`.
-/
@[rep_depth operator]
theorem zero_of_nonzero_mul_zero
    {R Z : ℂ → ℂ}
    {z : ℂ}
    (hR : R z ≠ 0)
    (hz : R z * Z z = 0) :
    Z z = 0 := by
  exact (mul_eq_zero.mp hz).resolve_left hR

/--
A nonvanishing renormalization introduces no new zero-locus points.
-/
@[rep_depth operator]
theorem renormalized_zero_locus
    {R Z : ℂ → ℂ}
    {Locus : ℂ → Prop}
    (hR : ∀ z, R z ≠ 0)
    (hZ : ∀ z, Z z = 0 → Locus z) :
    ∀ z, R z * Z z = 0 → Locus z := by
  intro z hz
  exact hZ z (zero_of_nonzero_mul_zero (hR z) hz)


/-! ## Self-reciprocal zero pairing -/

/--
If a function is self-reciprocal, then a zero at `z` forces a zero at `z⁻¹`.
-/
@[rep_depth operator]
theorem zero_inv_of_selfReciprocal
    (F : ℂ → ℂ)
    (degree : ℕ)
    (hSelf : ∀ z : ℂ, z ≠ 0 → F z = z ^ degree * F z⁻¹)
    {z : ℂ}
    (hz : z ≠ 0)
    (hzero : F z = 0) :
    F z⁻¹ = 0 := by
  have hEq := hSelf z hz
  rw [hzero] at hEq
  have hmul : z ^ degree * F z⁻¹ = 0 := hEq.symm
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero degree hz)

/--
Self-reciprocal zero pairing, both directions.
-/
@[rep_depth operator]
theorem zero_inv_iff_of_selfReciprocal
    (F : ℂ → ℂ)
    (degree : ℕ)
    (hSelf : ∀ z : ℂ, z ≠ 0 → F z = z ^ degree * F z⁻¹)
    {z : ℂ}
    (hz : z ≠ 0) :
    F z⁻¹ = 0 ↔ F z = 0 := by
  constructor
  · intro hzeroInv
    have hzinv : z⁻¹ ≠ 0 := inv_ne_zero hz
    have hEq := hSelf z⁻¹ hzinv
    rw [hzeroInv] at hEq
    have hmul : (z⁻¹) ^ degree * F (z⁻¹)⁻¹ = 0 := hEq.symm
    have hF : F (z⁻¹)⁻¹ = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero degree hzinv)
    simpa using hF
  · intro hzero
    exact zero_inv_of_selfReciprocal F degree hSelf hz hzero


/-! ## Unit-circle boundary forcing -/

/--
If a function is zero-free inside and outside the unit circle, every zero lies
on the unit circle.
-/
@[rep_depth operator]
theorem zero_on_unitCircle_of_zeroFree_inside_outside
    (F : ℂ → ℂ)
    (hInside : ∀ z : ℂ, Complex.normSq z < 1 → F z ≠ 0)
    (hOutside : ∀ z : ℂ, 1 < Complex.normSq z → F z ≠ 0)
    {z : ℂ}
    (hz : F z = 0) :
    Complex.normSq z = 1 := by
  rcases lt_trichotomy (Complex.normSq z) 1 with hlt | heq | hgt
  · exact False.elim ((hInside z hlt) hz)
  · exact heq
  · exact False.elim ((hOutside z hgt) hz)


/-! ## Cayley critical-line algebra, in real coordinates -/

/--
Real-coordinate Cayley boundary identity.

For `s = σ + i t`, the equality

`|s|² = |1 - s|²`

is equivalent to `σ = 1/2`.
-/
@[rep_depth operator]
theorem cayley_unit_circle_real_reduction
    (σ t : ℝ) :
    σ ^ 2 + t ^ 2 = (1 - σ) ^ 2 + t ^ 2 ↔
      σ = (1 / 2 : ℝ) := by
  constructor
  · intro h
    nlinarith
  · intro h
    subst σ
    ring

@[rep_depth operator]
theorem critical_of_cayley_real_boundary
    {σ t : ℝ}
    (h : σ ^ 2 + t ^ 2 = (1 - σ) ^ 2 + t ^ 2) :
    σ = (1 / 2 : ℝ) :=
  (cayley_unit_circle_real_reduction σ t).mp h

@[rep_depth operator]
theorem cayley_real_boundary_of_critical
    {σ t : ℝ}
    (h : σ = (1 / 2 : ℝ)) :
    σ ^ 2 + t ^ 2 = (1 - σ) ^ 2 + t ^ 2 :=
  (cayley_unit_circle_real_reduction σ t).mpr h


/-! ## Shifted Riemann field -/

/-- `fieldRe(s) = Re(s) - 1/2`. -/
@[rep_depth operator]
def shiftedRiemannFieldRe (s : ℂ) : ℝ :=
  s.re - (1 / 2 : ℝ)

@[rep_depth operator]
theorem shiftedRiemannField_zero_iff_critical
    (s : ℂ) :
    shiftedRiemannFieldRe s = 0 ↔
      s.re = (1 / 2 : ℝ) := by
  unfold shiftedRiemannFieldRe
  constructor
  · intro h
    linarith
  · intro h
    linarith

end InfoGeometry.Canonical.PrimeCl11ModularAtomCore

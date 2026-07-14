import Mathlib
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.PrimeCloseNowProofs

Mathlib-based closure of the elementary sockets:

* Cayley critical-line algebra, in real coordinates.
* Ferromagnetic positivity of the prime Hopfield matrix.
* Nonvanishing renormalization preserves zero-location.
* Zero-free inside/outside regions force boundary location.

No Lee--Yang theorem, Hurwitz theorem, Clifford wavelet theorem, or RH-level
convergence claim is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace PrimeCloseNowProofs

/-! ## 1. Cayley critical-line algebra -/

/--
Real-coordinate Cayley unit-circle reduction.

For `s = σ + i t`, the condition

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

/--
The same statement in boundary-forcing form.
-/
@[rep_depth operator]
theorem critical_of_cayley_real_boundary
    {σ t : ℝ}
    (h : σ ^ 2 + t ^ 2 = (1 - σ) ^ 2 + t ^ 2) :
    σ = (1 / 2 : ℝ) :=
  (cayley_unit_circle_real_reduction σ t).mp h

/--
The critical line implies the Cayley unit-circle equality in real coordinates.
-/
@[rep_depth operator]
theorem cayley_real_boundary_of_critical
    {σ t : ℝ}
    (h : σ = (1 / 2 : ℝ)) :
    σ ^ 2 + t ^ 2 = (1 - σ) ^ 2 + t ^ 2 :=
  (cayley_unit_circle_real_reduction σ t).mpr h

/-! ## 1b. Real Cayley / Möbius inverse lemmas -/

/--
Left inverse for the real Cayley transform.

For

  C x = (1 + x) / (1 - x)

and

  C⁻¹ y = (y - 1) / (y + 1),

we have `C⁻¹ (C x) = x`, away from the pole `x = 1`.
-/
@[rep_depth operator]
theorem real_cayley_inverse_left
    (x : ℝ)
    (hx : x ≠ 1) :
    (((1 + x) / (1 - x) - 1) /
      (((1 + x) / (1 - x)) + 1)) = x := by
  have hx' : (1 - x : ℝ) ≠ 0 := by
    intro h
    apply hx
    linarith
  field_simp [hx']
  ring

/--
Right inverse for the real Cayley transform.

For

  C x = (1 + x) / (1 - x)

and

  C⁻¹ y = (y - 1) / (y + 1),

we have `C (C⁻¹ y) = y`, away from the pole `y = -1`.
-/
@[rep_depth operator]
theorem real_cayley_inverse_right
    (y : ℝ)
    (hy : y ≠ -1) :
    ((1 + ((y - 1) / (y + 1))) /
      (1 - ((y - 1) / (y + 1)))) = y := by
  have hy' : (y + 1 : ℝ) ≠ 0 := by
    intro h
    apply hy
    linarith
  field_simp [hy']
  ring

/-! ## 2. Ferromagnetic prime-chain matrix -/

/--
Finite prime-chain data.

The intended model is `ell i = log (p i)`, but the positivity of `ell` is
stored as data so this file proves the matrix positivity without importing
number-theoretic logarithm lemmas.
-/
@[rep_depth thermo]
structure FinitePrimeChainData (N : ℕ) where
  p : Fin N → ℕ
  prime : ∀ i, Nat.Prime (p i)
  ell : Fin N → ℝ
  ell_pos : ∀ i, 0 < ell i

namespace FinitePrimeChainData

variable {N : ℕ} (D : FinitePrimeChainData N)

/--
Rank-one Hopfield / Curie--Weiss prime coupling.

`Jᵢⱼ = λ/2 * ellᵢ * ellⱼ` off diagonal, and zero on the diagonal.
-/
@[rep_depth thermo]
def spinCoupling (lam : ℝ) (i j : Fin N) : ℝ :=
  if i = j then 0 else (lam / 2) * D.ell i * D.ell j

@[rep_depth thermo]
theorem spinCoupling_nonneg
    {lam : ℝ}
    (hLam : 0 ≤ lam)
    (i j : Fin N) :
    0 ≤ D.spinCoupling lam i j := by
  unfold spinCoupling
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]
    have hLam2 : 0 ≤ lam / 2 := by
      exact div_nonneg hLam (by norm_num)
    exact mul_nonneg
      (mul_nonneg hLam2 (le_of_lt (D.ell_pos i)))
      (le_of_lt (D.ell_pos j))

@[rep_depth thermo]
theorem spinCoupling_pos_of_ne
    {lam : ℝ}
    (hLam : 0 < lam)
    {i j : Fin N}
    (hij : i ≠ j) :
    0 < D.spinCoupling lam i j := by
  unfold spinCoupling
  simp [hij]
  have hLam2 : 0 < lam / 2 := by
    exact div_pos hLam (by norm_num)
  exact mul_pos
    (mul_pos hLam2 (D.ell_pos i))
    (D.ell_pos j)

end FinitePrimeChainData


/-! ## 3. Renormalization preserves zero location -/

/--
If `R z` is nonzero, then zeros of `R z * Z z` are zeros of `Z z`.
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
A nonvanishing renormalization cannot introduce off-locus zeros.
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


/-! ## 4. Zero-free inside/outside regions force boundary -/

/--
Abstract real-valued field coordinate. This is the proof skeleton used after
pulling local Lee--Yang fugacities back to the Riemann field coordinate.
-/
@[rep_depth operator]
structure RealFieldZeroFree where
  fieldRe : ℂ → ℝ
  F : ℂ → ℂ
  inner_zero_free :
    ∀ s : ℂ, 0 < fieldRe s → F s ≠ 0
  outer_zero_free :
    ∀ s : ℂ, fieldRe s < 0 → F s ≠ 0

namespace RealFieldZeroFree

/--
If a function is zero-free when `fieldRe > 0` and also zero-free when
`fieldRe < 0`, then every zero lies on `fieldRe = 0`.
-/
@[rep_depth operator]
theorem zero_forces_field_boundary
    (A : RealFieldZeroFree)
    {s : ℂ}
    (hz : A.F s = 0) :
    A.fieldRe s = 0 := by
  rcases lt_trichotomy (A.fieldRe s) 0 with hneg | hzero | hpos
  · exact False.elim ((A.outer_zero_free s hneg) hz)
  · exact hzero
  · exact False.elim ((A.inner_zero_free s hpos) hz)

end RealFieldZeroFree


/-! ## 5. Pullback boundary to the Riemann critical line -/

/--
A proof-carrying field coordinate whose zero boundary is the Riemann critical
line. This is not a witness for analytic convergence; it is only the algebraic
boundary map.
-/
@[rep_depth operator]
structure CriticalField where
  fieldRe : ℂ → ℝ
  field_zero_iff_critical :
    ∀ s : ℂ, fieldRe s = 0 ↔ s.re = (1 / 2 : ℝ)

namespace CriticalField

@[rep_depth operator]
theorem critical_of_field_zero
    (C : CriticalField)
    {s : ℂ}
    (h : C.fieldRe s = 0) :
    s.re = (1 / 2 : ℝ) :=
  (C.field_zero_iff_critical s).mp h

@[rep_depth operator]
theorem field_zero_of_critical
    (C : CriticalField)
    {s : ℂ}
    (h : s.re = (1 / 2 : ℝ)) :
    C.fieldRe s = 0 :=
  (C.field_zero_iff_critical s).mpr h

end CriticalField

/--
Combine zero-free inside/outside with the field-critical-line identification.
-/
@[rep_depth operator]
theorem zero_forces_critical_line
    (A : RealFieldZeroFree)
    (C : CriticalField)
    (hSame : ∀ s : ℂ, A.fieldRe s = C.fieldRe s)
    {s : ℂ}
    (hz : A.F s = 0) :
    s.re = (1 / 2 : ℝ) := by
  have hBoundaryA : A.fieldRe s = 0 :=
    A.zero_forces_field_boundary hz
  have hBoundaryC : C.fieldRe s = 0 := by
    simpa [hSame s] using hBoundaryA
  exact C.critical_of_field_zero hBoundaryC


/-! ## 6. Concrete shifted Riemann field -/

/--
The shifted Riemann field coordinate.

`fieldRe(s) = Re(s) - 1/2`.
-/
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

@[rep_depth operator]
def shiftedCriticalField : CriticalField where
  fieldRe := shiftedRiemannFieldRe
  field_zero_iff_critical := shiftedRiemannField_zero_iff_critical

end PrimeCloseNowProofs

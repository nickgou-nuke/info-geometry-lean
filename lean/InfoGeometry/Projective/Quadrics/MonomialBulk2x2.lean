import Mathlib.Tactic

set_option autoImplicit false

/-!
# InfoGeometry.Projective.Quadrics.MonomialBulk2x2

Finite coordinate readouts for a monomial-shaped boundary label mapped to a
`2×2` split-quadratic coordinate packet.

This file proves only elementary algebraic facts about the displayed map

`(coeff, exp) ↦ (t, x, z) = (coeff, exp, 0)`

and the quadratic readout `t² - x² - z²`.

No AdS/CFT theorem.
No holographic isomorphism.
No black-hole horizon theorem.
No proof-carrying witness class.
No axiom.
-/

namespace InfoGeometry.Projective.Quadrics.MonomialBulk2x2

/-- A two-coordinate monomial-style label. -/
structure MonomialLabel where
  coeff : ℝ
  exp : ℝ

/-- Scalar multiplication of a monomial-style label. -/
def smulMonomial (c : ℝ) (M : MonomialLabel) : MonomialLabel where
  coeff := c * M.coeff
  exp := c * M.exp

/-- Split `2×2` symmetric-coordinate packet with coordinates `(t,x,z)`. -/
structure SymmState2x2 (R : Type*) [CommRing R] where
  t : R
  x : R
  z : R

/-- Uniform scalar scaling of a split `2×2` coordinate packet. -/
def smulState {R : Type*} [CommRing R] (c : R) (S : SymmState2x2 R) : SymmState2x2 R where
  t := c * S.t
  x := c * S.x
  z := c * S.z

/-- The trace-style linear readout `2t`. -/
def trace2 {R : Type*} [CommRing R] (S : SymmState2x2 R) : R :=
  S.t + S.t

/-- The split quadratic determinant-style readout `t² - x² - z²`. -/
def det2 {R : Type*} [CommRing R] (S : SymmState2x2 R) : R :=
  S.t * S.t - S.x * S.x - S.z * S.z

/-- The finite coordinate map `(coeff, exp) ↦ (coeff, exp, 0)`. -/
def monomialToState (M : MonomialLabel) : SymmState2x2 ℝ where
  t := M.coeff
  x := M.exp
  z := 0

/-- The coordinate map intertwines scalar multiplication. -/
theorem monomialToState_smul (c : ℝ) (M : MonomialLabel) :
    monomialToState (smulMonomial c M) = smulState c (monomialToState M) := by
  cases M
  unfold monomialToState smulMonomial smulState
  congr
  ring

/-- The trace-style readout of the mapped label is `2 * coeff`. -/
theorem trace2_monomialToState (M : MonomialLabel) :
    trace2 (monomialToState M) = 2 * M.coeff := by
  unfold trace2 monomialToState
  ring

/-- The determinant-style readout of the mapped label is `coeff² - exp²`. -/
theorem det2_monomialToState (M : MonomialLabel) :
    det2 (monomialToState M) = M.coeff ^ 2 - M.exp ^ 2 := by
  unfold det2 monomialToState
  ring

/-- The trace-style readout scales linearly under uniform state scaling. -/
theorem trace2_smul {R : Type*} [CommRing R] (c : R) (S : SymmState2x2 R) :
    trace2 (smulState c S) = c * trace2 S := by
  unfold trace2 smulState
  ring

/-- The determinant-style readout scales quadratically under uniform state scaling. -/
theorem det2_smul {R : Type*} [CommRing R] (c : R) (S : SymmState2x2 R) :
    det2 (smulState c S) = c ^ 2 * det2 S := by
  unfold det2 smulState
  ring

/-- The determinant-style readout vanishes when `coeff² = exp²`. -/
theorem det2_monomialToState_eq_zero_of_sq_eq
    (M : MonomialLabel) (h : M.coeff ^ 2 = M.exp ^ 2) :
    det2 (monomialToState M) = 0 := by
  rw [det2_monomialToState, h]
  ring

/-- The determinant-style readout vanishes on the line `coeff = exp`. -/
theorem det2_monomialToState_eq_zero_of_coeff_eq_exp
    (M : MonomialLabel) (h : M.coeff = M.exp) :
    det2 (monomialToState M) = 0 := by
  apply det2_monomialToState_eq_zero_of_sq_eq
  rw [h]

/-- The determinant-style readout vanishes on the line `coeff = -exp`. -/
theorem det2_monomialToState_eq_zero_of_coeff_eq_neg_exp
    (M : MonomialLabel) (h : M.coeff = -M.exp) :
    det2 (monomialToState M) = 0 := by
  apply det2_monomialToState_eq_zero_of_sq_eq
  rw [h]
  ring

/-- If both displayed coordinates vanish, the mapped packet is null. -/
theorem det2_monomialToState_eq_zero_of_coeff_eq_zero_of_exp_eq_zero
    (M : MonomialLabel) (hcoeff : M.coeff = 0) (hexp : M.exp = 0) :
    det2 (monomialToState M) = 0 := by
  rw [det2_monomialToState, hcoeff, hexp]
  ring

/-- Vanishing of `coeff` alone is not enough to force the mapped packet to be null. -/
theorem coeff_zero_not_sufficient_for_det2_zero :
    ∃ M : MonomialLabel, M.coeff = 0 ∧ det2 (monomialToState M) ≠ 0 := by
  refine ⟨{ coeff := 0, exp := 1 }, rfl, ?_⟩
  rw [det2_monomialToState]
  norm_num

/-!
Closed finite algebra in this file:

* `monomialToState_smul`
* `trace2_monomialToState`
* `det2_monomialToState`
* `trace2_smul`
* `det2_smul`
* null criteria from explicit equations on the two coordinates
* `coeff_zero_not_sufficient_for_det2_zero`

Open closure debt, deliberately not encoded as declarations:

* any AdS/CFT or holographic dictionary theorem;
* any isomorphism between bulk and boundary algebras;
* any black-hole horizon or nilpotent-orbit interpretation.
-/

end InfoGeometry.Projective.Quadrics.MonomialBulk2x2

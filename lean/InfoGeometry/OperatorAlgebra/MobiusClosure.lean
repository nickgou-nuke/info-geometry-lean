/-
InfoGeometry/OperatorAlgebra/MobiusClosure.lean

Projective survivors of a Möbius/closure inversion.

This module is deliberately small.  It formalizes the statement:

  the affine representative may change, but the projective ray survives when
  `I x = λ • x` for some nonzero scalar `λ`.

It does not identify the survivor with a center, horizon, winding number,
natural cone, BPS charge, or any other model-specific invariant.  Those
identifications require separate witness structures.
-/

import Mathlib

noncomputable section

namespace MobiusClosure

/--
A linear Möbius/closure inversion on an ambient carrier.

The null cone is an abstract admissible cone; concrete conformal models may
instantiate it as an ambient projective light cone.
-/
structure MobiusInversionDatum
    (W : Type*) [AddCommGroup W] [Module ℝ W] where
  /-- Linear inversion/chart swap. -/
  inv : W →ₗ[ℝ] W

  /-- Involution law. -/
  inv_sq :
    ∀ x : W, inv (inv x) = x

  /-- Null cone or admissible projective cone. -/
  nullCone : Set W

  /-- The inversion preserves the null cone. -/
  preserves_null :
    ∀ x : W, x ∈ nullCone → inv x ∈ nullCone

namespace MobiusInversionDatum

variable
    {W : Type*} [AddCommGroup W] [Module ℝ W]

variable (I : MobiusInversionDatum W)

/--
The inversion also reflects nullness backwards.

This follows from involutivity, so null-cone preservation is reversible along
inversion orbits.
-/
theorem preserves_null_reverse
    {x : W}
    (hx : I.inv x ∈ I.nullCone) :
    x ∈ I.nullCone := by
  have h := I.preserves_null (I.inv x) hx
  simpa [I.inv_sq x] using h

/--
Projective fixedness of a nonzero null vector.

This says the ray `[x]` is fixed, not necessarily the vector representative
`x` itself.
-/
def IsProjectiveFixed
    (x : W) : Prop :=
  x ≠ 0 ∧
    x ∈ I.nullCone ∧
      ∃ c : ℝ, c ≠ 0 ∧ I.inv x = c • x

/-- A readout is projective when it ignores nonzero scalar rescaling. -/
def IsProjectiveReadout
    {α : Type*}
    (read : W → α) : Prop :=
  ∀ (c : ℝ) (x : W), c ≠ 0 → read (c • x) = read x

/-- A readout is Möbius-invariant on the null cone. -/
def IsMobiusInvariantReadout
    {α : Type*}
    (read : W → α) : Prop :=
  ∀ x : W, x ∈ I.nullCone → read (I.inv x) = read x

/-- The fixed linear subspace predicate for the inversion. -/
def IsFixedVector
    (x : W) : Prop :=
  I.inv x = x

/-- The anti-fixed linear subspace predicate for the inversion. -/
def IsAntiFixedVector
    (x : W) : Prop :=
  I.inv x = -x

/-- A strictly fixed nonzero null vector gives a projectively fixed ray. -/
theorem projectiveFixed_of_fixed
    {x : W}
    (hx0 : x ≠ 0)
    (hxnull : x ∈ I.nullCone)
    (hfix : I.IsFixedVector x) :
    I.IsProjectiveFixed x := by
  refine ⟨hx0, hxnull, 1, one_ne_zero, ?_⟩
  simpa [IsFixedVector] using hfix

/-- An anti-fixed nonzero null vector also gives a projectively fixed ray. -/
theorem projectiveFixed_of_antiFixed
    {x : W}
    (hx0 : x ≠ 0)
    (hxnull : x ∈ I.nullCone)
    (hfix : I.IsAntiFixedVector x) :
    I.IsProjectiveFixed x := by
  refine ⟨hx0, hxnull, -1, by norm_num, ?_⟩
  simpa [IsAntiFixedVector] using hfix

/-- The inverted representative of a projectively fixed ray is projectively fixed. -/
theorem inv_projectiveFixed
    {x : W}
    (hfix : I.IsProjectiveFixed x) :
    I.IsProjectiveFixed (I.inv x) := by
  rcases hfix with ⟨hx0, hxnull, c, hc, hscale⟩
  have hinv0 : I.inv x ≠ 0 := by
    intro hzero
    apply hx0
    have h := congrArg I.inv hzero
    simpa [I.inv_sq x] using h
  refine ⟨hinv0, I.preserves_null x hxnull, c⁻¹, inv_ne_zero hc, ?_⟩
  have hx : x = c⁻¹ • I.inv x := by
    rw [hscale]
    simp [hc]
  simpa [I.inv_sq x] using hx

/--
For a nonzero projectively fixed representative, the projective scale squares
to one.

This is the algebraic content of `I² = 1` on projectively fixed rays.
-/
theorem scale_sq_eq_one_of_projectiveFixed_scale
    [NoZeroSMulDivisors ℝ W]
    {x : W}
    {c : ℝ}
    (hx0 : x ≠ 0)
    (hscale : I.inv x = c • x) :
    c ^ 2 = 1 := by
  have happly : x = (c ^ 2) • x := by
    calc
      x = I.inv (I.inv x) := (I.inv_sq x).symm
      _ = I.inv (c • x) := by rw [hscale]
      _ = c • I.inv x := by simp
      _ = c • (c • x) := by rw [hscale]
      _ = (c ^ 2) • x := by
          simpa [pow_two] using (smul_smul c c x)
  have hzero : (c ^ 2 - 1) • x = 0 := by
    have hsub : (c ^ 2) • x - (1 : ℝ) • x = 0 := by
      rw [one_smul]
      exact sub_eq_zero.mpr happly.symm
    simpa [sub_smul] using hsub
  rcases smul_eq_zero.mp hzero with hcoef | hx
  · exact sub_eq_zero.mp hcoef
  · exact (hx0 hx).elim

/-- The projective fixed scale is either `1` or `-1`. -/
theorem scale_eq_one_or_neg_one_of_projectiveFixed_scale
    [NoZeroSMulDivisors ℝ W]
    {x : W}
    {c : ℝ}
    (hx0 : x ≠ 0)
    (hscale : I.inv x = c • x) :
    c = 1 ∨ c = -1 := by
  have hsquare :
      c ^ 2 = 1 :=
    I.scale_sq_eq_one_of_projectiveFixed_scale hx0 hscale
  have hfactor : (c - 1) * (c + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · left
    linarith
  · right
    linarith

/--
A nonzero projectively fixed vector is represented by either a fixed vector or
an anti-fixed vector.

This is the Lean form of:

`projective fixed = fixed ∪ anti-fixed`

at the level of a chosen nonzero representative.
-/
theorem projectiveFixed_fixed_or_antiFixed
    [NoZeroSMulDivisors ℝ W]
    {x : W}
    (hfix : I.IsProjectiveFixed x) :
    I.IsFixedVector x ∨ I.IsAntiFixedVector x := by
  rcases hfix with ⟨hx0, _hxnull, c, _hc, hscale⟩
  rcases I.scale_eq_one_or_neg_one_of_projectiveFixed_scale hx0 hscale with hc | hc
  · left
    simpa [IsFixedVector, hc] using hscale
  · right
    simpa [IsAntiFixedVector, hc] using hscale

/-- Projective readouts are unchanged on projectively fixed rays. -/
theorem readout_eq_on_projectiveFixed
    {α : Type*}
    {read : W → α}
    (hread : IsProjectiveReadout read)
    {x : W}
    (hfix : I.IsProjectiveFixed x) :
    read (I.inv x) = read x := by
  rcases hfix with ⟨_hx0, _hxnull, c, hc, hIx⟩
  rw [hIx]
  exact hread c x hc

/-- Möbius-invariant readouts survive inversion on null data. -/
theorem invariantReadout_inv_eq
    {α : Type*}
    {read : W → α}
    (hread : I.IsMobiusInvariantReadout read)
    {x : W}
    (hx : x ∈ I.nullCone) :
    read (I.inv x) = read x :=
  hread x hx

/--
The paired readout that remembers both chart representatives.

This is the formal socket for symmetrized visible/hidden memory accounting:
under inversion, the two components swap.
-/
def symmetrizedReadout
    {α : Type*}
    (read : W → α)
    (x : W) : α × α :=
  (read x, read (I.inv x))

/-- Möbius inversion swaps the two entries of the symmetrized readout. -/
theorem symmetrizedReadout_inv
    {α : Type*}
    (read : W → α)
    (x : W) :
    I.symmetrizedReadout read (I.inv x) =
      (read (I.inv x), read x) := by
  simp [symmetrizedReadout, I.inv_sq x]

end MobiusInversionDatum

end MobiusClosure

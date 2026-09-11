import InfoGeometry.Projective.SplitOctonions.ZornMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Octonionic Projective Line: Local Associator Lemmas

This module records conservative algebraic pieces behind Lemma 4.5.2 from
Konrad Voelkel's thesis, *Motivic Cell Structures for Projective Spaces over
Split Quaternions*.

The file proves only Zorn-coordinate associator vanishings available from the
current repository substrate:

- the residual `b` component in the first case of Lemma 4.5.2 vanishes when
  either participating `v^{21}` component is zero;
- diagonal right and left factors associate by the already-proved Zorn diagonal
  associativity lemmas;
- the source-shaped factor `(v_j * x)^*` has the coordinate needed by the
  simplified associator lemma when `x` is a half-inverter and `v_j^{21}=0`.

It defines a conservative projective-shell quotient model for `OP1`, but does
  not prove the full motivic equivalence theorem for `OP1`.

## Audit buckets

### Closed finite theorem surface

- `lemma452ResidualB_eq_zero_of_left_v21_zero`
- `lemma452ResidualB_eq_zero_of_right_v21_zero`
- `lemma452_first_case_residual_vanishes`
- `lemma452_first_case_residual_vanishes_of_half_inverter`
- `associator_vanishes_right_diag`
- `associator_vanishes_left_diag`
- `associator_vanishes_of_half_inverter`
- `star_mul_half_inverter_right_x21_zero`
- `associator_vanishes_of_half_inverter_star_mul`
- `associator_vanishes_of_half_inverter_star_mul_of_second_half`
- `associator_vanishes_of_half_inverter_star_mul_of_first_half`
- `lemma_4_5_2_exact`
- `associator_vanishes_star_mul_left_diag`
- `associator_vanishes_of_half_inverter_star_mul_diag`
- `mkOP1_eq_scale`

### Conditional theorem surface from explicit hypotheses

- The associator results depend on explicit coordinate hypotheses such as
  `is_half_inverter x`, `is_half_inverter vi ∨ is_half_inverter vj`, or
  zero lower-left coordinates.
- The local projective-shell quotient is a reduced Zorn-coordinate carrier,
  not a global OP1 motivic construction.

## Open closure debt

- Transport from these local associator lemmas to a full `OP1` chart-gluing
  theorem.
- The full motivic equivalence theorem for `OP1`.
- Any comparison between this reduced Zorn product and Voelkel's full
  split-octonion algebra with cross-product conventions.
-/

namespace InfoGeometry.Projective.SplitOctonions.ZornMatrix

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable (B : V →ₗ[R] V →ₗ[R] R)

/-! ## Local associator packet -/

/--
The associator `[x, y, z] = (xy)z - x(yz)` for the reduced Zorn product
available in `ZornMatrix.lean`.
-/
def associator (x y z : ZornMatrix R V) : ZornMatrix R V where
  x11 := (mul B (mul B x y) z).x11 - (mul B x (mul B y z)).x11
  x12 := (mul B (mul B x y) z).x12 - (mul B x (mul B y z)).x12
  x21 := (mul B (mul B x y) z).x21 - (mul B x (mul B y z)).x21
  x22 := (mul B (mul B x y) z).x22 - (mul B x (mul B y z)).x22

/-- Coordinate condition used for the local Lemma 4.5.2 calculations. -/
def is_half_inverter (x : ZornMatrix R V) : Prop :=
  x.x11 = 1 ∧ x.x12 = 1 ∧ x.x21 = 0

/--
Residual vector component from Voelkel's Computation 4.5.1:
`b = vj21 * (vi21 · x22) - vi21 * (vj21 · x22)`.
-/
def lemma452ResidualB (vi vj x : ZornMatrix R V) : V :=
  (B vi.x21 x.x22) • vj.x21 - (B vj.x21 x.x22) • vi.x21

/-- The residual `b` component vanishes if the first `v^{21}` component is zero. -/
theorem lemma452ResidualB_eq_zero_of_left_v21_zero
    (vi vj x : ZornMatrix R V) (hvi : vi.x21 = 0) :
    lemma452ResidualB B vi vj x = 0 := by
  simp [lemma452ResidualB, hvi]

/-- The residual `b` component vanishes if the second `v^{21}` component is zero. -/
theorem lemma452ResidualB_eq_zero_of_right_v21_zero
    (vi vj x : ZornMatrix R V) (hvj : vj.x21 = 0) :
    lemma452ResidualB B vi vj x = 0 := by
  simp [lemma452ResidualB, hvj]

/--
First-case residual of Voelkel Lemma 4.5.2.

This is the reduced vector term after the `half(x)=e_1` coordinate reduction.
-/
theorem lemma452_first_case_residual_vanishes
    (vi vj x : ZornMatrix R V)
    (hzero : vi.x21 = 0 ∨ vj.x21 = 0) :
    lemma452ResidualB B vi vj x = 0 := by
  cases hzero with
  | inl hvi => exact lemma452ResidualB_eq_zero_of_left_v21_zero (B := B) vi vj x hvi
  | inr hvj => exact lemma452ResidualB_eq_zero_of_right_v21_zero (B := B) vi vj x hvj

/--
First-case residual vanishing under the half-inverter hypotheses appearing in
Voelkel Lemma 4.5.2.
-/
theorem lemma452_first_case_residual_vanishes_of_half_inverter
    (vi vj x : ZornMatrix R V)
    (_hx : is_half_inverter x)
    (hhalf : is_half_inverter vi ∨ is_half_inverter vj) :
    lemma452ResidualB B vi vj x = 0 := by
  apply lemma452_first_case_residual_vanishes
  cases hhalf with
  | inl hvi => exact Or.inl hvi.2.2
  | inr hvj => exact Or.inr hvj.2.2

/-- Diagonal right factors associate by the existing Zorn diagonal lemma. -/
theorem associator_vanishes_right_diag
    (v x : ZornMatrix R V) (α β : R) :
    associator B v x (diag α β) = diag 0 0 := by
  have h := diag_assoc_right (B := B) v x α β
  ext
  · simpa [associator, diag] using sub_eq_zero.mpr (congrArg ZornMatrix.x11 h)
  · simpa [associator, diag] using sub_eq_zero.mpr (congrArg ZornMatrix.x12 h)
  · simpa [associator, diag] using sub_eq_zero.mpr (congrArg ZornMatrix.x21 h)
  · simpa [associator, diag] using sub_eq_zero.mpr (congrArg ZornMatrix.x22 h)

/-- Diagonal left factors associate by the existing Zorn diagonal lemma. -/
theorem associator_vanishes_left_diag
    (x y : ZornMatrix R V) (α β : R) :
    associator B (diag α β) x y = diag 0 0 := by
  have h := diag_assoc_left (B := B) x y α β
  ext
  · simpa [associator, diag] using sub_eq_zero.mpr (congrArg ZornMatrix.x11 h)
  · simpa [associator, diag] using sub_eq_zero.mpr (congrArg ZornMatrix.x12 h)
  · simpa [associator, diag] using sub_eq_zero.mpr (congrArg ZornMatrix.x21 h)
  · simpa [associator, diag] using sub_eq_zero.mpr (congrArg ZornMatrix.x22 h)

/--
If `x` is a local half-inverter and `w.x21 = 0`, then the reduced associator
`[v,x,w]` vanishes.
-/
theorem associator_vanishes_of_half_inverter
    (v x w : ZornMatrix R V)
    (hx : is_half_inverter x)
    (hw : w.x21 = 0) :
    associator B v x w = diag 0 0 := by
  ext <;> (
    dsimp [associator, mul, diag]
    simp [hx.1, hx.2.1, hx.2.2, hw, map_zero, mul_comm]
    try ring
    try module
  )

/--
If `x` satisfies the half-inverter coordinate condition and `v` has zero
lower-left vector coordinate, then the thesis-shaped factor `(v * x)^*` also
has zero lower-left vector coordinate.
-/
theorem star_mul_half_inverter_right_x21_zero
    (v x : ZornMatrix R V)
    (hx : is_half_inverter x)
    (hv : v.x21 = 0) :
    (star (mul B v x)).x21 = 0 := by
  dsimp [star, mul]
  simp [hx.2.1, hx.2.2, hv]

/--
Source-shaped specialization of `associator_vanishes_of_half_inverter`.
This matches the local form `[v_i, x, (v_j * x)^*] = 0` under the explicit
half-inverter condition on `x` and the lower-left coordinate condition on
`v_j`.
-/
theorem associator_vanishes_of_half_inverter_star_mul
    (vi vj x : ZornMatrix R V)
    (hx : is_half_inverter x)
    (hvj : vj.x21 = 0) :
    associator B vi x (star (mul B vj x)) = diag 0 0 :=
  associator_vanishes_of_half_inverter B vi x (star (mul B vj x)) hx
    (star_mul_half_inverter_right_x21_zero B vj x hx hvj)

/-- Source-shaped theorem when the second participant is a half-inverter. -/
theorem associator_vanishes_of_half_inverter_star_mul_of_second_half
    (vi vj x : ZornMatrix R V)
    (hx : is_half_inverter x)
    (hvj : is_half_inverter vj) :
    associator B vi x (star (mul B vj x)) = diag 0 0 :=
  associator_vanishes_of_half_inverter_star_mul B vi vj x hx hvj.2.2

/-- Source-shaped theorem when the first participant is a half-inverter. -/
theorem associator_vanishes_of_half_inverter_star_mul_of_first_half
    (vi vj x : ZornMatrix R V)
    (hx : is_half_inverter x)
    (hvi : is_half_inverter vi) :
    associator B vi x (star (mul B vj x)) = diag 0 0 := by
  ext <;> (
    dsimp [associator, mul, star, diag]
    simp [hx.1, hx.2.1, hx.2.2, hvi.2.2, map_zero, map_neg, mul_comm]
    try ring
    try module
  )

/--
Exact reduced-coordinate form of Voelkel Lemma 4.5.2 under the first-case
half-inverter hypotheses.
-/
theorem lemma_4_5_2_exact
    (vi vj x : ZornMatrix R V)
    (hx : is_half_inverter x)
    (hhalf : is_half_inverter vi ∨ is_half_inverter vj) :
    associator B vi x (star (mul B vj x)) = diag 0 0 := by
  cases hhalf with
  | inl hvi => exact associator_vanishes_of_half_inverter_star_mul_of_first_half B vi vj x hx hvi
  | inr hvj => exact associator_vanishes_of_half_inverter_star_mul_of_second_half B vi vj x hx hvj

/-- Source-shaped diagonal-left case from Voelkel's diagonal associativity branch. -/
theorem associator_vanishes_star_mul_left_diag
    (vj x : ZornMatrix R V) (α β : R) :
    associator B (diag α β) x (star (mul B vj x)) = diag 0 0 :=
  associator_vanishes_left_diag B x (star (mul B vj x)) α β

/-- Diagonal specialization of the source-shaped associator-vanishing lemma. -/
theorem associator_vanishes_of_half_inverter_star_mul_diag
    (vi x : ZornMatrix R V)
    (α β : R)
    (hx : is_half_inverter x) :
    associator B vi x (star (mul B (diag α β) x)) = diag 0 0 :=
  associator_vanishes_of_half_inverter_star_mul B vi (diag α β) x hx rfl

/-! ## Projective-shell carrier -/

/-- Unit scalar scaling on reduced Zorn matrices. -/
def unitScale (u : Rˣ) (x : ZornMatrix R V) : ZornMatrix R V where
  x11 := (u : R) * x.x11
  x12 := (u : R) * x.x12
  x21 := (u : R) • x.x21
  x22 := (u : R) • x.x22

@[simp] theorem unitScale_one (x : ZornMatrix R V) : unitScale (1 : Rˣ) x = x := by
  cases x with
  | mk a b c d => simp [unitScale]

@[simp] theorem unitScale_mul (u v : Rˣ) (x : ZornMatrix R V) :
    unitScale (u * v) x = unitScale u (unitScale v x) := by
  ext <;> simp [unitScale, smul_smul, mul_left_comm, mul_comm]

@[simp] theorem unitScale_inv (u : Rˣ) (x : ZornMatrix R V) :
    unitScale (u⁻¹) (unitScale u x) = x := by
  cases x with
  | mk a b c d => ext <;> simp [unitScale, smul_smul, mul_comm]

@[simp] theorem unitScale_zero (u : Rˣ) : unitScale u (0 : ZornMatrix R V) = 0 := by
  ext
  · change (u : R) * (0 : R) = (0 : R)
    simp
  · change (u : R) * (0 : R) = (0 : R)
    simp
  · change (u : R) • (0 : V) = (0 : V)
    simp
  · change (u : R) • (0 : V) = (0 : V)
    simp

/-- Boundary norm used for the local OP¹ shell. -/
abbrev octonionicBoundaryNorm (x : ZornMatrix R V) : R :=
  norm (B := B) x

lemma octonionicBoundaryNorm_scale (u : Rˣ) (x : ZornMatrix R V) :
    octonionicBoundaryNorm (B := B) (unitScale u x)
      = ((u : R) ^ 2) * octonionicBoundaryNorm (B := B) x := by
  unfold octonionicBoundaryNorm
  simp [norm, unitScale, map_smul, smul_eq_mul, mul_add, mul_assoc, mul_left_comm, mul_comm]
  ring

lemma octonionicBoundaryNorm_scale_eq_zero_iff (u : Rˣ) (x : ZornMatrix R V) :
    octonionicBoundaryNorm (B := B) (unitScale u x) = 0 ↔
      octonionicBoundaryNorm (B := B) x = 0 := by
  rw [octonionicBoundaryNorm_scale]
  constructor
  · intro h
    let iu : R := (↑(u⁻¹ : Rˣ) : R)
    have h1 := congrArg (fun z => iu * z) h
    have h1' : (u : R) * octonionicBoundaryNorm (B := B) x = 0 := by
      simpa [iu, pow_two, mul_assoc, mul_left_comm, mul_comm] using h1
    have h2 := congrArg (fun z => iu * z) h1'
    simpa [iu, mul_assoc, mul_left_comm, mul_comm] using h2
  · intro h
    rw [h]
    simp

/--
A concrete nonzero representative for the local OP¹ quotient.
-/
structure OP1Representative where
  rep : ZornMatrix R V
  boundary : octonionicBoundaryNorm (B := B) rep = 0
  nonzero : rep ≠ 0

/-- Unit scaling on OP¹ representatives. -/
def OP1RepScale (u : Rˣ)
    (x : OP1Representative (B := B)) :
    OP1Representative (B := B) where
  rep := unitScale u x.rep
  boundary := (octonionicBoundaryNorm_scale_eq_zero_iff (B := B) u x.rep).2 x.boundary
  nonzero := by
    intro h
    apply x.nonzero
    have h' := congrArg (fun z => unitScale (u⁻¹) z) h
    simpa [unitScale_mul, unitScale_zero, unitScale_inv] using h'

/-- Projective scale relation on representatives. -/
def OP1RayRel (x y : OP1Representative (B := B)) : Prop :=
  ∃ u : Rˣ, unitScale u x.rep = y.rep

instance op1Setoid : Setoid (OP1Representative (B := B)) where
  r := OP1RayRel (B := B)
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro X
      exact ⟨1, by simp⟩
    · intro X Y hXY
      rcases hXY with ⟨u, huv⟩
      refine ⟨u⁻¹, ?_⟩
      calc
        unitScale (u⁻¹) Y.rep = unitScale (u⁻¹) (unitScale u X.rep) := by
          rw [← huv]
        _ = X.rep := by simp
    · intro X Y Z hXY hYZ
      rcases hXY with ⟨u, huv⟩
      rcases hYZ with ⟨v, hvz⟩
      refine ⟨v * u, ?_⟩
      calc
        unitScale (v * u) X.rep = unitScale v (unitScale u X.rep) := by
          simp [unitScale_mul]
        _ = unitScale v Y.rep := by rw [huv]
        _ = Z.rep := hvz

/-- OP¹ shell as unit-projective boundary quotient in this chart. -/
def OctonionicProjectiveLine : Type _ := Quotient (op1Setoid (B := B))

/-- Quotient constructor from representative to shell point. -/
def mkOP1 (x : OP1Representative (B := B)) :
    OctonionicProjectiveLine (B := B) :=
  Quotient.mk _ x

/-- Quotient identification under unit scaling. -/
theorem mkOP1_eq_scale (u : Rˣ) (x : OP1Representative (B := B)) :
    mkOP1 (B := B) x = mkOP1 (B := B) (OP1RepScale (B := B) u x) := by
  apply Quotient.sound
  exact ⟨u, rfl⟩

end InfoGeometry.Projective.SplitOctonions.ZornMatrix

import InfoGeometry.Projective.SplitOctonions.OctonionicProjectiveLine

/-!
# Octonionic Projective Line Wrapper

This file is a compatibility wrapper for the conservative OP1 shell and
Voelkel Lemma 4.5.2 local associator packet owned by
`SplitOctonions/OctonionicProjectiveLine.lean`.

It does not introduce a second projective-line construction.
-/

namespace InfoGeometry.Projective.SplitOctonions

open InfoGeometry.Projective.SplitOctonions.ZornMatrix

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable (B : V →ₗ[R] V →ₗ[R] R)

/-- `half(x)=e₁` shorthand for the local coordinate convention. -/
def half_inverter (x : ZornMatrix R V) : Prop := is_half_inverter x

def half (x : ZornMatrix R V) : Prop := is_half_inverter x

/-- Explicit chart condition matching the `half = e₁` picture used in Voelkel-style notes. -/
def half_eq_e1 (x : ZornMatrix R V) : Prop := x.x11 = 1 ∧ x.x12 = 1 ∧ x.x21 = 0

lemma half_eq_e1_iff_half_inverter (x : ZornMatrix R V) :
    half_eq_e1 x ↔ half x := by
  constructor
  · intro hx
    rcases hx with ⟨hx11, hx12, hx21⟩
    exact ⟨hx11, hx12, hx21⟩
  · intro hx
    exact hx

/-- Boundary norm on the reduced OP1 shell. -/
def op1BoundaryNorm (x : ZornMatrix R V) : R :=
  octonionicBoundaryNorm (B := B) x

/--
Conservative source associator lemma for the intended projective-line boundary:

`[v_i, x, (v_j * x)^*] = 0` under the explicit reduced-coordinate
half-inverter hypotheses.
-/
theorem op1_associator_vanishes_of_half_inverter
    (v_i v_j x : ZornMatrix R V)
    (hx : half_inverter x)
    (h_either : half_inverter v_i ∨ half_inverter v_j) :
    associator B v_i x (star (mul B v_j x)) = diag 0 0 := by
  exact lemma_4_5_2_exact (B := B) v_i v_j x hx h_either

/--
Conservative lemma matching Voelkel-style one-point projector conventions:
If `half(x)=e₁` and either `half(v_i)=e₁` or `half(v_j)=e₁`, then the source associator vanishes.
-/
theorem op1_associator_vanishes_of_half_projector
    (v_i v_j x : ZornMatrix R V)
    (hx : half_eq_e1 x)
    (h_either : half_eq_e1 v_i ∨ half_eq_e1 v_j) :
    associator B v_i x (star (mul B v_j x)) = diag 0 0 := by
  have hx' : half x := (half_eq_e1_iff_half_inverter x).1 hx
  rcases h_either with hvi | hvj
  · exact op1_associator_vanishes_of_half_inverter (B := B) v_i v_j x hx'
      (Or.inl ((half_eq_e1_iff_half_inverter v_i).1 hvi))
  · exact op1_associator_vanishes_of_half_inverter (B := B) v_i v_j x hx'
      (Or.inr ((half_eq_e1_iff_half_inverter v_j).1 hvj))

/--
Diagonal special case from Lemma 4.5.2:
if the left factor is `diag (1, z)`, no restriction on `x` is needed for the
source associator to vanish.
-/
theorem op1_associator_vanishes_of_diag_left
    (v_j x : ZornMatrix R V) (z : R) :
    associator B (diag (1 : R) z) x (star (mul B v_j x)) = diag 0 0 := by
  exact associator_vanishes_star_mul_left_diag (B := B) v_j x (1 : R) z

/--
Source theorem from Lemma 4.5.2 in the repository-local notation.
If `half(x)=e₁` and either `v_i` has the `e₁` half-inverter chart,
or `v_i` is diagonal `diag (1, z)`, then the associator vanishes.
-/
theorem op1_associator_vanishes_of_half_or_diag_left
    (v_i v_j x : ZornMatrix R V)
    (hx : half_eq_e1 x)
    (h_left : half_eq_e1 v_i ∨ ∃ z : R, v_i = diag (1 : R) z) :
    associator B v_i x (star (mul B v_j x)) = diag 0 0 := by
  rcases h_left with hvi | ⟨z, hz⟩
  · exact op1_associator_vanishes_of_half_projector (B := B) v_i v_j x hx (Or.inl hvi)
  · rw [hz]
    exact op1_associator_vanishes_of_diag_left (B := B) v_j x z

/-- Representative type for the conservative local OP1 shell. -/
abbrev OP1Representative (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] (B : V →ₗ[R] V →ₗ[R] R) : Type _ :=
  ZornMatrix.OP1Representative (B := B)

/-- Quotient type for the conservative local OP1 shell. -/
abbrev OP1Quotient (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] (B : V →ₗ[R] V →ₗ[R] R) : Type _ :=
  ZornMatrix.OctonionicProjectiveLine (B := B)

/-- Unit scaling on OP1 representatives, re-exported from the owner file. -/
def scaleRep (u : Rˣ)
    (x : OP1Representative (R := R) (V := V) B) :
    OP1Representative (R := R) (V := V) B :=
  OP1RepScale (B := B) u x

/-- Quotient constructor for the conservative local OP1 shell. -/
def mkOP1Quotient
    (x : OP1Representative (R := R) (V := V) B) :
    OP1Quotient (R := R) (V := V) B :=
  mkOP1 (B := B) x

/-- Scaling a representative by a unit does not change its local OP1 point. -/
theorem mkOP1Quotient_eq_scale (u : Rˣ)
    (x : OP1Representative (R := R) (V := V) B) :
    mkOP1Quotient (B := B) x =
      mkOP1Quotient (B := B) (scaleRep (B := B) u x) := by
  exact mkOP1_eq_scale (B := B) u x

end InfoGeometry.Projective.SplitOctonions

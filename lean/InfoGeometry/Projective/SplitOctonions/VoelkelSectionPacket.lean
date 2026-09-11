import InfoGeometry.Projective.SplitOctonions.ProjectiveLine
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Voelkel OP1 Section Packet

This file extracts the next kernel-checkable layer from Voelkel's thesis after
Lemma 4.5.2.

The thesis proof of Lemma 4.5.3 uses two ingredients:

* the coordinate reduction `N(x) = 1` and `half(x) = e1`, which forces the
  missing diagonal coordinate of `x` to be `1`;
* the explicit half-inverter construction from Lemma 3.2.6 in a unit
  half-coordinate chart;
* the associator vanishing from Lemma 4.5.2.

The actual chart-section construction and motivic equivalence theorem remain
open debt here.  We only package the explicit algebraic premises that make the
section associator vanish in the reduced Zorn model.
-/

namespace InfoGeometry.Projective.SplitOctonions.ZornMatrix

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable (B : V →ₗ[R] V →ₗ[R] R)

/-- The `half` projection from Voelkel Definition 3.2.1 in reduced Zorn coordinates. -/
def halfCoord (x : ZornMatrix R V) : R × V :=
  (x.x11, x.x21)

/-- The complementary `ohalf` projection in reduced Zorn coordinates. -/
def ohalfCoord (x : ZornMatrix R V) : R × V :=
  (x.x12, x.x22)

/-- Pairing between the `half` and `ohalf` coordinate halves. -/
def halfPairing (p q : R × V) : R :=
  p.1 * q.1 + B p.2 q.2

/-- Reduced form of Voelkel Remark 3.2.2: `N(x) = half(x) · ohalf(x)`. -/
theorem norm_eq_halfPairing (x : ZornMatrix R V) :
    norm B x = halfPairing B (halfCoord x) (ohalfCoord x) := by
  rfl

/-- The coordinate equation `half(x)=e1`. -/
def halfEqE1 (x : ZornMatrix R V) : Prop :=
  x.x11 = 1 ∧ x.x21 = 0

/-- The unit-norm half-equation used in Lemma 4.5.2/4.5.3. -/
def unitHalfEqE1 (x : ZornMatrix R V) : Prop :=
  norm B x = 1 ∧ halfEqE1 x

/-- `x` is a half-inverter of `y` in the sense of Voelkel Definition 3.2.5. -/
def isHalfInverterOf (y x : ZornMatrix R V) : Prop :=
  norm B x = 1 ∧ halfEqE1 (mul B y x)

/--
If `N(x)=1` and `half(x)=e1`, then the missing diagonal coordinate is `1`.
This is the explicit coordinate step used in Voelkel's proof of Lemma 4.5.2.
-/
theorem unitHalfEqE1_x12_eq_one
    (x : ZornMatrix R V)
    (hx : unitHalfEqE1 (B := B) x) :
    x.x12 = 1 := by
  have hnorm : norm B x = 1 := hx.1
  have hx11 : x.x11 = 1 := hx.2.1
  have hx21 : x.x21 = 0 := hx.2.2
  simpa [norm, hx11, hx21] using hnorm

/--
The thesis-style premise `N(x)=1 ∧ half(x)=e1` implies the local
`is_half_inverter` predicate used by the Lemma 4.5.2 packet.
-/
theorem unitHalfEqE1_is_half_inverter
    (x : ZornMatrix R V)
    (hx : unitHalfEqE1 (B := B) x) :
    is_half_inverter x := by
  exact ⟨hx.2.1, unitHalfEqE1_x12_eq_one (B := B) x hx, hx.2.2⟩

/--
The `i=0` half-inverter formula from Voelkel Lemma 3.2.6 in the reduced Zorn
model, with a sign adjusted to the repository's stored lower-left coordinate
convention.
-/
def lemma326HalfInverter0
    (y : ZornMatrix R V) (u : Rˣ) (κ : V) : ZornMatrix R V where
  x11 := (↑(u⁻¹ : Rˣ) : R) - B y.x21 κ
  x12 := (u : R)
  x21 := -y.x21
  x22 := -(u : R) • κ

/--
Lemma 3.2.6, reduced `half(y)_0` chart: if `y.x11` is a unit, then the explicit
formula `lemma326HalfInverter0` is a half-inverter of `y`.
-/
theorem lemma326_half_inverter0_isHalfInverterOf
    (y : ZornMatrix R V) (u : Rˣ) (κ : V)
    (hy : y.x11 = (u : R)) :
    isHalfInverterOf (B := B) y (lemma326HalfInverter0 (B := B) y u κ) := by
  have hu : (u : R) * (↑(u⁻¹ : Rˣ) : R) = 1 := by
    simp
  constructor
  · dsimp [lemma326HalfInverter0, norm]
    simp [map_neg, map_smul, smul_eq_mul, mul_comm]
    ring_nf
    exact hu
  · constructor
    · dsimp [lemma326HalfInverter0, halfEqE1, mul]
      simp [map_neg, map_smul, smul_eq_mul, hy]
      ring_nf
      exact hu
    · dsimp [lemma326HalfInverter0, halfEqE1, mul]
      simp [hy]

/--
Existence form of the reduced Lemma 3.2.6 chart: a unit first half-coordinate
gives a half-inverter.
-/
theorem lemma326_half_invertible_of_x11_unit
    (y : ZornMatrix R V) (u : Rˣ)
    (hy : y.x11 = (u : R)) :
    ∃ x : ZornMatrix R V, isHalfInverterOf (B := B) y x := by
  exact ⟨lemma326HalfInverter0 (B := B) y u 0,
    lemma326_half_inverter0_isHalfInverterOf (B := B) y u 0 hy⟩

/--
Explicit algebraic hypotheses for the section step in Voelkel Lemma 4.5.3.
This is not the global section construction; it is the local data needed to
invoke Lemma 4.5.2 on a section-shaped triple.
-/
structure OP1SectionAssociatorDatum where
  vi : ZornMatrix R V
  vj : ZornMatrix R V
  x : ZornMatrix R V
  hx : unitHalfEqE1 (B := B) x
  hsource : unitHalfEqE1 (B := B) vi ∨ unitHalfEqE1 (B := B) vj

/--
Conditional Lemma 4.5.3 algebraic core: any section-shaped datum satisfying the
explicit unit-half premises has vanishing source associator.
-/
theorem lemma453_section_associator_vanishes
    (D : OP1SectionAssociatorDatum (B := B)) :
    associator B D.vi D.x (star (mul B D.vj D.x)) = diag 0 0 := by
  have hx : is_half_inverter D.x :=
    unitHalfEqE1_is_half_inverter (B := B) D.x D.hx
  have hsource : is_half_inverter D.vi ∨ is_half_inverter D.vj := by
    cases D.hsource with
    | inl hvi =>
        exact Or.inl (unitHalfEqE1_is_half_inverter (B := B) D.vi hvi)
    | inr hvj =>
        exact Or.inr (unitHalfEqE1_is_half_inverter (B := B) D.vj hvj)
  exact lemma_4_5_2_exact (B := B) D.vi D.vj D.x hx hsource

end InfoGeometry.Projective.SplitOctonions.ZornMatrix

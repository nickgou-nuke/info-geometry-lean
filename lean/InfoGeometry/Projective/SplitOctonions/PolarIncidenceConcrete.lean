import InfoGeometry.Projective.SplitOctonions.Polar
import Mathlib.Tactic

/-!
# Projective Zorn polar incidence

Concrete-facing notation and formula layer around the owned projective Zorn
polar incidence descent in `InfoGeometry.Projective.SplitOctonions.Polar`.

Repository boundary:

* Zorn cells are not ordinary associative `2 × 2` matrices; they are
  vector-matrix coordinates for split-octonion algebraic data.
* The determinant/polar lane below is the split-octonion norm/polarity lane.
* Quotient-level incidence is delegated to
  `ZornProjectiveDatum.PolarDatum`.
-/

namespace InfoGeometry.Projective.SplitOctonions

universe u v

/-! ## Concrete three-vector formulas -/

/-- Three-dimensional coordinate vector used for local concrete Zorn cells. -/
abbrev Vec3 (𝕜 : Type u) := 𝕜 × 𝕜 × 𝕜

namespace Vec3

variable {𝕜 : Type u} [CommRing 𝕜]

/-- Standard coordinate dot product on `𝕜³`. -/
def dot (p q : Vec3 𝕜) : 𝕜 :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

@[simp] theorem dot_comm (p q : Vec3 𝕜) :
    dot p q = dot q p := by
  unfold dot
  ring

end Vec3

namespace ZornCell

variable {𝕜 : Type u} [CommRing 𝕜]

/-- Concrete addition of Zorn cells over `𝕜³`. -/
def add3 (X Y : ZornCell 𝕜 (Vec3 𝕜)) : ZornCell 𝕜 (Vec3 𝕜) where
  a := X.a + Y.a
  b := X.b + Y.b
  v := X.v + Y.v
  w := X.w + Y.w

/-- Concrete Zorn determinant/norm `ab - v·w` over `𝕜³`. -/
def detZ3c (X : ZornCell 𝕜 (Vec3 𝕜)) : 𝕜 :=
  X.a * X.b - Vec3.dot X.v X.w

/-- Polarization numerator `det(X + Y) - det(X) - det(Y)`. -/
def polarZ3 (X Y : ZornCell 𝕜 (Vec3 𝕜)) : 𝕜 :=
  detZ3c (add3 X Y) - detZ3c X - detZ3c Y

/-- Explicit expanded Zorn polarization numerator. -/
def polarFormula3 (X Y : ZornCell 𝕜 (Vec3 𝕜)) : 𝕜 :=
  X.a * Y.b + Y.a * X.b - Vec3.dot X.v Y.w - Vec3.dot Y.v X.w

/-- Half-polar bilinear form associated with the concrete Zorn determinant. -/
def BZ3 [Inv 𝕜] (X Y : ZornCell 𝕜 (Vec3 𝕜)) : 𝕜 :=
  (2 : 𝕜)⁻¹ * polarZ3 X Y

/-- Expanding determinant polarization gives the standard explicit formula. -/
theorem polarZ3_eq_formula (X Y : ZornCell 𝕜 (Vec3 𝕜)) :
    polarZ3 X Y = polarFormula3 X Y := by
  unfold polarZ3 polarFormula3 detZ3c add3 Vec3.dot
  simp [Prod.fst_add, Prod.snd_add, add_mul, mul_add, sub_eq_add_neg]
  ring_nf

/-- The explicit Zorn polarization numerator is symmetric. -/
theorem polarFormula3_symm (X Y : ZornCell 𝕜 (Vec3 𝕜)) :
    polarFormula3 X Y = polarFormula3 Y X := by
  unfold polarFormula3 Vec3.dot
  ring

/-- The concrete Zorn polarization numerator is symmetric. -/
theorem polarZ3_symm (X Y : ZornCell 𝕜 (Vec3 𝕜)) :
    polarZ3 X Y = polarZ3 Y X := by
  rw [polarZ3_eq_formula, polarZ3_eq_formula, polarFormula3_symm]

/-- The half-polar concrete Zorn form is symmetric. -/
theorem BZ3_symm [Inv 𝕜] (X Y : ZornCell 𝕜 (Vec3 𝕜)) :
    BZ3 X Y = BZ3 Y X := by
  unfold BZ3
  rw [polarZ3_symm]

end ZornCell

/-! ## Link to the existing quotient-level polar incidence owner -/

namespace ZornProjectiveDatum
namespace PolarDatum

variable {R : Type u} {V : Type v}
variable [Field R] [CharZero R]
variable [AddCommGroup V] [Module R V]

/-- Half of the determinant-polarization numerator. -/
def halfPolar (D : PolarDatum R V) (X Y : ZornCell R V) : R :=
  (2 : R)⁻¹ * D.polarZ X Y

/-- Representative incidence is equivalent to vanishing half-polar form. -/
theorem incidentRep_iff_halfPolar_eq_zero
    (D : PolarDatum R V)
    (X Y : ZornProjectiveDatum.NullRep D.base) :
    D.IncidentRep X Y ↔ D.halfPolar X.rep Y.rep = 0 := by
  constructor
  · intro h
    unfold ZornProjectiveDatum.PolarDatum.IncidentRep at h
    unfold ZornProjectiveDatum.PolarDatum.halfPolar
    simp [h]
  · intro h
    unfold halfPolar at h
    have htwo : ((2 : R)⁻¹) ≠ 0 := by
      exact inv_ne_zero (by norm_num : (2 : R) ≠ 0)
    have hpolar : D.polarZ X.rep Y.rep = 0 :=
      (mul_eq_zero.mp h).resolve_left htwo
    simpa [IncidentRep] using hpolar

/--
Projective polar incidence theorem for canonical representatives.

`[X] ⟂_Z [Y] ↔ B_Z(X,Y) = 0` on the repository `NullRay` quotient surface.
-/
theorem incident_mk_iff_halfPolar_eq_zero
    (D : PolarDatum R V)
    (X Y : ZornProjectiveDatum.NullRep D.base) :
    D.Incident (ZornProjectiveDatum.nullRayMk D.base X)
      (ZornProjectiveDatum.nullRayMk D.base Y)
      ↔ D.halfPolar X.rep Y.rep = 0 := by
  rw [incident_mk_iff]
  exact incidentRep_iff_halfPolar_eq_zero D X Y

/-- Symmetry of half-polar form from symmetry of representative polar numerator. -/
theorem halfPolar_symm
    (D : PolarDatum R V)
    (hSymm : ∀ X Y : ZornCell R V, D.polarZ X Y = D.polarZ Y X)
    (X Y : ZornCell R V) :
    D.halfPolar X Y = D.halfPolar Y X := by
  unfold halfPolar
  rw [hSymm]

end PolarDatum
end ZornProjectiveDatum

end InfoGeometry.Projective.SplitOctonions

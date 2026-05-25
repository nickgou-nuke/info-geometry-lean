import InfoGeometry.Projective.SplitOctonions.Polar
import Mathlib.Tactic

/-!
# Projective Zorn polar incidence

This module adds a concrete-facing notation layer around the already-owned
projective Zorn polar incidence descent in
`InfoGeometry.Projective.SplitOctonions.Polar`.

Repository boundary:

* Zorn cells are not ordinary associative `2 × 2` matrices.  They are
  vector-matrix coordinates for split-octonions with custom nonassociative
  multiplication supplied elsewhere.
* The determinant/polar form below is the split-octonion norm/polarity lane,
  not ordinary matrix determinant multiplicativity.
* Quotient-level incidence is still delegated to `ZornProjectiveDatum.PolarDatum`.
-/

namespace InfoGeometry.Projective.SplitOctonions

universe u v

/-! ## Concrete three-vector formulas -/

/-- Three-dimensional coordinate vector used for the local concrete Zorn cell. -/
abbrev Vec3 (𝕜 : Type u) := 𝕜 × 𝕜 × 𝕜

namespace Vec3

variable {𝕜 : Type u} [CommRing 𝕜]

/-- Standard coordinate dot product on `𝕜³`, written in product coordinates. -/
def dot (p q : Vec3 𝕜) : 𝕜 :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

@[simp] theorem dot_comm (p q : Vec3 𝕜) :
    dot p q = dot q p := by
  unfold dot
  ring

end Vec3

namespace ZornCell

variable {𝕜 : Type u} [CommRing 𝕜]

/-- Concrete addition of local Zorn cells over `𝕜³`. -/
def add3 (X Y : ZornCell 𝕜 (Vec3 𝕜)) : ZornCell 𝕜 (Vec3 𝕜) where
  a := X.a + Y.a
  b := X.b + Y.b
  v := X.v + Y.v
  w := X.w + Y.w

/-- Concrete Zorn determinant/norm `ab - v·w` over `𝕜³`. -/
def detZ3 (X : ZornCell 𝕜 (Vec3 𝕜)) : 𝕜 :=
  X.a * X.b - Vec3.dot X.v X.w

/-- Polarization numerator `det(X + Y) - det(X) - det(Y)`. -/
def polarZ3 (X Y : ZornCell 𝕜 (Vec3 𝕜)) : 𝕜 :=
  detZ3 (add3 X Y) - detZ3 X - detZ3 Y

/-- The standard explicit Zorn polar numerator. -/
def polarFormula3 (X Y : ZornCell 𝕜 (Vec3 𝕜)) : 𝕜 :=
  X.a * Y.b + Y.a * X.b - Vec3.dot X.v Y.w - Vec3.dot Y.v X.w

/-- The half-polar bilinear form associated with the concrete Zorn determinant. -/
def BZ3 [Inv 𝕜] (X Y : ZornCell 𝕜 (Vec3 𝕜)) : 𝕜 :=
  (2 : 𝕜)⁻¹ * polarZ3 X Y

/-- Expanding the Zorn determinant polarization gives the standard formula. -/
theorem polarZ3_eq_formula
    (X Y : ZornCell 𝕜 (Vec3 𝕜)) :
    polarZ3 X Y = polarFormula3 X Y := by
  cases X with
  | mk aX bX vX wX =>
    cases Y with
    | mk aY bY vY wY =>
      cases vX with
      | mk vX1 vX23 =>
        cases vX23 with
        | mk vX2 vX3 =>
          cases wX with
          | mk wX1 wX23 =>
            cases wX23 with
            | mk wX2 wX3 =>
              cases vY with
              | mk vY1 vY23 =>
                cases vY23 with
                | mk vY2 vY3 =>
                  cases wY with
                  | mk wY1 wY23 =>
                    cases wY23 with
                    | mk wY2 wY3 =>
                      simp [polarZ3, polarFormula3, detZ3, add3, Vec3.dot]
                      ring

/-- The explicit Zorn polar numerator is symmetric. -/
theorem polarFormula3_symm
    (X Y : ZornCell 𝕜 (Vec3 𝕜)) :
    polarFormula3 X Y = polarFormula3 Y X := by
  unfold polarFormula3 Vec3.dot
  ring

/-- The concrete Zorn polar numerator is symmetric. -/
theorem polarZ3_symm
    (X Y : ZornCell 𝕜 (Vec3 𝕜)) :
    polarZ3 X Y = polarZ3 Y X := by
  rw [polarZ3_eq_formula, polarZ3_eq_formula, polarFormula3_symm]

/-- The half-polar concrete Zorn form is symmetric. -/
theorem BZ3_symm [Inv 𝕜]
    (X Y : ZornCell 𝕜 (Vec3 𝕜)) :
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

/-- Half of the determinant-polarization numerator used for conventional bilinear notation. -/
def halfPolar (D : PolarDatum R V) (X Y : ZornCell R V) : R :=
  (2 : R)⁻¹ * D.polarZ X Y

/-- Representative incidence is equivalent to vanishing of the half-polar form. -/
theorem incidentRep_iff_halfPolar_eq_zero
    (D : PolarDatum R V)
    (X Y : ZornProjectiveDatum.NullRep D.base) :
    D.IncidentRep X Y ↔ D.halfPolar X.rep Y.rep = 0 := by
  constructor
  · intro h
    unfold IncidentRep at h
    unfold halfPolar
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

This is the projective statement `[X] ⊥_Z [Y] ↔ B_Z(X,Y) = 0`, phrased in the
repository's existing `NullRay` quotient surface.
-/
theorem incident_mk_iff_halfPolar_eq_zero
    (D : PolarDatum R V)
    (X Y : ZornProjectiveDatum.NullRep D.base) :
    D.Incident (ZornProjectiveDatum.nullRayMk D.base X)
      (ZornProjectiveDatum.nullRayMk D.base Y)
      ↔ D.halfPolar X.rep Y.rep = 0 := by
  rw [incident_mk_iff]
  exact incidentRep_iff_halfPolar_eq_zero D X Y

omit [CharZero R] in
/-- Symmetry of half-polar incidence when the representative polar numerator is symmetric. -/
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

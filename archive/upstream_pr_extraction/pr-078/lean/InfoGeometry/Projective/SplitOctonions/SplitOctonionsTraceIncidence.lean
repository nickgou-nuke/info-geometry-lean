import InfoGeometry.Projective.SplitOctonions.PolarIncidenceConcrete

/-!
# InfoGeometry.Projective.SplitOctonions.SplitOctonionsTraceIncidence

Concrete trace-style incidence form for Zorn cells over `𝕜³`.

This file proves that the explicit incidence bilinear form

`a₁ b₂ + b₁ a₂ - v₁·w₂ - v₂·w₁`

agrees with the finite polarization formulas already established in
`PolarIncidenceConcrete`.

No wrappers. No placeholders.
-/

namespace InfoGeometry.Projective.SplitOctonions

universe u

namespace ZornCell

variable {𝕜 : Type u} [CommRing 𝕜]

/-- Diagonal-trace cross term `a₁ b₂ + b₁ a₂`. -/
def traceCross3 (X Y : ZornCell 𝕜 (Vec3 𝕜)) : 𝕜 :=
  X.a * Y.b + X.b * Y.a

/--
Trace-style concrete incidence bilinear form on Zorn cells over `𝕜³`.

This is the explicit finite form

`a₁ b₂ + b₁ a₂ - v₁·w₂ - v₂·w₁`.
-/
def traceIncidence3 (X Y : ZornCell 𝕜 (Vec3 𝕜)) : 𝕜 :=
  traceCross3 X Y - Vec3.dot X.v Y.w - Vec3.dot Y.v X.w

@[simp]
theorem traceIncidence3_eq_polarFormula3 (X Y : ZornCell 𝕜 (Vec3 𝕜)) :
    traceIncidence3 X Y = polarFormula3 X Y := by
  unfold traceIncidence3 traceCross3 polarFormula3
  ring

@[simp]
theorem traceIncidence3_eq_polarZ3 (X Y : ZornCell 𝕜 (Vec3 𝕜)) :
    traceIncidence3 X Y = polarZ3 X Y := by
  rw [traceIncidence3_eq_polarFormula3, polarZ3_eq_formula]

theorem traceIncidence3_zero_iff_polarZ3_zero (X Y : ZornCell 𝕜 (Vec3 𝕜)) :
    traceIncidence3 X Y = 0 ↔ polarZ3 X Y = 0 := by
  rw [traceIncidence3_eq_polarZ3]

theorem traceIncidence3_symm (X Y : ZornCell 𝕜 (Vec3 𝕜)) :
    traceIncidence3 X Y = traceIncidence3 Y X := by
  rw [traceIncidence3_eq_polarFormula3, traceIncidence3_eq_polarFormula3]
  exact polarFormula3_symm X Y

theorem traceIncidence3_zero_iff_BZ3_zero
    {K : Type u} [Field K] [CharZero K]
    (X Y : ZornCell K (Vec3 K)) :
    traceIncidence3 X Y = 0 ↔ BZ3 X Y = 0 := by
  constructor
  · intro h
    unfold BZ3
    rw [traceIncidence3_eq_polarZ3] at h
    simp [h]
  · intro h
    unfold BZ3 at h
    have h' : polarZ3 X Y = 0 := by
      have htwo : (2 : K) ≠ 0 := by norm_num
      have hmul := congrArg (fun t : K => (2 : K) * t) h
      have hmul' : ((2 : K) * (2 : K)⁻¹) * polarZ3 X Y = 0 := by
        simpa [mul_assoc] using hmul
      simpa [htwo] using hmul'
    rwa [traceIncidence3_eq_polarZ3]

end ZornCell

namespace ZornProjectiveDatum
namespace PolarDatum

variable {R : Type u}
variable [Field R] [CharZero R]

/--
Representative incidence rewritten through the concrete trace-style form,
assuming the datum polar numerator matches `ZornCell.polarZ3` on `R³`.
-/
theorem incidentRep_iff_traceIncidence3_eq_zero
    (D : PolarDatum R (Vec3 R))
    (hpolar3 : ∀ U V : ZornCell R (Vec3 R), D.polarZ U V = ZornCell.polarZ3 U V)
    (X Y : ZornProjectiveDatum.NullRep D.base) :
    D.IncidentRep X Y ↔ ZornCell.traceIncidence3 X.rep Y.rep = 0 := by
  rw [incidentRep_iff_halfPolar_eq_zero]
  unfold halfPolar
  constructor
  · intro h
    have h' : D.polarZ X.rep Y.rep = 0 := by
      exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (by norm_num : (2 : R) ≠ 0))
    have h3 : ZornCell.polarZ3 X.rep Y.rep = 0 := by simpa [hpolar3 X.rep Y.rep] using h'
    exact (ZornCell.traceIncidence3_zero_iff_polarZ3_zero X.rep Y.rep).2 h3
  · intro h
    have h3 : ZornCell.polarZ3 X.rep Y.rep = 0 :=
      (ZornCell.traceIncidence3_zero_iff_polarZ3_zero X.rep Y.rep).1 h
    have h' : D.polarZ X.rep Y.rep = 0 := by simpa [hpolar3 X.rep Y.rep] using h3
    simp [h']

/--
Projective incidence rewritten through the concrete trace-style form,
assuming the datum polar numerator matches `ZornCell.polarZ3` on `R³`.
-/
theorem incident_mk_iff_traceIncidence3_eq_zero
    (D : PolarDatum R (Vec3 R))
    (hpolar3 : ∀ U V : ZornCell R (Vec3 R), D.polarZ U V = ZornCell.polarZ3 U V)
    (X Y : ZornProjectiveDatum.NullRep D.base) :
    D.Incident (ZornProjectiveDatum.nullRayMk D.base X)
      (ZornProjectiveDatum.nullRayMk D.base Y)
      ↔ ZornCell.traceIncidence3 X.rep Y.rep = 0 := by
  rw [incident_mk_iff]
  exact incidentRep_iff_traceIncidence3_eq_zero D hpolar3 X Y

end PolarDatum
end ZornProjectiveDatum

end InfoGeometry.Projective.SplitOctonions

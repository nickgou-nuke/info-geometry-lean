import InfoGeometry.Projective.SplitOctonions.SplitOctonionsTraceIncidence

/-!
Direct readback theorems for the finite split-octonion incidence model.

The imported projective/Zorn modules own the algebraic statements.  This
module deliberately contains no hardcoded dimension packet or global-status
property; no global Cartan-geometry theorem is claimed here.
-/

namespace InfoGeometry.Lie.SplitOctonion235Distribution

open InfoGeometry.Projective.SplitOctonions

theorem splitOctonion235TraceIncidence_formula
    (X Y : ZornCell ℚ (Vec3 ℚ)) :
    ZornCell.traceIncidence3 X Y = ZornCell.polarZ3 X Y := by
  simpa using ZornCell.traceIncidence3_eq_polarZ3 X Y

theorem splitOctonion235TraceIncidence_symm
    (X Y : ZornCell ℚ (Vec3 ℚ)) :
    ZornCell.traceIncidence3 X Y = ZornCell.traceIncidence3 Y X := by
  exact ZornCell.traceIncidence3_symm X Y

theorem splitOctonion235TraceIncidence_zero_iff_polarZ3_zero
    (X Y : ZornCell ℚ (Vec3 ℚ)) :
    ZornCell.traceIncidence3 X Y = 0 ↔ ZornCell.polarZ3 X Y = 0 := by
  rw [ZornCell.traceIncidence3_eq_polarZ3]

theorem splitOctonion235Incident_iff_traceIncidence3_eq_zero
    (D : ZornProjectiveDatum.PolarDatum ℚ (Vec3 ℚ))
    (hpolar3 : ∀ U V : ZornCell ℚ (Vec3 ℚ), D.polarZ U V = ZornCell.polarZ3 U V)
    (X Y : ZornProjectiveDatum.NullRep D.base) :
    D.IncidentRep X Y ↔ ZornCell.traceIncidence3 X.rep Y.rep = 0 := by
  exact ZornProjectiveDatum.PolarDatum.incidentRep_iff_traceIncidence3_eq_zero
    D hpolar3 X Y

end InfoGeometry.Lie.SplitOctonion235Distribution

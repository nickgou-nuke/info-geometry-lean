import InfoGeometry.Algebra.JordanCayleyInversionCs
import InfoGeometry.Algebra.JordanCayleyInversionHs
import InfoGeometry.Algebra.JordanCayleyInversionOs
import InfoGeometry.Algebra.JordanCayleyInversionOsQ
import InfoGeometry.Algebra.SplitOctonionIsomorphism
import InfoGeometry.Algebra.KleinSpinorOrbit
import InfoGeometry.Algebra.KleinSpinorOrbitClosure

/-! # Geometric bridge: Jordan-Cayley inversion and Klein-quadric coordinate packets

Re-exports finite theorem-safe coordinate identities from the arXiv:1603.09063v2
formalization layer.  This module is a dictionary/aggregation surface only: it
does not prove CCC, analytic conformality, full orbit classification, or any
Spin/structure-group isomorphism. -/

namespace InfoGeometry.Algebra.GeometricBridge

/-! ## 1. Cs Jordan-Cayley (4D, 2+2 signature) -/

theorem cs_fundamental_identity :
  ∀ (X : JordanCayleyInversionCs.Herm2x2Cs),
    X.mulTraceReversal = { e11 := X.det, e22 := -X.det } :=
  JordanCayleyInversionCs.Herm2x2Cs.fundamental_identity

theorem cs_klein_quadric (X : JordanCayleyInversionCs.Herm2x2Cs) (x1 x2 x3 x4 : ℚ)
    (hxp : X.xp = x1 + x4) (hxm : X.xm = x1 - x4) (ha : X.a = ⟨x3, x2⟩) :
    (X.det = 0) ↔ x1 ^ 2 + x2 ^ 2 - x3 ^ 2 - x4 ^ 2 = 0 :=
  JordanCayleyInversionCs.Herm2x2Cs.klein_quadric_equation X x1 x2 x3 x4 hxp hxm ha

/-! ## 2. Hs Jordan-Cayley (6D, 3+3 signature) -/

theorem hs_fundamental_identity :
  ∀ (X : JordanCayleyInversionHs.Herm2x2Hs),
    X.mulTraceReversal = (X.det, -X.det) :=
  JordanCayleyInversionHs.Herm2x2Hs.fundamental_identity

theorem hs_klein_quadric (X : JordanCayleyInversionHs.Herm2x2Hs) (x1 x2 x3 x4 x5 x6 : ℚ)
    (hxp : X.xp = x3 + x6) (hxm : X.xm = x3 - x6) (hz : X.z = ⟨x5, x1, x4, x2⟩) :
    (X.det = 0) ↔ x1 ^ 2 + x2 ^ 2 + x3 ^ 2 - x4 ^ 2 - x5 ^ 2 - x6 ^ 2 = 0 :=
  JordanCayleyInversionHs.Herm2x2Hs.klein_quadric_equation X x1 x2 x3 x4 x5 x6 hxp hxm hz

/-! ## 3. Os Jordan-Cayley (10D, 5+5 signature) — ℤ-based lane (Lane 2) -/

theorem os_fundamental_identity :
  ∀ (X : JordanCayleyInversionOs.Herm2x2Os),
    X.mulTraceReversal = { e11 := X.det, e22 := -X.det } :=
  JordanCayleyInversionOs.Herm2x2Os.fundamental_identity

theorem os_klein_quadric (X : JordanCayleyInversionOs.Herm2x2Os)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : ℚ)
    (hxp : X.xp = x1 + x6) (hxm : X.xm = x1 - x6)
    (hza : (X.z.a : ℚ) = x7 + x2) (hzb : (X.z.b : ℚ) = x7 - x2)
    (hzx0 : (X.z.x0 : ℚ) = x3 + x8) (hzy0 : (X.z.y0 : ℚ) = x3 - x8)
    (hzx1 : (X.z.x1 : ℚ) = x4 + x9) (hzy1 : (X.z.y1 : ℚ) = x4 - x9)
    (hzx2 : (X.z.x2 : ℚ) = x5 + x10) (hzy2 : (X.z.y2 : ℚ) = x5 - x10) :
    (X.det = 0) ↔ x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2 - x6 ^ 2 - x7 ^ 2 - x8 ^ 2 - x9 ^ 2 - x10 ^ 2 = 0 :=
  JordanCayleyInversionOs.Herm2x2Os.klein_quadric_equation' X x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    hxp hxm hza hzb hzx0 hzy0 hzx1 hzy1 hzx2 hzy2

/-! ## 4. Os Jordan-Cayley (10D, 5+5 signature) — pure ℚ lane (Lane 1) -/

theorem osQ_fundamental_identity :
  ∀ (X : JordanCayleyInversionOsQ.Herm2x2OsQ),
    X.mulTraceReversal = { e11 := X.det, e22 := -X.det } :=
  JordanCayleyInversionOsQ.Herm2x2OsQ.fundamental_identity

theorem osQ_klein_quadric (X : JordanCayleyInversionOsQ.Herm2x2OsQ)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : ℚ)
    (hxp : X.xp = x1 + x6) (hxm : X.xm = x1 - x6)
    (hza : X.z.a = x7 + x2) (hzb : X.z.b = x7 - x2)
    (hzx0 : X.z.x0 = x3 + x8) (hzy0 : X.z.y0 = x3 - x8)
    (hzx1 : X.z.x1 = x4 + x9) (hzy1 : X.z.y1 = x4 - x9)
    (hzx2 : X.z.x2 = x5 + x10) (hzy2 : X.z.y2 = x5 - x10) :
    (X.det = 0) ↔ x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2 - x6 ^ 2 - x7 ^ 2 - x8 ^ 2 - x9 ^ 2 - x10 ^ 2 = 0 :=
  JordanCayleyInversionOsQ.Herm2x2OsQ.klein_quadric_equation X x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    hxp hxm hza hzb hzx0 hzy0 hzx1 hzy1 hzx2 hzy2

/-! ## 5. Os lane isomorphism -/

theorem os_isomorphism_packet :
  (∀ (X : JordanCayleyInversionOs.Herm2x2Os),
      (SplitOctonionIsomorphism.hermitianPromotion X).det = X.det) ∧
  (∀ (X : JordanCayleyInversionOs.Herm2x2Os),
      SplitOctonionIsomorphism.hermitianPromotion (X.traceReversal) =
      (SplitOctonionIsomorphism.hermitianPromotion X).traceReversal) ∧
  (∀ (X : JordanCayleyInversionOs.Herm2x2Os),
      (SplitOctonionIsomorphism.hermitianPromotion X).mulTraceReversal.e11 =
      X.mulTraceReversal.e11) :=
  ⟨SplitOctonionIsomorphism.det_preserved,
    SplitOctonionIsomorphism.traceReversal_preserved,
    SplitOctonionIsomorphism.mulTraceReversal_e11_preserved⟩

/-! ## 6. Spinor orbit stratification -/

theorem orbit_stabilizers_exist :
    ∃ (g n : KleinSpinorOrbit.CsSpinor),
      KleinSpinorOrbit.Stabilizes KleinSpinorOrbit.CsMatrix2.identity g ∧
      KleinSpinorOrbit.Stabilizes KleinSpinorOrbit.CsMatrix2.identity n :=
  ⟨KleinSpinorOrbit.genericRep, KleinSpinorOrbit.nullRep,
    KleinSpinorOrbit.identity_stabilizes _,
    KleinSpinorOrbit.identity_stabilizes _⟩

/-! ## 7. Geometric dictionary -/

/--
Informal dictionary marker for the verified coordinate layers:

| Signature | Algebra | Klein quadric     | Kernel content                     |
|-----------|---------|-------------------|------------------------------------|
| (2,2)     | ℂ_s     | ℙ³                | ✓ determinant and trace-reversal   |
| (3,3)     | ℍ_s     | ℙ⁵                | ✓ determinant and trace-reversal   |
| (5,5)     | 𝕆_s     | ℙ⁹                | ✓ two lanes + isomorphism proved   |

The global conformal, CCC, and Spin/structure-group interpretations remain
mathematical motivation/proof debt unless separately kernel-proved.
-/
structure GeometricDictionary : Type where
  cs_fundamental :
    ∀ (X : JordanCayleyInversionCs.Herm2x2Cs),
      X.mulTraceReversal = { e11 := X.det, e22 := -X.det }
  hs_fundamental :
    ∀ (X : JordanCayleyInversionHs.Herm2x2Hs),
      X.mulTraceReversal = (X.det, -X.det)
  os_fundamental :
    ∀ (X : JordanCayleyInversionOs.Herm2x2Os),
      X.mulTraceReversal = { e11 := X.det, e22 := -X.det }
  osQ_fundamental :
    ∀ (X : JordanCayleyInversionOsQ.Herm2x2OsQ),
      X.mulTraceReversal = { e11 := X.det, e22 := -X.det }
  os_isomorphism :
    ∀ (X : JordanCayleyInversionOs.Herm2x2Os),
      (SplitOctonionIsomorphism.hermitianPromotion X).det = X.det
  os_trace_reversal_isomorphism :
    ∀ (X : JordanCayleyInversionOs.Herm2x2Os),
      SplitOctonionIsomorphism.hermitianPromotion (X.traceReversal) =
        (SplitOctonionIsomorphism.hermitianPromotion X).traceReversal
  orbit_stabilizers :
    ∃ (g n : KleinSpinorOrbit.CsSpinor),
      KleinSpinorOrbit.Stabilizes KleinSpinorOrbit.CsMatrix2.identity g ∧
      KleinSpinorOrbit.Stabilizes KleinSpinorOrbit.CsMatrix2.identity n

def geometricDictionary : GeometricDictionary where
  cs_fundamental := cs_fundamental_identity
  hs_fundamental := hs_fundamental_identity
  os_fundamental := os_fundamental_identity
  osQ_fundamental := osQ_fundamental_identity
  os_isomorphism := SplitOctonionIsomorphism.det_preserved
  os_trace_reversal_isomorphism := SplitOctonionIsomorphism.traceReversal_preserved
  orbit_stabilizers := orbit_stabilizers_exist

end InfoGeometry.Algebra.GeometricBridge

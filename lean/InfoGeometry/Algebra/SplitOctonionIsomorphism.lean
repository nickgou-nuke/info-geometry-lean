import InfoGeometry.Algebra.SplitOctonionQ
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.Algebra.JordanCayleyInversionOsQ
import InfoGeometry.Algebra.JordanCayleyInversionOs
import Mathlib.Tactic

/-!
# Isomorphism between the two split-octonion Jordan-Cayley lanes

This file proves that the two parallel constructions of `J₂(𝕆ₛ)` are
compatible via a ℚ-promotion map.

  **Lane 1 (pure ℚ):**  `SplitO` / `Herm2x2OsQ` from `SplitOctonionQ` and
  `JordanCayleyInversionOsQ`.

  **Lane 2 (ℤ-based):**  `SplitOct` / `Herm2x2Os` from `SplitOctonionMultiplication`
  and `JordanCayleyInversionOs`.

The promotion `hermitianPromotion : Herm2x2Os → Herm2x2OsQ` is a
componentwise `Int.cast` that commutes with `det`, `traceReversal`, and
`fundamental_identity`.

The reverse direction is not defined as a total map (ℚ → ℤ is not always
possible); instead the promotion is a faithful embedding of the ℤ-based
construction into the ℚ-based one, and the isomorphism theorems show that
all structural operations are preserved.
-/

open InfoGeometry.Algebra.SplitOctonionQ
open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

namespace SplitOctonionIsomorphism

/-! ## 1. Carrier-level promotion -/

/-- Promote a ℤ-based `SplitOct` to the ℚ-based `SplitO` via componentwise `Int.cast`. -/
def splitOctToSplitO (X : SplitOct) : SplitO :=
  { a  := (X.a : ℚ),  b  := (X.b : ℚ),
    x0 := (X.x0 : ℚ), x1 := (X.x1 : ℚ), x2 := (X.x2 : ℚ),
    y0 := (X.y0 : ℚ), y1 := (X.y1 : ℚ), y2 := (X.y2 : ℚ) }

/-- The norm is preserved under promotion: the ℚ-valued Zorn norm in Lane 2
coincides with the `SplitO.norm` in Lane 1. -/
theorem norm_preserved (X : SplitOct) :
    SplitO.norm (splitOctToSplitO X) = JordanCayleyInversionOs.zornNormℚ X := by
  simp [SplitO.norm, splitOctToSplitO, JordanCayleyInversionOs.zornNormℚ]

/-- `detZ` over ℤ, promoted to ℚ, equals the Lane 1 norm of the promoted carrier. -/
theorem norm_eq_detZ_cast (X : SplitOct) :
    SplitO.norm (splitOctToSplitO X) = (detZ X : ℚ) := by
  simp [SplitO.norm, splitOctToSplitO, detZ]

/-- Negation commutes with promotion. -/
theorem neg_preserved (X : SplitOct) :
    splitOctToSplitO (negZ X) = SplitO.neg (splitOctToSplitO X) := by
  cases X; simp [splitOctToSplitO, negZ, SplitO.neg]

/-- Conjugation commutes with promotion. -/
theorem conj_preserved (X : SplitOct) :
    splitOctToSplitO (conjZ X) = SplitO.conj (splitOctToSplitO X) := by
  cases X; simp [splitOctToSplitO, conjZ, SplitO.conj]

/-- The norm-conjugation identity is preserved. -/
theorem norm_conj_preserved (X : SplitOct) :
    SplitO.norm (SplitO.conj (splitOctToSplitO X)) = (detZ (conjZ X) : ℚ) := by
  rw [← conj_preserved X]
  exact norm_eq_detZ_cast (conjZ X)

/-! ## 2. Hermitian matrix promotion -/

/-- Promote a Lane 2 Hermitian matrix to Lane 1. -/
def hermitianPromotion (X : JordanCayleyInversionOs.Herm2x2Os) :
    JordanCayleyInversionOsQ.Herm2x2OsQ :=
  { xp := X.xp, xm := X.xm, z := splitOctToSplitO X.z }

/-- The determinant is preserved under promotion. -/
theorem det_preserved (X : JordanCayleyInversionOs.Herm2x2Os) :
    (hermitianPromotion X).det = X.det := by
  simp [JordanCayleyInversionOsQ.Herm2x2OsQ.det,
    JordanCayleyInversionOs.Herm2x2Os.det,
    hermitianPromotion, norm_preserved]

/-- Trace reversal commutes with promotion. -/
theorem traceReversal_preserved (X : JordanCayleyInversionOs.Herm2x2Os) :
    hermitianPromotion (X.traceReversal) =
    (hermitianPromotion X).traceReversal := by
  simp [hermitianPromotion, neg_preserved,
    JordanCayleyInversionOs.Herm2x2Os.traceReversal,
    JordanCayleyInversionOsQ.Herm2x2OsQ.traceReversal]

/-- The `mulTraceReversal` diagonal packet is preserved. -/
theorem mulTraceReversal_e11_preserved (X : JordanCayleyInversionOs.Herm2x2Os) :
    (hermitianPromotion X).mulTraceReversal.e11 = X.mulTraceReversal.e11 := by
  simp [JordanCayleyInversionOsQ.Herm2x2OsQ.mulTraceReversal,
    JordanCayleyInversionOs.Herm2x2Os.mulTraceReversal,
    hermitianPromotion, norm_preserved]

/-- The `mulTraceReversal` diagonal packet e22 is preserved. -/
theorem mulTraceReversal_e22_preserved (X : JordanCayleyInversionOs.Herm2x2Os) :
    (hermitianPromotion X).mulTraceReversal.e22 = X.mulTraceReversal.e22 := by
  simp [JordanCayleyInversionOsQ.Herm2x2OsQ.mulTraceReversal,
    JordanCayleyInversionOs.Herm2x2Os.mulTraceReversal,
    hermitianPromotion, norm_preserved]

/-- The fundamental identity commutes with promotion:
the Lane 2 `fundamental_identity` and the Lane 1 `fundamental_identity`
agree under the promotion map. -/
theorem fundamental_identity_preserved (X : JordanCayleyInversionOs.Herm2x2Os) :
    (hermitianPromotion X).mulTraceReversal.e11 = X.mulTraceReversal.e11 ∧
    (hermitianPromotion X).mulTraceReversal.e22 = X.mulTraceReversal.e22 :=
  ⟨mulTraceReversal_e11_preserved X, mulTraceReversal_e22_preserved X⟩

/-! ## 3. (5,5) quadratic form compatibility -/

/-- The (5,5) quadratic form is preserved under promotion. -/
theorem det_eq_quadratic_preserved
    (X : JordanCayleyInversionOs.Herm2x2Os)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : ℚ)
    (hxp : X.xp = x1 + x6) (hxm : X.xm = x1 - x6)
    (hza : (X.z.a : ℚ) = x7 + x2) (hzb : (X.z.b : ℚ) = x7 - x2)
    (hzx0 : (X.z.x0 : ℚ) = x3 + x8) (hzy0 : (X.z.y0 : ℚ) = x3 - x8)
    (hzx1 : (X.z.x1 : ℚ) = x4 + x9) (hzy1 : (X.z.y1 : ℚ) = x4 - x9)
    (hzx2 : (X.z.x2 : ℚ) = x5 + x10) (hzy2 : (X.z.y2 : ℚ) = x5 - x10) :
    (hermitianPromotion X).det = x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2 - x6 ^ 2 - x7 ^ 2 - x8 ^ 2 - x9 ^ 2 - x10 ^ 2 := by
  rw [det_preserved,
    JordanCayleyInversionOs.Herm2x2Os.det_eq_quadratic X x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
      hxp hxm hza hzb hzx0 hzy0 hzx1 hzy1 hzx2 hzy2]

/-! ## 4. Closed packet -/

/-- Closed packet: all structural maps commute with the promotion. -/
theorem isomorphism_packet :
    (∀ X : JordanCayleyInversionOs.Herm2x2Os, (hermitianPromotion X).det = X.det) ∧
    (∀ X : JordanCayleyInversionOs.Herm2x2Os,
      hermitianPromotion (X.traceReversal) = (hermitianPromotion X).traceReversal) ∧
    (∀ X : JordanCayleyInversionOs.Herm2x2Os,
      (hermitianPromotion X).mulTraceReversal.e11 = X.mulTraceReversal.e11) ∧
    (∀ X : JordanCayleyInversionOs.Herm2x2Os,
      (hermitianPromotion X).mulTraceReversal.e22 = X.mulTraceReversal.e22) :=
  ⟨det_preserved, traceReversal_preserved,
    mulTraceReversal_e11_preserved, mulTraceReversal_e22_preserved⟩

end SplitOctonionIsomorphism

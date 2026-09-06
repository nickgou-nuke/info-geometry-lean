import InfoGeometry.Algebra.JordanCayleyInversionCs
import InfoGeometry.Algebra.JordanCayleyInversionHs
import InfoGeometry.Algebra.JordanCayleyInversionOs

/-!
# Coordinate determinant strata for `J₂(C_s)`, `J₂(H_s)`, and `J₂(O_s)` packets

This file packages already-proved coordinate trace-reversal identities into
null/generic determinant strata.

Boundary: despite historical names containing "orbit", these theorems do **not**
prove a group orbit classification, stabilizer completeness, CCC, analytic
conformality, or a global conformal inversion theorem.  They only say:

* if `det X = 0`, the diagonal trace-reversal packet vanishes;
* for every `X`, the diagonal packet equals `{ e11 := det X, e22 := -det X }`.
-/

open InfoGeometry.Algebra.JordanCayleyInversionCs
open InfoGeometry.Algebra.JordanCayleyInversionHs
open InfoGeometry.Algebra.JordanCayleyInversionOs

namespace InfoGeometry.Algebra.OrbitClassification

/-! ## 1. Coordinate strata for J₂(ℂ_s) [2+2 signature] -/

theorem cs_null_orbit (X : Herm2x2Cs) (hzero : X.det = 0) :
    X.mulTraceReversal.e11 = 0 ∧ X.mulTraceReversal.e22 = 0 :=
  Herm2x2Cs.on_klein_quadric X hzero

theorem cs_generic_orbit (X : Herm2x2Cs) (_hdet : X.det ≠ 0) :
    X.mulTraceReversal = { e11 := X.det, e22 := -X.det } :=
  Herm2x2Cs.fundamental_identity X

/-! ## 2. Coordinate strata for J₂(ℍ_s) [3+3 signature] -/

theorem hs_null_orbit (X : JordanCayleyInversionHs.Herm2x2Hs) (hzero : X.det = 0) :
    X.mulTraceReversal.e11 = 0 ∧ X.mulTraceReversal.e22 = 0 :=
  JordanCayleyInversionHs.Herm2x2Hs.on_klein_quadric X hzero

theorem hs_generic_orbit (X : JordanCayleyInversionHs.Herm2x2Hs) (_hdet : X.det ≠ 0) :
    X.mulTraceReversal = { e11 := X.det, e22 := -X.det } :=
  JordanCayleyInversionHs.Herm2x2Hs.fundamental_identity X

/-! ## 3. Coordinate strata for J₂(𝕆_s) [5+5 signature] -/

theorem os_null_orbit (X : JordanCayleyInversionOs.Herm2x2Os) (hzero : X.det = 0) :
    X.mulTraceReversal.e11 = 0 ∧ X.mulTraceReversal.e22 = 0 :=
  JordanCayleyInversionOs.Herm2x2Os.on_klein_quadric X hzero

theorem os_generic_orbit (X : JordanCayleyInversionOs.Herm2x2Os) (_hdet : X.det ≠ 0) :
    X.mulTraceReversal = { e11 := X.det, e22 := -X.det } :=
  JordanCayleyInversionOs.Herm2x2Os.fundamental_identity X

/-! ## 4. Uniform coordinate packets -/

/-- Uniform null-locus diagonal-vanishing packet across the three coordinate models. -/
theorem uniform_null_orbit :
  (∀ (X : Herm2x2Cs), X.det = 0 → X.mulTraceReversal.e11 = 0 ∧ X.mulTraceReversal.e22 = 0) ∧
  (∀ (X : JordanCayleyInversionHs.Herm2x2Hs), X.det = 0 → X.mulTraceReversal.e11 = 0 ∧ X.mulTraceReversal.e22 = 0) ∧
  (∀ (X : JordanCayleyInversionOs.Herm2x2Os), X.det = 0 → X.mulTraceReversal.e11 = 0 ∧ X.mulTraceReversal.e22 = 0) :=
  ⟨fun X => cs_null_orbit X, fun X => hs_null_orbit X, fun X => os_null_orbit X⟩

/-- Uniform diagonal trace-reversal determinant packet across the three coordinate models. -/
theorem uniform_fundamental_identity :
  (∀ (X : Herm2x2Cs), X.mulTraceReversal = { e11 := X.det, e22 := -X.det }) ∧
  (∀ (X : JordanCayleyInversionHs.Herm2x2Hs), X.mulTraceReversal = { e11 := X.det, e22 := -X.det }) ∧
  (∀ (X : JordanCayleyInversionOs.Herm2x2Os), X.mulTraceReversal = { e11 := X.det, e22 := -X.det }) :=
  ⟨Herm2x2Cs.fundamental_identity,
   JordanCayleyInversionHs.Herm2x2Hs.fundamental_identity,
   JordanCayleyInversionOs.Herm2x2Os.fundamental_identity⟩

/-- Historical name for the `C_s` null-locus diagonal-vanishing packet. -/
theorem ccc_crossover (X : Herm2x2Cs) (hzero : X.det = 0) :
    X.mulTraceReversal.e11 = 0 ∧ X.mulTraceReversal.e22 = 0 :=
  cs_null_orbit X hzero

end InfoGeometry.Algebra.OrbitClassification

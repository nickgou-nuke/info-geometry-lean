import InfoGeometry.Algebra.OrbitStratification
import InfoGeometry.Algebra.OrbitClassification
import InfoGeometry.Algebra.JordanCayleyOrbitStratification
import InfoGeometry.Physics.Pin55Formal

/-!
# Bridge for coordinate determinant strata and finite Pin `(5,5)` names

This bridge connects existing theorem-safe packets:

* `OrbitStratification`: zero/nonzero case split for `C_s` spinors;
* `OrbitClassification`: determinant-null and determinant-generic coordinate
  trace-reversal packets for `J₂(C_s)`, `J₂(H_s)`, `J₂(O_s)`;
* `JordanCayleyOrbitStratification`: zero/null/generic predicate split for the
  rational split-octonionic coordinate packet;
* `Pin55Formal`: mathlib Clifford names and finite generator relations.

It does **not** prove a full group orbit classification, CCC, analytic
conformality, conformal inversion, or a quotient group theorem.
-/

open InfoGeometry.Algebra.OrbitStratification
open InfoGeometry.Algebra.OrbitClassification
open InfoGeometry.Algebra.JordanCayleyInversionCs
open InfoGeometry.Algebra.JordanCayleyInversionHs
open InfoGeometry.Algebra.JordanCayleyInversionOs
open InfoGeometry.Algebra.JordanCayleyInversionOsQ

namespace InfoGeometry.Algebra.OrbitClassificationBridge

/-- Re-export: every split-complex spinor is zero or nonzero. -/
theorem cs_spinor_zero_or_nonzero
    (ψ : InfoGeometry.Algebra.KleinSpinorOrbit.CsSpinor) :
    OrbitStratification.OrbitType ψ :=
  OrbitStratification.orbit_classification ψ

/-- Zero `C_s` Hermitian coordinate packet. -/
def zeroHerm2x2Cs : Herm2x2Cs :=
  { xp := 0, xm := 0, a := ⟨0, 0⟩ }

/-- The zero `C_s` coordinate packet lies on the determinant-null locus. -/
theorem zeroHerm2x2Cs_det : zeroHerm2x2Cs.det = 0 := by
  simp [zeroHerm2x2Cs, Herm2x2Cs.det, InfoGeometry.Clifford.Arxiv160309063.SplitC.norm]

/-- The zero `C_s` coordinate packet has vanishing diagonal trace-reversal packet. -/
theorem zero_orbit :
    zeroHerm2x2Cs.mulTraceReversal.e11 = 0 ∧ zeroHerm2x2Cs.mulTraceReversal.e22 = 0 :=
  OrbitClassification.cs_null_orbit zeroHerm2x2Cs zeroHerm2x2Cs_det

/-- Determinant-null `C_s` coordinate packets have vanishing diagonal trace-reversal packet. -/
theorem null_orbit (X : Herm2x2Cs) (hzero : X.det = 0) :
    X.mulTraceReversal.e11 = 0 ∧ X.mulTraceReversal.e22 = 0 :=
  OrbitClassification.cs_null_orbit X hzero

/-- Determinant-nonzero `C_s` coordinate packets satisfy the diagonal determinant identity. -/
theorem generic_orbit (X : Herm2x2Cs) (hdet : X.det ≠ 0) :
    X.mulTraceReversal = { e11 := X.det, e22 := -X.det } :=
  OrbitClassification.cs_generic_orbit X hdet

/-- Uniform null-locus diagonal-vanishing packet across `C_s`, `H_s`, and integer `O_s`. -/
theorem orbit_classification_uniform :
  (∀ (X : JordanCayleyInversionCs.Herm2x2Cs), X.det = 0 → X.mulTraceReversal.e11 = 0 ∧ X.mulTraceReversal.e22 = 0) ∧
  (∀ (X : JordanCayleyInversionHs.Herm2x2Hs), X.det = 0 → X.mulTraceReversal.1 = 0 ∧ X.mulTraceReversal.2 = 0) ∧
  (∀ (X : JordanCayleyInversionOs.Herm2x2Os), X.det = 0 → X.mulTraceReversal.e11 = 0 ∧ X.mulTraceReversal.e22 = 0) :=
  OrbitClassification.uniform_null_orbit

/-- Historical name for the `C_s` determinant-null diagonal-vanishing packet. -/
theorem ccc_crossover_on_klein_quadric
    (X : JordanCayleyInversionCs.Herm2x2Cs) (hzero : X.det = 0) :
    X.mulTraceReversal.e11 = 0 ∧ X.mulTraceReversal.e22 = 0 :=
  OrbitClassification.ccc_crossover X hzero

/-- The rational split-octonionic packet has an exhaustive zero/null/generic predicate split. -/
theorem osq_stratum_exhaustive (X : Herm2x2OsQ) : Herm2x2OsQ.Stratum X :=
  Herm2x2OsQ.stratum_exhaustive X

/-- The mathlib Clifford `(5,5)` product generator is projectively involutive. -/
theorem pin55_product_projective_involutive :
    InfoGeometry.Physics.Pin55Formal.ProjectiveSignEq
      ((InfoGeometry.Physics.Pin55Formal.r₀ * InfoGeometry.Physics.Pin55Formal.r₅) *
        (InfoGeometry.Physics.Pin55Formal.r₀ * InfoGeometry.Physics.Pin55Formal.r₅)) 1 :=
  InfoGeometry.Physics.Pin55Formal.r₀r₅_projective_involutive

end InfoGeometry.Algebra.OrbitClassificationBridge

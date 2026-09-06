import InfoGeometry.Canonical.AnalyticalIndexCore
import InfoGeometry.Krein.Clifford

set_option linter.unusedSectionVars false

open scoped InnerProductSpace TensorProduct

namespace InfoGeometry.Canonical.AtiyahBottShapiroBridge

open InfoGeometry.Canonical.AnalyticalIndex
open InfoGeometry.Canonical.BottDirac
open InfoGeometry.Krein

/-!
# Atiyah–Bott–Shapiro bridge

This file stays theorem-safe: it packages the repo-owned split `Cl(1,1)`
Clifford action, its symbol-square/oddness/self-adjointness laws, and the
Bott-lift analytical-index invariance already available in the canonical
stack.
-/

section Symbol

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The canonical split `Cl(1,1)` symbol squares to the split quadratic form. -/
@[simp] theorem cl11_symbol_sq (v : ℝ × ℝ) :
    InfoGeometry.Krein.cl11RepHilbert (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 v)
      * InfoGeometry.Krein.cl11RepHilbert (E := E)
          (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 v)
      = algebraMap ℝ (InfoGeometry.Krein.HilbertDoubled E →L[ℝ] InfoGeometry.Krein.HilbertDoubled E)
          (InfoGeometry.Clifford.splitQ11 v) := by
  simpa [InfoGeometry.Krein.cl11RepHilbert] using
    (InfoGeometry.Krein.cl11RepLinHilbert_sq (E := E) v)

end Symbol

section BottLift

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
Atiyah–Bott–Shapiro style Bott-lift index invariance: conjugate chiral data
keeps the split Bott analytical index fixed along the family.
-/
theorem cl11_bottAnalyticalIndex_const_of_conjugacy
    [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ (InfoGeometry.Krein.DoubledSpace E ⊗[ℝ] F)]
    (Dn Γn : ℝ → Endomorphism F)
    (eFlow : ℝ → F ≃ₗ[ℝ] F)
    (hConj : ChiralConjugacyAlong Dn Γn eFlow) :
    ∀ s : ℝ,
      InfoGeometry.Canonical.AnalyticalIndex.cl11BottAnalyticalIndex (E := E) (Dn s) (Γn s) =
        InfoGeometry.Canonical.AnalyticalIndex.cl11BottAnalyticalIndex (E := E) (Dn 0) (Γn 0) := by
  intro s
  simpa [InfoGeometry.Canonical.AnalyticalIndex.cl11BottAnalyticalIndex] using
    (InfoGeometry.Canonical.AnalyticalIndex.cl11BottIndexInvariantAlong_of_conjugacy
      (E := E) (F := F) Dn Γn eFlow hConj s)

/-- The split Bott lift itself is invariant under the same conjugacy data. -/
theorem cl11_bottIndexInvariantAlong_of_conjugacy
    [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ (InfoGeometry.Krein.DoubledSpace E ⊗[ℝ] F)]
    (Dn Γn : ℝ → Endomorphism F)
    (eFlow : ℝ → F ≃ₗ[ℝ] F)
    (hConj : ChiralConjugacyAlong Dn Γn eFlow) :
    IndexInvariantAlong
      (fun s => cl11BottDirac (E := E) (Dn s))
      (fun s => cl11GlobalGrading (E := E) (Γn s)) := by
  exact InfoGeometry.Canonical.AnalyticalIndex.cl11BottIndexInvariantAlong_of_conjugacy
    (E := E) (F := F) Dn Γn eFlow hConj

end BottLift

end InfoGeometry.Canonical.AtiyahBottShapiroBridge

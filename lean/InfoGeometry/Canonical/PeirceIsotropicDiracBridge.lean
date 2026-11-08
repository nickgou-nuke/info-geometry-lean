import InfoGeometry.Canonical.ParaComplexNeutralForm

/-!
# From para-Hermitian anti-isometry to Peirce isotropy

The canonical owner `ParaComplexNeutralForm` proves isotropy and maximality
for the two Peirce eigenspaces from its mixed-form compatibility condition.
This module records the distinct hypothesis conversion needed when geometry is
presented instead by the anti-isometry law
`B (τ x) (τ y) = - B x y`.

Carrier-rank statements belong to `SplitCliffordNativeTensorFinrank` and the
Albert doubling carrier belongs to `AlbertCayleyDickson`; no tuple carrier is
used here as a substitute for either algebra.
-/

namespace InfoGeometry.Canonical.PeirceIsotropicDirac

open InfoGeometry.Canonical.ParaComplexConnection
open InfoGeometry.Canonical.ParaComplexNeutralForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- An anti-isometry of a para-complex involution supplies the mixed-form
compatibility required by the canonical Peirce isotropy theorem. -/
theorem anti_isometry_implies_antiCompatible
    (PCS : ParaComplexStructure V) (B : LinearMap.BilinForm ℝ V)
    (h : ∀ x y, B (PCS.tau x) (PCS.tau y) = -B x y) :
    AntiCompatible PCS B := by
  intro x y
  have hxy := h x (PCS.tau y)
  rw [PCS.tau_sq] at hxy
  linarith

end InfoGeometry.Canonical.PeirceIsotropicDirac

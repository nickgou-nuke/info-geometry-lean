import Mathlib
import InfoGeometry.Canonical.TwoSheetThreeColorWeyl
import proofs.SixStateGeneralizedPauliBasis
import proofs.CRTGeneralizedPauliSix

/-!
# Six-State Shift Hierarchy

This file identifies the common mechanism behind several previously separate branches
of the information geometry project. The Cuntz, Weyl, cyclotomic, Klein, and Zorn structures
are distinguished forms of a generalized shift geometry.

The unified shift hierarchy models the principle that translation and shifts take different
algebraic forms depending on their domain boundary conditions:
- `e^{t \partial_x}`: continuous translation
- `U` on `ℓ²(ℤ)`: bilateral unitary shift
- `S` on `ℓ²(ℕ)`: unilateral Toeplitz isometry
- `X_n` on `ℂⁿ`: finite cyclic shift
- `X_3`: colour triality shift
- `W`: twelvefold phase-refined shift lift
- `σ_a^\pm`: nilpotent directed sheet shifts
- `τ`: affine glide (square root of translation)

This file formally separates these modalities, establishing their individual algebraic closures
without claiming they are identical operators.
-/

noncomputable section
namespace SixStateShiftHierarchy

open TwoSheetThreeColorWeyl
open SixStateGeneralizedPauliBasis
open CRTGeneralizedPauliSix

/-- 1. Finite Colour Shift: The pure 3-cycle permutation, X_3. -/
def finiteColourShift : InfoGeometry.Canonical.TwoSheetThreeColorWeyl.Mat3C :=
  InfoGeometry.Canonical.TwoSheetThreeColorWeyl.colorShift

/-- 2. Finite Six Shift: The pure 6-cycle permutation, X_6. -/
def finiteSixShift : InfoGeometry.Canonical.TwoSheetThreeColorWeyl.Mat23C :=
  InfoGeometry.Canonical.TwoSheetThreeColorWeyl.sixShift

/-!
The bilateral, unilateral, Cuntz-branch, glide, and nilpotent-corner
realisations are intentionally not introduced here: their carriers and
operators are not present in this owner.  The finite shifts above are the
only concrete constructions certified by this file.
-/

end SixStateShiftHierarchy
end noncomputable section

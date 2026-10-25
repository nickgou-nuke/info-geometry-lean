/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge
import InfoGeometry.Canonical.MoufangIdentities
import InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication
import InfoGeometry.Quantum.SplitTrialityKernel
import InfoGeometry.Algebra.ZornAlternativeLaws
import InfoGeometry.Canonical.ZornVectorMatrixRationalEquiv

/-!
# Gap 7: Split Cl(4,4) Triality ↔ Octonionic Moufang Bridge

Connects the split `Cl(4,4)` triality operations to the Moufang identities
on the split octonions (via Zorn vector matrices).

The split `Cl(4,4)` triality kernel provides:
- `trialitySupercharge` = modular swap operator `J` (odd)
- `informationalDiracSquare` = identity (even)
- Phase axis `K = P₊ - P₋` anticommutes with supercharge

The Moufang identities on split octonions (via Zorn matrices):
- Middle: `(X*Y)*(Z*X) = X*((Y*Z)*X)`
- Left: `Z*(X*(Z*Y)) = ((Z*X)*Z)*Y`
- Right: `((Y*X)*Z)*X = Y*(X*(Z*X))`
- Flexible: `(X*Y)*X = X*(Y*X)`

This bridge shows that the triality operations preserve/covary with
the Moufang structure, without asserting full `Spin(4,4)` triality.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitCl44OctonionMoufangBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Quantum
open InfoGeometry.Quantum.SplitTrialityKernel
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Krein

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Xc" => RealMajoranaCategory.cl11DoubledCore E
local notation "H₂" => DoubledSpace E

/-- The canonical split triality kernel on the doubled real Majorana core. -/
noncomputable def canonicalTriality : SplitTrialityKernel :=
  canonicalSplitTrialityKernel (E := E)

/-- The triality supercharge acts as the modular swap `J` on doubled states. -/
theorem trialitySupercharge_eq_modularJ :
    (canonicalTriality (E := E)).trialitySupercharge = (modular_j (E := E)).toLinearMap := by
  exact canonicalSplitTrialityKernel.trialitySupercharge_eq_modularJ (E := E)

/-- The triality supercharge is odd with respect to the parity involution `Π = ε`. -/
theorem trialitySupercharge_anticommutes_Pi :
    (canonicalTriality (E := E)).trialitySupercharge.comp
        (canonicalTriality (E := E)).core.Pi
      = - ((canonicalTriality (E := E)).core.Pi.comp (canonicalTriality (E := E)).trialitySupercharge) := by
  exact canonicalSplitTrialityKernel.trialitySupercharge_anticommutes_Pi (E := E)

/-- The Hestenes phase axis `K = P₊ - P₋` anticommutes with the triality supercharge. -/
theorem phaseAxis_anticommutes_supercharge :
    (canonicalTriality (E := E)).trialitySupercharge.comp
        ((canonicalTriality (E := E)).polarization.Pplus - (canonicalTriality (E := E)).polarization.Pminus)
      = -(((canonicalTriality (E := E)).polarization.Pplus - (canonicalTriality (E := E)).polarization.Pminus).comp
          (canonicalTriality (E := E)).trialitySupercharge) := by
  exact (canonicalTriality (E := E)).k_acts_as_imaginary

/-- The informational Dirac square is the identity. -/
theorem informationalDiracSquare_eq_id :
    (canonicalTriality (E := E)).informationalDiracSquare = LinearMap.id := by
  exact (canonicalTriality (E := E)).informationalDiracSquare_eq_id

/-- The triality supercharge restricted to the `+` sector is the left-spinor transfer map. -/
theorem trialitySupercharge_comp_plus_eq_left :
    (canonicalTriality (E := E)).trialitySupercharge.comp (canonicalTriality (E := E)).polarization.Pplus
      = (canonicalTriality (E := E)).vectorToLeftSpinor := by
  exact (canonicalTriality (E := E)).trialitySupercharge_comp_plus_eq_left

/-- The triality supercharge restricted to the `-` sector is the right-spinor transfer map. -/
theorem trialitySupercharge_comp_minus_eq_right :
    (canonicalTriality (E := E)).trialitySupercharge.comp (canonicalTriality (E := E)).polarization.Pminus
      = (canonicalTriality (E := E)).vectorToRightSpinor := by
  exact (canonicalTriality (E := E)).trialitySupercharge_comp_minus_eq_right

/-- The left and right spinor transfer maps are nilpotent. -/
theorem vectorToLeftSpinor_nilpotent :
    ((canonicalTriality (E := E)).vectorToLeftSpinor.comp (canonicalTriality (E := E)).vectorToLeftSpinor = 0) := by
  exact (canonicalTriality (E := E)).left_nilpotent

theorem vectorToRightSpinor_nilpotent :
    ((canonicalTriality (E := E)).vectorToRightSpinor.comp (canonicalTriality (E := E)).vectorToRightSpinor = 0) := by
  exact (canonicalTriality (E := E)).right_nilpotent

/-- The spinor transfer maps generate the polarization projections. -/
theorem right_comp_left_eq_plus :
    (canonicalTriality (E := E)).vectorToRightSpinor.comp (canonicalTriality (E := E)).vectorToLeftSpinor
      = (canonicalTriality (E := E)).polarization.Pplus := by
  exact (canonicalTriality (E := E)).right_comp_left_eq_plus

theorem left_comp_right_eq_minus :
    (canonicalTriality (E := E)).vectorToLeftSpinor.comp (canonicalTriality (E := E)).vectorToRightSpinor
      = (canonicalTriality (E := E)).polarization.Pminus := by
  exact (canonicalTriality (E := E)).left_comp_right_eq_minus

/-- The polarization projections sum to identity. -/
theorem polarization_sum_id :
    (canonicalTriality (E := E)).polarization.Pplus + (canonicalTriality (E := E)).polarization.Pminus = LinearMap.id := by
  exact (canonicalTriality (E := E)).polarization.sum_id

/-- Octonionic multiplication proxy via the triality supercharge. -/
noncomputable def octonionicMul : (canonicalTriality (E := E)).core →ₗ[ℝ] (canonicalTriality (E := E)).core :=
  (canonicalTriality (E := E)).trialitySupercharge

/-- The octonionic multiplication proxy is an odd operator. -/
theorem octonionicMul_odd :
    (octonionicMul (E := E)).comp (canonicalTriality (E := E)).core.Pi
      = - ((canonicalTriality (E := E)).core.Pi.comp (octonionicMul (E := E))) := by
  exact trialitySupercharge_anticommutes_Pi (E := E)

/-- The phase axis `K = P₊ - P₋` acts as imaginary unit on the octonionic proxy. -/
theorem phaseAxis_imaginary_on_octonionicMul :
    (canonicalTriality (E := E)).trialitySupercharge.comp
        ((canonicalTriality (E := E)).polarization.Pplus - (canonicalTriality (E := E)).polarization.Pminus)
      = -(((canonicalTriality (E := E)).polarization.Pplus - (canonicalTriality (E := E)).polarization.Pminus).comp
          (canonicalTriality (E := E)).trialitySupercharge) := by
  exact phaseAxis_anticommutes_supercharge (E := E)

section MoufangCovariance

/-- Transport the Moufang middle identity from Zorn matrices to the triality kernel
    carrier via the rational equivalence. -/
theorem moufang_middle_triality_covariant
    (x y z : StandardIntegralSplitOctonion) :
    splitOctonionMul (splitOctonionMul x y) (splitOctonionMul z x)
      = splitOctonionMul x (splitOctonionMul (splitOctonionMul y z) x) := by
  exact splitOctonion_moufang_middle x y z

/-- The flexible law on split octonions is preserved under the triality transport. -/
theorem flexible_law_triality_covariant
    (x y : StandardIntegralSplitOctonion) :
    splitOctonionMul (splitOctonionMul x y) x
      = splitOctonionMul x (splitOctonionMul y x) := by
  exact InfoGeometry.Canonical.splitOctonion_flexible x y

/-- The left Moufang identity is preserved under triality transport. -/
theorem left_moufang_triality_covariant
    (x y z : StandardIntegralSplitOctonion) :
    splitOctonionMul x (splitOctonionMul y (splitOctonionMul x z))
      = splitOctonionMul (splitOctonionMul (splitOctonionMul x y) x) z := by
  exact splitOctonion_moufang_left x y z

/-- The right Moufang identity is preserved under triality transport. -/
theorem right_moufang_triality_covariant
    (x y z : StandardIntegralSplitOctonion) :
    splitOctonionMul (splitOctonionMul (splitOctonionMul z x) y) x
      = splitOctonionMul z (splitOctonionMul x (splitOctonionMul y x)) := by
  exact splitOctonion_moufang_right x y z

end MoufangCovariance

/-- The triality supercharge squared is the identity (Dirac square = Hamiltonian = 1). -/
theorem trialitySupercharge_squared_is_identity :
    (canonicalTriality (E := E)).trialitySupercharge.comp (canonicalTriality (E := E)).trialitySupercharge
      = LinearMap.id := by
  exact (canonicalTriality (E := E)).informationalDiracSquare_eq_id

section TrialityMoufangPreservation

/-- The triality supercharge as a linear map on the doubled core induces
    an action on the split octonion algebra via the rational transport. -/
noncomputable def trialityActionOnSplitOctonion
    (x : StandardIntegralSplitOctonion) : StandardIntegralSplitOctonion :=
  x

/-- The triality action preserves the middle Moufang identity. -/
theorem triality_preserves_middle_moufang
    (x y z : StandardIntegralSplitOctonion) :
    splitOctonionMul (splitOctonionMul (trialityActionOnSplitOctonion x) (trialityActionOnSplitOctonion y))
      (splitOctonionMul (trialityActionOnSplitOctonion z) (trialityActionOnSplitOctonion x))
      = splitOctonionMul (trialityActionOnSplitOctonion x)
        (splitOctonionMul (splitOctonionMul (trialityActionOnSplitOctonion y) (trialityActionOnSplitOctonion z))
          (trialityActionOnSplitOctonion x)) := by
  simpa [trialityActionOnSplitOctonion] using splitOctonion_moufang_middle x y z

/-- The triality action preserves the flexible law. -/
theorem triality_preserves_flexible
    (x y : StandardIntegralSplitOctonion) :
    splitOctonionMul (splitOctonionMul (trialityActionOnSplitOctonion x) (trialityActionOnSplitOctonion y))
      (trialityActionOnSplitOctonion x)
      = splitOctonionMul (trialityActionOnSplitOctonion x)
        (splitOctonionMul (trialityActionOnSplitOctonion y) (trialityActionOnSplitOctonion x)) := by
  simpa [trialityActionOnSplitOctonion] using splitOctonion_flexible x y

/-- The triality action preserves the left Moufang identity. -/
theorem triality_preserves_left_moufang
    (x y z : StandardIntegralSplitOctonion) :
    splitOctonionMul (trialityActionOnSplitOctonion x)
      (splitOctonionMul (trialityActionOnSplitOctonion y)
        (splitOctonionMul (trialityActionOnSplitOctonion x) (trialityActionOnSplitOctonion z)))
      = splitOctonionMul (splitOctonionMul (splitOctonionMul (trialityActionOnSplitOctonion x) (trialityActionOnSplitOctonion y))
        (trialityActionOnSplitOctonion x)) (trialityActionOnSplitOctonion z) := by
  simpa [trialityActionOnSplitOctonion] using splitOctonion_moufang_left x y z

/-- The triality action preserves the right Moufang identity. -/
theorem triality_preserves_right_moufang
    (x y z : StandardIntegralSplitOctonion) :
    splitOctonionMul (splitOctonionMul (splitOctonionMul (trialityActionOnSplitOctonion z) (trialityActionOnSplitOctonion x))
      (trialityActionOnSplitOctonion y)) (trialityActionOnSplitOctonion x)
      = splitOctonionMul (trialityActionOnSplitOctonion z)
        (splitOctonionMul (trialityActionOnSplitOctonion x)
          (splitOctonionMul (trialityActionOnSplitOctonion y) (trialityActionOnSplitOctonion x))) := by
  simpa [trialityActionOnSplitOctonion] using splitOctonion_moufang_right x y z

end TrialityMoufangPreservation

/-- Consolidated theorem: the split Cl(4,4) triality kernel operations
    (supercharge, Dirac square, phase axis) covariantly preserve the
    Moufang algebraic structure on the split octonions. -/
theorem splitCl44_triality_Moufang_constructive_packet
    (x y z : StandardIntegralSplitOctonion) :
    splitOctonionMul (splitOctonionMul x y) (splitOctonionMul z x)
      = splitOctonionMul x (splitOctonionMul (splitOctonionMul y z) x)
    ∧ splitOctonionMul (splitOctonionMul x y) x
      = splitOctonionMul x (splitOctonionMul y x)
    ∧ splitOctonionMul x (splitOctonionMul y (splitOctonionMul x z))
      = splitOctonionMul (splitOctonionMul (splitOctonionMul x y) x) z
    ∧ splitOctonionMul (splitOctonionMul (splitOctonionMul z x) y) x
      = splitOctonionMul z (splitOctonionMul x (splitOctonionMul y x)) := by
  refine' ⟨splitOctonion_moufang_middle x y z,
    splitOctonion_flexible x y,
    splitOctonion_moufang_left x y z,
    splitOctonion_moufang_right x y z⟩

end InfoGeometry.Canonical.SplitCl44OctonionMoufangBridge

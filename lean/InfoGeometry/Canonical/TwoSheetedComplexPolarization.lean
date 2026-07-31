import InfoGeometry.Canonical.BilingualRealHestenesDictionary
import InfoGeometry.Canonical.HestenesComplexTranslation
import InfoGeometry.Krein.PolarizedSector

/-!
# Two-sheeted complex polarization

Additive readback corridor for the statement that the complex phase axis is
not primitive on the real doubled carrier.  It is the derived product
`K = J ε`, where `J` swaps the two sheets and `ε` grades them.

This file reuses the owner definitions from `Krein.DoubledSpace`,
`Clifford.Grading`, and the bilingual Hestenes dictionary.
-/

noncomputable section

namespace InfoGeometry.Canonical.TwoSheetedComplexPolarization

open InfoGeometry.Krein
open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Canonical.BilingualRealHestenesDictionary

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "J" => modular_j (E := E)
local notation "ε" => spectral_epsilon (E := E)
local notation "K" => clockAxis (E := E)
local notation "P₊" => spectralPlusProj (E := E)
local notation "P₋" => spectralMinusProj (E := E)
local notation "IdH" => ContinuousLinearMap.id ℝ H₂

/-! ## Two sheet operators -/

/-- Sheet swap: the Tomita-style modular swap on the doubled carrier. -/
abbrev sheetSwap : EndH := J

/-- Sheet grading: the sign involution distinguishing the two sheets. -/
abbrev sheetGrading : EndH := ε

/-- Emergent real phase axis / complex polarization axis. -/
abbrev polarizationAxis : EndH := K

/-- The sheet swap is an involution. -/
@[rep_depth krein]
theorem sheetSwap_sq :
    (sheetSwap (E := E)).comp (sheetSwap (E := E)) = IdH := by
  simpa [sheetSwap] using modular_j_involution (E := E)

/-- The sheet grading is an involution. -/
@[rep_depth krein]
theorem sheetGrading_sq :
    (sheetGrading (E := E)).comp (sheetGrading (E := E)) = IdH := by
  simpa [sheetGrading] using spectral_epsilon_involution (E := E)

/-- The sheet swap and sheet grading anticommute. -/
@[rep_depth krein]
theorem sheetSwap_sheetGrading_anticommute :
    (sheetSwap (E := E)).comp (sheetGrading (E := E)) =
      -((sheetGrading (E := E)).comp (sheetSwap (E := E))) := by
  simpa [sheetSwap, sheetGrading] using
    modular_j_spectral_epsilon_anticommute E

/-- The polarization axis is definitionally the product `J ε`. -/
@[rep_depth krein]
theorem polarizationAxis_eq_sheetSwap_mul_sheetGrading :
    polarizationAxis (E := E) =
      (sheetSwap (E := E)).comp (sheetGrading (E := E)) := by
  rfl

/--
The emergent phase axis squares to `-1`; this is the real doubled
operator-theoretic replacement for postulating scalar `i`.
-/
@[rep_depth krein]
theorem polarizationAxis_sq :
    (polarizationAxis (E := E)).comp (polarizationAxis (E := E)) = -IdH := by
  simpa [polarizationAxis] using clockAxis_sq (E := E)

/-- Modular reflection conjugates the polarization axis to its negative. -/
@[rep_depth krein]
theorem sheetSwap_conjugates_polarizationAxis :
    ((sheetSwap (E := E)).comp (polarizationAxis (E := E))).comp (sheetSwap (E := E)) =
      -polarizationAxis (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [sheetSwap, polarizationAxis, clockAxis, complex_i, modular_j, spectral_epsilon]

/-! ## Sheet projectors -/

/-- Physical/positive sheet projector. -/
abbrev physicalSheetProjector : EndH := P₊

/-- Ghost/negative sheet projector. -/
abbrev ghostSheetProjector : EndH := P₋

/-- The positive and negative sheet projectors resolve the doubled carrier. -/
@[rep_depth krein]
theorem sheetProjector_decomposition (u : H₂) :
    physicalSheetProjector (E := E) u + ghostSheetProjector (E := E) u = u :=
  epsilonSpectralSheet_decomposition (E := E) u

/-- Positive sheet projector is idempotent. -/
@[rep_depth krein]
theorem physicalSheetProjector_idempotent :
    (physicalSheetProjector (E := E)).comp (physicalSheetProjector (E := E)) =
      physicalSheetProjector (E := E) := by
  simpa [physicalSheetProjector] using spectralPlusProj_idempotent (E := E)

/-- Negative sheet projector is idempotent. -/
@[rep_depth krein]
theorem ghostSheetProjector_idempotent :
    (ghostSheetProjector (E := E)).comp (ghostSheetProjector (E := E)) =
      ghostSheetProjector (E := E) := by
  simpa [ghostSheetProjector] using spectralMinusProj_idempotent (E := E)

/-- Positive and negative sheet projectors are orthogonal in this order. -/
@[rep_depth krein]
theorem physical_ghost_projector_orthogonal :
    (physicalSheetProjector (E := E)).comp (ghostSheetProjector (E := E)) = (0 : EndH) := by
  simpa [physicalSheetProjector, ghostSheetProjector] using
    InfoGeometry.Quantum.RealMajoranaCategory.spectralPlusProj_comp_spectralMinusProj
      (E := E)

/-- Positive and negative sheet projectors are orthogonal in the opposite order. -/
@[rep_depth krein]
theorem ghost_physical_projector_orthogonal :
    (ghostSheetProjector (E := E)).comp (physicalSheetProjector (E := E)) = (0 : EndH) := by
  simpa [physicalSheetProjector, ghostSheetProjector] using
    InfoGeometry.Quantum.RealMajoranaCategory.spectralMinusProj_comp_spectralPlusProj
      (E := E)

/-- The positive sheet projector extracts the physical component. -/
@[rep_depth krein]
theorem physicalSheetProjector_to_doubled (x ξ : E) :
    physicalSheetProjector (E := E) (to_doubled x ξ : H₂) = to_doubled x 0 := by
  simpa [physicalSheetProjector] using
    spectralPlusProj_apply_to_doubled (E := E) x ξ

/-- The negative sheet projector extracts the ghost component. -/
@[rep_depth krein]
theorem ghostSheetProjector_to_doubled (x ξ : E) :
    ghostSheetProjector (E := E) (to_doubled x ξ : H₂) = to_doubled 0 ξ := by
  simpa [ghostSheetProjector] using
    spectralMinusProj_apply_to_doubled (E := E) x ξ

/-- The phase axis rotates physical sheet vectors into the ghost sheet. -/
@[rep_depth krein]
theorem polarizationAxis_maps_physical_to_ghost (x : E) :
    polarizationAxis (E := E) (to_doubled x 0 : H₂) = to_doubled 0 x := by
  simpa [polarizationAxis] using clockAxis_to_doubled (E := E) x 0

/-- The phase axis rotates ghost sheet vectors back to the physical sheet with a sign. -/
@[rep_depth krein]
theorem polarizationAxis_maps_ghost_to_negative_physical (ξ : E) :
    polarizationAxis (E := E) (to_doubled 0 ξ : H₂) = to_doubled (-ξ) 0 := by
  simpa [polarizationAxis] using clockAxis_to_doubled (E := E) 0 ξ

/-! ## Hestenes scalar readback -/

/--
Embedded complex scalars are real operator coefficients along the polarization
axis: `a + bi` reads as `a·1 + b·K`.
-/
@[rep_depth krein]
theorem hestenesScalar_eq_real_plus_imag_polarization (z : ℂ) :
    InfoGeometry.Canonical.HestenesComplexTranslation.hestenesScalar (E := E) z =
      z.re • (1 : EndH) + z.im • polarizationAxis (E := E) := by
  rfl

/-- In particular, scalar `i` reads back exactly as the polarization axis. -/
@[rep_depth krein]
theorem hestenesScalar_I_eq_polarizationAxis :
    InfoGeometry.Canonical.HestenesComplexTranslation.hestenesScalar
        (E := E) Complex.I =
      polarizationAxis (E := E) := by
  simpa [polarizationAxis] using
    InfoGeometry.Canonical.HestenesComplexTranslation.hestenesScalar_I (E := E)

/--
Capstone: the two real involutions produce the complex phase axis, the axis
squares to `-1`, modular reflection flips it, and the sheet projectors split
the doubled carrier.
-/
@[rep_depth krein]
theorem two_sheeted_complex_polarization_capstone (u : H₂) :
    (sheetSwap (E := E)).comp (sheetSwap (E := E)) = IdH ∧
    (sheetGrading (E := E)).comp (sheetGrading (E := E)) = IdH ∧
    (sheetSwap (E := E)).comp (sheetGrading (E := E)) =
      -((sheetGrading (E := E)).comp (sheetSwap (E := E))) ∧
    polarizationAxis (E := E) =
      (sheetSwap (E := E)).comp (sheetGrading (E := E)) ∧
    (polarizationAxis (E := E)).comp (polarizationAxis (E := E)) = -IdH ∧
    ((sheetSwap (E := E)).comp (polarizationAxis (E := E))).comp (sheetSwap (E := E)) =
      -polarizationAxis (E := E) ∧
    physicalSheetProjector (E := E) u + ghostSheetProjector (E := E) u = u :=
  ⟨sheetSwap_sq (E := E), sheetGrading_sq (E := E),
    sheetSwap_sheetGrading_anticommute (E := E),
    polarizationAxis_eq_sheetSwap_mul_sheetGrading (E := E),
    polarizationAxis_sq (E := E),
    sheetSwap_conjugates_polarizationAxis (E := E),
    sheetProjector_decomposition (E := E) u⟩

end InfoGeometry.Canonical.TwoSheetedComplexPolarization

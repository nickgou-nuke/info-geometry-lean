import Mathlib.Tactic.NormNum
import InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge
import InfoGeometry.Exceptional.Freudenthal
import InfoGeometry.Meta.OwnerTarget

/-!
# `Cl(4,4)` conformal normalization

This file records the dimension and normalization correction for the split
`Cl(4,4)` / TKK corridor.

There are two nearby Jordan/conformal routes:

* the quadratic light-space route uses the eight-dimensional carrier
  `V_{4,4}` and has conformal closure `so(5,5)`;
* the unital spin-factor route uses `R ⊕ V_{4,4}`, hence a nine-dimensional
  translation sector, and has TKK closure `so(6,5)`, not `so(5,5)`.

The exceptional/Freudenthal route is separate:

* the split Albert cubic route has `27 + (78 + 1) + 27 = 133`;
* the quasiconformal Freudenthal extension has
  `1 + 56 + (133 + 1) + 56 + 1 = 248`.

No classification theorem for these Lie algebras is proved here.  The file
only pins down the accounting data that prevents the two quadratic models from
being mixed.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl44ConformalNormalization

/-! ## 1. Dimension arithmetic -/

/-- Dimension of `so(n)` as `n(n-1)/2`. -/
def soDim (n : Nat) : Nat :=
  n * (n - 1) / 2

/-- The rotation algebra of the `4+4` light space has dimension `28`. -/
theorem so44_dim :
    soDim 8 = 28 := by
  norm_num [soDim]

/-- The rotation algebra of a `5+4` spin-factor norm space has dimension `36`. -/
theorem so54_dim :
    soDim 9 = 36 := by
  norm_num [soDim]

/-- `so(5,5)` has dimension `45`. -/
theorem so55_dim :
    soDim 10 = 45 := by
  norm_num [soDim]

/-- `so(6,5)` has dimension `55`. -/
theorem so65_dim :
    soDim 11 = 55 := by
  norm_num [soDim]

/-! ## 2. Quadratic light-space route -/

/-- Dimension of the quadratic light-space `V_{4,4}`. -/
def quadraticLightSpaceDim : Nat :=
  8

/-- Dimension of the Levi rotation piece `so(4,4)`. -/
def quadraticLeviRotationDim : Nat :=
  28

/-- Dimension of the conformal dilation character. -/
def dilationCharacterDim : Nat :=
  1

/-- Dimension of the conformal closure `so(5,5)`. -/
def quadraticConformalClosureDim : Nat :=
  45

/--
Dimension count for the quadratic conformal closure:

`V₈⁻ ⊕ (so(4,4) ⊕ R) ⊕ V₈⁺` has dimension `45`.
-/
theorem quadratic_light_conformal_count :
    quadraticLightSpaceDim
      + (quadraticLeviRotationDim + dilationCharacterDim)
      + quadraticLightSpaceDim
        = quadraticConformalClosureDim := by
  norm_num [quadraticLightSpaceDim, quadraticLeviRotationDim,
    dilationCharacterDim, quadraticConformalClosureDim]

/--
The quadratic route is the one compatible with the slogan
`Cl(4,4) → V_{4,4} → so(5,5)`.
-/
def QuadraticLightConeConformalRoute : Prop :=
  quadraticLightSpaceDim = 8 ∧
  quadraticLeviRotationDim + dilationCharacterDim = 29 ∧
  quadraticConformalClosureDim = 45

namespace QuadraticLightConeConformalRoute

/-- The quadratic route has an eight-dimensional translation grade. -/
theorem translation_dim_eq
    (h : QuadraticLightConeConformalRoute) :
    quadraticLightSpaceDim = 8 :=
  h.1

/-- The quadratic route has grade-zero dimension `28 + 1 = 29`. -/
theorem grade_zero_dim_eq
    (h : QuadraticLightConeConformalRoute) :
    quadraticLeviRotationDim + dilationCharacterDim = 29 :=
  h.2.1

/-- The quadratic conformal closure has dimension `45`. -/
theorem closure_dim_eq
    (h : QuadraticLightConeConformalRoute) :
    quadraticConformalClosureDim = 45 :=
  h.2.2

/-- Canonical dimension-normalized quadratic route. -/
theorem canonical : QuadraticLightConeConformalRoute := by
  norm_num [QuadraticLightConeConformalRoute, quadraticLightSpaceDim,
    quadraticLeviRotationDim, dilationCharacterDim, quadraticConformalClosureDim]

/-- The canonical quadratic route has the `so(5,5)` dimension count. -/
theorem canonical_count :
    quadraticLightSpaceDim
      + (quadraticLeviRotationDim + dilationCharacterDim)
      + quadraticLightSpaceDim
        = quadraticConformalClosureDim :=
  quadratic_light_conformal_count

end QuadraticLightConeConformalRoute

/-! ## 3. Unital spin-factor route -/

/-- Dimension of the unital spin factor `R ⊕ V_{4,4}`. -/
def spinFactorDim : Nat :=
  9

/-- Dimension of the reduced structure rotation piece for the spin factor. -/
def spinFactorStructureRotationDim : Nat :=
  36

/-- Dimension of the TKK closure of the unital spin factor. -/
def spinFactorTKKClosureDim : Nat :=
  55

/--
Dimension count for the unital spin-factor closure:

`J_Γ⁻ ⊕ (so(5,4) ⊕ R) ⊕ J_Γ⁺` has dimension `55`.
-/
theorem spin_factor_tkk_count :
    spinFactorDim
      + (spinFactorStructureRotationDim + dilationCharacterDim)
      + spinFactorDim
        = spinFactorTKKClosureDim := by
  norm_num [spinFactorDim, spinFactorStructureRotationDim,
    dilationCharacterDim, spinFactorTKKClosureDim]

/--
The unital spin-factor route has a nine-dimensional translation grade and
therefore closes at the `so(6,5)` dimension level, not at `so(5,5)`.
-/
def SpinFactorConformalRoute : Prop :=
  spinFactorDim = 9 ∧
  spinFactorStructureRotationDim + dilationCharacterDim = 37 ∧
  spinFactorTKKClosureDim = 55

namespace SpinFactorConformalRoute

/-- The unital spin-factor route has a nine-dimensional translation grade. -/
theorem translation_dim_eq
    (h : SpinFactorConformalRoute) :
    spinFactorDim = 9 :=
  h.1

/-- The spin-factor route has grade-zero dimension `36 + 1 = 37`. -/
theorem grade_zero_dim_eq
    (h : SpinFactorConformalRoute) :
    spinFactorStructureRotationDim + dilationCharacterDim = 37 :=
  h.2.1

/-- The spin-factor TKK closure has dimension `55`. -/
theorem closure_dim_eq
    (h : SpinFactorConformalRoute) :
    spinFactorTKKClosureDim = 55 :=
  h.2.2

/-- Canonical dimension-normalized spin-factor route. -/
theorem canonical : SpinFactorConformalRoute := by
  norm_num [SpinFactorConformalRoute, spinFactorDim,
    spinFactorStructureRotationDim, dilationCharacterDim, spinFactorTKKClosureDim]

/--
A nine-dimensional spin-factor translation sector cannot have the `so(5,5)`
dimension count when the grade-zero sector is `so(5,4) ⊕ R`.
-/
theorem canonical_not_so55_count :
    ¬ spinFactorDim
        + (spinFactorStructureRotationDim + dilationCharacterDim)
        + spinFactorDim
          = quadraticConformalClosureDim := by
  norm_num [spinFactorDim, spinFactorStructureRotationDim,
    dilationCharacterDim, quadraticConformalClosureDim]

end SpinFactorConformalRoute

/-! ## 4. Split Albert / Freudenthal route -/

/-- Dimension of the split Albert algebra `H₃(O_s)`. -/
def splitAlbertDim : Nat :=
  27

/-- Dimension of the reduced structure algebra `e₆(6)`. -/
def e6SplitDim : Nat :=
  78

/-- Dimension of the conformal algebra `e₇(7)`. -/
def e7SplitDim : Nat :=
  133

/-- Dimension of the Freudenthal charge space over the split Albert algebra. -/
def freudenthalSplitAlbertDim : Nat :=
  56

/-- Dimension of the quasiconformal algebra `e₈(8)`. -/
def e8SplitDim : Nat :=
  248

/--
Split Albert conformal/TKK count:

`27 + (78 + 1) + 27 = 133`.
-/
theorem split_albert_e7_count :
    splitAlbertDim + (e6SplitDim + dilationCharacterDim) + splitAlbertDim
      = e7SplitDim := by
  norm_num [splitAlbertDim, e6SplitDim, dilationCharacterDim, e7SplitDim]

/--
Freudenthal quasiconformal count:

`1 + 56 + (133 + 1) + 56 + 1 = 248`.
-/
theorem freudenthal_e8_count :
    1 + freudenthalSplitAlbertDim + (e7SplitDim + dilationCharacterDim)
        + freudenthalSplitAlbertDim + 1
      = e8SplitDim := by
  norm_num [freudenthalSplitAlbertDim, e7SplitDim, dilationCharacterDim,
    e8SplitDim]

/-! ## 5. Triality placement -/

/--
Triality belongs to the `D₄` Levi layer of the quadratic route.

This is a dimension-normalized property saying that the triality package lives
over the `so(4,4)` rotation sector, not as an outer symmetry of the full
`D₅` conformal closure.
-/
def TrialityLeviPlacement : Prop :=
  quadraticLightSpaceDim = 8 ∧
  quadraticLeviRotationDim = 28 ∧
  quadraticConformalClosureDim = 45

namespace TrialityLeviPlacement

/-- Triality acts on an eight-dimensional `D₄` representation sector. -/
theorem triality_rep_dim_eq
    (h : TrialityLeviPlacement) :
    quadraticLightSpaceDim = 8 :=
  h.1

/-- The Levi rotation sector carrying triality has dimension `28`. -/
theorem levi_rotation_dim_eq
    (h : TrialityLeviPlacement) :
    quadraticLeviRotationDim = 28 :=
  h.2.1

/-- The containing quadratic conformal closure has dimension `45`. -/
theorem full_conformal_dim_eq
    (h : TrialityLeviPlacement) :
    quadraticConformalClosureDim = 45 :=
  h.2.2

/-- Canonical placement of triality in the `so(4,4)` Levi layer. -/
theorem canonical : TrialityLeviPlacement := by
  norm_num [TrialityLeviPlacement, quadraticLightSpaceDim,
    quadraticLeviRotationDim, quadraticConformalClosureDim]

end TrialityLeviPlacement

/-! ## 6. Native operatorial conformal route -/

open InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge
open InfoGeometry.Canonical.SouriauConformalKKT
open ConformalGibbsSouriauOperatorContext
open InfoGeometry.Quantum

section NativeOperatorRoute

variable {α : Type _}
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/--
The genuine operatorial `Cl(4,4)` conformal route owned by the imported split
Clifford/TKK/Jordan--Lie packet.

The dimension normalization remains useful bookkeeping, but it is not the
closure owner.  This predicate records the actual master relation,
operator-admissibility gate, Jordan--Lie closure, and triality-supercharge law.
-/
def NativeCl44ConformalRoute
    (T : SplitTrialityKernel)
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (tkkParameter : ℝ) : Prop :=
  QuadraticLightConeConformalRoute
    ∧ C.SatisfiesOperatorTKKMasterRelation tkkParameter
    ∧ C.IsOperatorAdmissible
    ∧ T.trialitySupercharge.comp T.trialitySupercharge =
        LinearMap.id

/--
Every native split `Cl(4,4)` TKK/Jordan--Lie packet realizes the operatorial
conformal route; the numerical `so(5,5)` normalization is only its first
compatibility component.
-/
@[rep_depth transport]
theorem nativeCl44ConformalRoute
    (T : SplitTrialityKernel)
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (tkkParameter : ℝ)
    (hTKK : C.SatisfiesOperatorTKKMasterRelation tkkParameter)
    (hOperatorAdmissible : C.IsOperatorAdmissible) :
    NativeCl44ConformalRoute T C tkkParameter :=
  ⟨QuadraticLightConeConformalRoute.canonical,
    hTKK,
    hOperatorAdmissible,
    SplitTrialityKernel.trialitySupercharge_sq_eq_id T⟩
end NativeOperatorRoute

/-! ## 7. Compatibility owner target -/

/--
Compatibility target for the dimension normalization.  The actual operatorial
owner is `NativeCl44ConformalRoute`.
-/
@[owner_target_tag]
def Cl44ConformalNormalizationOwnerTarget : Prop :=
  QuadraticLightConeConformalRoute
    ∧ SpinFactorConformalRoute
    ∧ TrialityLeviPlacement

/-- The corrected normalization owner target is inhabited. -/
theorem cl44ConformalNormalizationOwnerTarget :
    Cl44ConformalNormalizationOwnerTarget :=
  ⟨QuadraticLightConeConformalRoute.canonical,
    SpinFactorConformalRoute.canonical,
    TrialityLeviPlacement.canonical⟩

end InfoGeometry.Canonical.Cl44ConformalNormalization

import InfoGeometry.KK.DiracFredholmModule
import InfoGeometry.Meta.Architecture
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open scoped InnerProductSpace

/-!
# InfoGeometry.KK.DiracFredholmIndex

Operatorial Fredholm/chiral-index surface for the real split-Krein
Dirac/Fredholm module.

This file is intentionally rooted in the bounded operator carrier
`RealSplitKreinDiracFredholmModule`. It does not route through the old scalar
or diagonal analytical-index facades. The ambient Hilbert carrier may be
infinite-dimensional; only the plus/minus chiral defect sectors are required
to be finite-dimensional in order to define the index.
-/

namespace InfoGeometry.KK

open InfoGeometry.Krein

namespace RealSplitKreinKasparovCycle

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

/-- The bounded Dirac operator carried by the real split-Krein Dirac/Fredholm module. -/
@[rep_depth krein]
abbrev diracOperator
    (X : RealSplitKreinDiracFredholmModule A B H) : EndH H :=
  X.F

/-- The chirality involution used by the Fredholm surface. -/
@[rep_depth krein]
noncomputable abbrev chirality
    (_X : RealSplitKreinDiracFredholmModule A B H) : EndH H :=
  KreinGradedModule.gradeCLM (H := H)

/-- The positive chiral projector attached to the grading involution. -/
@[rep_depth krein]
noncomputable abbrev chiralProjectorPlus
    (_X : RealSplitKreinDiracFredholmModule A B H) : EndH H :=
  KreinGradedModule.gradeProjPlus (H := H)

/-- The negative chiral projector attached to the grading involution. -/
@[rep_depth krein]
noncomputable abbrev chiralProjectorMinus
    (_X : RealSplitKreinDiracFredholmModule A B H) : EndH H :=
  KreinGradedModule.gradeProjMinus (H := H)

/-- The positive chiral kernel defect sector of the bounded Dirac operator. -/
@[rep_depth krein]
noncomputable def chiralKernelSlicePlus
    (X : RealSplitKreinDiracFredholmModule A B H) : Submodule ℝ H :=
  LinearMap.ker X.diracOperator.toLinearMap ⊓
    LinearMap.range X.chiralProjectorPlus.toLinearMap

/-- The negative chiral kernel defect sector of the bounded Dirac operator. -/
@[rep_depth krein]
noncomputable def chiralKernelSliceMinus
    (X : RealSplitKreinDiracFredholmModule A B H) : Submodule ℝ H :=
  LinearMap.ker X.diracOperator.toLinearMap ⊓
    LinearMap.range X.chiralProjectorMinus.toLinearMap

/-- The grading involution still squares to `Id` on the bounded Fredholm surface. -/
@[rep_depth krein, simp] theorem chirality_sq
    (X : RealSplitKreinDiracFredholmModule A B H) :
    X.chirality.comp X.chirality = ContinuousLinearMap.id ℝ H := by
  simp [chirality]

/-- The bounded Dirac operator is grading-odd on the Fredholm surface. -/
@[rep_depth krein] theorem dirac_anticommutes_chirality
    (X : RealSplitKreinDiracFredholmModule A B H) :
    X.chirality.comp X.diracOperator = -(X.diracOperator.comp X.chirality) := by
  let Γ : EndH H := X.chirality
  let F : EndH H := X.diracOperator
  have hOdd : KreinGradedModule.gradeConj (H := H) F = -F := X.F_odd
  have hComp := congrArg (fun T : EndH H => T.comp Γ) hOdd
  simpa [Γ, F, diracOperator, chirality, KreinGradedModule.gradeConj,
    ContinuousLinearMap.comp_assoc] using hComp

/-- The positive chiral sector is carried into the negative sector by the bounded Dirac operator. -/
@[rep_depth krein] theorem dirac_comp_chiralProjectorPlus_eq_chiralProjectorMinus_comp_dirac
    (X : RealSplitKreinDiracFredholmModule A B H) :
    X.diracOperator.comp X.chiralProjectorPlus
      = X.chiralProjectorMinus.comp X.diracOperator := by
  ext x
  have hAnti :
      KreinGradedModule.gradeCLM (H := H) (X.F x)
        = -(X.F (KreinGradedModule.gradeCLM (H := H) x)) := by
    simpa [diracOperator, chirality] using
      congrArg (fun T : EndH H => T x) (X.dirac_anticommutes_chirality)
  have hExpanded :
      ((2 : ℝ)⁻¹) • (X.F x + X.F (KreinGradedModule.gradeCLM (H := H) x))
        =
      ((2 : ℝ)⁻¹) •
        (X.F x - KreinGradedModule.gradeCLM (H := H) (X.F x)) := by
    rw [hAnti]
    simp [sub_eq_add_neg]
  simpa [diracOperator, chiralProjectorPlus, chiralProjectorMinus,
    KreinGradedModule.gradeProjPlus, KreinGradedModule.gradeProjMinus]
    using hExpanded

/-- The negative chiral sector is carried into the positive sector by the bounded Dirac operator. -/
@[rep_depth krein] theorem dirac_comp_chiralProjectorMinus_eq_chiralProjectorPlus_comp_dirac
    (X : RealSplitKreinDiracFredholmModule A B H) :
    X.diracOperator.comp X.chiralProjectorMinus
      = X.chiralProjectorPlus.comp X.diracOperator := by
  ext x
  have hAnti :
      KreinGradedModule.gradeCLM (H := H) (X.F x)
        = -(X.F (KreinGradedModule.gradeCLM (H := H) x)) := by
    simpa [diracOperator, chirality] using
      congrArg (fun T : EndH H => T x) (X.dirac_anticommutes_chirality)
  have hExpanded :
      ((2 : ℝ)⁻¹) • (X.F x - X.F (KreinGradedModule.gradeCLM (H := H) x))
        =
      ((2 : ℝ)⁻¹) •
        (X.F x + KreinGradedModule.gradeCLM (H := H) (X.F x)) := by
    rw [hAnti]
    simp [sub_eq_add_neg]
  simpa [diracOperator, chiralProjectorPlus, chiralProjectorMinus,
    KreinGradedModule.gradeProjPlus, KreinGradedModule.gradeProjMinus]
    using hExpanded

/--
Infinite-dimensional Fredholm surface for the bounded real split-Krein
Dirac/Fredholm module.

The ambient carrier `H` may be infinite-dimensional; the only finite-dimensional
data demanded here are the plus/minus chiral kernel defect sectors.
-/
@[rep_depth krein]
def ChiralFredholmSurface
    (X : RealSplitKreinDiracFredholmModule A B H) : Prop :=
  FiniteDimensional ℝ (X.chiralKernelSlicePlus) ∧
  FiniteDimensional ℝ (X.chiralKernelSliceMinus)

/--
The Fredholm/chiral analytical index of the bounded real split-Krein
Dirac/Fredholm module.

This is defined directly from the operatorial plus/minus chiral defect sectors
and does not assume the full ambient carrier is finite-dimensional.
-/
@[rep_depth krein]
noncomputable def analyticalIndex
    (X : RealSplitKreinDiracFredholmModule A B H)
    (hX : ChiralFredholmSurface X) : ℤ := by
  rcases hX with ⟨hPlus, hMinus⟩
  letI := hPlus
  letI := hMinus
  exact
    (Module.finrank ℝ (X.chiralKernelSlicePlus) : ℤ) -
      (Module.finrank ℝ (X.chiralKernelSliceMinus) : ℤ)

/-- A finite-dimensional ambient carrier induces the Fredholm surface automatically. -/
@[rep_depth krein]
noncomputable def chiralFredholmSurfaceOfFiniteAmbient
    [FiniteDimensional ℝ H]
    (X : RealSplitKreinDiracFredholmModule A B H) :
    ChiralFredholmSurface X := by
  refine ⟨?_, ?_⟩
  · infer_instance
  · infer_instance

/-- On a finite-dimensional carrier, the operatorial Fredholm index reduces to the same kernel asymmetry formula. -/
@[rep_depth krein, simp] theorem analyticalIndex_eq_finrank_chiralKernelDifference
    [FiniteDimensional ℝ H]
    (X : RealSplitKreinDiracFredholmModule A B H) :
    X.analyticalIndex (X.chiralFredholmSurfaceOfFiniteAmbient)
      =
    (Module.finrank ℝ (X.chiralKernelSlicePlus) : ℤ) -
      (Module.finrank ℝ (X.chiralKernelSliceMinus) : ℤ) := by
  cases X.chiralFredholmSurfaceOfFiniteAmbient
  simp [analyticalIndex]

end RealSplitKreinKasparovCycle

end InfoGeometry.KK

import InfoGeometry.Canonical.DrazinKreinCompatibility
import InfoGeometry.KK.RealSplitKreinKasparovCycle
import InfoGeometry.Meta.Architecture
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.DrazinFredholmBridge

Thin Fredholm-facing bridge above the Drazin/Krein compatibility layer.

This file is intentionally narrow:
- it treats `P₀` (the Drazin defect projector) as the noninvertible block;
- it splits that block into chiral components using `P₊/P₋`;
- it defines an index on defect chiral kernel slices;
- it packages compactness assumptions for downstream KK/Fredholm lanes.

No determinant/trace-class analytics are introduced here.
-/

namespace DrazinFredholmBridge

open InfoGeometry.Canonical.DrazinKreinCompatibility
open InfoGeometry.KK
open InfoGeometry.Krein

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH₂" => H₂ →L[ℝ] H₂

/-- Drazin defect block operator `P₀ = 1 - T*Tᴰ`. -/
@[rep_depth transport]
noncomputable abbrev defectProjector (T TD : EndH₂) : EndH₂ :=
  Pzero (E := E) T TD

/-- Chiral `+` defect block `P₀ ∘ P₊`. -/
@[rep_depth transport]
noncomputable def defectChiralBlockPlus (T TD : EndH₂) : EndH₂ :=
  (defectProjector (E := E) T TD).comp (chiralPlus (E := E))

/-- Chiral `-` defect block `P₀ ∘ P₋`. -/
@[rep_depth transport]
noncomputable def defectChiralBlockMinus (T TD : EndH₂) : EndH₂ :=
  (defectProjector (E := E) T TD).comp (chiralMinus (E := E))

/-- The defect projector splits as the sum of its chiral blocks. -/
@[rep_depth transport, capstone]
theorem defectProjector_eq_sum_defectChiralBlocks (T TD : EndH₂) :
    defectProjector (E := E) T TD
      =
    defectChiralBlockPlus (E := E) T TD
      +
    defectChiralBlockMinus (E := E) T TD := by
  have hSplit :
      chiralPlus (E := E) + chiralMinus (E := E)
        = ContinuousLinearMap.id ℝ H₂ :=
    Pplus_add_Pminus (E := E)
  apply ContinuousLinearMap.ext
  intro u
  have hSplitAtU :
      (chiralPlus (E := E) + chiralMinus (E := E)) u
        = (ContinuousLinearMap.id ℝ H₂) u := by
    exact congrArg (fun f : EndH₂ => f u) hSplit
  calc
    defectProjector (E := E) T TD u
      = (defectProjector (E := E) T TD) ((ContinuousLinearMap.id ℝ H₂) u) := by simp
    _ =
      (defectProjector (E := E) T TD)
        ((chiralPlus (E := E) + chiralMinus (E := E)) u) := by rw [hSplitAtU]
    _ =
      (defectProjector (E := E) T TD) ((chiralPlus (E := E)) u)
        +
      (defectProjector (E := E) T TD) ((chiralMinus (E := E)) u) := by
          change
            (defectProjector (E := E) T TD)
                (((chiralPlus (E := E)) u) + ((chiralMinus (E := E)) u))
              =
            (defectProjector (E := E) T TD) ((chiralPlus (E := E)) u)
              +
            (defectProjector (E := E) T TD) ((chiralMinus (E := E)) u)
          exact (defectProjector (E := E) T TD).map_add
            ((chiralPlus (E := E)) u) ((chiralMinus (E := E)) u)
    _ =
      (defectChiralBlockPlus (E := E) T TD
        + defectChiralBlockMinus (E := E) T TD) u := by
          simp [defectChiralBlockPlus, defectChiralBlockMinus, ContinuousLinearMap.add_apply]

/-- Positive defect kernel slice: `ker(P₀) ∩ range(P₊)`. -/
@[rep_depth transport]
noncomputable def defectKernelSlicePlus (T TD : EndH₂) : Submodule ℝ H₂ :=
  LinearMap.ker (defectProjector (E := E) T TD).toLinearMap ⊓
    LinearMap.range (chiralPlus (E := E)).toLinearMap

/-- Negative defect kernel slice: `ker(P₀) ∩ range(P₋)`. -/
@[rep_depth transport]
noncomputable def defectKernelSliceMinus (T TD : EndH₂) : Submodule ℝ H₂ :=
  LinearMap.ker (defectProjector (E := E) T TD).toLinearMap ⊓
    LinearMap.range (chiralMinus (E := E)).toLinearMap

/--
Fredholm-surface finiteness for the Drazin defect lane:
only the defect plus/minus slices are required finite-dimensional.
-/
@[rep_depth transport]
structure DefectChiralFredholmSurface (T TD : EndH₂) : Prop where
  plusFinite : FiniteDimensional ℝ (defectKernelSlicePlus (E := E) T TD)
  minusFinite : FiniteDimensional ℝ (defectKernelSliceMinus (E := E) T TD)

/-- The defect chiral index: plus/minus defect-slice dimension difference. -/
@[rep_depth transport]
noncomputable def defectChiralIndex
    (T TD : EndH₂) (hS : DefectChiralFredholmSurface (E := E) T TD) : ℤ := by
  rcases hS with ⟨hPlus, hMinus⟩
  letI := hPlus
  letI := hMinus
  exact
    (Module.finrank ℝ (defectKernelSlicePlus (E := E) T TD) : ℤ)
      -
    (Module.finrank ℝ (defectKernelSliceMinus (E := E) T TD) : ℤ)

-- Nonzero defect chiral index forces plus/minus defect-slice dimension mismatch.
omit [CompleteSpace E] in
@[rep_depth transport]
theorem defectKernelDimMismatch_of_defectChiralIndex_ne_zero
    (T TD : EndH₂)
    (hS : DefectChiralFredholmSurface (E := E) T TD)
    (hIndex : defectChiralIndex (E := E) T TD hS ≠ 0) :
    Module.finrank ℝ (defectKernelSlicePlus (E := E) T TD)
      ≠
    Module.finrank ℝ (defectKernelSliceMinus (E := E) T TD) := by
  intro hEq
  apply hIndex
  unfold defectChiralIndex
  rcases hS with ⟨hPlus, hMinus⟩
  letI := hPlus
  letI := hMinus
  simp [hEq]

end Core

section CompactnessPackage

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH₂" => H₂ →L[ℝ] H₂

/--
Compactness package for KK/Fredholm consumption on the Drazin defect lane.

This is an interface layer only: it records compactness/finiteness assumptions
without introducing additional physics or spectral claims.
-/
@[rep_depth transport]
structure DrazinDefectFredholmPackage
    (T TD : EndH₂) (k : ℕ) where
  compat : KreinGradedDrazinCompatibility (E := E) T TD k
  defectCompact : IsCompactEnd H₂ (defectProjector (E := E) T TD)
  defectCommPlusCompact :
    IsCompactEnd H₂
      ((defectProjector (E := E) T TD) * (chiralPlus (E := E))
        - (chiralPlus (E := E)) * (defectProjector (E := E) T TD))
  defectCommMinusCompact :
    IsCompactEnd H₂
      ((defectProjector (E := E) T TD) * (chiralMinus (E := E))
        - (chiralMinus (E := E)) * (defectProjector (E := E) T TD))
  defectSurface : DefectChiralFredholmSurface (E := E) T TD

/-- The packaged defect block is nontrivial whenever the underlying compat layer says so. -/
@[rep_depth transport, capstone]
theorem defectProjector_ne_zero_of_package
    {T TD : EndH₂} {k : ℕ}
    (_hPkg : DrazinDefectFredholmPackage (E := E) T TD k)
    (hNontrivial : DefectSectorData (E := E) T TD k) :
    defectProjector (E := E) T TD ≠ 0 := by
  exact hNontrivial.nontrivial_defect

end CompactnessPackage

end DrazinFredholmBridge

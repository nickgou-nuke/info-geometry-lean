import InfoGeometry.Canonical.AnalyticalIndexCore
import InfoGeometry.Canonical.OperatorialCentralCharge
import InfoGeometry.KK.QuasilatticeIndexInvariance
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ChiralDefectIndexBridge

Thin bridge from the transported Dirac/Fredholm defect lane to the chiral
kernel-asymmetry surface.

This file deliberately does not invent a new defect ontology. It reuses:

- the transported Dirac family from the KK quasilattice-index lane,
- the ambient grading projectors already used by that lane,
- and the operatorial central-charge transport invariant.

Its job is only to expose the off-diagonal defect blocks and prove the first
load-bearing consequence needed by any honest vortex/zero-mode package:
 nonzero transported index, hence nonzero operatorial central charge, forces a
 genuine mismatch between the transported plus/minus chiral kernel sectors.
-/

namespace InfoGeometry.Canonical.ChiralDefectIndexBridge

open InfoGeometry.Canonical.AnalyticalIndex
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Krein

section Core

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E
local notation "EndHL" => H₂ →ₗ[ℝ] H₂

/-- The transported positive defect block `D⁺_def = D_t ∘ P₊`. -/
@[rep_depth transport]
noncomputable abbrev transportedDefectBlockPlus
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ) : EndHL :=
  InfoGeometry.Canonical.AnalyticalIndex.chiralPartPlus
    (quasilatticeDiracFamily (A := A) (B := B) (E := E) V X t)
    ((KreinGradedModule.gradeCLM (H := H₂)).toLinearMap)

/-- The transported negative defect block `D⁻_def = D_t ∘ P₋`. -/
@[rep_depth transport]
noncomputable abbrev transportedDefectBlockMinus
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ) : EndHL :=
  InfoGeometry.Canonical.AnalyticalIndex.chiralPartMinus
    (quasilatticeDiracFamily (A := A) (B := B) (E := E) V X t)
    ((KreinGradedModule.gradeCLM (H := H₂)).toLinearMap)

/-- The transported positive defect block is the transported Dirac family restricted to `P₊`. -/
@[rep_depth transport]
theorem transportedDefectBlockPlus_eq_dirac_comp_gradeProjPlus
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ) :
    transportedDefectBlockPlus (A := A) (B := B) (E := E) V X t
      =
    (quasilatticeDiracFamily (A := A) (B := B) (E := E) V X t).comp
      (KreinGradedModule.gradeProjPlus (H := H₂)).toLinearMap := by
  ext u <;>
    simp [transportedDefectBlockPlus,
      InfoGeometry.Canonical.AnalyticalIndex.chiralPartPlus,
      InfoGeometry.Canonical.AnalyticalIndex.chiralProjectorPlus,
      KreinGradedModule.gradeProjPlus]

/-- The transported negative defect block is the transported Dirac family restricted to `P₋`. -/
@[rep_depth transport]
theorem transportedDefectBlockMinus_eq_dirac_comp_gradeProjMinus
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ) :
    transportedDefectBlockMinus (A := A) (B := B) (E := E) V X t
      =
    (quasilatticeDiracFamily (A := A) (B := B) (E := E) V X t).comp
      (KreinGradedModule.gradeProjMinus (H := H₂)).toLinearMap := by
  ext u <;>
    simp [transportedDefectBlockMinus,
      InfoGeometry.Canonical.AnalyticalIndex.chiralPartMinus,
      InfoGeometry.Canonical.AnalyticalIndex.chiralProjectorMinus,
      KreinGradedModule.gradeProjMinus]

/--
Transported chiral-kernel dimension mismatch.

This is the first honest defect predicate above the flat bulk root lane: it is
 defined only once the transported plus/minus kernel slices are known to be
finite-dimensional.
-/
@[rep_depth transport]
def TransportedChiralKernelDimMismatch
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t) : Prop :=
  letI := hVX.1
  letI := hVX.2
  Module.finrank ℝ (quasilatticeChiralKernelSlicePlus V X t)
    ≠
  Module.finrank ℝ (quasilatticeChiralKernelSliceMinus V X t)

/-- Nonzero transported analytical index forces chiral-kernel dimension mismatch. -/
@[rep_depth transport]
theorem transportedChiralKernelDimMismatch_of_quasilatticeAnalyticalIndex_ne_zero
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t)
    (hNonzero : quasilatticeAnalyticalIndex V X t hVX ≠ 0) :
    TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E) V X t hVX := by
  classical
  rcases hVX with ⟨hPlus, hMinus⟩
  letI := hPlus
  letI := hMinus
  intro hEq
  apply hNonzero
  simp [quasilatticeAnalyticalIndex, hEq]

/--
Nonzero operatorial central charge forces chiral-kernel dimension mismatch on
every transported quasilattice slice.
-/
@[rep_depth transport]
theorem transportedChiralKernelDimMismatch_of_operatorialCentralCharge_ne_zero
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (hCentral : operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0) :
    TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E)
      V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) := by
  let hVX := quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t
  have hSliceNonzero :
      quasilatticeAnalyticalIndex V X t hVX ≠ 0 :=
    quasilatticeSlice_ne_zero_of_operatorialCentralCharge_ne_zero
      (A := A) (B := B) (E := E) V X hX hEven hCentral t
  exact
    transportedChiralKernelDimMismatch_of_quasilatticeAnalyticalIndex_ne_zero
      (A := A) (B := B) (E := E) V X t hVX hSliceNonzero

end Core

end InfoGeometry.Canonical.ChiralDefectIndexBridge

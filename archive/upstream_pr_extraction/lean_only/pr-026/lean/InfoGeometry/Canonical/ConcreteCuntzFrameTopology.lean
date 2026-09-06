import InfoGeometry.Canonical.ConcreteCuntzMatrixIsometries
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Topological realization of the finite rectangular frame

The two concrete 2×1 matrices are continuous linear maps between the finite
Hilbert carriers `Fin 1 → ℂ` and `Fin 2 → ℂ`.  This is the topological status
of the frame; it is deliberately not a Cuntz-algebra completion.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConcreteCuntzFrameTopology

open InfoGeometry.Canonical.ConcreteCuntzMatrixIsometries
open CategoryTheory

def frameS1ContinuousLinearMap :
    (Fin 1 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  LinearMap.toContinuousLinearMap cuntzMatrixS1.mulVecLin

def frameS2ContinuousLinearMap :
    (Fin 1 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  LinearMap.toContinuousLinearMap cuntzMatrixS2.mulVecLin

@[simp] theorem frameS1ContinuousLinearMap_apply (x : Fin 1 → ℂ) :
    frameS1ContinuousLinearMap x = Matrix.mulVec cuntzMatrixS1 x :=
  rfl

@[simp] theorem frameS2ContinuousLinearMap_apply (x : Fin 1 → ℂ) :
    frameS2ContinuousLinearMap x = Matrix.mulVec cuntzMatrixS2 x :=
  rfl

theorem frameS1_continuous :
    Continuous (frameS1ContinuousLinearMap : (Fin 1 → ℂ) → (Fin 2 → ℂ)) :=
  frameS1ContinuousLinearMap.continuous

theorem frameS2_continuous :
    Continuous (frameS2ContinuousLinearMap : (Fin 1 → ℂ) → (Fin 2 → ℂ)) :=
  frameS2ContinuousLinearMap.continuous

/-! The same maps, now exposed as actual arrows of `TopCat`. -/

def frameS1TopCatHom : TopCat.of (Fin 1 → ℂ) ⟶ TopCat.of (Fin 2 → ℂ) :=
  TopCat.ofHom frameS1ContinuousLinearMap

def frameS2TopCatHom : TopCat.of (Fin 1 → ℂ) ⟶ TopCat.of (Fin 2 → ℂ) :=
  TopCat.ofHom frameS2ContinuousLinearMap

@[simp] theorem frameS1TopCatHom_apply (x : Fin 1 → ℂ) :
    frameS1TopCatHom x = cuntzMatrixS1.mulVec x :=
  rfl

@[simp] theorem frameS2TopCatHom_apply (x : Fin 1 → ℂ) :
    frameS2TopCatHom x = cuntzMatrixS2.mulVec x :=
  rfl

end InfoGeometry.Canonical.ConcreteCuntzFrameTopology

import InfoGeometry.Canonical.FiniteSingleModeCAROperatorAlgebra
import InfoGeometry.Canonical.FiniteSingleModeCARPairingTopological
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Transport of the finite CAR operators to a native Hilbert carrier

`EuclideanSpace ℂ Bool` has Mathlib's standard finite-dimensional
inner-product structure.  The coordinate equivalence transports the existing
one-mode operators by continuous-linear conjugation; no new representation
assumptions are introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteSingleModeCARHilbertTransport

open InfoGeometry.Algebra.FiniteSingleModeCAR
open InfoGeometry.Canonical.FiniteSingleModeCAROperatorAlgebra
open InfoGeometry.Canonical.FiniteSingleModeCARPairingTopological
open CategoryTheory

abbrev OneModeHilbert := EuclideanSpace ℂ Bool

noncomputable def coordinateEquiv : OneModeHilbert ≃L[ℂ] OneModeVec :=
  EuclideanSpace.equiv Bool ℂ

noncomputable def annHilbert : OneModeHilbert →L[ℂ] OneModeHilbert :=
  ContinuousLinearMap.comp coordinateEquiv.symm.toContinuousLinearMap
    (ContinuousLinearMap.comp annContinuousLinearMap coordinateEquiv.toContinuousLinearMap)

noncomputable def creHilbert : OneModeHilbert →L[ℂ] OneModeHilbert :=
  ContinuousLinearMap.comp coordinateEquiv.symm.toContinuousLinearMap
    (ContinuousLinearMap.comp creContinuousLinearMap coordinateEquiv.toContinuousLinearMap)

@[simp] theorem coordinateEquiv_annHilbert (ψ : OneModeHilbert) :
    coordinateEquiv (annHilbert ψ) =
      ann (coordinateEquiv ψ) := by
  change coordinateEquiv
      (coordinateEquiv.symm (annContinuousLinearMap (coordinateEquiv ψ))) =
    ann (coordinateEquiv ψ)
  rw [coordinateEquiv.apply_symm_apply]
  exact annContinuousLinearMap_apply _

@[simp] theorem coordinateEquiv_creHilbert (ψ : OneModeHilbert) :
    coordinateEquiv (creHilbert ψ) =
      cre (coordinateEquiv ψ) := by
  change coordinateEquiv
      (coordinateEquiv.symm (creContinuousLinearMap (coordinateEquiv ψ))) =
    cre (coordinateEquiv ψ)
  rw [coordinateEquiv.apply_symm_apply]
  exact creContinuousLinearMap_apply _

@[simp] theorem coordinateEquiv_symm_apply (f : OneModeVec) (i : Bool) :
    coordinateEquiv.symm f i = f i := by
  rfl

theorem annHilbert_adjoint :
    ContinuousLinearMap.adjoint annHilbert = creHilbert := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [annHilbert, creHilbert, PiLp.inner_apply,
    annContinuousLinearMap_apply, creContinuousLinearMap_apply, ann, cre,
    coordinateEquiv, PiLp.continuousLinearEquiv_apply]

theorem creHilbert_adjoint :
    ContinuousLinearMap.adjoint creHilbert = annHilbert := by
  rw [← annHilbert_adjoint]
  exact ContinuousLinearMap.adjoint_adjoint annHilbert

def annHilbertTopCatHom :
    TopCat.of OneModeHilbert ⟶ TopCat.of OneModeHilbert :=
  TopCat.ofHom
    { toFun := annHilbert
      continuous_toFun := annHilbert.continuous }

def creHilbertTopCatHom :
    TopCat.of OneModeHilbert ⟶ TopCat.of OneModeHilbert :=
  TopCat.ofHom
    { toFun := creHilbert
      continuous_toFun := creHilbert.continuous }

end InfoGeometry.Canonical.FiniteSingleModeCARHilbertTransport

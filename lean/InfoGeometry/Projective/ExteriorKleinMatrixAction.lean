/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.ExteriorPowerPluckerBridge
import InfoGeometry.Projective.PluckerMatrixAction
import Mathlib.LinearAlgebra.Determinant

/-!
# Exterior-square functoriality and the native Klein relative invariant

The native exterior-square action is transported through the existing
Plücker linear equivalence. Its coordinate matrix is identified with the
existing generic second compound, so the determinant multiplier applies to
all native bivectors, including nondecomposable ones.

-/

noncomputable section

namespace InfoGeometry.Projective.ExteriorKleinMatrixAction

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorPowerPluckerBridge

/-- The native exterior square in the existing six-coordinate carrier.
Multiplicativity retains the original operator order. -/
def pluckerAction : Module.End ℝ Vec4 →* Module.End ℝ (Fin 6 → ℝ) where
  toFun f := pluckerExteriorLinearEquiv.conj (exteriorPower.map 2 f)
  map_one' := by
    change pluckerExteriorLinearEquiv.conj
      (exteriorPower.map 2 (LinearMap.id (R := ℝ) (M := Vec4))) = LinearMap.id
    rw [exteriorPower.map_id, LinearEquiv.conj_id]
  map_mul' f g := by
    change pluckerExteriorLinearEquiv.conj (exteriorPower.map 2 (f.comp g)) =
      (pluckerExteriorLinearEquiv.conj (exteriorPower.map 2 f)).comp
        (pluckerExteriorLinearEquiv.conj (exteriorPower.map 2 g))
    rw [exteriorPower.map_comp, LinearEquiv.conj_comp]

@[simp] theorem pluckerAction_apply (f : Module.End ℝ Vec4) (p : Fin 6 → ℝ) :
    pluckerAction f p =
      pluckerExteriorLinearEquiv
        (exteriorPower.map 2 f (pluckerExteriorLinearEquiv.symm p)) := rfl

@[simp] theorem pluckerAction_intertwines (f : Module.End ℝ Vec4)
    (X : ⋀[ℝ]^2 Vec4) :
    pluckerAction f (pluckerExteriorLinearEquiv X) =
      pluckerExteriorLinearEquiv (exteriorPower.map 2 f X) := by
  simp only [pluckerAction_apply, LinearEquiv.symm_apply_apply]

/-- Naturality on simple wedges, used to compute the matrix columns. -/
theorem pluckerAction_pluckerCoords (f : Module.End ℝ Vec4) (u v : Vec4) :
    pluckerAction f (pluckerCoords u v) = pluckerCoords (f u) (f v) := by
  have hcoords (a b : Vec4) :
      pluckerExteriorLinearEquiv (exteriorPower.ιMulti ℝ 2 ![a, b]) =
        pluckerCoords a b := pluckerExteriorMap_ιMulti a b
  rw [← hcoords, pluckerAction_intertwines, exteriorPower.map_apply_ιMulti]
  have hpair : f ∘ ![u, v] = ![f u, f v] := by
    funext i
    fin_cases i <;> rfl
  rw [hpair, hcoords]

theorem pluckerAction_basis (f : Module.End ℝ Vec4) (j : Fin 6) :
    pluckerAction f (Pi.single j 1) =
      pluckerCoords (f (i4Basis (pluckerBasisPair j 0)))
        (f (i4Basis (pluckerBasisPair j 1))) := by
  rw [← pluckerBasisPair_readout j, pluckerAction_pluckerCoords]

/-- The explicit order `t,x,y,z` as an equivalence, rather than an arbitrary
noncomputable enumeration. -/
def standardIndex : Fin 4 ≃ I4 where
  toFun := ![I4.t, I4.x, I4.y, I4.z]
  invFun i := match i with
    | .t => 0
    | .x => 1
    | .y => 2
    | .z => 3
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by cases i <;> rfl

@[simp] theorem standardIndex_pair_fst (i : Fin 6) :
    standardIndex (PluckerMatrixAction.coordinatePair i).1 = pluckerBasisPair i 0 := by
  fin_cases i <;> rfl

@[simp] theorem standardIndex_pair_snd (i : Fin 6) :
    standardIndex (PluckerMatrixAction.coordinatePair i).2 = pluckerBasisPair i 1 := by
  fin_cases i <;> rfl

theorem i4Basis_eq_single (i : I4) : i4Basis i = Pi.single i 1 := by
  funext j
  simp [i4Basis, Pi.single_apply, eq_comm]

/-- The matrix of an arbitrary native four-dimensional endomorphism in the
explicit standard ordering. -/
def pointMatrix (f : Module.End ℝ Vec4) : Matrix (Fin 4) (Fin 4) ℝ :=
  (LinearMap.toMatrix' f).submatrix standardIndex standardIndex

@[simp] theorem pointMatrix_apply (f : Module.End ℝ Vec4) (i j : Fin 4) :
    pointMatrix f i j = f (i4Basis (standardIndex j)) (standardIndex i) := by
  simp [pointMatrix, LinearMap.toMatrix'_apply, i4Basis_eq_single]

/-- Simultaneous reindexing preserves determinant; this is the native
linear-endomorphism determinant, not a separately chosen multiplier. -/
theorem pointMatrix_det (f : Module.End ℝ Vec4) :
    (pointMatrix f).det = LinearMap.det f := by
  unfold pointMatrix
  rw [Matrix.det_submatrix_equiv_self, LinearMap.det_toMatrix']

/-- The native exterior-square matrix has the expected two-by-two minors. -/
theorem pluckerAction_matrix_apply (f : Module.End ℝ Vec4) (i j : Fin 6) :
    LinearMap.toMatrix' (pluckerAction f) i j =
      f (i4Basis (pluckerBasisPair j 0)) (pluckerBasisPair i 0) *
        f (i4Basis (pluckerBasisPair j 1)) (pluckerBasisPair i 1) -
      f (i4Basis (pluckerBasisPair j 1)) (pluckerBasisPair i 0) *
        f (i4Basis (pluckerBasisPair j 0)) (pluckerBasisPair i 1) := by
  rw [LinearMap.toMatrix'_apply, pluckerAction_basis]
  fin_cases i <;> simp [pluckerCoords, pluckerBasisPair] <;> ring

/-- The native functorial action and the generic minor formula are exactly
the same six-dimensional matrix. -/
theorem secondCompound_pointMatrix (f : Module.End ℝ Vec4) :
    PluckerMatrixAction.secondCompound (pointMatrix f) = LinearMap.toMatrix' (pluckerAction f) := by
  ext i j
  rw [pluckerAction_matrix_apply]
  simp only [PluckerMatrixAction.secondCompound, pointMatrix_apply,
    standardIndex_pair_fst, standardIndex_pair_snd]

/-- Read a native exterior bivector in the existing generic Plücker carrier. -/
def exteriorPlucker (X : ⋀[ℝ]^2 Vec4) :
    InfoGeometry.Projective.KleinQuadric.Plucker6 ℝ :=
  PluckerMatrixAction.coordinates.symm (pluckerExteriorLinearEquiv X)

/-- Both owners use the same signed Klein polynomial in the same ordering. -/
theorem exteriorPlucker_kleinQ (X : ⋀[ℝ]^2 Vec4) :
    InfoGeometry.Projective.KleinQuadric.Plucker6.kleinQ (exteriorPlucker X) =
      exteriorKleinForm X := rfl

/-- Compatibility holds for all exterior bivectors, not just simple wedges. -/
theorem exteriorPlucker_map (f : Module.End ℝ Vec4) (X : ⋀[ℝ]^2 Vec4) :
    exteriorPlucker (exteriorPower.map 2 f X) =
      PluckerMatrixAction.transform (pointMatrix f) (exteriorPlucker X) := by
  apply PluckerMatrixAction.coordinates.injective
  simp only [exteriorPlucker, PluckerMatrixAction.coordinates_transform,
    Equiv.apply_symm_apply]
  rw [secondCompound_pointMatrix, LinearMap.toMatrix'_mulVec]
  exact (pluckerAction_intertwines f X).symm

/-- The full native exterior-square relative invariant, with no
invertibility, decomposability, or operator-commutation hypothesis. -/
theorem exteriorKleinForm_map (f : Module.End ℝ Vec4) (X : ⋀[ℝ]^2 Vec4) :
    exteriorKleinForm (exteriorPower.map 2 f X) =
      LinearMap.det f * exteriorKleinForm X := by
  rw [← exteriorPlucker_kleinQ, exteriorPlucker_map, PluckerMatrixAction.kleinQ_transform,
    pointMatrix_det, exteriorPlucker_kleinQ]

end InfoGeometry.Projective.ExteriorKleinMatrixAction

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.LocalZornColorSlice
import InfoGeometry.Canonical.ZornVectorMatrixMöbiusAction

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra
open scoped LinearAlgebra.Projectivization

/-!
# Projective action of a local norm-one Zorn slice

The ambient Zorn product is non-associative, so it is not promoted to a
global Möbius action.  A fixed vector direction gives an associative matrix
slice.  This file packages only the norm-one part of that slice as an
`SL₂(ℝ)` element and reuses Mathlib's projectivization action.
-/

noncomputable def localZornSliceSL2
    (e : ZornVec3 ℝ)
    (he : ZornVec3.dot e e = 1)
    (a b u v : ℝ)
    (hnorm : ZornVectorMatrix.norm (localZornSlice e a b u v) = 1) :
    SL2R :=
  ⟨localZornMatrix a b u v, by
    rw [← localZornSlice_norm_eq_det e he]
    exact hnorm⟩

theorem localZornSlice_norm_one_iff_det_one
    (e : ZornVec3 ℝ)
    (he : ZornVec3.dot e e = 1)
    (a b u v : ℝ) :
    ZornVectorMatrix.norm (localZornSlice e a b u v) = 1 ↔
      Matrix.det (localZornMatrix a b u v) = 1 := by
  rw [localZornSlice_norm_eq_det e he]

noncomputable def localZornSliceProjectiveAction
    (e : ZornVec3 ℝ)
    (he : ZornVec3.dot e e = 1)
    (a b u v : ℝ)
    (hnorm : ZornVectorMatrix.norm (localZornSlice e a b u v) = 1) :
    RealProjectiveBoundary → RealProjectiveBoundary :=
  localSL2ProjectiveAction (localZornSliceSL2 e he a b u v hnorm)

noncomputable def modularBoostProjectiveAction (s : ℝ) :
    RealProjectiveBoundary → RealProjectiveBoundary :=
  localSL2ProjectiveAction (modularBoostSL2 s)

theorem localZornSliceProjectiveAction_is_SL2
    (e : ZornVec3 ℝ)
    (he : ZornVec3.dot e e = 1)
    (a b u v : ℝ)
    (hnorm : ZornVectorMatrix.norm (localZornSlice e a b u v) = 1) :
    ((localZornSliceSL2 e he a b u v hnorm : SL2R) :
      Matrix (Fin 2) (Fin 2) ℝ) = localZornMatrix a b u v :=
  rfl

theorem localZornSlice_projectiveAction_is_native
    (e : ZornVec3 ℝ)
    (he : ZornVec3.dot e e = 1)
    (a b u v : ℝ)
    (hnorm : ZornVectorMatrix.norm (localZornSlice e a b u v) = 1)
    (p : RealProjectiveBoundary) :
    localZornSliceProjectiveAction e he a b u v hnorm p =
      localSL2ProjectiveAction
        (localZornSliceSL2 e he a b u v hnorm) p :=
  rfl

theorem localSL2ProjectiveAction_one :
    localSL2ProjectiveAction (1 : SL2R) = id := by
  ext p
  simp [localSL2ProjectiveAction]

theorem localSL2ProjectiveAction_mul
    (g h : SL2R) :
    localSL2ProjectiveAction (g * h) =
      localSL2ProjectiveAction g ∘ localSL2ProjectiveAction h := by
  unfold localSL2ProjectiveAction
  rw [← Projectivization.map_comp]
  congr 1
  ext x
  simp

noncomputable def localZornNormOneMul
    (m : ColorSector) (g h : LocalZornNormOne m) : LocalZornNormOne m :=
  (localZornNormOneEquivSL2 m).symm
    ((localZornNormOneEquivSL2 m g) *
      (localZornNormOneEquivSL2 m h))

theorem localZornSlice_projectiveAction_mul
    (m : ColorSector)
    (g h : LocalZornNormOne m) :
    localZornSliceProjectiveAction (colorDirection m) (colorDirection_norm m)
      g.1.a g.1.b g.1.u g.1.v g.2 ∘
    localZornSliceProjectiveAction (colorDirection m) (colorDirection_norm m)
      h.1.a h.1.b h.1.u h.1.v h.2 =
    localSL2ProjectiveAction
      (localZornNormOneEquivSL2 m (localZornNormOneMul m g h)) := by
  have hg :
      localZornSliceSL2 (colorDirection m) (colorDirection_norm m)
          g.1.a g.1.b g.1.u g.1.v g.2 =
        localZornNormOneEquivSL2 m g := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hh :
      localZornSliceSL2 (colorDirection m) (colorDirection_norm m)
          h.1.a h.1.b h.1.u h.1.v h.2 =
        localZornNormOneEquivSL2 m h := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  ext p
  simp only [Function.comp_apply]
  rw [localZornSlice_projectiveAction_is_native,
      localZornSlice_projectiveAction_is_native, hg, hh]
  have hprod :
      localZornNormOneEquivSL2 m (localZornNormOneMul m g h) =
        (localZornNormOneEquivSL2 m g) *
          (localZornNormOneEquivSL2 m h) := by
    simp [localZornNormOneMul]
  rw [hprod]
  exact congrFun
    (localSL2ProjectiveAction_mul
      (localZornNormOneEquivSL2 m g)
      (localZornNormOneEquivSL2 m h)).symm p

end InfoGeometry.Canonical

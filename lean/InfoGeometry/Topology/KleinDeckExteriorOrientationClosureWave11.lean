/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinBottleExteriorOrientationBridge

noncomputable section
namespace InfoGeometry.Topology.KleinDeckExteriorOrientationClosureWave11
open Matrix
open InfoGeometry.Topology.KleinQuotientDeckInvariants
open InfoGeometry.Topology.KleinBottleExteriorOrientationBridge

abbrev PlaneVector := Fin 2 → ℝ

def deckExterior (g : KleinDeckGroup) : ExteriorAlgebra ℝ PlaneVector →ₐ[ℝ]
    ExteriorAlgebra ℝ PlaneVector :=
  ExteriorAlgebra.map (Matrix.mulVecLin (deckLinearDiff g))

private theorem deckLinearDiff_mul_matrix (g h : KleinDeckGroup) :
    deckLinearDiff (KleinDeckGroup.mul g h) =
      deckLinearDiff g * deckLinearDiff h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [deckLinearDiff, KleinDeckGroup.mul, signR_add,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem deckExterior_generator (g : KleinDeckGroup) (v : PlaneVector) :
    deckExterior g (ExteriorAlgebra.ι ℝ v) =
      ExteriorAlgebra.ι ℝ (Matrix.mulVecLin (deckLinearDiff g) v) := by
  exact ExteriorAlgebra.map_apply_ι (Matrix.mulVecLin (deckLinearDiff g)) v

theorem deckExterior_mul (g h : KleinDeckGroup) :
    AlgHom.comp (deckExterior g) (deckExterior h) =
      deckExterior (KleinDeckGroup.mul g h) := by
  change AlgHom.comp
      (ExteriorAlgebra.map (Matrix.mulVecLin (deckLinearDiff g)))
      (ExteriorAlgebra.map (Matrix.mulVecLin (deckLinearDiff h))) = _
  rw [ExteriorAlgebra.map_comp_map]
  rw [← Matrix.mulVecLin_mul, ← deckLinearDiff_mul_matrix]
  rfl

private theorem deckLinearDiff_firstAxis (g : KleinDeckGroup) :
    Matrix.mulVecLin (deckLinearDiff g) firstAxis = signR g.n • firstAxis := by
  ext i
  fin_cases i <;> simp [firstAxis, deckLinearDiff, Matrix.mulVec,
    dotProduct]

private theorem deckLinearDiff_secondAxis (g : KleinDeckGroup) :
    Matrix.mulVecLin (deckLinearDiff g) secondAxis = secondAxis := by
  ext i
  fin_cases i <;> simp [secondAxis, deckLinearDiff, Matrix.mulVec,
    dotProduct]

theorem deckExterior_topForm (g : KleinDeckGroup) :
    deckExterior g (ExteriorAlgebra.ι ℝ firstAxis *
      ExteriorAlgebra.ι ℝ secondAxis) =
        signR g.n • (ExteriorAlgebra.ι ℝ firstAxis *
          ExteriorAlgebra.ι ℝ secondAxis) := by
  rw [map_mul, deckExterior_generator, deckExterior_generator,
    deckLinearDiff_firstAxis, deckLinearDiff_secondAxis]
  rw [map_smul]
  simp

theorem deckExterior_topForm_eq_orientation_character (g : KleinDeckGroup) :
    deckExterior g (ExteriorAlgebra.ι ℝ firstAxis *
      ExteriorAlgebra.ι ℝ secondAxis) =
        det (deckLinearDiff g) • (ExteriorAlgebra.ι ℝ firstAxis *
          ExteriorAlgebra.ι ℝ secondAxis) := by
  rw [deckExterior_topForm, deckLinearDiff_det]

end InfoGeometry.Topology.KleinDeckExteriorOrientationClosureWave11

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Synthesis.Cl22RealDiracCarrier

noncomputable section
open scoped Matrix
open Matrix

namespace InfoGeometry.Synthesis.Cl22RealDiracCarrier

/-- The four displayed Dirac generators are linearly independent in the concrete
matrix carrier. -/
theorem cl22_generators_linearIndependent :
    LinearIndependent ℝ ![e0, e1, e2, e3] := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g h i
  fin_cases i
  · change f 0 = g 0
    have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 2) h
    have h20 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 2 0) h
    simp [e0, e1, e2, e3, Matrix.add_apply,
      Fin.sum_univ_four] at h02 h20
    linarith
  · change f 1 = g 1
    have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 2) h
    have h20 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 2 0) h
    simp [e0, e1, e2, e3, Matrix.add_apply,
      Fin.sum_univ_four] at h02 h20
    linarith
  · change f 2 = g 2
    have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) h
    have h10 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 1 0) h
    simp [e0, e1, e2, e3, Matrix.add_apply,
      Fin.sum_univ_four] at h01 h10
    linarith
  · change f 3 = g 3
    have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) h
    have h10 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 1 0) h
    simp [e0, e1, e2, e3, Matrix.add_apply,
      Fin.sum_univ_four] at h01 h10
    linarith

end InfoGeometry.Synthesis.Cl22RealDiracCarrier

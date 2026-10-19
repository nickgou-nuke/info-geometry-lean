/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

namespace InfoGeometry.SuperGrassmannian.Matrix3NoncommutativityWitness

abbrev NativeMat3 := Matrix (Fin 3) (Fin 3) ℤ

def matrixUnit01 : NativeMat3 :=
  !![0, 1, 0; 0, 0, 0; 0, 0, 0]

def matrixUnit12 : NativeMat3 :=
  !![0, 0, 0; 0, 0, 1; 0, 0, 0]

theorem matrixUnit01_mul_matrixUnit12_ne_reverse :
    matrixUnit01 * matrixUnit12 ≠ matrixUnit12 * matrixUnit01 := by
  intro h
  have h02 := congrArg (fun M : NativeMat3 => M 0 2) h
  norm_num [matrixUnit01, matrixUnit12, Matrix.mul_apply,
    Fin.sum_univ_succ] at h02

end InfoGeometry.SuperGrassmannian.Matrix3NoncommutativityWitness

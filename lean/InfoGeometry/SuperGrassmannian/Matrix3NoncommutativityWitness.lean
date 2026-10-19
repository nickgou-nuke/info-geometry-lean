/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

namespace InfoGeometry.SuperGrassmannian.Matrix3NoncommutativityWitness

variable {R : Type*} [CommRing R] [Nontrivial R]

def matrixUnit01 (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![(0 : R), 1, 0; 0, 0, 0; 0, 0, 0]

def matrixUnit12 (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![(0 : R), 0, 0; 0, 0, 1; 0, 0, 0]

theorem matrixUnit01_mul_matrixUnit12_ne_reverse :
    matrixUnit01 R * matrixUnit12 R ≠ matrixUnit12 R * matrixUnit01 R := by
  intro h
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 0 2) h
  norm_num [matrixUnit01, matrixUnit12, Matrix.mul_apply,
    Fin.sum_univ_succ] at h02

abbrev matI : Matrix (Fin 3) (Fin 3) R := matrixUnit01 R
abbrev matJ : Matrix (Fin 3) (Fin 3) R := matrixUnit12 R

theorem matI_mul_matJ_ne_reverse :
    matI * matJ ≠ matJ * matI := by
  exact matrixUnit01_mul_matrixUnit12_ne_reverse

end InfoGeometry.SuperGrassmannian.Matrix3NoncommutativityWitness

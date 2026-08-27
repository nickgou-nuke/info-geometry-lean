/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

namespace InfoGeometry.QuantumAlgebra.G2ArtinLift

/-! A corrected 2-dimensional algebraic Coxeter model.

The matrices below use a parameter `a` with `a^2 = 3`.  Their Coxeter
product has order six; its third power, rather than its sixth power, is `-I`.
Thus this model is a Weyl shadow, not a spin lift.
-/

variable {K : Type*} [CommRing K]

abbrev RootPlane := Fin 2
abbrev RootOperator (K : Type*) := Matrix RootPlane RootPlane K

def BShort (a : K) : RootOperator K :=
  !![1, a; 0, -1]

def BLong (a : K) : RootOperator K :=
  !![-1, 0; a, 1]

def Coxeter (a : K) : RootOperator K := BShort a * BLong a

theorem coxeter_pow_three (a : K) (ha : a * a = 3) :
    Coxeter a ^ 3 = -(1 : RootOperator K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Coxeter, BShort, BLong, Matrix.mul_apply, Fin.sum_univ_two,
      pow_succ, pow_two, ha] <;> try simp [pow_two, ha] <;> ring

theorem coxeter_pow_six (a : K) (ha : a * a = 3) :
    Coxeter a ^ 6 = 1 := by
  rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, coxeter_pow_three a ha]
  simp [pow_two]

theorem coxeter_twelfth_power (a : K) (ha : a * a = 3) :
    Coxeter a ^ 12 = 1 := by
  rw [show (12 : ℕ) = 6 * 2 by norm_num, pow_mul, coxeter_pow_six a ha]
  simp [pow_two]

end InfoGeometry.QuantumAlgebra.G2ArtinLift

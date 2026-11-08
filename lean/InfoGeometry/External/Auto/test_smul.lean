/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.External.Auto.TestSmul

variable {F : Type*} [Field F] (A : F)
variable {A_alg : Type*} [Ring A_alg] [Algebra F A_alg]
variable (ei ej : A_alg)

lemma test : (A • 1 : A_alg) * (A⁻¹ • ei) = (A * A⁻¹) • ei := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, one_mul]

end InfoGeometry.External.Auto.TestSmul

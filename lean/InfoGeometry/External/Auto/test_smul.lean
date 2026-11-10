/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.External.Auto.TestSmul

variable {F : Type*} [Semiring F] [Inv F] (A : F)
variable {A_alg : Type*} [Ring A_alg] [Module F A_alg] [IsScalarTower F A_alg A_alg] [SMulCommClass F A_alg A_alg]
variable (ei ej : A_alg)

lemma test : (A • 1 : A_alg) * (A⁻¹ • ei) = (A * A⁻¹) • ei := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, one_mul]

end InfoGeometry.External.Auto.TestSmul

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Coxeter.Basic

/-!
# Coxeter matrix groups in the external Coxeter API

Mathlib already constructs the group presented by every Coxeter matrix. This
adapter equips each such presented group with the external `CoxeterGroup`
interface, making its geometric and permutation representations available
without rebuilding the presentation.
-/

namespace InfoGeometry.CoxeterPort

variable {B : Type*}

/-- Every group presented by a Coxeter matrix is a Coxeter group for the
external Coxeter library. -/
instance matrixGroup (M : CoxeterMatrix B) : Coxeter.CoxeterGroup M.Group where
  toGroup := inferInstance
  B := B
  M := M
  cs := M.toCoxeterSystem

end InfoGeometry.CoxeterPort

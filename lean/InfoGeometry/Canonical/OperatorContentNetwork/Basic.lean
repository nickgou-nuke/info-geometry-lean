/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic

/-!
# Real operator programs

Program syntax is the native free associative real algebra. Its generators are
interpreted as arbitrary real square matrices; generator order is retained.
-/

namespace InfoGeometry.Canonical.OperatorContentNetwork

abbrev Operator (n : Type*) := Matrix n n ℝ

abbrev Program (α : Type*) := FreeAlgebra ℝ α

end InfoGeometry.Canonical.OperatorContentNetwork

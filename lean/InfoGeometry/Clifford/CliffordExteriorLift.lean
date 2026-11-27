/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ExteriorDerivationLift
import InfoGeometry.Algebra.FiniteSpinAlgebra

open ExteriorAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

namespace InfoGeometry.CliffordExteriorLift

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-! The generic exterior-lift construction and its unchanged public API
are imported from `InfoGeometry.Clifford.ExteriorDerivationLift`. -/

end InfoGeometry.CliffordExteriorLift

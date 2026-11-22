/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.H3ZornJordanKantorCapstone
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.JordanInnerDerivations

/-! Compatibility owner for the upstream concrete H₃ Kantor path.

The current repository exposes the proved Jordan-boundary and inner-
derivation packets through the capstone owner.  The abstract Kantor instance
and any exceptional-Lie dimension identification remain separate obligations.
-/
namespace InfoGeometry.Canonical.H3ZornKantorTripleSystem

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornJordanTripleBridge
open InfoGeometry.Canonical.H3ZornTKKNative
open InfoGeometry.Canonical.H3ZornJordanKantorCapstone

abbrev H3 := H3Zorn ℝ

theorem jordanTriple_eq_mul_add_inner (x y z : H3) :
    jordanTriple x y z = (x * y) * z + innerDerivation x y z := by
  exact H3ZornTKKNative.jordanTriple_eq_mul_add_inner x y z

theorem inner_swap_apply (x y z : H3) :
    innerDerivation y x z = -innerDerivation x y z := by
  exact InfoGeometry.Canonical.H3ZornKantorTripleSystemBridge.innerDerivation_swap x y z

theorem jordan_boundary_packet (x y : H3) :
    kantorOperator x y = 0 := by
  exact kantorOperator_zero x y


private noncomputable abbrev innerK (x y : H3) : Module.End ℝ H3 :=
  (h3ZornJordanInnerDerivation x y : Module.End ℝ H3)


theorem inner_comm_inner_apply (u v x y z : H3) :
    innerK u v (innerK x y z) - innerK x y (innerK u v z) =
      innerK (innerK u v x) y z + innerK x (innerK u v y) z := by
  let I := h3ZornJordanInnerDerivation u v
  have hI := I.property
  change
    (I : Module.End ℝ H3) (x * (y * z) - y * (x * z)) -
        (x * (y * (I : Module.End ℝ H3) z) - y * (x * (I : Module.End ℝ H3) z)) =
      ((I : Module.End ℝ H3) x) * (y * z) -
          y * (((I : Module.End ℝ H3) x) * z) +
        (x * (((I : Module.End ℝ H3) y) * z) -
          ((I : Module.End ℝ H3) y) * (x * z))
  rw [map_sub, hI x (y * z), hI y (x * z), hI y z, hI x z]
  simp only [mul_add, add_mul]
  abel

end InfoGeometry.Canonical.H3ZornKantorTripleSystem

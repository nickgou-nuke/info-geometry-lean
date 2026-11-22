/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.H3ZornJordanTripleBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.H3ZornExplicitPeirceJordanSoldering

/-! Compatibility owner for the upstream combined H₃/G₂ bridge name. -/

namespace InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornJordanTripleBridge

abbrev H3 := H3Zorn ℝ
noncomputable abbrev jordanTriple :=
  InfoGeometry.Canonical.H3ZornJordanTripleBridge.jordanTriple

theorem jordanTriple_outer_symm (x y z : H3) :
    jordanTriple x y z = jordanTriple z y x := by
  exact InfoGeometry.Canonical.H3ZornJordanTripleBridge.jordanTriple_outer_symm x y z

theorem jordanTriple_K_expression_zero (x y z : H3) :
    jordanTriple x z y - jordanTriple y z x = 0 := by
  exact InfoGeometry.Canonical.H3ZornJordanTripleBridge.jordanTriple_K_expression_zero x y z


/-- Inner Jordan derivation `[L_x,L_y]`. -/
noncomputable def jordanInner (x y : H3) : Module.End ℝ H3 :=
  h3ZornJordanInnerDerivation x y

@[simp] theorem jordanInner_apply (x y z : H3) :
    jordanInner x y z =
      candidateJordanMul x (candidateJordanMul y z) -
        candidateJordanMul y (candidateJordanMul x z) := by
  simp [jordanInner, h3ZornJordanInnerDerivation_apply, candidateJordanMul_eq_mul]

end InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge

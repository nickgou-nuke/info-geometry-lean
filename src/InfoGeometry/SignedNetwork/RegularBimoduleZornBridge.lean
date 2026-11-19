/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SignedNetwork.RegularBimoduleSeparation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.AkivisLeftRegularBridge

namespace InfoGeometry.SignedNetwork.RegularBimoduleZornBridge

open InfoGeometry.Algebra

/-! The associative regular-bimodule laws do not extend to the Zorn carrier.
    The exact defect is the associator, as supplied by the canonical Akivis
    owner. -/

theorem zorn_left_regular_commutator_defect
    (x y z : ZornVectorMatrix ℝ) :
    leftRegularCommutatorObstruction x y z = -_root_.associator x y z := by
  apply leftRegular_commutator_obstruction_apply
  intro p q r
  exact alternative_associator_swap12
    (fun a b => zorn_left_alternative a b) q p r

end InfoGeometry.SignedNetwork.RegularBimoduleZornBridge

import InfoGeometry.SignedNetwork.RegularBimoduleSeparation
import InfoGeometry.Algebra.AkivisLeftRegularBridge

namespace InfoGeometry.SignedNetwork.RegularBimoduleZornBridge

open InfoGeometry.Algebra

/-! The associative regular-bimodule laws do not extend to the Zorn carrier.
    The exact defect is the associator, as supplied by the canonical Akivis
    owner. -/

theorem zorn_left_regular_commutator_defect
    (x y z : ZornVectorMatrix ℝ) :
    leftRegularCommutatorObstruction x y z = -_root_.associator x y z := by
  exact leftRegular_commutator_obstruction_apply
    zornVectorMatrix_alternative_associator_swap12 x y z

theorem zorn_regular_actions_commute_iff
    (x y z : ZornVectorMatrix ℝ) :
    (L_map (R := ℝ) x) (L_map (R := ℝ) y z) -
        (L_map (R := ℝ) y) (L_map (R := ℝ) x z) =
      (x * (y * z) - y * (x * z)) := by
  rfl

end InfoGeometry.SignedNetwork.RegularBimoduleZornBridge

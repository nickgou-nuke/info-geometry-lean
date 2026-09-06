import InfoGeometry.Projective.SplitQuaternionRankOneKreinProjective
import InfoGeometry.Projective.SplitQuaternionCausalEntropyAxes

/-!
# Causal--entropy bridge for the real rank-one Krein carrier

The causal/entropy frame and the rank-one projective frame use the same real
doubled carrier.  This owner records their concrete identifications without
introducing complex scalars: the product of the two real involutions is the
internal Majorana complex structure, while `ellAxis` remains the separate
hyperbolic flow generator.
-/

namespace InfoGeometry.Projective.SplitQuaternionRankOneKreinCausalBridge

open InfoGeometry.Projective.SplitQuaternionCausalEntropyAxes
open InfoGeometry.Projective.SplitQuaternionRankOneKreinProjective
open InfoGeometry.Quantum.NeutralKreinMajoranaFrame

theorem internalJ_eq_causalEntropy :
    internalJ = internalComplex := by
  exact internalComplex_eq_majorana.symm

end InfoGeometry.Projective.SplitQuaternionRankOneKreinCausalBridge

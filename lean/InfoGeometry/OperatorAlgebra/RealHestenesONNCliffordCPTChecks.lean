import InfoGeometry.OperatorAlgebra.RealHestenesONNCliffordCPT
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Checks for the real Hestenes / O(n,n) / Pin(n,n) CPT owner lane

This file is intentionally tiny.  It keeps the public names for the corrected
operator-owner boundary visible to tooling:

* real scalars only;
* real `Cl(n,n)`;
* full `O(n,n)` rather than only `SO(n,n)`;
* Pin reflections for CPT;
* diagonal data only as a KAN/Cartan shadow.
-/

/-
#check InfoGeometry.OperatorAlgebra.RealHestenesONNCliffordCPTPacket
#check InfoGeometry.OperatorAlgebra.RealHestenesONNCliffordCPTPacket.realOnlyWitnessType
#check InfoGeometry.OperatorAlgebra.RealHestenesONNCliffordCPTPacket.clnnWitnessType
#check InfoGeometry.OperatorAlgebra.RealHestenesONNCliffordCPTPacket.fullONNWitnessType
#check InfoGeometry.OperatorAlgebra.RealHestenesONNCliffordCPTPacket.soInsufficientForCPTWitnessType
#check InfoGeometry.OperatorAlgebra.RealHestenesONNCliffordCPTPacket.pinReflectionWitnessType
#check InfoGeometry.OperatorAlgebra.RealHestenesONNCliffordCPTPacket.diagonalIsOnlyShadowWitnessType
#check InfoGeometry.OperatorAlgebra.RealHestenesONNCliffordCPTPacket.noComplexScalarCollapseWitnessType

#check InfoGeometry.OperatorAlgebra.RealHestenesO44PinCPTPacket
#check InfoGeometry.OperatorAlgebra.RealHestenesO44PinCPTPacket.parityPin_is_odd
#check InfoGeometry.OperatorAlgebra.RealHestenesO44PinCPTPacket.timeReversalPin_is_odd
#check InfoGeometry.OperatorAlgebra.RealHestenesO44PinCPTPacket.odd_reflection_socket_available
#check InfoGeometry.OperatorAlgebra.RealHestenesO44PinCPTPacket.chargeConjugation_sq
#check InfoGeometry.OperatorAlgebra.RealHestenesO44PinCPTPacket.parityAction_sq
#check InfoGeometry.OperatorAlgebra.RealHestenesO44PinCPTPacket.timeReversalAction_sq
#check InfoGeometry.OperatorAlgebra.RealHestenesO44PinCPTPacket.fullO44WitnessType
#check InfoGeometry.OperatorAlgebra.RealHestenesO44PinCPTPacket.so44InsufficientForCPTWitnessType
#check InfoGeometry.OperatorAlgebra.RealHestenesO44PinCPTPacket.pin44ReflectionWitnessType
#check InfoGeometry.OperatorAlgebra.RealHestenesO44PinCPTPacket.diagonalIsOnlyShadowWitnessType
#check InfoGeometry.OperatorAlgebra.RealHestenesO44PinCPTPacket.realOnlyWitnessType
-/

#check InfoGeometry.OperatorAlgebra.RealHestenesO44PinCPTPacket
#check InfoGeometry.OperatorAlgebra.RealHestenesO44PinCPTPacket.parityPin_is_odd
#check InfoGeometry.OperatorAlgebra.RealHestenesO44PinCPTPacket.timeReversalPin_is_odd
#check InfoGeometry.OperatorAlgebra.RealHestenesO44PinCPTPacket.chargeConjugation_sq

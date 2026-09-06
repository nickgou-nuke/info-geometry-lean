import InfoGeometry.SuperMetriplectic.BPS
import InfoGeometry.Algebraic.NarainSupervolumeBridgeData
import InfoGeometry.Algebraic.SplitSuperGeometry
import InfoGeometry.Canonical.OperatorThermodynamics

/-!
# Retired scalar BPS/black-hole entropy facade

The former declarations only chained arbitrary real-valued readouts.  They did
not construct a quartic invariant, a Casimir, a Witten index, or a protected
operator direction.  The compatibility module therefore exports no scalar
surrogate theorem surface.

Use the imported native owners for operator-valued supervolume data,
thermodynamic states, and protected directions.  Any future entropy theorem
must be stated against those carriers and an explicit state/weight or
representation, not against unrelated real variables.
-/

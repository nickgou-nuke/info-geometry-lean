import InfoGeometry.Arithmetic.FredholmGenuine
import InfoGeometry.Arithmetic.ZetaTraceVielbeinSpecialization
import InfoGeometry.OperatorAlgebra.VerifiedDeterminant

/-!
# Dynamical-zeta routing marker

The former file contained only unproved `Prop` schemas for finite matrix
determinants, weighted Milnor--Thurston identities, and an alternating
determinant product.  Those declarations were not theorems and did not carry
an operator, trace-class, or Fredholm construction.

Finite determinant identities and the analytic boundary are owned by
`FredholmClosure`/`FredholmGenuine`; the available trace-log arithmetic
specialization is owned by `ZetaTraceVielbeinSpecialization`.  This marker
exports no scalar replacement API.
-/

namespace InfoGeometry.Dynamics.DynamicalZetaFunction

end InfoGeometry.Dynamics.DynamicalZetaFunction

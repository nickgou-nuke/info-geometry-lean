import InfoGeometry.Analysis.NoncommutativeJacobiLiouvilleFlow
import InfoGeometry.Canonical.OperatorialHessianBridge
import InfoGeometry.Canonical.RelativeSurprisalJacobianCocycleBridge

/-!
# Retired scalar Liouville/spectral-defect facade

The former file represented a Liouville operator by an ad hoc two-real-
coordinate state and defined the spectral defect as a square of one
coordinate.  It did not define a Liouville measure, an ODE flow, or a spectral
operator.  The maintained noncommutative owners are the Jacobi/Liouville
operator flow, the operatorial Hessian, and the finite determinant/surprisal
cocycle.

This path is retained only for import compatibility and exports no scalar
`State`, `Gradient`, or defect API.
-/

namespace InfoGeometry.SuperMetriplectic.Liouville

end InfoGeometry.SuperMetriplectic.Liouville

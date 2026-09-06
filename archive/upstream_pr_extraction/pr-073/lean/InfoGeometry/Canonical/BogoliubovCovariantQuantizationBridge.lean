import InfoGeometry.Canonical.ThermalBogoliubov
import InfoGeometry.OperatorAlgebra.ThermalBogoliubovCAR
import InfoGeometry.Quantum.RealMajorana
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.BogoliubovTransport

/-!
# Retired scalar Bogoliubov covariance facade

The former implementation duplicated coefficient identities over `ℝ` and
treated scalar numbers as CCR/CAR observables.  Those statements were not a
quantization layer.  Genuine covariance is owned by the operator-valued CAR
and CCR modules imported above: `ThermalBogoliubovCAR`, `RealMajorana`,
`BogoliubovFockSuper`, and the real doubled-space transport.

This path remains only as an import-compatible retirement marker and exports
no scalar Bogoliubov coefficients or fake commutator API.
-/

namespace InfoGeometry.Canonical.BogoliubovCovariantQuantization

end InfoGeometry.Canonical.BogoliubovCovariantQuantization

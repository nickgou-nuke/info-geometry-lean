import InfoGeometry.Canonical.BohmMadelungOperatorialBridge
import InfoGeometry.Canonical.PolarizedMadelungBridge
import InfoGeometry.Canonical.OperatorialHessianBridge
import InfoGeometry.Krein.DoubledSpace

/-!
# Retired scalar Fisher--Wootters/Madelung facade

The former implementation exposed square-root amplitudes, scalar derivatives,
complex wavefunction norms, and an algebraic distance readout.  Those are
coordinate shadows rather than a Fisher metric or a quantum representation.
The native replacement is the doubled real Krein/Madelung carrier and its
operatorial Hessian/BKM readout, imported above.

This compatibility path intentionally exports no scalar amplitude or complex
wavefunction API.
-/

namespace InfoGeometry.Canonical.FisherWoottersQuantumPotential

end InfoGeometry.Canonical.FisherWoottersQuantumPotential

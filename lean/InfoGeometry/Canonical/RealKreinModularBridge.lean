import InfoGeometry.OperatorAlgebra.RealKreinModularSpectralTriple
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Real Krein Modular Bridge

Canonical re-export of the real doubled Krein modular phase-axis law.

This bridge stays in the real Hestenes/Krein language. It does not introduce
complex-analytic claims.
-/

namespace InfoGeometry.Canonical.RealKreinModularBridge

open InfoGeometry.OperatorAlgebra.RealKreinModularSpectralTriple

variable {A H Core : Type*}
variable [Ring A] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [AddCommMonoid Core] [Mul Core]

/-- The real doubled Krein modular phase axis squares to `-1`. -/
theorem modularPhaseAxis_square (T : RealKreinModularTriple A H Core) :
    T.Kmod.comp T.Kmod = -(1 : RealEnd H) :=
  T.Kmod_square

/-- Compatibility alias for the phase-axis square law. -/
theorem Kmod_square (T : RealKreinModularTriple A H Core) :
    T.Kmod.comp T.Kmod = -(1 : RealEnd H) :=
  modularPhaseAxis_square T

end InfoGeometry.Canonical.RealKreinModularBridge

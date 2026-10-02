import Mathlib
import InfoGeometry.Physics.MoorePenroseHodgeDrazinGhostBridge
import InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita

noncomputable section

namespace InfoGeometry.Physics.ChiralMassPseudoinverseBridge

open InfoGeometry.Physics.MoorePenroseHodgeDrazinGhostBridge
open InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {R : Type*} [CommRing R]

/-- The defect is A^+ - A^D -/
def pseudoinverseDefect (A_plus A_D : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  A_plus - A_D

/-- The scalar triple product -/
def scalarTripleProduct (χ : R) (u v w : Fin 3 → R) : R :=
  ∑ k : Fin 3, u k * parityTwistedCross χ v w k

/-- The trace of the defect generates the volume tensor (parityTwistedCross).
    We model this by a map taking a defect and producing the parity twist scalar χ. -/
def volumeGenerator (traceDefect : R) : R := traceDefect

/-- The resulting scalar triple product IS the mass gap. -/
def massGap (traceDefect : R) (u v w : Fin 3 → R) : R :=
  scalarTripleProduct (volumeGenerator traceDefect) u v w

end InfoGeometry.Physics.ChiralMassPseudoinverseBridge

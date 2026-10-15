import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import InfoGeometry.Canonical.ExteriorGradedDerivationBridge
import InfoGeometry.NCG.BlockSupermatrixGradedTrace

noncomputable section

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorGradedDerivationBridge
open InfoGeometry.NCG.BlockSupermatrixGradedTrace

namespace InfoGeometry.ChiralAnomaly

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

/-- Base interface for the full canonical differential on the exterior algebra tower (DGA). -/
class ExteriorDGA extends ExteriorDifferentialData R V

variable {R V}

/-- Graded Maurer-Cartan equation dω + 1/2[ω, ω] = 0 for an odd-degree form ω. -/
def graded_maurer_cartan_equation [Invertible (2 : R)]
    (dga : ExteriorDGA R V)
    (omega : ExteriorAlgebra R V) : Prop :=
  dga.d omega + (⅟(2 : R)) • ringSuperbracket .odd .odd omega omega = 0

end InfoGeometry.ChiralAnomaly

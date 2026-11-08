import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Clifford.Cl55BivectorVectorRepresentation
import InfoGeometry.Canonical.ExteriorGradedDerivationBridge

open InfoGeometry.Clifford.BivectorVectorRepresentation
open InfoGeometry.Canonical.ExteriorGradedDerivationBridge
open ExteriorAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

#check ExteriorAlgebra.lift

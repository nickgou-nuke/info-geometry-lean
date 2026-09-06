import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module
import InfoGeometry.Canonical.HestenesBivectorCarrier
import InfoGeometry.Canonical.HestenesBivectorSelfDuality
import Mathlib.RingTheory.TensorProduct.Basic

open InfoGeometry.Canonical.HestenesBivectorCarrier
open InfoGeometry.Canonical.HestenesBivectorSelfDuality
open TensorProduct

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M) [InfoGeometry.Canonical.CliffordParity.HasVolumeElement ℝ M Q] [HasSpacetimeBasis Q]

#check Module.finrank ℝ (Bivector13 Q)
#check finrank_bivector13

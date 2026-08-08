import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Canonical.CliffordParityBridge
import InfoGeometry.Canonical.HestenesBivectorCarrier
import InfoGeometry.Canonical.HestenesBivectorBracket
import InfoGeometry.Canonical.HestenesBivectorSelfDuality

namespace InfoGeometry.Canonical.LorentzSelfDualLieSplit

open CliffordAlgebra TensorProduct
open InfoGeometry.Canonical.HestenesBivectorCarrier

open InfoGeometry.Canonical.HestenesBivectorSelfDuality

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M) [InfoGeometry.Canonical.CliffordParity.HasVolumeElement ℝ M Q] [HasSpacetimeBasis Q]

abbrev ComplexClifford := TensorProduct ℝ ℂ (CliffordAlgebra Q)

-- The tensor product of algebras over a commutative ring is an algebra.
-- Mathlib provides this automatically, so we don't need manual instances.
-- However, we may need to specify LieAlgebra instance using inferInstance.
instance : LieRing (ComplexClifford Q) := inferInstance
instance : LieAlgebra ℂ (ComplexClifford Q) := inferInstance

/-- The complex bivectors as a submodule of the complexified Clifford algebra. -/
-- Wait, ComplexBivector Q is already defined in HestenesBivectorCarrier.lean
-- It is defined as: abbrev ComplexBivector := Bivector13 Q ⊗[ℝ] ℂ
-- However, Bivector13 Q ⊗[ℝ] ℂ is abstractly a tensor product of modules.
-- To treat it as a Lie subalgebra, we need to map it into `ComplexClifford Q`.
-- Let's define the inclusion map.

def complexBivectorInclusion : ComplexBivector Q →ₗ[ℂ] ComplexClifford Q :=
  TensorProduct.AlgebraTensorModule.map LinearMap.id (Bivector13 Q).subtype

-- We need to prove this inclusion preserves the bracket, so its range is a LieSubalgebra.
-- But wait, Bivector13 Q ⊗[ℝ] ℂ does not have a bracket yet!
-- Instead of defining a bracket on Bivector13 Q ⊗[ℝ] ℂ and proving it maps over,
-- we can just define the Lie subalgebra of ComplexClifford Q spanned by the image of this inclusion!

def complexBivectorLieSubalgebra : LieSubalgebra ℂ (ComplexClifford Q) :=
  LieSubalgebra.lieSpan ℂ (ComplexClifford Q) (LinearMap.range (complexBivectorInclusion Q))

end InfoGeometry.Canonical.LorentzSelfDualLieSplit

#exit
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

namespace InfoGeometry.Canonical.LorentzSelfDualLieSplit

open CliffordAlgebra TensorProduct
open InfoGeometry.Canonical.HestenesBivectorCarrier

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M) [HasVolumeElement ℝ M Q] [HasSpacetimeBasis Q]

abbrev ComplexClifford := CliffordAlgebra Q ⊗[ℝ] ℂ

instance : Ring (ComplexClifford Q) := TensorProduct.instRing
instance : Algebra ℂ (ComplexClifford Q) := Algebra.TensorProduct.rightAlgebra

-- This is the lie ring and lie algebra on the full complexified Clifford algebra
instance : LieRing (ComplexClifford Q) := inferInstance
instance : LieAlgebra ℂ (ComplexClifford Q) := inferInstance

/-- The complex bivectors as a submodule of the complexified Clifford algebra. -/
-- Wait, ComplexBivector Q is already defined in HestenesBivectorCarrier.lean
-- It is defined as: abbrev ComplexBivector := Bivector13 Q ⊗[ℝ] ℂ
-- However, Bivector13 Q ⊗[ℝ] ℂ is abstractly a tensor product of modules.
-- To treat it as a Lie subalgebra, we need to map it into `ComplexClifford Q`.
-- Let's define the inclusion map.

def complexBivectorInclusion : ComplexBivector Q →ₗ[ℂ] ComplexClifford Q :=
  TensorProduct.map (Bivector13 Q).subtype LinearMap.id

-- We need to prove this inclusion preserves the bracket, so its range is a LieSubalgebra.
-- But wait, Bivector13 Q ⊗[ℝ] ℂ does not have a bracket yet!
-- Instead of defining a bracket on Bivector13 Q ⊗[ℝ] ℂ and proving it maps over,
-- we can just define the Lie subalgebra of ComplexClifford Q spanned by the image of this inclusion!

def complexBivectorLieSubalgebra : LieSubalgebra ℂ (ComplexClifford Q) where
  carrier := LinearMap.range (complexBivectorInclusion Q)
  add_mem' := Submodule.add_mem _
  zero_mem' := Submodule.zero_mem _
  smul_mem' := Submodule.smul_mem _
  lie_mem' := by
    -- here we need to show that if x, y are in the range, their commutator is in the range
    sorry

end InfoGeometry.Canonical.LorentzSelfDualLieSplit

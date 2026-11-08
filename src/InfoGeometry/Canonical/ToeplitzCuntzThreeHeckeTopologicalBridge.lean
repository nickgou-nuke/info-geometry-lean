import InfoGeometry.Canonical.HeckeBraidTopologicalBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ToeplitzCuntzThreeBraidTopologicalBridge

/-!
# The `q = 1` Hecke specialization of the three-site Cuntz braid shadow

The involutive Artin generators already owned by the Toeplitz--Cuntz layer
give the Coxeter (permutation) specialization of the Hecke quadratic
relation.  This file transports that finite algebraic fact to `TopCat` via
the generic left-multiplication construction.  It does not assert a
non-trivial anyonic realization for general `q`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeHeckeTopologicalBridge

open CategoryTheory
open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeBraidTopologicalBridge
open InfoGeometry.Canonical.HeckeBraidTopologicalBridge

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
variable [TopologicalSpace R] [ContinuousMul R]
variable (g : ToeplitzCuntzThreeGenerators R)

/-- The generic topological Hecke relation specializes to the first Cuntz
braid generator at `q = 1`. -/
theorem toeplitzCuntzThree_hecke1_leftTopCat_relation :
    leftMulTopCatHom
        (braidGenerator1 g + algebraMap ℂ R (1 : ℂ)) ≫
      leftMulTopCatHom (braidGenerator1 g - algebraMap ℂ R (1 : ℂ)) =
      TopCat.ofHom (ContinuousMap.const R 0) := by
  have h1 :
      (braidGenerator1 g - algebraMap ℂ R (1 : ℂ)) *
          (braidGenerator1 g + algebraMap ℂ R (1 : ℂ)⁻¹) = 0 := by
    simp only [map_one, inv_one]
    calc
      (braidGenerator1 g - 1) * (braidGenerator1 g + 1) =
          braidGenerator1 g * braidGenerator1 g - 1 := by
            noncomm_ring
      _ = 0 := by rw [braidGenerator1_sq g, sub_self]
  simpa only [inv_one] using
    hecke1_leftTopCat_relation (1 : ℂ) (braidGenerator1 g) h1

/-- The corresponding topological Hecke relation for the second generator. -/
theorem toeplitzCuntzThree_hecke2_leftTopCat_relation :
    leftMulTopCatHom
        (braidGenerator2 g + algebraMap ℂ R (1 : ℂ)) ≫
      leftMulTopCatHom (braidGenerator2 g - algebraMap ℂ R (1 : ℂ)) =
      TopCat.ofHom (ContinuousMap.const R 0) := by
  have h2 :
      (braidGenerator2 g - algebraMap ℂ R (1 : ℂ)) *
          (braidGenerator2 g + algebraMap ℂ R (1 : ℂ)⁻¹) = 0 := by
    simp only [map_one, inv_one]
    calc
      (braidGenerator2 g - 1) * (braidGenerator2 g + 1) =
          braidGenerator2 g * braidGenerator2 g - 1 := by
            noncomm_ring
      _ = 0 := by rw [braidGenerator2_sq g, sub_self]
  simpa only [inv_one] using
    hecke2_leftTopCat_relation (1 : ℂ) (braidGenerator2 g) h2

/-- The Hecke data retain the Artin relation in the topological carrier. -/
theorem toeplitzCuntzThree_artin_leftTopCat_relation :
    leftMulTopCatHom (braidGenerator1 g) ≫
        leftMulTopCatHom (braidGenerator2 g) ≫
        leftMulTopCatHom (braidGenerator1 g) =
      leftMulTopCatHom (braidGenerator2 g) ≫
        leftMulTopCatHom (braidGenerator1 g) ≫
      leftMulTopCatHom (braidGenerator2 g) := by
  exact artin_leftTopCat_relation (braidGenerator1 g) (braidGenerator2 g)
    (artin_braid_relation g)

end InfoGeometry.Canonical.ToeplitzCuntzThreeHeckeTopologicalBridge

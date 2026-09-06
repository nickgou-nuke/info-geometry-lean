import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Canonical.ToeplitzCuntzThreeBraidRealizationBridge

/-!
# Topological cubic closure for a Toeplitz--Cuntz braid realization

The algebraic realization owner supplies the braided cubic charge and its full
twist closure.  This owner transports those operators to continuous
`TopCat` endomorphisms by left multiplication.  The carrier is still a
noncommutative star ring; no commutative or diagonal model is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeBraidCubicTopologicalBridge

open CategoryTheory
open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeBraidRealizationBridge
open ToeplitzCuntzThreeGenerators

variable {R : Type*} [Ring R] [StarRing R]
variable [TopologicalSpace R] [ContinuousMul R]
variable (g : ToeplitzCuntzThreeGenerators R)

/-- Continuous left multiplication by an element of the carrier. -/
def leftMulTopCatHom (a : R) : TopCat.of R ⟶ TopCat.of R :=
  TopCat.ofHom
    { toFun := fun x => a * x
      continuous_toFun := continuous_const.mul continuous_id }

@[simp]
theorem leftMulTopCatHom_apply (a x : R) :
    leftMulTopCatHom a x = a * x := rfl

theorem leftMulTopCatHom_comp (a b : R) :
    leftMulTopCatHom a ≫ leftMulTopCatHom b =
      leftMulTopCatHom (b * a) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change b * (a * x) = (b * a) * x
  simp only [mul_assoc]

theorem leftMulTopCatHom_one :
    leftMulTopCatHom (1 : R) = 𝟙 (TopCat.of R) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (1 : R) * x = x
  exact one_mul x

/-- TopCat endomorphism induced by the braided cubic supercharge. -/
def braidedCubicSuperchargeTopCatHom
    (D : ToeplitzBraidData g) : TopCat.of R ⟶ TopCat.of R :=
  leftMulTopCatHom (braidedCubicSupercharge g D)

/-- TopCat endomorphism induced by the full twist. -/
def fullTwistTopCatHom
    (D : ToeplitzBraidData g) : TopCat.of R ⟶ TopCat.of R :=
  leftMulTopCatHom (fullTwist g D)

/-- TopCat endomorphism induced by the excitation Hamiltonian. -/
def susyHamiltonianTopCatHom : TopCat.of R ⟶ TopCat.of R :=
  leftMulTopCatHom g.susyHamiltonian

/-- TopCat endomorphism induced by the defect projection. -/
def defectProjectionTopCatHom : TopCat.of R ⟶ TopCat.of R :=
  leftMulTopCatHom g.P0

theorem braidedCubicSuperchargeTopCatHom_cube
    (D : ToeplitzBraidData g) :
    braidedCubicSuperchargeTopCatHom g D ≫
        braidedCubicSuperchargeTopCatHom g D ≫
        braidedCubicSuperchargeTopCatHom g D =
      susyHamiltonianTopCatHom g ≫ fullTwistTopCatHom g D := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change braidedCubicSupercharge g D *
      (braidedCubicSupercharge g D *
        (braidedCubicSupercharge g D * x)) =
    fullTwist g D * (g.susyHamiltonian * x)
  simpa only [mul_assoc] using
    congrArg (fun z : R => z * x)
      (braidedCubicSupercharge_cube g D)

theorem braidedCubicSuperchargeTopCatHom_comp_defect_zero
    (D : ToeplitzBraidData g) :
    braidedCubicSuperchargeTopCatHom g D ≫
        defectProjectionTopCatHom g =
      leftMulTopCatHom (0 : R) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change g.P0 * (braidedCubicSupercharge g D * x) = (0 : R) * x
  rw [← mul_assoc, braidedCubicSupercharge_vacuum_annihilation_left g D]

theorem defectProjectionTopCatHom_comp_braidedCubicSupercharge_zero
    (D : ToeplitzBraidData g) :
    defectProjectionTopCatHom g ≫
        braidedCubicSuperchargeTopCatHom g D =
      leftMulTopCatHom (0 : R) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change braidedCubicSupercharge g D * (g.P0 * x) = (0 : R) * x
  rw [← mul_assoc, braidedCubicSupercharge_vacuum_annihilation_right g D]

end InfoGeometry.Canonical.ToeplitzCuntzThreeBraidCubicTopologicalBridge

import InfoGeometry.Canonical.FilteredStarAlgebraDirectLimitTopologicalRealization
import InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitComparison
import InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution

/-!
# Topological coefficientwise comparison for finite-group crossed products

Given an explicitly supplied continuous star-algebra realization of the stage
system, this owner sends a finite-stage crossed-product coefficient family to
the corresponding finite-group family in the target.  The target topology is
supplied by the realization; no topology is placed on the algebraic direct
limit, and no crossed-product completion or universal isomorphism is claimed.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductTopologicalComparison

open CategoryTheory
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimitTopologicalRealization
open InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitComparison
open InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution

universe u

variable {I G : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [Group G] [Fintype G] [DecidableEq G]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def topologicalCoefficientwiseComparison
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
    (i : I) :
    stageCrossedProduct I G Stage i → (G → B) :=
  fun F g => R.ι i (F g)

@[simp] theorem topologicalCoefficientwiseComparison_apply
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
    (i : I) (F : stageCrossedProduct I G Stage i) (g : G) :
    topologicalCoefficientwiseComparison Stage sys R i F g =
      R.ι i (F g) := rfl

theorem topologicalCoefficientwiseComparison_transition
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
    (hι_comm : ∀ {i j : I} (hij : i ≤ j),
      (R.ι j).comp (sys.map hij) = R.ι i)
    {i j : I} (hij : i ≤ j)
    (F : stageCrossedProduct I G Stage i) :
    topologicalCoefficientwiseComparison Stage sys R j
        (fun g => sys.map hij (F g)) =
      topologicalCoefficientwiseComparison Stage sys R i F := by
  funext g
  change R.ι j (sys.map hij (F g)) = R.ι i (F g)
  exact congrArg (fun f : Stage i → B => f (F g))
    (congrArg (fun f : Stage i →⋆ₐ[ℂ] B => f.toFun)
      (hι_comm hij))

theorem continuous_topologicalCoefficientwiseComparison
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
    (i : I) :
    Continuous
      (topologicalCoefficientwiseComparison Stage sys R i :
        stageCrossedProduct I G Stage i → (G → B)) := by
  apply continuous_pi
  intro g
  exact
    (starAlgHomToContinuousLinearMap (R.ι i)).continuous.comp
      (continuous_apply g)

def topologicalCoefficientwiseComparisonHom
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
    (i : I) :
    TopCat.of (stageCrossedProduct I G Stage i) ⟶
      TopCat.of (G → B) :=
  TopCat.ofHom
    { toFun := topologicalCoefficientwiseComparison Stage sys R i
      continuous_toFun := continuous_topologicalCoefficientwiseComparison
        Stage sys R i }

@[simp] theorem topologicalCoefficientwiseComparisonHom_apply
    (R : TopologicalRealization (Stage := Stage) (sys := sys) (B := B))
    (i : I) (F : stageCrossedProduct I G Stage i) :
    topologicalCoefficientwiseComparisonHom Stage sys R i F =
      topologicalCoefficientwiseComparison Stage sys R i F := rfl

end InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductTopologicalComparison

import InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution

/-!
# Equivariant transition laws for finite-stage crossed products

The connecting maps of the native star-algebra system are lifted
coefficientwise to the finite crossed-product-shaped carriers.  The two
operations below are the precise equivariance needed before any crossed
product/direct-limit comparison theorem can be stated.
-/

namespace InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductTransitionLaws

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionDirectLimit
open InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution

noncomputable section

universe u

variable {I G : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [Group G] [Fintype G] [DecidableEq G]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (A : CompatibleStarGroupAction I G Stage sys)

def stageCrossedProductTransition
    {i j : I} (hij : i ≤ j)
    (F : stageCrossedProduct I G Stage i) :
    stageCrossedProduct I G Stage j :=
  fun g => sys.map hij (F g)

@[simp] theorem stageCrossedProductTransition_apply
    {i j : I} (hij : i ≤ j)
    (F : stageCrossedProduct I G Stage i) (g : G) :
    stageCrossedProductTransition Stage sys hij F g =
      sys.map hij (F g) := rfl

theorem stageCrossedProductTransition_convolution
    {i j : I} (hij : i ≤ j)
    (F K : stageCrossedProduct I G Stage i) :
    stageCrossedProductTransition Stage sys hij
        (stageConvolution I G Stage sys A i F K) =
      stageConvolution I G Stage sys A j
        (stageCrossedProductTransition Stage sys hij F)
        (stageCrossedProductTransition Stage sys hij K) := by
  funext r
  simp only [stageCrossedProductTransition, stageConvolution]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [map_mul]
  rw [A.action_transition hij g (K (g⁻¹ * r))]

theorem stageCrossedProductTransition_star
    {i j : I} (hij : i ≤ j)
    (F : stageCrossedProduct I G Stage i) :
    stageCrossedProductTransition Stage sys hij
        (stageConvolutionStar I G Stage sys A i F) =
      stageConvolutionStar I G Stage sys A j
        (stageCrossedProductTransition Stage sys hij F) := by
  funext r
  simp only [stageCrossedProductTransition, stageConvolutionStar]
  rw [← map_star]
  exact A.action_transition hij r (star (F r⁻¹))

end

end InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductTransitionLaws

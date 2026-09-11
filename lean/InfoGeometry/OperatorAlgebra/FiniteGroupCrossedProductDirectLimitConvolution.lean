import InfoGeometry.Canonical.FilteredStarAlgebraFiniteGroupActionDirectLimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Convolution after descent to the native star-algebra direct limit

The theorem below is the honest noncommutative comparison needed before a
crossed-product colimit theorem: stagewise convolution agrees with the
coefficientwise direct-limit convolution.  No universal crossed-product
property or C*-completion is claimed.
-/

namespace InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution

open scoped BigOperators
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionDirectLimit

noncomputable section

universe u

variable {I G : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [Group G] [Fintype G] [DecidableEq G]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (A : CompatibleStarGroupAction I G Stage sys)

abbrev stageCrossedProduct (I G : Type u) (Stage : I → Type u) (i : I) := G → Stage i
abbrev limitCoefficient (Stage : I → Type u)
    [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage) := AlgebraicStarDirectLimit Stage sys

def stageConvolution
    (I G : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [Group G] [Fintype G] [DecidableEq G]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (A : CompatibleStarGroupAction I G Stage sys) (i : I)
    (F K : stageCrossedProduct I G Stage i) : stageCrossedProduct I G Stage i :=
  fun r => ∑ g : G, F g * A.action i g (K (g⁻¹ * r))

def stageConvolutionStar
    (I G : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [Group G] [Fintype G] [DecidableEq G]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (A : CompatibleStarGroupAction I G Stage sys) (i : I)
    (F : stageCrossedProduct I G Stage i) : stageCrossedProduct I G Stage i :=
  fun r => A.action i r (star (F r⁻¹))

def limitConvolution
    (I G : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [Group G] [Fintype G] [DecidableEq G]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (A : CompatibleStarGroupAction I G Stage sys)
    (F K : G → limitCoefficient Stage sys) : G → limitCoefficient Stage sys :=
  fun r => ∑ g : G, F g *
    algebraicColimitGroupAction I G Stage sys A g (K (g⁻¹ * r))

def limitConvolutionOne
    (I G : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [Group G] [Fintype G] [DecidableEq G]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage) :
    G → limitCoefficient Stage sys :=
  fun g => if g = 1 then 1 else 0

def limitConvolutionStar
    (I G : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [Group G] [Fintype G] [DecidableEq G]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (A : CompatibleStarGroupAction I G Stage sys)
    (F : G → limitCoefficient Stage sys) : G → limitCoefficient Stage sys :=
  fun r => algebraicColimitGroupAction I G Stage sys A r
    (star (F r⁻¹))

def coefficientwiseComparison
    (I G : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [Group G] [Fintype G] [DecidableEq G]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage) (i : I) :
    stageCrossedProduct I G Stage i → (G → limitCoefficient Stage sys) :=
  fun F g => algebraicStarDirectLimitOf Stage sys i (F g)

@[simp] theorem coefficientwiseComparison_apply
    (i : I) (F : stageCrossedProduct I G Stage i) (g : G) :
    coefficientwiseComparison I G Stage sys i F g =
      algebraicStarDirectLimitOf Stage sys i (F g) := rfl

theorem coefficientwiseComparison_convolution
    (i : I) (F K : stageCrossedProduct I G Stage i) :
    coefficientwiseComparison I G Stage sys i
        (stageConvolution I G Stage sys A i F K) =
      limitConvolution I G Stage sys A
        (coefficientwiseComparison I G Stage sys i F)
        (coefficientwiseComparison I G Stage sys i K) := by
  funext r
  change algebraicStarDirectLimitOf Stage sys i
      (∑ g : G, F g * A.action i g (K (g⁻¹ * r))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [map_mul]
  simp only [coefficientwiseComparison_apply,
    algebraicColimitGroupAction_on_stage]

theorem coefficientwiseComparison_star
    (i : I) (F : stageCrossedProduct I G Stage i) :
    coefficientwiseComparison I G Stage sys i
        (stageConvolutionStar I G Stage sys A i F) =
      limitConvolutionStar I G Stage sys A
        (coefficientwiseComparison I G Stage sys i F) := by
  funext r
  change algebraicStarDirectLimitOf Stage sys i
      (A.action i r (star (F r⁻¹))) =
    algebraicColimitGroupAction I G Stage sys A r
      (star (algebraicStarDirectLimitOf Stage sys i (F r⁻¹)))
  rw [map_star (A.action i r)]
  rw [map_star (algebraicStarDirectLimitOf Stage sys i)]
  rw [map_star (algebraicColimitGroupAction I G Stage sys A r)]
  rw [algebraicColimitGroupAction_on_stage]

theorem limitConvolution_assoc
    (F K L : G → limitCoefficient Stage sys) :
    limitConvolution I G Stage sys A
        (limitConvolution I G Stage sys A F K) L =
      limitConvolution I G Stage sys A F
        (limitConvolution I G Stage sys A K L) := by
  classical
  funext r
  change
    (∑ h : G, (∑ g : G, F g *
      algebraicColimitGroupAction I G Stage sys A g (K (g⁻¹ * h))) *
      algebraicColimitGroupAction I G Stage sys A h (L (h⁻¹ * r))) =
    ∑ g : G, F g *
      algebraicColimitGroupAction I G Stage sys A g
        (∑ k : G, K k *
          algebraicColimitGroupAction I G Stage sys A k
            (L (k⁻¹ * (g⁻¹ * r))))
  calc
    _ = ∑ g : G, ∑ h : G,
        (F g * algebraicColimitGroupAction I G Stage sys A g
          (K (g⁻¹ * h))) *
          algebraicColimitGroupAction I G Stage sys A h
            (L (h⁻¹ * r)) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [← (Equiv.mulLeft g).sum_comp]
      all_goals simp
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [algebraicColimitGroupAction_mul I G Stage sys A g k]
      simp only [StarAlgHom.comp_apply]

theorem limitConvolution_one_left
    (F : G → limitCoefficient Stage sys) :
    limitConvolution I G Stage sys A
        (limitConvolutionOne I G Stage sys) F = F := by
  funext r
  change
    (∑ g : G, (if g = 1 then 1 else 0) *
      algebraicColimitGroupAction I G Stage sys A g (F (g⁻¹ * r))) = F r
  rw [Finset.sum_eq_single 1]
  · rw [algebraicColimitGroupAction_one I G Stage sys A]
    simp
  · intro b hb hne
    simp [hne]
  · simp

theorem limitConvolution_one_right
    (F : G → limitCoefficient Stage sys) :
    limitConvolution I G Stage sys A F
        (limitConvolutionOne I G Stage sys) = F := by
  funext r
  change
    (∑ g : G, F g *
      algebraicColimitGroupAction I G Stage sys A g
        (if g⁻¹ * r = 1 then 1 else 0)) = F r
  rw [Finset.sum_eq_single r]
  · simp
  · intro b hb hne
    have hnot : b⁻¹ * r ≠ 1 := by
      intro h
      apply hne
      calc
        b = b * 1 := by simp
        _ = b * (b⁻¹ * r) := by rw [h]
        _ = (b * b⁻¹) * r := by rw [mul_assoc]
        _ = r := by simp
    simp [hnot]
  · simp

@[simp] theorem limitConvolutionStar_star
    (F : G → limitCoefficient Stage sys) :
    limitConvolutionStar I G Stage sys A
        (limitConvolutionStar I G Stage sys A F) = F := by
  funext r
  change
    algebraicColimitGroupAction I G Stage sys A r
      (star (algebraicColimitGroupAction I G Stage sys A r⁻¹
        (star (F ((r⁻¹)⁻¹))))) = F r
  rw [map_star]
  rw [← StarAlgHom.comp_apply]
  rw [← algebraicColimitGroupAction_mul I G Stage sys A r r⁻¹]
  simp only [mul_inv_cancel, inv_inv]
  rw [algebraicColimitGroupAction_one I G Stage sys A]
  simp

theorem limitConvolutionStar_mul
    (F K : G → limitCoefficient Stage sys) :
    limitConvolutionStar I G Stage sys A
        (limitConvolution I G Stage sys A F K) =
      limitConvolution I G Stage sys A
        (limitConvolutionStar I G Stage sys A K)
        (limitConvolutionStar I G Stage sys A F) := by
  classical
  funext r
  simp only [limitConvolutionStar, limitConvolution]
  rw [star_sum]
  simp only [star_mul]
  rw [map_sum]
  simp only [map_mul, map_star]
  rw [← (Equiv.mulLeft r⁻¹).sum_comp]
  apply Finset.sum_congr rfl
  intro g hg
  simp only [Equiv.coe_mulLeft]
  rw [← StarAlgHom.comp_apply]
  rw [← algebraicColimitGroupAction_mul I G Stage sys A r (r⁻¹ * g)]
  congr 1
  · simp [mul_assoc]
  · rw [← StarAlgHom.comp_apply]
    rw [← algebraicColimitGroupAction_mul I G Stage sys A g (g⁻¹ * r)]
    simp
  all_goals simp

end

end InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution

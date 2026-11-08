import InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.D4StarCrossedProductNonUnitalStarSurface

/-!
# Equivariant transition maps for the finite D₄-star crossed-product carrier

This owner records coefficient-level equivariance and its induced finite
crossed-product maps.  It deliberately does not install a global ring/direct-
limit structure and does not claim a crossed-product completion.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductTransitions

open D4StarFiniteCrossedProduct

noncomputable section

def observableMapComp
    (Φ Ψ : D4StarFiniteCrossedProduct.EquivariantObservableMap) :
    D4StarFiniteCrossedProduct.EquivariantObservableMap where
  map := Φ.map.comp Ψ.map
  equivariant := by
    intro σ f
    change Φ.map (Ψ.map (colorPullback σ f)) =
      colorPullback σ (Φ.map (Ψ.map f))
    rw [Ψ.equivariant, Φ.equivariant]

def identityObservableMap :
    D4StarFiniteCrossedProduct.EquivariantObservableMap where
  map := StarAlgHom.id ℂ D4StarFiniteCrossedProduct.D4StarObservable
  equivariant := by
    intro σ f
    rfl

@[simp] theorem observableMapComp_apply
    (Φ Ψ : D4StarFiniteCrossedProduct.EquivariantObservableMap)
    (f : D4StarFiniteCrossedProduct.D4StarObservable) :
    (observableMapComp Φ Ψ).map f = Φ.map (Ψ.map f) := rfl

@[simp] theorem EquivariantObservableMap.comp_identity
    (Φ : D4StarFiniteCrossedProduct.EquivariantObservableMap) :
    observableMapComp Φ identityObservableMap = Φ := by
  cases Φ with
  | mk map equivariant =>
      simp [observableMapComp, identityObservableMap]

@[simp] theorem EquivariantObservableMap.identity_comp
    (Φ : D4StarFiniteCrossedProduct.EquivariantObservableMap) :
    observableMapComp identityObservableMap Φ = Φ := by
  cases Φ with
  | mk map equivariant =>
      simp [observableMapComp, identityObservableMap]

theorem EquivariantObservableMap.comp_assoc
    (Φ Ψ Θ : D4StarFiniteCrossedProduct.EquivariantObservableMap) :
    observableMapComp (observableMapComp Φ Ψ) Θ =
      observableMapComp Φ (observableMapComp Ψ Θ) := by
  cases Φ with
  | mk Φ hΦ =>
      cases Ψ with
      | mk Ψ hΨ =>
          cases Θ with
          | mk Θ hΘ =>
              simp [observableMapComp]

theorem crossedProductMap_comp
    (Φ Ψ : D4StarFiniteCrossedProduct.EquivariantObservableMap)
    (F : D4StarFiniteCrossedProduct.D4StarCrossedProduct) :
    crossedProductMap (observableMapComp Φ Ψ) F =
      crossedProductMap Φ (crossedProductMap Ψ F) := by
  funext r
  rfl

@[simp] theorem crossedProductMap_identity
    (F : D4StarFiniteCrossedProduct.D4StarCrossedProduct) :
    crossedProductMap identityObservableMap F = F := by
  funext r
  rfl

theorem crossedProductMap_one
    (Φ : D4StarFiniteCrossedProduct.EquivariantObservableMap) :
    crossedProductMap Φ crossedProductOne = crossedProductOne := by
  funext r
  by_cases h : r = 1
  · simp [crossedProductMap, crossedProductOne, h]
  · simp [crossedProductMap, crossedProductOne, h]

theorem crossedProductMap_star
    (Φ : D4StarFiniteCrossedProduct.EquivariantObservableMap)
    (F : D4StarFiniteCrossedProduct.D4StarCrossedProduct) :
    crossedProductMap Φ (crossedProductStar F) =
      crossedProductStar (crossedProductMap Φ F) := by
  funext r
  change Φ.map (colorPullback r (star (F.coeff r.symm))) =
    colorPullback r (star (Φ.map (F.coeff r.symm)))
  rw [Φ.equivariant, map_star]

structure D4StarCrossedProductTransitionSystem
    (I : Type*) [Preorder I] where
  transition : ∀ {i j : I}, i ≤ j →
    D4StarFiniteCrossedProduct.EquivariantObservableMap
  transition_refl : ∀ i,
    transition (le_refl i) = identityObservableMap
  transition_trans : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
    transition (le_trans hij hjk) =
      observableMapComp (transition hjk) (transition hij)

variable {I : Type*} [Preorder I]
variable (T : D4StarCrossedProductTransitionSystem I)

def crossedProductTransition {i j : I} (hij : i ≤ j) :
    D4StarFiniteCrossedProduct.D4StarCrossedProduct →
      D4StarFiniteCrossedProduct.D4StarCrossedProduct :=
  crossedProductMap (T.transition hij)

@[simp] theorem crossedProductTransition_refl (i : I) :
    crossedProductTransition T (le_refl i) = id := by
  funext F
  simp [crossedProductTransition, T.transition_refl]

theorem crossedProductTransition_trans
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    (F : D4StarFiniteCrossedProduct.D4StarCrossedProduct) :
    crossedProductTransition T (le_trans hij hjk) F =
      crossedProductTransition T hjk
        (crossedProductTransition T hij F) := by
  rw [crossedProductTransition, T.transition_trans]
  exact crossedProductMap_comp (T.transition hjk) (T.transition hij) F

theorem crossedProductTransition_mul
    {i j : I} (hij : i ≤ j)
    (F K : D4StarFiniteCrossedProduct.D4StarCrossedProduct) :
    crossedProductTransition T hij (crossedProductMul F K) =
      crossedProductMul
        (crossedProductTransition T hij F)
        (crossedProductTransition T hij K) := by
  exact crossedProductMap_mul (T.transition hij) F K

theorem crossedProductTransition_star
    {i j : I} (hij : i ≤ j)
    (F : D4StarFiniteCrossedProduct.D4StarCrossedProduct) :
    crossedProductTransition T hij (crossedProductStar F) =
      crossedProductStar (crossedProductTransition T hij F) := by
  exact crossedProductMap_star (T.transition hij) F

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductTransitions

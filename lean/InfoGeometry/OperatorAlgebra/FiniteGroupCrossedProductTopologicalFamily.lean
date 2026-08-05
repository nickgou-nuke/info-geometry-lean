import Mathlib

/-!
# Varying-carrier finite-group crossed-product transitions

Each stage has its own semiring and topology.  Equivariant ring-homomorphisms
induce coefficientwise crossed-product maps; continuity is carried by an
explicit witness.  No direct-limit or completion theorem is asserted here.
-/

namespace InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductTopologicalFamily

open scoped BigOperators

noncomputable section

structure ActionFamily (I G : Type*) [Group G] (A : I → Type*)
    [∀ i, Semiring (A i)] where
  action : ∀ i, G → A i ≃+* A i
  action_one : ∀ i, action i 1 = RingEquiv.refl (A i)
  action_mul : ∀ i (g h : G),
    action i (g * h) = (action i h).trans (action i g)

abbrev crossedProduct (G : Type*) (A : I → Type*) (i : I) := G → A i

def convolution
    (I G : Type*) (A : I → Type*)
    [Group G] [Fintype G] [DecidableEq G]
    [∀ i, Semiring (A i)]
    (α : ActionFamily I G A) (i : I)
    (F K : crossedProduct G A i) : crossedProduct G A i :=
  fun r => ∑ g : G, F g * α.action i g (K (g⁻¹ * r))

def crossedProductMap
    (I G : Type*) [Preorder I] (A : I → Type*)
    [∀ i, Semiring (A i)]
    (transition : ∀ {i j : I}, i ≤ j → A i →+* A j)
    {i j : I} (hij : i ≤ j) :
    crossedProduct G A i → crossedProduct G A j :=
  fun F g => transition hij (F g)

@[simp] theorem crossedProductMap_apply
    (I G : Type*) [Preorder I] (A : I → Type*)
    [∀ i, Semiring (A i)]
    (transition : ∀ {i j : I}, i ≤ j → A i →+* A j)
    {i j : I} (hij : i ≤ j) (F : crossedProduct G A i) (g : G) :
    crossedProductMap I G A transition hij F g = transition hij (F g) := rfl

structure EquivariantTransition
    (I G : Type*) [Preorder I] [Group G] (A : I → Type*)
    [∀ i, Semiring (A i)]
    (α : ActionFamily I G A)
    (transition : ∀ {i j : I}, i ≤ j → A i →+* A j) : Prop where
  equivariant : ∀ {i j : I} (hij : i ≤ j) (g : G) (x : A i),
    transition hij (α.action i g x) =
      α.action j g (transition hij x)

theorem crossedProductMap_convolution
    {I G : Type*} [Preorder I] [Group G] [Fintype G] [DecidableEq G]
    (A : I → Type*) [∀ i, Semiring (A i)]
    (α : ActionFamily I G A)
    (transition : ∀ {i j : I}, i ≤ j → A i →+* A j)
    (hα : EquivariantTransition I G A α transition)
    {i j : I} (hij : i ≤ j)
    (F K : crossedProduct G A i) :
    crossedProductMap I G A transition hij
        (convolution I G A α i F K) =
      convolution I G A α j
        (crossedProductMap I G A transition hij F)
        (crossedProductMap I G A transition hij K) := by
  funext r
  change transition hij
      (∑ g : G, F g * α.action i g (K (g⁻¹ * r))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [map_mul, hα.equivariant]
  rfl

structure ContinuousTransition
    (I : Type*) [Preorder I] (A : I → Type*)
    [∀ i, Semiring (A i)] [∀ i, TopologicalSpace (A i)]
    (transition : ∀ {i j : I}, i ≤ j → A i →+* A j) : Prop where
  continuous : ∀ {i j : I} (hij : i ≤ j), Continuous (transition hij)

theorem continuous_crossedProductMap
    {I G : Type*} [Preorder I]
    (A : I → Type*) [∀ i, Semiring (A i)]
    [∀ i, TopologicalSpace (A i)]
    (transition : ∀ {i j : I}, i ≤ j → A i →+* A j)
    (hcont : ContinuousTransition I A transition)
    {i j : I} (hij : i ≤ j) :
    Continuous (crossedProductMap I G A transition hij :
      crossedProduct G A i → crossedProduct G A j) := by
  apply continuous_pi
  intro g
  exact (hcont.continuous hij).comp (continuous_apply g)

def crossedProductTopCatHom
    {I G : Type*} [Preorder I]
    (A : I → Type*) [∀ i, Semiring (A i)]
    [∀ i, TopologicalSpace (A i)]
    (transition : ∀ {i j : I}, i ≤ j → A i →+* A j)
    (hcont : ContinuousTransition I A transition)
    {i j : I} (hij : i ≤ j) :
    TopCat.of (crossedProduct G A i) ⟶ TopCat.of (crossedProduct G A j) :=
  TopCat.ofHom
    { toFun := crossedProductMap I G A transition hij
      continuous_toFun :=
        continuous_crossedProductMap (I := I) (G := G) A transition hcont hij }

@[simp] theorem crossedProductTopCatHom_apply
    {I G : Type*} [Preorder I]
    (A : I → Type*) [∀ i, Semiring (A i)]
    [∀ i, TopologicalSpace (A i)]
    (transition : ∀ {i j : I}, i ≤ j → A i →+* A j)
    (hcont : ContinuousTransition I A transition)
    {i j : I} (hij : i ≤ j) (F : crossedProduct G A i) :
    crossedProductTopCatHom A transition hcont hij F =
      crossedProductMap I G A transition hij F := rfl

end

end InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductTopologicalFamily

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.D4StarGraphQuotient

namespace InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct

open InfoGeometry.Canonical
open InfoGeometry.Topology.PauliJungD4Star

noncomputable section

noncomputable instance : Finite ColorChannel := Finite.of_fintype _
noncomputable instance : Fintype (Equiv.Perm ColorChannel) := Fintype.ofFinite _

/-!
# The finite D₄-star crossed-product carrier

The coarse orbit quotient forgets which color permutation moved an outer
vertex. This owner keeps that group label in a finite convolution carrier.
The observable coefficients are functions on the original four-vertex star;
they are not functions on the coarse quotient.

This file exposes the finite convolution carrier and proves its associativity
and coefficient laws. Involution compatibility and the full covariance
package remain separate proof obligations.
-/

abbrev D4StarObservable := FourPlaneVertex → ℂ

noncomputable def colorPullback
    (σ : Equiv.Perm ColorChannel) :
    D4StarObservable ≃+* D4StarObservable where
  toFun f := fun v => f (vertexPermutation σ.symm v)
  invFun f := fun v => f (vertexPermutation σ v)
  left_inv := by
    intro f
    funext v
    cases v <;> simp [vertexPermutation]
  right_inv := by
    intro f
    funext v
    cases v <;> simp [vertexPermutation]
  map_add' := by
    intro f g
    funext v
    simp
  map_mul' := by
    intro f g
    funext v
    simp

@[simp] theorem colorPullback_apply
    (σ : Equiv.Perm ColorChannel) (f : D4StarObservable)
    (v : FourPlaneVertex) :
    colorPullback σ f v = f (vertexPermutation σ.symm v) := rfl

theorem colorPullback_one :
    colorPullback (1 : Equiv.Perm ColorChannel) =
      RingEquiv.refl D4StarObservable := by
  ext f v
  cases v <;> rfl

theorem colorPullback_mul
    (σ τ : Equiv.Perm ColorChannel) :
    colorPullback (σ * τ) =
      (colorPullback τ).trans (colorPullback σ) := by
  ext f v
  cases v with
  | inl c =>
      change f (Sum.inl ((σ * τ)⁻¹ c)) =
        f (Sum.inl (τ.symm (σ.symm c)))
      rw [mul_inv_rev]
      rfl
  | inr u => rfl

abbrev D4StarCrossedProduct := Equiv.Perm ColorChannel → D4StarObservable

namespace D4StarCrossedProduct

abbrev coeff (F : D4StarCrossedProduct) :
    Equiv.Perm ColorChannel → D4StarObservable := F

end D4StarCrossedProduct

@[ext] theorem D4StarCrossedProduct.ext
    {F K : D4StarCrossedProduct}
    (h : ∀ σ, F.coeff σ = K.coeff σ) : F = K := by
  funext σ
  exact h σ

noncomputable def crossedProductMul
    (F K : D4StarCrossedProduct) : D4StarCrossedProduct := by
  classical
  exact fun r => (Finset.univ : Finset (Equiv.Perm ColorChannel)).sum
    (fun g => F.coeff g *
      colorPullback g (K.coeff (g.symm * r)))

instance : Mul D4StarCrossedProduct := ⟨crossedProductMul⟩

def crossedProductOne : D4StarCrossedProduct := by
  classical
  exact fun r => if r = 1 then 1 else 0

instance : One D4StarCrossedProduct := ⟨crossedProductOne⟩

noncomputable def crossedProductStar
    (F : D4StarCrossedProduct) : D4StarCrossedProduct :=
  fun r => colorPullback r (star (F.coeff r.symm))

def observableEmbedding (f : D4StarObservable) : D4StarCrossedProduct := by
  classical
  exact fun r => if r = 1 then f else 0

def groupUnitary (σ : Equiv.Perm ColorChannel) : D4StarCrossedProduct := by
  classical
  exact fun r => if r = σ then 1 else 0

def outerProjection (c : ColorChannel) : D4StarObservable :=
  fun v => if v = outerVertex c then 1 else 0

@[simp] theorem crossedProductMul_coeff
    (F K : D4StarCrossedProduct) (r : Equiv.Perm ColorChannel) :
    (crossedProductMul F K) r =
      (Finset.univ : Finset (Equiv.Perm ColorChannel)).sum
        (fun g => F.coeff g *
          colorPullback g (K.coeff (g.symm * r))) := by
  rfl

theorem crossedProductMul_assoc
    (F K L : D4StarCrossedProduct) :
    crossedProductMul (crossedProductMul F K) L =
      crossedProductMul F (crossedProductMul K L) := by
  classical
  apply D4StarCrossedProduct.ext
  intro r
  change
    (Finset.univ : Finset (Equiv.Perm ColorChannel)).sum
        (fun h =>
          ((Finset.univ : Finset (Equiv.Perm ColorChannel)).sum
            (fun g => F.coeff g *
              colorPullback g (K.coeff (g.symm * h)))) *
            colorPullback h (L.coeff (h.symm * r))) =
      (Finset.univ : Finset (Equiv.Perm ColorChannel)).sum
        (fun g => F.coeff g *
          colorPullback g
            ((Finset.univ : Finset (Equiv.Perm ColorChannel)).sum
              (fun k => K.coeff k *
                colorPullback k (L.coeff (k.symm * (g.symm * r))))))
  calc
    _ = (Finset.univ : Finset (Equiv.Perm ColorChannel)).sum
        (fun g =>
          (Finset.univ : Finset (Equiv.Perm ColorChannel)).sum
            (fun h =>
              (F.coeff g * colorPullback g (K.coeff (g.symm * h))) *
                colorPullback h (L.coeff (h.symm * r)))) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [← (Equiv.mulLeft g).sum_comp]
      rw [map_sum]
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      have hgk : g.symm * (g * k) = k := by
        rw [← mul_assoc, Equiv.Perm.symm_mul, one_mul]
      have hgr : (g * k).symm * r = k.symm * (g.symm * r) := by
        change (g * k)⁻¹ * r = _
        rw [mul_inv_rev]
        change k.symm * (g.symm * r) = k.symm * (g.symm * r)
        rfl
      change
        colorPullback g (K.coeff (g.symm * (g * k))) *
            colorPullback (g * k) (L.coeff ((g * k).symm * r)) = _
      rw [hgk, hgr, colorPullback_mul]
      rfl
      all_goals simp

@[simp] theorem crossedProductOne_coeff
    (r : Equiv.Perm ColorChannel) :
    crossedProductOne.coeff r = if r = 1 then 1 else 0 := by
  rfl

@[simp] theorem observableEmbedding_coeff
    (f : D4StarObservable) (r : Equiv.Perm ColorChannel) :
    (observableEmbedding f).coeff r = if r = 1 then f else 0 := by
  rfl

@[simp] theorem groupUnitary_coeff
    (σ r : Equiv.Perm ColorChannel) :
    (groupUnitary σ).coeff r = if r = σ then 1 else 0 := by
  rfl

@[simp] theorem crossedProductStar_coeff
    (F : D4StarCrossedProduct) (r : Equiv.Perm ColorChannel) :
    (crossedProductStar F).coeff r =
      colorPullback r (star (F.coeff r.symm)) := by
  rfl

@[simp] theorem crossedProductStar_star
    (F : D4StarCrossedProduct) :
    crossedProductStar (crossedProductStar F) = F := by
  funext r v
  cases v with
  | inl c =>
      simp [crossedProductStar, colorPullback, vertexPermutation]
  | inr u =>
      simp [crossedProductStar, colorPullback, vertexPermutation]

structure EquivariantObservableMap where
  map : D4StarObservable →⋆ₐ[ℂ] D4StarObservable
  equivariant : ∀ (σ : Equiv.Perm ColorChannel) (f : D4StarObservable),
    map (colorPullback σ f) = colorPullback σ (map f)

def crossedProductMap
    (Φ : EquivariantObservableMap) :
    D4StarCrossedProduct → D4StarCrossedProduct :=
  fun F r => Φ.map (F.coeff r)

@[simp] theorem crossedProductMap_coeff
    (Φ : EquivariantObservableMap)
    (F : D4StarCrossedProduct) (r : Equiv.Perm ColorChannel) :
    crossedProductMap Φ F r = Φ.map (F.coeff r) := rfl

theorem crossedProductMap_mul
    (Φ : EquivariantObservableMap)
    (F K : D4StarCrossedProduct) :
    crossedProductMap Φ (crossedProductMul F K) =
      crossedProductMul (crossedProductMap Φ F) (crossedProductMap Φ K) := by
  funext r
  rw [crossedProductMul_coeff]
  change Φ.map
      ((Finset.univ : Finset (Equiv.Perm ColorChannel)).sum
        (fun g => F.coeff g *
          colorPullback g (K.coeff (g.symm * r)))) = _
  rw [map_sum]
  change _ =
    (Finset.univ : Finset (Equiv.Perm ColorChannel)).sum
      (fun g => Φ.map (F.coeff g) *
        colorPullback g (Φ.map (K.coeff (g.symm * r))))
  apply Finset.sum_congr rfl
  intro g hg
  rw [map_mul, Φ.equivariant]

@[simp] theorem colorPullback_outerProjection
    (σ : Equiv.Perm ColorChannel) (c : ColorChannel) :
    colorPullback σ (outerProjection c) =
      outerProjection (σ c) := by
  ext v
  cases v with
  | inl d =>
      by_cases h : σ.symm d = c
      · have hd : d = σ c := by
          exact (Equiv.symm_apply_eq σ).mp h
        simp [colorPullback, outerProjection, vertexPermutation,
          outerVertex, h, hd]
      · have h' : d ≠ σ c := by
          intro hd
          apply h
          simpa [Equiv.symm_apply_eq] using hd
        simp [colorPullback, outerProjection, vertexPermutation,
          outerVertex, h, h']
  | inr u =>
      simp [colorPullback, outerProjection, vertexPermutation, outerVertex]

theorem groupUnitary_mul_observableEmbedding_coeff
    (σ r : Equiv.Perm ColorChannel) (f : D4StarObservable) :
    (groupUnitary σ * observableEmbedding f) r =
      if r = σ then colorPullback σ f else 0 := by
  classical
  change
    (Finset.univ : Finset (Equiv.Perm ColorChannel)).sum
        (fun g => (if g = σ then 1 else 0) *
          colorPullback g (if g.symm * r = 1 then f else 0)) = _
  rw [Finset.sum_eq_single σ]
  · by_cases hr : r = σ
    · subst r
      simp
    · have hne : σ.symm * r ≠ 1 := by
        intro h
        apply hr
        calc
          r = (1 : Equiv.Perm ColorChannel) * r := by simp
          _ = (σ * σ.symm) * r := by rw [Equiv.Perm.mul_symm]
          _ = σ * (σ.symm * r) := by rw [mul_assoc]
          _ = σ * 1 := by rw [h]
          _ = σ := by simp
      simp [hne, hr]
  · intro b hb hbs
    simp [hbs]
  · simp

@[simp] theorem observableEmbedding_mul_groupUnitary_coeff
    (f : D4StarObservable) (σ r : Equiv.Perm ColorChannel) :
    (observableEmbedding f * groupUnitary σ) r =
      if r = σ then f else 0 := by
  classical
  change
    (Finset.univ : Finset (Equiv.Perm ColorChannel)).sum
        (fun g => (if g = 1 then f else 0) *
          colorPullback g (if g.symm * r = σ then 1 else 0)) = _
  rw [Finset.sum_eq_single 1]
  · by_cases hr : r = σ
    · subst r
      simp
    · simp [hr]
  · intro b hb hbs
    simp [hbs]
  · simp

theorem crossedProduct_noncommutative
    (σ : Equiv.Perm ColorChannel)
    (c : ColorChannel)
    (hmove : σ c ≠ c) :
    groupUnitary σ * observableEmbedding (outerProjection c) ≠
      observableEmbedding (outerProjection c) * groupUnitary σ := by
  intro h
  have hcoeff :
      colorPullback σ (outerProjection c) = outerProjection c := by
    have hσ := congrArg (fun F : D4StarCrossedProduct => F σ) h
    simpa [groupUnitary_mul_observableEmbedding_coeff,
      observableEmbedding_mul_groupUnitary_coeff] using hσ
  have hproj : outerProjection (σ c) = outerProjection c := by
    simpa [colorPullback_outerProjection] using hcoeff
  have houter : outerVertex c ≠ outerVertex (σ c) := by
    intro h'
    apply hmove
    simpa [outerVertex] using h'.symm
  have hval := congrArg (fun f : D4StarObservable => f (outerVertex c)) hproj
  simp [outerProjection, houter] at hval

end

end InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct

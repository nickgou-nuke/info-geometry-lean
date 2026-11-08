import InfoGeometry.Algebra.FiveGradedTKKSpec
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra

/-! Symmetries and realizations of the common five-graded TKK contract. -/

structure TKKSymmetry (R : Type*) [CommRing R] (G : Type*) [Monoid G]
    (S : FiveGradedTKKSpec R) where
  act : G → S.lie.L →ₗ[R] S.lie.L
  act_one : act 1 = LinearMap.id
  act_mul : ∀ g h, act (g * h) = (act g).comp (act h)
  act_grade : ∀ g i x, x ∈ S.grade i → act g x ∈ S.grade i
  act_inversion : ∀ g x, act g (S.inversion x) = S.inversion (act g x)

def TKKSymmetry.trivial {R G : Type*} [CommRing R] [Monoid G]
    (S : FiveGradedTKKSpec R) : TKKSymmetry R G S where
  act _ := LinearMap.id
  act_one := rfl
  act_mul _ _ := by ext; rfl
  act_grade _ _ _ hx := hx
  act_inversion _ _ := rfl

structure EquivariantTKKRealization (R : Type*) [CommRing R] (G : Type*) [Monoid G]
    (S M : FiveGradedTKKSpec R) (σS : TKKSymmetry R G S) (σM : TKKSymmetry R G M)
    where
  map : S.lie.L ≃ₗ[R] M.lie.L
  map_bracket : ∀ x y, map ⁅x, y⁆ = ⁅map x, map y⁆
  map_grade : ∀ i x, x ∈ S.grade i ↔ map x ∈ M.grade i
  map_inversion : ∀ x, map (S.inversion x) = M.inversion (map x)
  metric_map : S.metric.V ≃ₗ[R] M.metric.V
  map_metric : ∀ x y,
    M.metric.beta (metric_map x) (metric_map y) = S.metric.beta x y
  equivariant : ∀ g x, map (σS.act g x) = σM.act g (map x)

theorem EquivariantTKKRealization.map_lie
    {R G : Type*} [CommRing R] [Monoid G]
    {S M : FiveGradedTKKSpec R} {σS : TKKSymmetry R G S} {σM : TKKSymmetry R G M}
    (F : EquivariantTKKRealization R G S M σS σM) (x y : S.lie.L) :
    F.map ⁅x, y⁆ = ⁅F.map x, F.map y⁆ :=
  F.map_bracket x y

theorem EquivariantTKKRealization.map_bijective
    {R G : Type*} [CommRing R] [Monoid G]
    {S M : FiveGradedTKKSpec R} {σS : TKKSymmetry R G S} {σM : TKKSymmetry R G M}
    (F : EquivariantTKKRealization R G S M σS σM) :
    Function.Bijective F.map := F.map.bijective

def EquivariantTKKRealization.trans
    {R G : Type*} [CommRing R] [Monoid G]
    {S M N : FiveGradedTKKSpec R}
    {σS : TKKSymmetry R G S} {σM : TKKSymmetry R G M} {σN : TKKSymmetry R G N}
    (F : EquivariantTKKRealization R G S M σS σM)
    (H : EquivariantTKKRealization R G M N σM σN) :
    EquivariantTKKRealization R G S N σS σN where
  map := F.map.trans H.map
  map_bracket x y := by
    change H.map (F.map ⁅x, y⁆) = ⁅H.map (F.map x), H.map (F.map y)⁆
    rw [F.map_bracket, H.map_bracket]
  map_grade i x := by
    change x ∈ S.grade i ↔ H.map (F.map x) ∈ N.grade i
    rw [F.map_grade i x, H.map_grade i (F.map x)]
  map_inversion x := by
    change H.map (F.map (S.inversion x)) = N.inversion (H.map (F.map x))
    rw [F.map_inversion, H.map_inversion]
  metric_map := F.metric_map.trans H.metric_map
  map_metric x y := by
    change N.metric.beta (H.metric_map (F.metric_map x))
      (H.metric_map (F.metric_map y)) = _
    rw [H.map_metric, F.map_metric]
  equivariant g x := by
    change H.map (F.map (σS.act g x)) = σN.act g (H.map (F.map x))
    rw [F.equivariant, H.equivariant]

theorem EquivariantTKKRealization.trans_bijective
    {R G : Type*} [CommRing R] [Monoid G]
    {S M N : FiveGradedTKKSpec R}
    {σS : TKKSymmetry R G S} {σM : TKKSymmetry R G M} {σN : TKKSymmetry R G N}
    (F : EquivariantTKKRealization R G S M σS σM)
    (H : EquivariantTKKRealization R G M N σM σN) :
    Function.Bijective (F.trans H).map := (F.trans H).map_bijective

end InfoGeometry.Algebra

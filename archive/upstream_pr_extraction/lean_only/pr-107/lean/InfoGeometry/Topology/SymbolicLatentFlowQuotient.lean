import Mathlib
import InfoGeometry.Topology.SymbolicLatentModularFlow

namespace InfoGeometry.Topology

/-!
A topological quotient presentation carrying a descended modular flow.
The quotient universal property is represented explicitly by surjectivity of
the projection and a descent equation.  This keeps the layer independent of a
particular quotient implementation while retaining the exact flow laws.
-/

structure SymbolicLatentFlowQuotient
    (X Q : Type*) [TopologicalSpace X] [TopologicalSpace Q]
    (Φ : SymbolicLatentModularFlow X) where
  quotientMap : X → Q
  quotientMap_surjective : Function.Surjective quotientMap
  act : ℝ → Q → Q
  continuous_act : Continuous (fun p : ℝ × Q => act p.1 p.2)
  descends : ∀ (t : ℝ) (x : X),
    act t (quotientMap x) = quotientMap (Φ.act t x)

theorem SymbolicLatentFlowQuotient.act_zero
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) :
    K.act 0 q = q := by
  rcases K.quotientMap_surjective q with ⟨x, rfl⟩
  rw [K.descends, Φ.zero_apply]

theorem SymbolicLatentFlowQuotient.act_add
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ)
    (s t : ℝ) (q : Q) :
    K.act (s + t) q = K.act s (K.act t q) := by
  rcases K.quotientMap_surjective q with ⟨x, rfl⟩
  calc
    K.act (s + t) (K.quotientMap x) =
        K.quotientMap (Φ.act (s + t) x) := K.descends (s + t) x
    _ = K.quotientMap (Φ.act s (Φ.act t x)) :=
      congrArg K.quotientMap (Φ.add_apply s t x)
    _ = K.act s (K.quotientMap (Φ.act t x)) :=
      (K.descends s (Φ.act t x)).symm
    _ = K.act s (K.act t (K.quotientMap x)) :=
      congrArg (K.act s) (K.descends t x).symm

theorem SymbolicLatentFlowQuotient.act_neg_left
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ)
    (t : ℝ) (q : Q) :
    K.act (-t) (K.act t q) = q := by
  calc
    K.act (-t) (K.act t q) = K.act 0 q := by
      simpa using (K.act_add (-t) t q).symm
    _ = q := K.act_zero q

theorem SymbolicLatentFlowQuotient.act_neg_right
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ)
    (t : ℝ) (q : Q) :
    K.act t (K.act (-t) q) = q := by
  calc
    K.act t (K.act (-t) q) = K.act 0 q := by
      simpa using (K.act_add t (-t) q).symm
    _ = q := K.act_zero q

theorem SymbolicLatentFlowQuotient.descends_representative
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ)
    (t : ℝ) (x : X) :
    K.act t (K.quotientMap x) = K.quotientMap (Φ.act t x) :=
  K.descends t x

theorem SymbolicLatentFlowQuotient.flow_respects_quotient
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ)
    (t : ℝ) {x y : X}
    (hxy : K.quotientMap x = K.quotientMap y) :
    K.quotientMap (Φ.act t x) = K.quotientMap (Φ.act t y) := by
  rw [← K.descends t x, ← K.descends t y, hxy]

theorem SymbolicLatentFlowQuotient.act_unique
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ)
    {a b : ℝ → Q → Q}
    (ha : ∀ (t : ℝ) (x : X),
      a t (K.quotientMap x) = K.quotientMap (Φ.act t x))
    (hb : ∀ (t : ℝ) (x : X),
      b t (K.quotientMap x) = K.quotientMap (Φ.act t x)) :
    ∀ (t : ℝ) (q : Q), a t q = b t q := by
  intro t q
  rcases K.quotientMap_surjective q with ⟨x, rfl⟩
  rw [ha t x, hb t x]

end InfoGeometry.Topology

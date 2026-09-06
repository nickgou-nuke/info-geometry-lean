import Mathlib
import InfoGeometry.Canonical.RealProjectionRank

/-!
# Exact rank doubling for a duplicated projection

The product model `p × p` is the linear-algebraic normal form of tensoring a
projection with a two-dimensional identity factor.  The range equivalence is
proved explicitly here; transporting it to the native matrix Kronecker map is
the next separate theorem.
-/

namespace InfoGeometry.Canonical

def doubleProjection {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (p : V →ₗ[K] V) :
    (V × V) →ₗ[K] (V × V) where
  toFun x := (p x.1, p x.2)
  map_add' x y := by
    apply Prod.ext <;> simp
  map_smul' c x := by
    apply Prod.ext <;> simp

def doubleProjectionRangeMap {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (p : V →ₗ[K] V) :
    LinearMap.range (doubleProjection p) →ₗ[K]
      (LinearMap.range p × LinearMap.range p) where
  toFun x :=
    ⟨⟨x.1.1, by
        rcases x.2 with ⟨y, hy⟩
        refine ⟨y.1, ?_⟩
        exact congrArg Prod.fst hy⟩,
      ⟨x.1.2, by
        rcases x.2 with ⟨y, hy⟩
        refine ⟨y.2, ?_⟩
        exact congrArg Prod.snd hy⟩⟩
  map_add' x y := by
    apply Prod.ext <;> rfl
  map_smul' c x := by
    apply Prod.ext <;> rfl

theorem doubleProjectionRangeMap_injective {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (p : V →ₗ[K] V) :
    Function.Injective (doubleProjectionRangeMap p) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z => (z : LinearMap.range p × LinearMap.range p).1.1) h
  · exact congrArg (fun z => (z : LinearMap.range p × LinearMap.range p).2.1) h

theorem doubleProjectionRangeMap_surjective {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (p : V →ₗ[K] V) :
    Function.Surjective (doubleProjectionRangeMap p) := by
  intro uv
  rcases uv with ⟨u, v⟩
  rcases u.property with ⟨a, ha⟩
  rcases v.property with ⟨b, hb⟩
  let x : LinearMap.range (doubleProjection p) :=
    ⟨(u.1, v.1), by
      refine ⟨(a, b), ?_⟩
      apply Prod.ext
      · exact ha
      · exact hb⟩
  refine ⟨x, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    exact rfl
  · apply Subtype.ext
    exact rfl

noncomputable def doubleProjectionRangeEquiv {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (p : V →ₗ[K] V) :
    LinearMap.range (doubleProjection p) ≃ₗ[K]
      (LinearMap.range p × LinearMap.range p) :=
  LinearEquiv.ofBijective (doubleProjectionRangeMap p)
    ⟨doubleProjectionRangeMap_injective p, doubleProjectionRangeMap_surjective p⟩

theorem projectionRank_double {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (p : V →ₗ[K] V) :
    projectionRank (doubleProjection p) = 2 * projectionRank p := by
  rw [projectionRank_eq_finrank_range]
  rw [(doubleProjectionRangeEquiv p).finrank_eq]
  rw [Module.finrank_prod]
  rw [projectionRank_eq_finrank_range]
  rw [two_mul]

end InfoGeometry.Canonical

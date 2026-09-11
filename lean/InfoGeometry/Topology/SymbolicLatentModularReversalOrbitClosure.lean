import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Orbit-closure transport under modular time reversal

The modular reversal owner already proves that the involution sends each orbit
into the reversed orbit.  This owner upgrades that statement to a genuine
homeomorphism between the corresponding orbit closures.  No compactness or
operator-algebraic interpretation is used here.
-/

namespace InfoGeometry.Topology

noncomputable section

private theorem reversal_mem_reversed_orbitClosure
    {X : Type*} [TopologicalSpace X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) (y : X)
    (hy : y ∈ Φ.orbitClosure x) :
    R.involution y ∈ Φ.orbitClosure (R.involution x) := by
  have hclosed :
      IsClosed (R.involution ⁻¹' Φ.orbitClosure (R.involution x)) :=
    isClosed_closure.preimage R.involution.continuous
  have horbit :
      Φ.orbit x ⊆ R.involution ⁻¹' Φ.orbitClosure (R.involution x) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    exact Φ.orbit_subset_orbitClosure (R.involution x)
      (R.orbit_image x ⟨Φ.act t x, ⟨t, rfl⟩, rfl⟩)
  exact (closure_minimal horbit hclosed) hy

theorem SymbolicLatentModularReversal.fixedPoint_orbitClosure_invariant
    {X : Type*} [TopologicalSpace X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X)
    (hx : x ∈ symbolicLatentInvolutionFixedPointSet R.involution) :
    R.involution '' Φ.orbitClosure x = Φ.orbitClosure x := by
  have hx' : R.involution x = x := hx
  apply Set.Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    simpa [hx'] using
      (reversal_mem_reversed_orbitClosure R x z hz)
  · intro y hy
    have hy0 : y ∈ Φ.orbitClosure (R.involution x) := by
      simpa [hx'] using hy
    have hy' := reversal_mem_reversed_orbitClosure R (R.involution x) y hy0
    refine ⟨R.involution y, ?_, R.involution.involutive y⟩
    simpa [R.involution.involutive x, hx'] using hy'

def SymbolicLatentModularReversal.orbitClosureMap
    {X : Type} [TopologicalSpace X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) :
    SymbolicLatentModularOrbitClosure Φ x →
      SymbolicLatentModularOrbitClosure Φ (R.involution x) :=
  fun y => ⟨R.involution y.1,
    reversal_mem_reversed_orbitClosure R x y.1 y.2⟩

theorem SymbolicLatentModularReversal.orbitClosureMap_continuous
    {X : Type} [TopologicalSpace X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) :
    Continuous (R.orbitClosureMap x) := by
  exact (R.involution.continuous.comp continuous_subtype_val).subtype_mk
    (fun y => reversal_mem_reversed_orbitClosure R x y.1 y.2)

noncomputable def SymbolicLatentModularReversal.orbitClosureHomeomorph
    {X : Type} [TopologicalSpace X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) :
    SymbolicLatentModularOrbitClosure Φ x ≃ₜ
      SymbolicLatentModularOrbitClosure Φ (R.involution x) where
  toFun := R.orbitClosureMap x
  invFun := fun y =>
    ⟨R.involution y.1, by
      have hy := reversal_mem_reversed_orbitClosure R
        (R.involution x) y.1 y.2
      simpa [R.involution.involutive x] using hy⟩
  left_inv := by
    intro y
    apply Subtype.ext
    exact R.involution.involutive y.1
  right_inv := by
    intro y
    apply Subtype.ext
    exact R.involution.involutive y.1
  continuous_toFun := R.orbitClosureMap_continuous x
  continuous_invFun := by
    exact (R.involution.continuous.comp continuous_subtype_val).subtype_mk
      (fun y => by
        have hy := reversal_mem_reversed_orbitClosure R
          (R.involution x) y.1 y.2
        simpa [R.involution.involutive x] using hy)

@[simp] theorem SymbolicLatentModularReversal.orbitClosureHomeomorph_apply
    {X : Type} [TopologicalSpace X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X)
    (y : SymbolicLatentModularOrbitClosure Φ x) :
    R.orbitClosureHomeomorph x y = R.orbitClosureMap x y :=
  rfl

end
end InfoGeometry.Topology

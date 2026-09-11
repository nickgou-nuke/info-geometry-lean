import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentQuotientOrbitClosureFlowHomeomorph
import InfoGeometry.Topology.SymbolicLatentQuotientFlowTopCat

/-!
# `TopCat` packaging for quotient orbit-closure flow

The restricted quotient flow is already a native homeomorphism.  This owner
exposes its continuous map in `TopCat` and certifies it as an isomorphism.
-/

namespace InfoGeometry.Topology

open CategoryTheory

def SymbolicLatentFlowQuotient.orbitClosureFlowTopCatHom
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) (t : ℝ) :
    TopCat.of (SymbolicLatentOrbitClosure K q) ⟶
      TopCat.of (SymbolicLatentOrbitClosure K (K.act t q)) :=
  TopCat.ofHom
    { toFun := fun y =>
        ⟨K.act t y.1, by
          rw [← K.actHomeomorph_image_orbitClosure t q]
          exact ⟨y.1, y.2, rfl⟩⟩
      continuous_toFun :=
        ((K.actHomeomorph t).continuous_toFun.comp continuous_subtype_val).subtype_mk _ }

@[simp] theorem SymbolicLatentFlowQuotient.orbitClosureFlowTopCatHom_apply
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) (t : ℝ)
    (y : SymbolicLatentOrbitClosure K q) :
    K.orbitClosureFlowTopCatHom q t y =
      K.orbitClosureFlowHomeomorph q t y :=
  rfl

theorem SymbolicLatentFlowQuotient.orbitClosureFlowTopCatHom_isIso
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) (t : ℝ) :
    IsIso (K.orbitClosureFlowTopCatHom q t) := by
  exact (TopCat.isIso_iff_isHomeomorph
    (K.orbitClosureFlowTopCatHom q t)).2
      (K.orbitClosureFlowHomeomorph q t).isHomeomorph

theorem SymbolicLatentFlowQuotient.orbitClosureFlowTopCatHom_natural
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) (t : ℝ) :
    K.orbitClosureFlowTopCatHom q t ≫
        symbolicLatentOrbitClosureInclusion K (K.act t q) =
      symbolicLatentOrbitClosureInclusion K q ≫ K.actTopCatHom t := by
  ext y
  rfl

theorem SymbolicLatentFlowQuotient.orbitClosureFlowTopCatHom_comp_apply
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) (s t : ℝ)
    (y : SymbolicLatentOrbitClosure K q) :
    ((K.orbitClosureFlowTopCatHom q s ≫
        K.orbitClosureFlowTopCatHom (K.act s q) t) y).1 =
      (K.orbitClosureFlowTopCatHom q (t + s) y).1 := by
  change K.act t (K.act s y.1) = K.act (t + s) y.1
  simpa [add_comm] using (K.act_add t s y.1).symm

end InfoGeometry.Topology

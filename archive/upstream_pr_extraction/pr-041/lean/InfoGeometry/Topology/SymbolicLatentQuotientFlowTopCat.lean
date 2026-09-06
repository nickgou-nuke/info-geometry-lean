import Mathlib
import InfoGeometry.Topology.SymbolicLatentQuotientFlowHomeomorph

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# The quotient modular flow in `TopCat`

The previous owner constructs a homeomorphism for each time.  This file
packages those homeomorphisms as morphisms of `TopCat` and records the
identity and composition laws pointwise.
-/

def SymbolicLatentFlowQuotient.actTopCatHom
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (t : ℝ) :
    TopCat.of Q ⟶ TopCat.of Q :=
  TopCat.ofHom
    { toFun := K.actHomeomorph t
      continuous_toFun := (K.actHomeomorph t).continuous }

@[simp] theorem SymbolicLatentFlowQuotient.actTopCatHom_apply
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (t : ℝ) (q : Q) :
    K.actTopCatHom t q = K.act t q := rfl

theorem SymbolicLatentFlowQuotient.actTopCatHom_zero
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) :
    (SymbolicLatentFlowQuotient.actTopCatHom K 0) = 𝟙 (TopCat.of Q) := by
  ext q
  change K.actHomeomorph 0 q = q
  exact K.actHomeomorph_zero_apply q

theorem SymbolicLatentFlowQuotient.actTopCatHom_add
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ)
    (s t : ℝ) :
    (SymbolicLatentFlowQuotient.actTopCatHom K (s + t)) =
      (SymbolicLatentFlowQuotient.actTopCatHom K s) ≫
        (SymbolicLatentFlowQuotient.actTopCatHom K t) := by
  ext q
  simpa [SymbolicLatentFlowQuotient.actTopCatHom,
    CategoryTheory.comp_apply, add_comm] using
    K.actHomeomorph_add_apply t s q

/-!
`≫` applies the left morphism first.  Since the time parameters form an
abelian group, the action law also gives the composition in this categorical
orientation.
-/
theorem SymbolicLatentFlowQuotient.actTopCatHom_comp
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ)
    (s t : ℝ) :
    (SymbolicLatentFlowQuotient.actTopCatHom K (s + t)) =
      (SymbolicLatentFlowQuotient.actTopCatHom K t) ≫
        (SymbolicLatentFlowQuotient.actTopCatHom K s) := by
  ext q
  simpa [SymbolicLatentFlowQuotient.actTopCatHom,
    CategoryTheory.comp_apply, add_comm] using
    K.actHomeomorph_add_apply s t q

theorem SymbolicLatentFlowQuotient.actTopCatHom_isIso
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (t : ℝ) :
    IsIso (SymbolicLatentFlowQuotient.actTopCatHom K t) := by
  refine IsIso.mk ⟨TopCat.ofHom
    { toFun := (K.actHomeomorph t).symm
      continuous_toFun := (K.actHomeomorph t).symm.continuous_toFun }, ?_, ?_⟩
  · apply TopCat.hom_ext
    ext q
    simpa [SymbolicLatentFlowQuotient.actTopCatHom,
      TopCat.comp_app, TopCat.id_app, TopCat.ofHom]
      using (K.actHomeomorph t).symm_apply_apply q
  · apply TopCat.hom_ext
    ext q
    simpa [SymbolicLatentFlowQuotient.actTopCatHom,
      TopCat.comp_app, TopCat.id_app, TopCat.ofHom]
      using (K.actHomeomorph t).apply_symm_apply q

end InfoGeometry.Topology

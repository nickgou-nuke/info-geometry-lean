import InfoGeometry.Topology.SymbolicLatentModularReversalOrbitClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentInvolutionTopCat
import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureCompHaus
import Mathlib.Topology.Category.CompHaus.Basic

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` restriction of modular reversal to a fixed-point orbit closure

For a reversal-fixed base point, the preceding owner proves that its orbit
closure is invariant.  We package the restricted continuous map and its
ambient commutative square in `TopCat`.
-/

abbrev SymbolicLatentModularReversalOrbitClosureObject
    {X : Type*} [TopologicalSpace X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) :=
  TopCat.of (closure (Φ.orbit x))

noncomputable def SymbolicLatentModularReversal.fixedPointOrbitClosureTopCatHom
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X)
    (hx : x ∈ symbolicLatentInvolutionFixedPointSet R.involution) :
    SymbolicLatentModularReversalOrbitClosureObject R x ⟶
      SymbolicLatentModularReversalOrbitClosureObject R x := by
  let hInv :=
    SymbolicLatentModularReversal.fixedPoint_orbitClosure_invariant R x hx
  have hInv' : R.involution '' closure (Φ.orbit x) = closure (Φ.orbit x) := hInv
  have hmem : ∀ z : closure (Φ.orbit x),
      R.involution z.1 ∈ closure (Φ.orbit x) := by
    intro z
    change R.involution z.1 ∈ closure (Φ.orbit x)
    have hz : R.involution z.1 ∈
        R.involution '' closure (Φ.orbit x) :=
      ⟨z.1, z.2, rfl⟩
    rw [hInv'] at hz
    exact hz
  let f : closure (Φ.orbit x) → closure (Φ.orbit x) := fun z =>
    ⟨R.involution z.1, hmem z⟩
  exact TopCat.ofHom
    { toFun := f
      continuous_toFun :=
        (R.involution.continuous.comp continuous_subtype_val).subtype_mk hmem }

noncomputable def SymbolicLatentModularReversal.fixedPointOrbitClosureInclusionTopCatHom
    {X : Type*} [TopologicalSpace X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) :
    SymbolicLatentModularReversalOrbitClosureObject R x ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := fun z => z.1
      continuous_toFun := continuous_subtype_val }

noncomputable def SymbolicLatentModularReversal.involutionTopCatHom
    {X : Type*} [TopologicalSpace X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) :
    TopCat.of X ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := R.involution
      continuous_toFun := R.involution.continuous }

noncomputable def SymbolicLatentModularReversal.fixedPointOrbitClosureHomeomorph
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X)
    (hx : x ∈ symbolicLatentInvolutionFixedPointSet R.involution) :
    closure (Φ.orbit x) ≃ₜ closure (Φ.orbit x) := by
  let hInv :=
    SymbolicLatentModularReversal.fixedPoint_orbitClosure_invariant R x hx
  have hInv' : R.involution '' closure (Φ.orbit x) = closure (Φ.orbit x) := hInv
  let hmem : ∀ z : closure (Φ.orbit x),
      R.involution z.1 ∈ closure (Φ.orbit x) := by
    intro z
    change R.involution z.1 ∈ closure (Φ.orbit x)
    have hz : R.involution z.1 ∈
        R.involution '' closure (Φ.orbit x) :=
      ⟨z.1, z.2, rfl⟩
    rw [hInv'] at hz
    exact hz
  exact
    { toFun := fun z => ⟨R.involution z.1, hmem z⟩
      invFun := fun z => ⟨R.involution z.1, hmem z⟩
      left_inv := by
        intro z
        apply Subtype.ext
        exact R.involution.involutive z.1
      right_inv := by
        intro z
        apply Subtype.ext
        exact R.involution.involutive z.1
      continuous_toFun :=
        (R.involution.continuous.comp continuous_subtype_val).subtype_mk hmem
      continuous_invFun :=
        (R.involution.continuous.comp continuous_subtype_val).subtype_mk hmem }

noncomputable def SymbolicLatentModularReversal.fixedPointOrbitClosureCompHausIso
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X)
    (hx : x ∈ symbolicLatentInvolutionFixedPointSet R.involution) :
    symbolicLatentModularOrbitClosureCompHaus Φ x ≅
      symbolicLatentModularOrbitClosureCompHaus Φ x := by
  letI : CompactSpace (SymbolicLatentModularOrbitClosure Φ x) :=
    isCompact_iff_compactSpace.mp (Φ.isCompact_orbitClosure x)
  dsimp [symbolicLatentModularOrbitClosureCompHaus]
  change CompHaus.of (SymbolicLatentModularOrbitClosure Φ x) ≅
    CompHaus.of (SymbolicLatentModularOrbitClosure Φ x)
  let e := R.fixedPointOrbitClosureHomeomorph x hx
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := e
          continuous_toFun := e.continuous_toFun }⟩
      inv := ⟨TopCat.ofHom
        { toFun := e.symm
          continuous_toFun := e.symm.continuous_toFun }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e.symm (e y) = y
        exact e.symm_apply_apply y
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e (e.symm y) = y
        exact e.apply_symm_apply y }

theorem SymbolicLatentModularReversal.fixedPointOrbitClosureTopCatHom_natural
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X)
    (hx : x ∈ symbolicLatentInvolutionFixedPointSet R.involution) :
    R.fixedPointOrbitClosureInclusionTopCatHom x ≫
        R.involutionTopCatHom =
      R.fixedPointOrbitClosureTopCatHom x hx ≫
        R.fixedPointOrbitClosureInclusionTopCatHom x := by
  ext z
  simp [SymbolicLatentModularReversal.fixedPointOrbitClosureTopCatHom,
    SymbolicLatentModularReversal.fixedPointOrbitClosureInclusionTopCatHom,
    SymbolicLatentModularReversal.involutionTopCatHom]

end InfoGeometry.Topology

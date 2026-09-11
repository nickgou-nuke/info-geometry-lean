import InfoGeometry.Topology.SymbolicLatentModularReversalOrbitClosureTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentInvolutionFixedPointsCompHaus
import InfoGeometry.Topology.SymbolicLatentReversalOrbitTopCat
import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureFlowCompHaus

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Fixed-point `CompHaus` subobject inside a reversal-invariant orbit closure

For a reversal-fixed base point, the restricted reversal is a continuous
involution on the closed orbit subtype.  The generic fixed-point `CompHaus`
owner can therefore be applied without introducing a second compactness
construction.
-/

noncomputable def SymbolicLatentModularReversal.orbitClosureInvolution
    {X : Type} [TopologicalSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X)
    (hx : x ∈ symbolicLatentInvolutionFixedPointSet R.involution) :
    SymbolicLatentInvolution (closure (Φ.orbit x)) := by
  let hInv := R.fixedPoint_orbitClosure_invariant x hx
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
      continuous_toFun :=
        (R.involution.continuous.comp continuous_subtype_val).subtype_mk hmem
      involutive := by
        intro z
        apply Subtype.ext
        exact R.involution.involutive z.1 }

noncomputable def SymbolicLatentModularReversal.orbitClosureFixedPointCompHaus
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X)
    (hx : x ∈ symbolicLatentInvolutionFixedPointSet R.involution) : CompHaus := by
  letI : CompactSpace (closure (Φ.orbit x)) :=
    isCompact_iff_compactSpace.mp (Φ.isCompact_orbitClosure x)
  exact symbolicLatentInvolutionFixedPointCompHaus
    (R.orbitClosureInvolution x hx)

noncomputable def SymbolicLatentModularReversal.orbitClosureFixedPointInclusion
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X)
    (hx : x ∈ symbolicLatentInvolutionFixedPointSet R.involution) :
    compHausToTop.obj (R.orbitClosureFixedPointCompHaus x hx) ⟶
      TopCat.of (closure (Φ.orbit x)) := by
  letI : CompactSpace (closure (Φ.orbit x)) :=
    isCompact_iff_compactSpace.mp (Φ.isCompact_orbitClosure x)
  change TopCat.of
      (symbolicLatentInvolutionFixedPointSet
        (R.orbitClosureInvolution x hx)) ⟶
      TopCat.of (closure (Φ.orbit x))
  exact (R.orbitClosureInvolution x hx).fixedPointInclusion

theorem SymbolicLatentModularReversal.orbitClosureFixedPointInclusion_invariant
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X)
    (hx : x ∈ symbolicLatentInvolutionFixedPointSet R.involution) :
    R.orbitClosureFixedPointInclusion x hx ≫
        (R.orbitClosureInvolution x hx).toTopCatHom =
      R.orbitClosureFixedPointInclusion x hx := by
  exact (R.orbitClosureInvolution x hx).fixedPointInclusion_invariant

noncomputable def SymbolicLatentModularReversal.orbitClosureFixedPointCompHausHom
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X)
    (hx : x ∈ symbolicLatentInvolutionFixedPointSet R.involution) :
    R.orbitClosureFixedPointCompHaus x hx ⟶
      symbolicLatentModularOrbitClosureCompHaus Φ x := by
  letI : CompactSpace (closure (Φ.orbit x)) :=
    isCompact_iff_compactSpace.mp (Φ.isCompact_orbitClosure x)
  let J := R.orbitClosureInvolution x hx
  let hclosed : IsClosed (symbolicLatentInvolutionFixedPointSet J) :=
    isClosed_symbolicLatentInvolutionFixedPointSet J
  let hcompact : IsCompact (symbolicLatentInvolutionFixedPointSet J) :=
    IsCompact.of_isClosed_subset isCompact_univ hclosed (Set.subset_univ _)
  letI : CompactSpace (symbolicLatentInvolutionFixedPointSet J) :=
    isCompact_iff_compactSpace.mp hcompact
  dsimp [SymbolicLatentModularReversal.orbitClosureFixedPointCompHaus,
    symbolicLatentModularOrbitClosureCompHaus]
  change CompHaus.of
      (symbolicLatentInvolutionFixedPointSet
        (R.orbitClosureInvolution x hx)) ⟶
    CompHaus.of (closure (Φ.orbit x))
  exact ⟨R.orbitClosureFixedPointInclusion x hx⟩

theorem SymbolicLatentModularReversal.orbitClosureFixedPointCompHausHom_forget
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X)
    (hx : x ∈ symbolicLatentInvolutionFixedPointSet R.involution) :
    compHausToTop.map (R.orbitClosureFixedPointCompHausHom x hx) =
      R.orbitClosureFixedPointInclusion x hx := by
  unfold SymbolicLatentModularReversal.orbitClosureFixedPointCompHausHom
  rfl

noncomputable def SymbolicLatentModularReversal.orbitClosureFixedPointToAmbientCompHausHom
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X)
    (hx : x ∈ symbolicLatentInvolutionFixedPointSet R.involution) :
    R.orbitClosureFixedPointCompHaus x hx ⟶ CompHaus.of X :=
  R.orbitClosureFixedPointCompHausHom x hx ≫
    symbolicLatentModularOrbitClosureCompHausHom Φ x

theorem SymbolicLatentModularReversal.orbitClosureFixedPointToAmbientCompHausHom_forget
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X)
    (hx : x ∈ symbolicLatentInvolutionFixedPointSet R.involution) :
    compHausToTop.map
        (R.orbitClosureFixedPointToAmbientCompHausHom x hx) =
      R.orbitClosureFixedPointInclusion x hx ≫
        Φ.orbitClosureInclusionTopCatHom x := by
  rw [SymbolicLatentModularReversal.orbitClosureFixedPointToAmbientCompHausHom,
    Functor.map_comp,
    R.orbitClosureFixedPointCompHausHom_forget,
    symbolicLatentModularOrbitClosureCompHausHom_forget]

noncomputable def SymbolicLatentModularReversal.orbitClosureReversalCompHausHom
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) :
    symbolicLatentModularOrbitClosureCompHaus Φ x ⟶
      symbolicLatentModularOrbitClosureCompHaus Φ (R.involution x) := by
  letI : CompactSpace (closure (Φ.orbit x)) :=
    isCompact_iff_compactSpace.mp (Φ.isCompact_orbitClosure x)
  letI : CompactSpace (closure (Φ.orbit (R.involution x))) :=
    isCompact_iff_compactSpace.mp
      (Φ.isCompact_orbitClosure (R.involution x))
  dsimp [symbolicLatentModularOrbitClosureCompHaus]
  change CompHaus.of (closure (Φ.orbit x)) ⟶
    CompHaus.of (closure (Φ.orbit (R.involution x)))
  exact ⟨R.orbitClosureTopCatHom x⟩

theorem SymbolicLatentModularReversal.orbitClosureReversalCompHausHom_forget
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) :
    compHausToTop.map (R.orbitClosureReversalCompHausHom x) =
      R.orbitClosureTopCatHom x := by
  rfl

theorem SymbolicLatentModularReversal.orbitClosureReversal_flow_readout
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) (s : ℝ)
    (y : symbolicLatentModularOrbitClosureCompHaus Φ x) :
    ((R.orbitClosureReversalCompHausHom (Φ.act s x))
        ((Φ.orbitClosureFlowCompHausHom x s) y)).1 =
      ((Φ.orbitClosureFlowCompHausHom (R.involution x) (-s))
        ((R.orbitClosureReversalCompHausHom x) y)).1 := by
  change R.involution (Φ.act s y.1) =
    Φ.act (-s) (R.involution y.1)
  exact R.reverses_flow s y.1

noncomputable def SymbolicLatentModularReversal.orbitClosureFlowReversalTransport
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) (s : ℝ) :
    symbolicLatentModularOrbitClosureCompHaus Φ (R.involution (Φ.act s x)) ≅
      symbolicLatentModularOrbitClosureCompHaus Φ
        (Φ.act (-s) (R.involution x)) :=
  CategoryTheory.eqToIso
    (congrArg (fun z : X => symbolicLatentModularOrbitClosureCompHaus Φ z)
      (R.reverses_flow s x))

end InfoGeometry.Topology

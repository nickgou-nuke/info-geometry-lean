import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientCompHaus
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientReversalTopCatNaturality
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotientCompHaus
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# `CompHaus` endpoint and reversal bridges for based-loop fibres

This owner packages the existing `TopCat` endpoint and reversal laws.  The
compact/Hausdorff hypotheses are explicit for the fibre and base space; no
claim is made that a general path quotient is automatically compact.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable def symbolicLatentBasedLoopHomotopyQuotientEndpointCompHausHom
    {X : Type} [TopologicalSpace X]
    [CompactSpace X] [T2Space X]
    {x : X}
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient x)] :
    CompHaus.of (SymbolicLatentBasedLoopHomotopyQuotient x) ⟶
      CompHaus.of (X × X) := by
  exact ⟨symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom x⟩

theorem symbolicLatentBasedLoopHomotopyQuotientEndpointCompHausHom_forget
    {X : Type} [TopologicalSpace X]
    [CompactSpace X] [T2Space X]
    {x : X}
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient x)] :
    compHausToTop.map
        (symbolicLatentBasedLoopHomotopyQuotientEndpointCompHausHom (x := x)) =
      symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom x := by
  rfl

noncomputable def symbolicLatentBasedLoopHomotopyQuotientReversalCompHausIso
    {X : Type} [TopologicalSpace X] {x : X}
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient x)] :
    CompHaus.of (SymbolicLatentBasedLoopHomotopyQuotient x) ≅
      CompHaus.of (SymbolicLatentBasedLoopHomotopyQuotient x) := by
  let e := symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x
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

theorem symbolicLatentBasedLoopHomotopyQuotientReversalCompHausIso_involutive
    {X : Type} [TopologicalSpace X] {x : X}
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient x)] :
    (symbolicLatentBasedLoopHomotopyQuotientReversalCompHausIso (x := x)).hom ≫
        (symbolicLatentBasedLoopHomotopyQuotientReversalCompHausIso (x := x)).hom =
      𝟙 (CompHaus.of (SymbolicLatentBasedLoopHomotopyQuotient x)) := by
  have hFF : (compHausToTop).FullyFaithful := by
    simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
  apply hFF.map_injective
  simpa [Functor.map_comp,
    symbolicLatentBasedLoopHomotopyQuotientReversalCompHausIso] using
    (symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom_involutive
      (X := X) x)

theorem symbolicLatentBasedLoopHomotopyQuotientReversalCompHausIso_endpoint
    {X : Type} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] {x : X}
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient x)] :
    (symbolicLatentBasedLoopHomotopyQuotientReversalCompHausIso (x := x)).hom ≫
        symbolicLatentBasedLoopHomotopyQuotientEndpointCompHausHom (x := x) =
      symbolicLatentBasedLoopHomotopyQuotientEndpointCompHausHom (x := x) := by
  have hFF : (compHausToTop).FullyFaithful := by
    simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
  apply hFF.map_injective
  simpa [Functor.map_comp,
    symbolicLatentBasedLoopHomotopyQuotientReversalCompHausIso,
    symbolicLatentBasedLoopHomotopyQuotientEndpointCompHausHom] using
    (symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom_endpoint
      (X := X) x)

theorem symbolicLatentBasedLoopHomotopyQuotientEndpointCompHausHom_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    {x : X} {y : Y} (f : C(X, Y)) (hxy : f x = y)
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient y)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient y)] :
    symbolicLatentBasedLoopHomotopyQuotientCompHausHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientEndpointCompHausHom (x := y) =
      symbolicLatentBasedLoopHomotopyQuotientEndpointCompHausHom (x := x) ≫
        symbolicLatentPathHomotopyEndpointMapCompHausHom f := by
  have hFF : (compHausToTop).FullyFaithful := by
    simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
  apply hFF.map_injective
  simpa [Functor.map_comp,
    symbolicLatentBasedLoopHomotopyQuotientCompHausHom,
    symbolicLatentBasedLoopHomotopyQuotientEndpointCompHausHom,
    symbolicLatentPathHomotopyEndpointMapCompHausHom] using
    (symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom_natural
      f hxy)

theorem symbolicLatentBasedLoopHomotopyQuotientReversalCompHausIso_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (hxy : f x = y)
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient y)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient y)] :
    symbolicLatentBasedLoopHomotopyQuotientCompHausHom f hxy ≫
        (symbolicLatentBasedLoopHomotopyQuotientReversalCompHausIso
          (x := y)).hom =
      (symbolicLatentBasedLoopHomotopyQuotientReversalCompHausIso
          (x := x)).hom ≫
        symbolicLatentBasedLoopHomotopyQuotientCompHausHom f hxy := by
  have hFF : (compHausToTop).FullyFaithful := by
    simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
  apply hFF.map_injective
  simpa [Functor.map_comp,
    symbolicLatentBasedLoopHomotopyQuotientCompHausHom,
    symbolicLatentBasedLoopHomotopyQuotientReversalCompHausIso] using
    (symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom_natural
      f hxy)

end InfoGeometry.Topology

end

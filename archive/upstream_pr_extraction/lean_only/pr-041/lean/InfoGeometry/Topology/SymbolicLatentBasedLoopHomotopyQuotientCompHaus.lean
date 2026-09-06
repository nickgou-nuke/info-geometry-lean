import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Conditional `CompHaus` transport for based-loop homotopy quotients

The based-loop endpoint fibres are not automatically compact Hausdorff.  This
owner keeps that analytic issue explicit and transports only the already
proved `TopCat` functoriality to `CompHaus` under compact/Hausdorff instances
for the relevant fibres.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable def symbolicLatentBasedLoopHomotopyQuotientCompHausHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y}
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient y)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient y)]
    (f : C(X, Y)) (hxy : f x = y) :
    CompHaus.of (SymbolicLatentBasedLoopHomotopyQuotient x) ⟶
      CompHaus.of (SymbolicLatentBasedLoopHomotopyQuotient y) := by
  exact ⟨symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy⟩

theorem symbolicLatentBasedLoopHomotopyQuotientCompHausHom_forget
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y}
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient y)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient y)]
    (f : C(X, Y)) (hxy : f x = y) :
    compHausToTop.map
        (symbolicLatentBasedLoopHomotopyQuotientCompHausHom f hxy) =
      symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy := by
  rfl

@[simp] theorem symbolicLatentBasedLoopHomotopyQuotientCompHausHom_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y}
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient y)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient y)]
    (f : C(X, Y)) (hxy : f x = y)
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    symbolicLatentBasedLoopHomotopyQuotientCompHausHom f hxy q =
      mapSymbolicLatentBasedLoopHomotopyQuotient f hxy q := by
  rfl

theorem symbolicLatentBasedLoopHomotopyQuotientCompHausHom_id
    {X : Type} [TopologicalSpace X] {x : X}
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient x)] :
    symbolicLatentBasedLoopHomotopyQuotientCompHausHom
        (ContinuousMap.id X) (x := x) (y := x) rfl =
      𝟙 (CompHaus.of (SymbolicLatentBasedLoopHomotopyQuotient x)) := by
  have hFF : (compHausToTop).FullyFaithful := by
    simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
  apply hFF.map_injective
  simpa [Functor.map_comp,
    symbolicLatentBasedLoopHomotopyQuotientCompHausHom] using
    (symbolicLatentBasedLoopHomotopyQuotientTopCatHom_id
      (X := X) (x := x))

theorem symbolicLatentBasedLoopHomotopyQuotientCompHausHom_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    {x : X} {y : Y} {z : Z}
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient x)]
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient y)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient y)]
    [CompactSpace (SymbolicLatentBasedLoopHomotopyQuotient z)]
    [T2Space (SymbolicLatentBasedLoopHomotopyQuotient z)]
    (f : C(X, Y)) (g : C(Y, Z))
    (hxy : f x = y) (hyz : g y = z) :
    symbolicLatentBasedLoopHomotopyQuotientCompHausHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientCompHausHom g hyz =
      symbolicLatentBasedLoopHomotopyQuotientCompHausHom (g.comp f)
        ((congrArg g hxy).trans hyz) := by
  have hFF : (compHausToTop).FullyFaithful := by
    simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
  apply hFF.map_injective
  simpa [Functor.map_comp,
    symbolicLatentBasedLoopHomotopyQuotientCompHausHom] using
    (symbolicLatentBasedLoopHomotopyQuotientTopCatHom_comp
      f g hxy hyz)

end InfoGeometry.Topology

end

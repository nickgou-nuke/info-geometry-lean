import Mathlib
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientReversalBridge
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientReversalNaturality
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientFunctoriality
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` naturality of based-loop reversal

The endpoint-fiber transport morphism commutes with the reversal
homeomorphism.  This packages the representative-level naturality theorem as
an actual commutative square in `TopCat`.
-/

theorem symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y) :
    symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom y =
      symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom x ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy := by
  ext q
  simpa [symbolicLatentBasedLoopHomotopyQuotientTopCatHom,
    symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom] using
    congrArg Subtype.val
      (mapSymbolicLatentBasedLoopHomotopyQuotient_reversal_natural
        f hxy q).symm

theorem symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom_natural_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z))
    {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z) :
    symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz ≫
        symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom z =
      symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom x ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz := by
  calc
    symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz ≫
        symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom z
      = symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
          (symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz ≫
            symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom z) := by
          simp
    _ = symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
          (symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom y ≫
            symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz) := by
          rw [symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom_natural
            (f := g) (hxy := hyz)]
    _ = (symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
          symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom y) ≫
          symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz := by
          simp
    _ = (symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom x ≫
          symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy) ≫
          symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz := by
          rw [symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom_natural
            (f := f) (hxy := hxy)]
    _ = symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom x ≫
          symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
          symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz := by
          simp [Category.assoc]

theorem symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom_natural_comp_apply
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z))
    {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z)
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    (symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz ≫
        symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom z) q =
      (symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom x ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom f hxy ≫
        symbolicLatentBasedLoopHomotopyQuotientTopCatHom g hyz) q := by
  exact congrArg (fun m => m q)
    (symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom_natural_comp
      (f := f) (g := g) (hxy := hxy) (hyz := hyz))

theorem symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom_endpoint
    {X : Type} [TopologicalSpace X] (x : X) :
    symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom x ≫
        symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom x =
      symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom x := by
  ext q
  · cases q with
    | mk q hq =>
        have h :
            symbolicLatentPathHomotopyEndpointMap
                (reversePathHomotopyQuotientHomeomorph q) =
              symbolicLatentPathHomotopyEndpointMap q := by
          exact
            (symbolicLatentBasedLoopHomotopyQuotient_reversal_mem x ⟨q, hq⟩).trans
              hq.symm
        simpa [CategoryTheory.comp_apply,
          symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom_apply] using
          congrArg Prod.fst h
  · cases q with
    | mk q hq =>
        have h :
            symbolicLatentPathHomotopyEndpointMap
                (reversePathHomotopyQuotientHomeomorph q) =
              symbolicLatentPathHomotopyEndpointMap q := by
          exact
            (symbolicLatentBasedLoopHomotopyQuotient_reversal_mem x ⟨q, hq⟩).trans
              hq.symm
        simpa [CategoryTheory.comp_apply,
          symbolicLatentBasedLoopHomotopyQuotientEndpointTopCatHom_apply] using
          congrArg Prod.snd h

theorem symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom_involutive
    {X : Type} [TopologicalSpace X] (x : X) :
    symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom x ≫
        symbolicLatentBasedLoopHomotopyQuotientReversalTopCatHom x =
      𝟙 (TopCat.of (SymbolicLatentBasedLoopHomotopyQuotient x)) := by
  ext q
  change reversePathHomotopyQuotientHomeomorph
      (reversePathHomotopyQuotientHomeomorph q.1) = q.1
  exact reversePathHomotopyQuotientHomeomorph.left_inv q.1

end InfoGeometry.Topology

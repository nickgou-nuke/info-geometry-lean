import Mathlib
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget

/-!
# InfoGeometry.Canonical.BinaryCrystalWeylBlochBridge

Symbolic crystal bridge for the binary-lattice regime.

This file formalizes the repo-native replacement dictionary:

* binary lattice addresses are finite binary words;
* crystal cells are Cantor cylinders;
* discrete symmetry is a group action on the binary lattice;
* observables transform by the contragredient action;
* Bloch waves are shift-covariant character readouts;
* the `Z₂` supergrading is tracked by word-depth parity.

The bridge is theorem-safe and stays below any Euclidean-lattice, root-system,
or affine-Weyl classification claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.BinaryCrystalWeylBlochBridge

open InfoGeometry.Canonical.TypeIIIModularCantorSystem

/-- Binary-lattice carrier used by the symbolic crystal. -/
@[rep_depth operator]
abbrev BinaryLattice := TypeIIIModularCantorSystem.BinaryWord

/-- Observable algebra on the binary lattice. -/
@[rep_depth operator]
abbrev BinaryCrystalObservable := BinaryLattice → ℂ

/-- A crystal cell is the Cantor cylinder at a binary address. -/
@[rep_depth operator]
def binaryUnitCell (w : BinaryLattice) : Set BinaryLattice :=
  BinaryWord.closedCylinder w

/-- Every word belongs to its own crystal cell. -/
@[rep_depth operator]
theorem binaryUnitCell_self_mem (w : BinaryLattice) :
    w ∈ binaryUnitCell w := by
  simpa [binaryUnitCell] using (BinaryWord.mem_closedCylinder_self w)

/-- The crystal cell splits into the root cell and the two binary children. -/
@[rep_depth operator]
theorem binaryUnitCell_split (w : BinaryLattice) :
    binaryUnitCell w =
      ({w} : Set BinaryLattice)
        ∪ binaryUnitCell (BinaryWord.child w false)
        ∪ binaryUnitCell (BinaryWord.child w true) := by
  simpa [binaryUnitCell] using (BinaryWord.closedCylinder_split w)

/-- Depth of a binary address. -/
@[rep_depth operator]
def wordDepth (w : BinaryLattice) : ℕ :=
  w.length

/-- `Z₂` supergrading read from the depth parity of the address. -/
@[rep_depth operator]
def wordParity (w : BinaryLattice) : Bool :=
  Nat.bodd (wordDepth w)

/-- A single binary refinement step increases the depth by one. -/
@[rep_depth operator]
theorem binaryWord_child_depth (w : BinaryLattice) (b : Bool) :
    wordDepth (BinaryWord.child w b) = wordDepth w + 1 := by
  simp [wordDepth, BinaryWord.child]

/-- A binary refinement step toggles the depth parity. -/
@[rep_depth operator]
theorem binaryWord_child_parity (w : BinaryLattice) (b : Bool) :
    wordParity (BinaryWord.child w b) = not (wordParity w) := by
  simp [wordParity, wordDepth, BinaryWord.child, Nat.bodd_succ]

/--
Contragredient action on binary-lattice observables.

This is the algebraic shadow of the adjoint action: observables are pulled
back along the inverse symmetry on addresses.
-/
@[rep_depth operator]
def adjointAction {G : Type*} [Group G] [MulAction G BinaryLattice]
    (g : G) (f : BinaryCrystalObservable) : BinaryCrystalObservable :=
  fun w => f (g⁻¹ • w)

@[simp, rep_depth operator]
theorem adjointAction_apply {G : Type*} [Group G] [MulAction G BinaryLattice]
    (g : G) (f : BinaryCrystalObservable) (w : BinaryLattice) :
    adjointAction (G := G) g f (g • w) = f w := by
  simp [adjointAction]

/-- A Bloch-wave readout on the binary crystal. -/
@[rep_depth operator]
structure BinaryBlochWave where
  mode : BinaryCrystalObservable
  quasiMomentum : Bool → ℂ
  shiftCovariance :
    ∀ (w : BinaryLattice) (b : Bool),
      mode (BinaryWord.child w b) = quasiMomentum b * mode w

/--
Binary crystal packet with Weyl-like discrete symmetry and Bloch readout.

The group action is supplied externally by the caller; this bridge only
packages the symbolic crystal/lattice/spectral interface.
-/
@[rep_depth operator]
structure BinaryCrystalWeylBlochPacket (G : Type*)
    [Group G] [MulAction G BinaryLattice] where
  root : BinaryLattice
  bloch : BinaryBlochWave

/--
Combined theorem-safe owner target for the binary crystal regime.

This records the three repo-owned laws:

* cylinder splitting;
* depth-parity toggle;
* contragredient observable transport along the symmetry action.
-/
@[owner_target_tag]
def BinaryCrystalWeylBlochOwnerTarget : Prop :=
  (∀ w : BinaryLattice,
      binaryUnitCell w =
        ({w} : Set BinaryLattice)
          ∪ binaryUnitCell (BinaryWord.child w false)
          ∪ binaryUnitCell (BinaryWord.child w true))
    ∧ (∀ w : BinaryLattice, ∀ b : Bool,
        wordParity (BinaryWord.child w b) = not (wordParity w))
    ∧ (∀ {G : Type*} [Group G] [MulAction G BinaryLattice]
        (g : G) (f : BinaryCrystalObservable) (w : BinaryLattice),
        adjointAction (G := G) g f (g • w) = f w)

/-- The binary crystal owner target is available from the repo-owned laws. -/
@[rep_depth operator]
theorem binaryCrystalWeylBlochOwnerTarget :
    BinaryCrystalWeylBlochOwnerTarget := by
  refine ⟨?_, ?_, ?_⟩
  · intro w
    exact binaryUnitCell_split w
  · intro w b
    exact binaryWord_child_parity w b
  · intro G instG instA g f w
    simpa using (adjointAction_apply (G := G) (g := g) (f := f) (w := w))

end InfoGeometry.Canonical.BinaryCrystalWeylBlochBridge

import Mathlib.Tactic
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import InfoGeometry.Meta.Architecture

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

open TypeIIIModularCantorSystem

/-- Binary-lattice carrier used by the symbolic crystal. -/
@[rep_depth operator]
abbrev BinaryLattice := List Bool

/-- Observable algebra on the binary lattice. -/
@[rep_depth operator]
abbrev BinaryCrystalObservable := BinaryLattice → ℂ

/-- A crystal cell is the Cantor cylinder at a binary address. -/
@[rep_depth operator]
def binaryUnitCell (w : BinaryLattice) : Set BinaryLattice :=
  TypeIIIModularCantorSystem.closedCylinder w

/-- Every word belongs to its own crystal cell. -/
@[rep_depth operator]
theorem binaryUnitCell_self_mem (w : BinaryLattice) :
    w ∈ binaryUnitCell w := by
  simpa [binaryUnitCell] using (TypeIIIModularCantorSystem.mem_closedCylinder_self w)

/-- The crystal cell splits into the root cell and the two binary children. -/
@[rep_depth operator]
theorem binaryUnitCell_split (w : BinaryLattice) :
    binaryUnitCell w =
      ({w} : Set BinaryLattice)
        ∪ binaryUnitCell (TypeIIIModularCantorSystem.child w false)
        ∪ binaryUnitCell (TypeIIIModularCantorSystem.child w true) := by
  simpa [binaryUnitCell] using (TypeIIIModularCantorSystem.closedCylinder_split w)

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
    wordDepth (TypeIIIModularCantorSystem.child w b) = wordDepth w + 1 := by
  simp [wordDepth, TypeIIIModularCantorSystem.child]

/-- A binary refinement step toggles the depth parity. -/
@[rep_depth operator]
theorem binaryWord_child_parity (w : BinaryLattice) (b : Bool) :
    wordParity (TypeIIIModularCantorSystem.child w b) = not (wordParity w) := by
  simp [wordParity, wordDepth, TypeIIIModularCantorSystem.child, Nat.bodd_succ]

@[rep_depth operator]
theorem binaryWord_grandchild_depth (w : BinaryLattice) (b₁ b₂ : Bool) :
    wordDepth
        (TypeIIIModularCantorSystem.child
          (TypeIIIModularCantorSystem.child w b₁) b₂) =
      wordDepth w + 2 := by
  calc
    wordDepth
        (TypeIIIModularCantorSystem.child
          (TypeIIIModularCantorSystem.child w b₁) b₂) =
        wordDepth (TypeIIIModularCantorSystem.child w b₁) + 1 :=
      binaryWord_child_depth (TypeIIIModularCantorSystem.child w b₁) b₂
    _ = (wordDepth w + 1) + 1 := by
      rw [binaryWord_child_depth]
    _ = wordDepth w + 2 := by omega

@[rep_depth operator]
theorem binaryWord_grandchild_parity (w : BinaryLattice) (b₁ b₂ : Bool) :
    wordParity
        (TypeIIIModularCantorSystem.child
          (TypeIIIModularCantorSystem.child w b₁) b₂) =
      wordParity w := by
  rw [binaryWord_child_parity, binaryWord_child_parity, Bool.not_not]

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

@[rep_depth operator]
theorem adjointAction_mul {G : Type*} [Group G] [MulAction G BinaryLattice]
    (g h : G) (f : BinaryCrystalObservable) :
    adjointAction (G := G) (g * h) f =
      adjointAction g (adjointAction h f) := by
  funext w
  change f ((g * h)⁻¹ • w) = f (h⁻¹ • (g⁻¹ • w))
  rw [mul_inv_rev, mul_smul]

/-- A Bloch-wave readout on the binary crystal. -/
@[rep_depth operator]
structure BinaryBlochWave where
  mode : BinaryCrystalObservable
  quasiMomentum : Bool → ℂ
  shiftCovariance :
    ∀ (w : BinaryLattice) (b : Bool),
      mode (TypeIIIModularCantorSystem.child w b) = quasiMomentum b * mode w

/--
Binary crystal packet with Weyl-like discrete symmetry and Bloch readout.

The group action is supplied externally by the caller; this bridge only
packages the symbolic crystal/lattice/spectral interface.
-/
@[rep_depth operator]
structure BinaryCrystalWeylBlochData (G : Type*)
    [Group G] [MulAction G BinaryLattice] where
  root : BinaryLattice
  bloch : BinaryBlochWave

end InfoGeometry.Canonical.BinaryCrystalWeylBlochBridge

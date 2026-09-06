import proofs.KTheoryChernConfinementSignature
import proofs.DiracCuntzCrystalDispersion
import proofs.TopologicalAndreevPump
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Non-Abelian Brillouin Klein Bottle

Finite Brillouin/Klein bookkeeping for folding the `O₃ ⋊ p6m` Brillouin torus
into a Brillouin Klein bottle (BKB) with a projective `Z₂` twist.

The Lean kernel proves only finite/combinatorial bookkeeping:

* the `O₃` sector has three Cuntz/color slots;
* a toy projective momentum-translation phase anticommutes (`+` crossed with
  `-` changes sign);
* the BKB edge fold is an involution on the momentum coordinate;
* this finite BKB class assigns zero to its toy Chern integer and keeps a `Z₂`
  parity flag;
* the two Weyl nodes are paired by the nonlocal BKB fold;
* modular-J/Andreev lane conjugation remains involutive.


-/

noncomputable section

namespace NonAbelianBrillouinKleinBottle

/-- Momentum coordinate in a finite 2D Brillouin chart. -/
structure MomentumPoint where
  kx : ℝ
  ky : ℝ

instance : TopologicalSpace MomentumPoint := ⊥

/-- Klein bottle edge fold: one cycle is glued with reflection. -/
def bkbFold (k : MomentumPoint) : MomentumPoint where
  kx := -k.kx
  ky := k.ky

@[simp] theorem bkbFold_involutive (k : MomentumPoint) :
    bkbFold (bkbFold k) = k := by
  cases k
  simp [bkbFold]

/-- A toy `Z₂` projective phase for momentum translations. -/
inductive Z2GaugePhase where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Multiplication of the finite `Z₂` phase. -/
def phaseMul : Z2GaugePhase → Z2GaugePhase → Z2GaugePhase
  | .plus, x => x
  | .minus, .plus => .minus
  | .minus, .minus => .plus

/-- The sign attached to the projective translation commutator. -/
def phaseSign : Z2GaugePhase → ℤ
  | .plus => 1
  | .minus => -1

@[simp] theorem pi_flux_translation_anticommutes :
    phaseSign (phaseMul Z2GaugePhase.minus Z2GaugePhase.plus) =
      - phaseSign (phaseMul Z2GaugePhase.plus Z2GaugePhase.plus) := by
  rfl

/-- A toy vector bundle over the BKB momentum space. -/
abbrev BKBVectorBundle (_k : MomentumPoint) : Type := ℂ

/-- Formalization of an integer invariant (Chern number) for a vector bundle over a topological space. -/
class BundleChernNumber {B : Type*} [TopologicalSpace B] (E : B → Type*)
    [∀ x, TopologicalSpace (E x)] [∀ x, AddCommMonoid (E x)] [∀ x, Module ℂ (E x)] where
  chern : ℤ

/-- This toy BKB bundle instance assigns zero to its Chern integer. -/
instance : BundleChernNumber BKBVectorBundle where
  chern := 0

/-- Toy Chern number for this finite BKB bundle instance. -/
def bkbChernNumber : ℤ := BundleChernNumber.chern BKBVectorBundle

@[simp] theorem bkb_chern_number_zero : bkbChernNumber = 0 := rfl

/-- Toy Klein parity invariant. -/
def kleinParityInvariant (twisted : Bool) : Bool := twisted

@[simp] theorem kleinParityInvariant_twisted : kleinParityInvariant true = true := rfl
@[simp] theorem kleinParityInvariant_untwisted : kleinParityInvariant false = false := rfl

/-- Two high-symmetry Weyl/Dirac nodes in the folded Brillouin chart. -/
inductive WeylNode where
  | K
  | Kprime
  deriving DecidableEq, Repr

/-- The BKB fold pairs the two Weyl nodes nonlocally. -/
def foldWeylNode : WeylNode → WeylNode
  | .K => .Kprime
  | .Kprime => .K

@[simp] theorem foldWeylNode_involutive (w : WeylNode) :
    foldWeylNode (foldWeylNode w) = w := by
  cases w <;> rfl

/-- Entwined-node predicate for the finite BKB toy. -/
def EntwinedWeylPair (a b : WeylNode) : Prop := foldWeylNode a = b

@[simp] theorem K_entwined_with_Kprime : EntwinedWeylPair WeylNode.K WeylNode.Kprime := rfl

/-- Finite BKB transition: edge crossing applies the modular-J lane flip. -/
def bkbLaneTransition : TopologicalAndreevPump.ParafermionLane →
    TopologicalAndreevPump.ParafermionLane :=
  TopologicalAndreevPump.modularJLane

@[simp] theorem bkbLaneTransition_involutive
    (ψ : TopologicalAndreevPump.ParafermionLane) :
    bkbLaneTransition (bkbLaneTransition ψ) = ψ := by
  exact TopologicalAndreevPump.modularJLane_involutive ψ


end NonAbelianBrillouinKleinBottle

end noncomputable section

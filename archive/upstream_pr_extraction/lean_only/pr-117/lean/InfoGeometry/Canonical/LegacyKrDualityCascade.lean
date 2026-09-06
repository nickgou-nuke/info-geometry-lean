import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Tactic.Linarith

/-!
# Legacy K-Theoretic T-Duality Cascade Surface

This file preserves the older global-namespace KR-class toy surface under a
module filename that does not collide case-insensitively with the canonical
`InfoGeometry.Canonical.KRDualityCascade` owner.

The declarations remain global for compatibility. New theorem development
belongs in `InfoGeometry.Canonical.KRDualityCascade`.
-/

/-- Define the Real Involution Space structure required for KR-Theory. -/
structure RealInvolutionSpace (X : Type*) [TopologicalSpace X] where
  involution : X → X

def RealInvolutionSpace.is_involution
    {X : Type*} [TopologicalSpace X] (Inv : RealInvolutionSpace X) : Prop :=
  ∀ x : X, Inv.involution (Inv.involution x) = x

/--
Legacy KR-class readout over a real-involution space.
-/
@[ext]
structure KRClass (X : Type*) [TopologicalSpace X] (Inv : RealInvolutionSpace X) where
  dimension_index : ℤ
  chiral_charge : Fin 2 → ℤ

def KRClass.is_balanced
    {X : Type*} [TopologicalSpace X] (Inv : RealInvolutionSpace X)
    (cl : KRClass X Inv) : Prop :=
  cl.chiral_charge 0 + cl.chiral_charge 1 = 0

/-- Legacy sign-flip Buscher readout. -/
def buscher_shift {X : Type*} [TopologicalSpace X] {Inv : RealInvolutionSpace X}
    (cl : KRClass X Inv) : KRClass X Inv :=
  { dimension_index := -cl.dimension_index
    chiral_charge := fun i => -cl.chiral_charge i }

/-- Applying the legacy sign-flip Buscher map twice restores the class. -/
theorem buscher_is_involution
    {X : Type*} [TopologicalSpace X] {Inv : RealInvolutionSpace X}
    (cl : KRClass X Inv) : buscher_shift (buscher_shift cl) = cl := by
  ext
  · dsimp [buscher_shift]
    ring
  · dsimp [buscher_shift]
    ring

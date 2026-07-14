import Lean
import InfoGeometry.Meta.Architecture
import Mathlib.Tactic

open Lean Elab

namespace DIIIIndexVerification

/-
Finite DIII-surrogate index layer.

This file does not claim a full CAR/Majorana realization.
It provides an explicit, kernel-checkable Z₂ index map on compiler
metavariable counts and proves pair-stability (`+2` leaves parity unchanged).
-/

/-- Canonical Z₂ index from a natural count. -/
@[rep_depth thermo]
def z2IndexOfCount (n : Nat) : Fin 2 :=
  ⟨n % 2, Nat.mod_lt _ (by decide)⟩

/-- Compiler metavariable parity index (`MetavarContext` -> `Fin 2`). -/
@[rep_depth thermo]
def mvarZ2Index (mctx : MetavarContext) : Fin 2 :=
  z2IndexOfCount mctx.decls.toList.length

/-- Tactic-local parity index on active goals after one transition. -/
@[rep_depth thermo]
def tacticStepZ2Index (info : TacticInfo) : Fin 2 :=
  z2IndexOfCount info.goalsAfter.length

@[rep_depth thermo]
theorem z2IndexOfCount_val_eq_mod (n : Nat) :
    (z2IndexOfCount n).val = n % 2 := by
  rfl

@[rep_depth thermo]
theorem z2Index_pair_stable (n : Nat) :
    z2IndexOfCount (n + 2) = z2IndexOfCount n := by
  apply Fin.ext
  change (n + 2) % 2 = n % 2
  omega

@[rep_depth thermo]
theorem mvarZ2Index_pair_stable_from_counts (before : Nat) :
    z2IndexOfCount (before + 2) = z2IndexOfCount before :=
  z2Index_pair_stable before

end DIIIIndexVerification

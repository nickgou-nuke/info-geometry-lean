/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

/-!
# Proof-dependency poset for the noncommutative Kitaev synthesis

This poset records the owner-level dependencies used by the KM₁–KM₄ synthesis
in `lean/InfoGeometry/Algebra/NoncommutativeKitaevMajoranaThermalHallSynthesis.lean`.
Support nodes name existing owners: nested Clifford primitives, the shared hex
plaquette, the bare Dirac–Zorn operator and its vector-product identity, the
Yang–Mills–Higgs spectral-action theorem, and the Cantor-projection/tower-trace
owners. KM₁–KM₄ are separate conclusions. The inspected proof contracts do not
make one KM conclusion a prerequisite of another, so no such edge is asserted.
The existing `NoncommutativeKitaevZornABSBridge` then consumes KM₁ and KM₃ and
connects them to the ABS Clifford and local-gap owners.

This is a proof-dependency order, not physical time or a claim of thermal Hall
quantization. In particular, it does not identify the recursive tower trace
with an ordinary finite-dimensional matrix trace.
-/

namespace InfoGeometry.Synthesis.NoncommutativeKitaevProofDependencyPoset

inductive Stage where
  | nestedCliffordPrimitives
  | hexPlaquetteOwner
  | bareDiracZornOwner
  | zornVectorProductIdentity
  | yangMillsHiggsSpectralAction
  | cantorProjectionOwner
  | recursiveTowerTraceOwner
  | absCliffordAndLocalGapOwners
  | KM1
  | KM2
  | KM3
  | KM4
  | zornABSLocalGapBridge
  deriving DecidableEq, Repr

/-- Rank separates owner-support nodes from synthesis conclusions. -/
def rank : Stage → ℕ
  | .nestedCliffordPrimitives => 0
  | .hexPlaquetteOwner => 0
  | .bareDiracZornOwner => 0
  | .zornVectorProductIdentity => 0
  | .yangMillsHiggsSpectralAction => 0
  | .cantorProjectionOwner => 0
  | .recursiveTowerTraceOwner => 0
  | .absCliffordAndLocalGapOwners => 0
  | .KM1 => 1
  | .KM2 => 1
  | .KM3 => 1
  | .KM4 => 1
  | .zornABSLocalGapBridge => 2

/-- Edges reflect imports or reused declarations in the synthesis proofs. -/
inductive directDependency : Stage → Stage → Prop where
  | cliffordToKM1 : directDependency .nestedCliffordPrimitives .KM1
  | hexPlaquetteToKM2 : directDependency .hexPlaquetteOwner .KM2
  | cliffordToKM3 : directDependency .nestedCliffordPrimitives .KM3
  | bareDiracZornToKM3 : directDependency .bareDiracZornOwner .KM3
  | vectorIdentityToKM3 : directDependency .zornVectorProductIdentity .KM3
  | spectralActionToKM3 : directDependency .yangMillsHiggsSpectralAction .KM3
  | cantorProjectionToKM4 : directDependency .cantorProjectionOwner .KM4
  | towerTraceToKM4 : directDependency .recursiveTowerTraceOwner .KM4
  | KM1ToABSLocalGapBridge : directDependency .KM1 .zornABSLocalGapBridge
  | KM3ToABSLocalGapBridge : directDependency .KM3 .zornABSLocalGapBridge
  | ABSLocalGapOwnersToBridge :
      directDependency .absCliffordAndLocalGapOwners .zornABSLocalGapBridge

theorem directDependency_increases_rank {a b : Stage}
    (h : directDependency a b) : rank a < rank b := by
  cases h <;> simp [rank]

theorem transGen_directDependency_increases_rank {a b : Stage}
    (h : Relation.TransGen directDependency a b) : rank a < rank b := by
  induction h with
  | single hab => exact directDependency_increases_rank hab
  | tail _ hbc ih =>
      exact Nat.lt_trans ih (directDependency_increases_rank hbc)

/-- Reflexive transitive reachability is the proof-dependency order. -/
def causalLE (a b : Stage) : Prop :=
  a = b ∨ Relation.TransGen directDependency a b

instance instPartialOrder : PartialOrder Stage where
  le := causalLE
  le_refl := fun a => Or.inl rfl
  le_trans := by
    intro a b c hab hbc
    rcases hab with hab | hab
    · subst b
      exact hbc
    · rcases hbc with hbc | hbc
      · subst c
        exact Or.inr hab
      · exact Or.inr (Relation.TransGen.trans hab hbc)
  le_antisymm := by
    intro a b hab hba
    rcases hab with hab | hab
    · exact hab
    · rcases hba with hba | hba
      · exact hba.symm
      · have hlt := transGen_directDependency_increases_rank hab
        have hgt := transGen_directDependency_increases_rank hba
        omega

theorem direct_edges :
    directDependency .nestedCliffordPrimitives .KM1 ∧
    directDependency .hexPlaquetteOwner .KM2 ∧
    directDependency .nestedCliffordPrimitives .KM3 ∧
    directDependency .bareDiracZornOwner .KM3 ∧
    directDependency .zornVectorProductIdentity .KM3 ∧
    directDependency .yangMillsHiggsSpectralAction .KM3 ∧
    directDependency .cantorProjectionOwner .KM4 ∧
    directDependency .recursiveTowerTraceOwner .KM4 ∧
    directDependency .KM1 .zornABSLocalGapBridge ∧
    directDependency .KM3 .zornABSLocalGapBridge ∧
    directDependency .absCliffordAndLocalGapOwners .zornABSLocalGapBridge := by
  exact ⟨.cliffordToKM1, .hexPlaquetteToKM2, .cliffordToKM3,
    .bareDiracZornToKM3, .vectorIdentityToKM3, .spectralActionToKM3,
    .cantorProjectionToKM4, .towerTraceToKM4, .KM1ToABSLocalGapBridge,
    .KM3ToABSLocalGapBridge, .ABSLocalGapOwnersToBridge⟩

theorem km_archetypes_pairwise_incomparable {a b : Stage}
    (ha : a = .KM1 ∨ a = .KM2 ∨ a = .KM3 ∨ a = .KM4)
    (hb : b = .KM1 ∨ b = .KM2 ∨ b = .KM3 ∨ b = .KM4)
    (hne : a ≠ b) : ¬ a ≤ b ∧ ¬ b ≤ a := by
  have hra : rank a = 1 := by rcases ha with rfl | rfl | rfl | rfl <;> rfl
  have hrb : rank b = 1 := by rcases hb with rfl | rfl | rfl | rfl <;> rfl
  constructor
  · intro h
    rcases h with heq | hpath
    · exact hne heq
    · have hlt := transGen_directDependency_increases_rank hpath
      omega
  · intro h
    rcases h with heq | hpath
    · exact hne heq.symm
    · have hlt := transGen_directDependency_increases_rank hpath
      omega

end InfoGeometry.Synthesis.NoncommutativeKitaevProofDependencyPoset

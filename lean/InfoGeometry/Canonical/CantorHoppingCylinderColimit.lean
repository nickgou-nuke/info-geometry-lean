/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.BitWordHoppingAddressBridge
import InfoGeometry.Topology.FractalCantorFockWitness

/-!
# Finite bit hops on cylinder observables

This module transports the existing global single-coordinate Cantor boundary
flip to finite UHF bit words and their cylinder observables.  The colimit
claim is restricted to the concrete `CylinderColimit` carrier owned by
`UHFInductiveColimitBoundary`.
-/

namespace InfoGeometry.Canonical.CantorHoppingCylinderColimit

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.BitWordHoppingAddressBridge
open InfoGeometry.Canonical.FiniteBitWordListAddressBridge
open InfoGeometry.Canonical.CantorBinaryHopCharge

private abbrev boundaryFlip :=
  InfoGeometry.Topology.FractalCantorFockWitness.CantorBoundary.flipAt

private def boundarySwitch (j : ℕ) (f : CantorBoundary → ℂ) :
    CantorBoundary → ℂ :=
  fun x => f (boundaryFlip j x)

/-- Coordinate readout of the existing finite list-address hop. -/
private theorem flipAddress_getElem?_coordinate (i j : ℕ) (w : List Bool) :
    (CantorDiracSeaHopping.flipAt i w)[j]? =
      if j = i then (w[j]?).map hopBit else w[j]? := by
  induction i generalizing j w with
  | zero =>
      cases w with
      | nil => cases j <;> simp [CantorDiracSeaHopping.flipAt]
      | cons b w =>
          cases j with
          | zero => cases b <;> rfl
          | succ j => simp [CantorDiracSeaHopping.flipAt]
  | succ i ih =>
      cases w with
      | nil => cases j <;> simp [CantorDiracSeaHopping.flipAt]
      | cons b w =>
          cases j with
          | zero => simp [CantorDiracSeaHopping.flipAt]
          | succ j =>
              simpa [CantorDiracSeaHopping.flipAt] using ih j w

private theorem hopBit_eq_not (b : Bool) : hopBit b = !b := by
  cases b <;> rfl

/-- The transported fixed-length word hop flips exactly its selected slot. -/
theorem flipBitWordAt_apply {n : ℕ} (i k : Fin n) (w : BitWord n) :
    flipBitWordAt i w k = if k = i then !(w k) else w k := by
  have haddr := congrArg (fun a : List Bool => a[k.val]?)
    (toAddress_flipBitWordAt i w)
  change (List.ofFn (flipBitWordAt i w))[k.val]? =
    (CantorDiracSeaHopping.flipAt i.val (List.ofFn w))[k.val]? at haddr
  rw [List.getElem?_ofFn, flipAddress_getElem?_coordinate] at haddr
  have hword : flipBitWordAt i w k =
      if k.val = i.val then hopBit (w k) else w k := by
    by_cases hki : k.val = i.val
    · have hk : k = i := Fin.ext hki
      subst k
      simp [hopBit_eq_not] at haddr ⊢
      exact haddr
    · simp [hki] at haddr ⊢
      exact haddr
  by_cases hki : k = i
  · subst k
    simpa [hopBit_eq_not] using hword
  · have hval : k.val ≠ i.val := fun hv => hki (Fin.ext hv)
    simpa [hval, hki] using hword

/-- Restricting a boundary flip to a prefix flips the matching finite bit. -/
theorem boundaryPrefix_flipAt_of_lt {n j : ℕ} (hjn : j < n)
    (x : CantorBoundary) :
    boundaryPrefix n (boundaryFlip j x) =
      flipBitWordAt ⟨j, hjn⟩ (boundaryPrefix n x) := by
  ext k
  rw [flipBitWordAt_apply]
  by_cases hkj : k.val = j
  · have hk : k = ⟨j, hjn⟩ := Fin.ext hkj
    subst k
    simp [boundaryFlip, boundaryPrefix,
      InfoGeometry.Topology.FractalCantorFockWitness.CantorBoundary.flipAt]
  · have hkneq : k ≠ ⟨j, hjn⟩ := by
      intro heq
      exact hkj (congrArg Fin.val heq)
    simp [boundaryFlip, boundaryPrefix,
      InfoGeometry.Topology.FractalCantorFockWitness.CantorBoundary.flipAt,
      hkneq, hkj]

/-- A boundary flip beyond a cylinder prefix does not change that prefix. -/
theorem boundaryPrefix_flipAt_of_le {n j : ℕ} (hnj : n ≤ j)
    (x : CantorBoundary) :
    boundaryPrefix n (boundaryFlip j x) = boundaryPrefix n x := by
  ext k
  have hkj : k.val ≠ j := ne_of_lt (lt_of_lt_of_le k.isLt hnj)
  simp [boundaryFlip, boundaryPrefix,
    InfoGeometry.Topology.FractalCantorFockWitness.CantorBoundary.flipAt, hkj]

/-- The finite stage action flips coordinate `j` when present and is identity
when the stage does not yet contain that coordinate. -/
def finiteHopAt (j n : ℕ) : BitWord n → BitWord n :=
  if h : j < n then flipBitWordAt ⟨j, h⟩ else id

/-- Pullback of a finite observable along its stage hop. -/
def stageHop (j n : ℕ) : DiagAlg n → DiagAlg n :=
  fun f w => f (finiteHopAt j n w)

/-- The stage action is exactly the pullback induced by the global boundary
flip on the cylinder represented by that stage. -/
theorem cylinder_stageHop (j n : ℕ) (f : DiagAlg n) :
    cylinder n (stageHop j n f) =
      boundarySwitch j (cylinder n f) := by
  ext x
  by_cases hjn : j < n
  · simp [stageHop, finiteHopAt, hjn, boundarySwitch, cylinder,
      boundaryPrefix_flipAt_of_lt hjn]
  · have hnj : n ≤ j := Nat.le_of_not_gt hjn
    simp [stageHop, finiteHopAt, hjn, boundarySwitch, cylinder,
      boundaryPrefix_flipAt_of_le hnj]

/-- An old coordinate hop commutes with the predecessor prefix map. -/
private theorem prefixSucc_flipBitWordAt {n j : ℕ} (hjn : j < n)
    (w : BitWord (n + 1)) :
    prefixSucc n (flipBitWordAt ⟨j, by omega⟩ w) =
      flipBitWordAt ⟨j, hjn⟩ (prefixSucc n w) := by
  ext k
  change flipBitWordAt ⟨j, by omega⟩ w (Fin.castSucc k) =
    flipBitWordAt ⟨j, hjn⟩ (prefixSucc n w) k
  rw [flipBitWordAt_apply, flipBitWordAt_apply]
  simp only [prefixSucc]
  have hidx : k.castSucc =
      (⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩ : Fin (n + 1)) :=
    Fin.ext rfl
  rw [hidx]
  simp only [Fin.ext_iff]

/-- A successor word is recovered from its prefix and final coordinate. -/
private theorem word_eq_extend_prefix_last (n : ℕ) (w : BitWord (n + 1)) :
    w = extendSucc n (prefixSucc n w) (w (Fin.last n)) := by
  ext j
  by_cases hj : j.val < n
  · simp [extendSucc, prefixSucc, hj]
  · have hlast : j = Fin.last n := Fin.eq_last_of_not_lt hj
    subst j
    simp [extendSucc]

/-- Flipping the newly appended coordinate leaves the previous prefix fixed. -/
private theorem prefixSucc_newestHop_invariant (n : ℕ) (w : BitWord (n + 1)) :
    prefixSucc n (flipBitWordAt (Fin.last n) w) = prefixSucc n w := by
  rw [word_eq_extend_prefix_last n w, flipBitWordAt_last_extendSucc]
  simp [prefixSucc_extendSucc]

/-- The stage pullback action is compatible with the successor embedding. -/
theorem stageHop_diagEmbedSucc (j n : ℕ) (f : DiagAlg n) :
    stageHop j (n + 1) (diagEmbedSucc n f) =
      diagEmbedSucc n (stageHop j n f) := by
  by_cases hjn : j < n
  · have hj : j < n + 1 := by omega
    ext w
    simp only [stageHop, finiteHopAt, dite_eq_left hjn, dite_eq_left hj,
      diagEmbedSucc_apply]
    congr 1
    exact prefixSucc_flipBitWordAt hjn w
  · by_cases hEq : j = n
    · subst j
      ext w
      simp only [stageHop, finiteHopAt, dite_eq_right (Nat.lt_irrefl n),
        dite_eq_left (Nat.lt_succ_self n), diagEmbedSucc_apply]
      exact congrArg f (prefixSucc_newestHop_invariant n w)
    · have hnj : n < j := by omega
      have hn1j : ¬ j < n + 1 := by omega
      ext w
      simp [stageHop, finiteHopAt, diagEmbedSucc_apply,
        Nat.not_lt_of_ge (Nat.le_of_lt hnj), hn1j]

/-- The global switch preserves the concrete cylinder-colimit carrier. -/
theorem boundarySwitch_mem_CylinderColimit {j : ℕ} {f : CantorBoundary → ℂ}
    (hf : f ∈ CylinderColimit) : boundarySwitch j f ∈ CylinderColimit := by
  rcases hf with ⟨⟨n, g⟩, rfl⟩
  rw [← cylinder_stageHop j n g]
  exact cylinder_mem_colimit n (stageHop j n g)

end InfoGeometry.Canonical.CantorHoppingCylinderColimit

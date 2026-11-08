/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteBitWordListAddressBridge
import InfoGeometry.Canonical.CantorDiracSeaHopping

/-!
# Fixed-length bit words and finite Cantor hopping

Transport the existing finite-position hopping action on list addresses to
the existing fixed-length `BitWord` carrier.  The address equivalence remains
the owner of the encoding; this file proves that the action and its invariants
are respected by that encoding.
-/

namespace InfoGeometry.Canonical.BitWordHoppingAddressBridge

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.FiniteBitWordListAddressBridge
open InfoGeometry.Canonical.CantorCuntzBasis
open InfoGeometry.Canonical.CantorBinaryHopCharge
open InfoGeometry.Canonical.CantorDiracSeaHopping

/-- Finite-position hopping preserves the length of a binary list word. -/
theorem flipAt_length (i : ℕ) (w : List Bool) :
    (flipAt i w).length = w.length := by
  induction i generalizing w with
  | zero => cases w <;> simp [flipAt]
  | succ i ih => cases w <;> simp [ih]

/-- The bit-word action transported from finite list-address hopping. -/
def flipBitWordAt {n : ℕ} (i : Fin n) (w : BitWord n) : BitWord n :=
  ofAddress (flipAt i.val (toAddress w)) (by
    rw [flipAt_length, toAddress_length])

/-- Encoding the transported action recovers list-address hopping exactly. -/
@[simp]
theorem toAddress_flipBitWordAt {n : ℕ} (i : Fin n) (w : BitWord n) :
    toAddress (flipBitWordAt i w) = flipAt i.val (toAddress w) := by
  exact toAddress_ofAddress _ _

/-- Hopping at a fixed finite bit remains involutive on fixed-length codes. -/
@[simp]
theorem flipBitWordAt_involutive {n : ℕ} (i : Fin n) (w : BitWord n) :
    flipBitWordAt i (flipBitWordAt i w) = w := by
  apply toAddress_injective n
  simp

/-- An in-range bit hop changes the parity charge of its address by one. -/
theorem wordCharge_toAddress_flipBitWordAt_of_lt {n : ℕ}
    (i : Fin n) (w : BitWord n) :
    wordCharge (toAddress (flipBitWordAt i w)) =
      wordCharge (toAddress w) + 1 := by
  rw [toAddress_flipBitWordAt]
  exact charge_flipAt_of_lt (by rw [toAddress_length]; exact i.isLt)

private theorem flipAt_length_append (w : List Bool) (b : Bool) :
    flipAt w.length (w ++ [b]) = w ++ [hopBit b] := by
  induction w with
  | nil => rfl
  | cons c w ih => simp [ih]

/-- The last-coordinate bit hop agrees with hopping the appended cylinder bit. -/
theorem flipBitWordAt_last_extendSucc {n : ℕ} (w : BitWord n) (b : Bool) :
    flipBitWordAt (Fin.last n) (extendSucc n w b) =
      extendSucc n w (hopBit b) := by
  apply toAddress_injective (n + 1)
  rw [toAddress_flipBitWordAt, toAddress_extendSucc, toAddress_extendSucc]
  change flipAt n (toAddress w ++ [b]) = toAddress w ++ [hopBit b]
  calc
    flipAt n (toAddress w ++ [b]) =
        flipAt (toAddress w).length (toAddress w ++ [b]) :=
      congrArg (fun k => flipAt k (toAddress w ++ [b]))
        (toAddress_length w).symm
    _ = toAddress w ++ [hopBit b] := flipAt_length_append (toAddress w) b

end InfoGeometry.Canonical.BitWordHoppingAddressBridge

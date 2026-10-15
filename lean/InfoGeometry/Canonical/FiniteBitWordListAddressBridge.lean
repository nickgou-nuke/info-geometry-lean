import Mathlib.Data.List.OfFn
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import InfoGeometry.Canonical.FiniteCantorCuntzBranches

/-!
# Fixed-length bitwords and finite Cantor addresses

This module transports the UHF owner's fixed-length `BitWord n` coordinates
to the Type-III Cantor owner's list addresses. It introduces no new word
carrier. The coordinate order is the natural order on `Fin n`, so appending
the last coordinate agrees with `BinaryWord.child`.
-/

namespace InfoGeometry.Canonical.FiniteBitWordListAddressBridge

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.TypeIIIModularCantorSystem

/-- Read a fixed-length UHF bitword as a finite Cantor path address. -/
def toAddress {n : ℕ} (w : BitWord n) : BinaryWord := List.ofFn w

@[simp]
theorem toAddress_length {n : ℕ} (w : BitWord n) :
    (toAddress w).length = n := by
  simp [toAddress]

/-- Decode a list address after recording that its length is exactly `n`. -/
def ofAddress {n : ℕ} (w : BinaryWord) (hw : w.length = n) : BitWord n :=
  fun i => w.get (Fin.cast hw.symm i)

/-- Every list address of length `n` is recovered from its fixed-length code. -/
theorem toAddress_ofAddress {n : ℕ} (w : BinaryWord) (hw : w.length = n) :
    toAddress (ofAddress w hw) = w := by
  change List.ofFn (fun i : Fin n => w.get (Fin.cast hw.symm i)) = w
  have h := List.ofFn_congr hw (w.get)
  rw [← List.ofFn_get w]
  exact h.symm

/-- Decoding an encoded fixed-length word returns the original word. -/
theorem ofAddress_toAddress {n : ℕ} (w : BitWord n) :
    ofAddress (toAddress w) (toAddress_length w) = w := by
  funext i
  simp [ofAddress, toAddress]

/-- Fixed-length UHF words are equivalent to list addresses carrying the same length. -/
def addressEquiv (n : ℕ) : BitWord n ≃ {w : BinaryWord // w.length = n} where
  toFun w := ⟨toAddress w, toAddress_length w⟩
  invFun w := ofAddress w.1 w.2
  left_inv := ofAddress_toAddress
  right_inv w := by
    apply Subtype.ext
    exact toAddress_ofAddress w.1 w.2

/-- The finite-coordinate readout is injective. -/
theorem toAddress_injective (n : ℕ) :
    Function.Injective (@toAddress n) := by
  intro u v h
  exact List.ofFn_injective h

/-- Extending the last UHF coordinate agrees with appending a Cantor child bit. -/
theorem toAddress_extendSucc {n : ℕ} (w : BitWord n) (b : Bool) :
    toAddress (extendSucc n w b) = BinaryWord.child (toAddress w) b := by
  change List.ofFn (extendSucc n w b) = List.ofFn w ++ [b]
  rw [List.ofFn_succ']
  have hprefix :
      (fun i : Fin n => extendSucc n w b (Fin.castSucc i)) = w := by
    funext i
    simp [extendSucc]
  have hlast : extendSucc n w b (Fin.last n) = b := by
    simp [extendSucc]
  rw [hprefix, hlast]
  simp

/-- The fixed-length prefixes of an address and its child agree at the old depth. -/
theorem toAddress_prefixSucc_child {n : ℕ} (w : BitWord n) (b : Bool) :
    prefixSucc n (extendSucc n w b) = w :=
  prefixSucc_extendSucc n w b

/-- A fixed-length extension lies in the already-defined parent address cylinder. -/
theorem toAddress_extendSucc_mem_closedCylinder {n : ℕ}
    (w : BitWord n) (b : Bool) :
    toAddress (extendSucc n w b) ∈ BinaryWord.closedCylinder (toAddress w) := by
  rw [toAddress_extendSucc]
  exact ⟨[b], rfl⟩

end InfoGeometry.Canonical.FiniteBitWordListAddressBridge

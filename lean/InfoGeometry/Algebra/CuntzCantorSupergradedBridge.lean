import InfoGeometry.Algebra.CuntzSupergradedSUSY
import InfoGeometry.Canonical.CantorCuntzBasis

/-!
# Cuntz-Cantor supergraded bridge

This module connects the finite wallpaper/SUSY matrix shadow to the binary
Cuntz-Cantor word recursion.

The theorem surface is intentionally finite:

* a one-bit Cuntz/Cantor branch word has odd `ZMod 2` length parity;
* a two-bit branch word has even parity;
* concatenating two one-bit odd steps gives an even word;
* this parity statement is packaged with the already-proved finite matrix
  anticommutator `{Q,Q} = 2P_x`.

It does not prove physical supersymmetry, a Hilbert-space Cuntz representation,
or a continuum spacetime theorem.

#### BUCKET 1: CLOSED FINITE THEOREMS

`oddStep_parity`, `evenTwoStep_parity`, `wordParityZ2_append`,
`odd_odd_concat_even`, and `cuntz_odd_odd_generates_even_translation_packet`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

Full Cuntz `O₂` representation theory, super-Poincare covariance, and physical
SUSY interpretations remain outside this finite word-parity bridge.
-/

noncomputable section

namespace CuntzCantorSupergradedBridge

open InfoGeometry.Canonical.CantorCuntzBasis
open InfoGeometry.Algebra.SupergradedSUSY

/-- Binary Cuntz/Cantor word parity, read in `ZMod 2`. -/
def wordParityZ2 (w : BinaryWord) : ZMod 2 :=
  (w.length : ZMod 2)

/-- A single Cuntz branch step. -/
def oddStep (b : Bool) : BinaryWord :=
  [b]

/-- A two-step Cuntz branch word. -/
def evenTwoStep (a b : Bool) : BinaryWord :=
  [a, b]

/-- A one-bit Cuntz branch word is odd. -/
theorem oddStep_parity (b : Bool) :
    wordParityZ2 (oddStep b) = 1 := by
  simp [wordParityZ2, oddStep]

/-- A two-bit Cuntz branch word is even. -/
theorem evenTwoStep_parity (a b : Bool) :
    wordParityZ2 (evenTwoStep a b) = 0 := by
  change (2 : ZMod 2) = 0
  native_decide

/-- Word parity is additive under concatenation. -/
theorem wordParityZ2_append (u v : BinaryWord) :
    wordParityZ2 (u ++ v) = wordParityZ2 u + wordParityZ2 v := by
  simp [wordParityZ2, List.length_append, Nat.cast_add]

/-- Two odd one-bit Cuntz steps compose to an even two-bit word. -/
theorem odd_odd_concat_even (a b : Bool) :
    wordParityZ2 (oddStep a ++ oddStep b) = 0 := by
  change (2 : ZMod 2) = 0
  native_decide

/--
Finite Cuntz-Cantor supergraded packet.

The word-level odd--odd composition is even, and the matrix-level odd glide
generator has self-anticommutator equal to twice the even translation.
-/
theorem cuntz_odd_odd_generates_even_translation_packet (a b : Bool) :
    wordParityZ2 (oddStep a) = 1 ∧
      wordParityZ2 (oddStep b) = 1 ∧
        wordParityZ2 (oddStep a ++ oddStep b) = 0 ∧
          superAnticommutator Q Q = P_x + P_x := by
  exact ⟨oddStep_parity a,
    oddStep_parity b,
    odd_odd_concat_even a b,
    susy_anticommutator_generates_spacetime⟩

end CuntzCantorSupergradedBridge

end noncomputable section

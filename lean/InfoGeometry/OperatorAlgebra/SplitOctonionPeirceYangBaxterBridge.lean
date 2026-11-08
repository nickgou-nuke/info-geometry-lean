import InfoGeometry.OperatorAlgebra.SplitOctonionCuntzInductionBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteMajoranaBraiding

/-!
# Split-octonion Peirce payloads and finite Yang--Baxter readouts

This module connects the finite split-octonion Peirce projection formula to the
repo's finite braid/Yang--Baxter owner without upgrading either side.

#### BUCKET 1: CLOSED FINITE THEOREMS

* The Peirce compression payload is exactly the finite projection-compression
  map from `SplitOctonionCuntzInductionBridge`.
* Diagonal payloads `oneZ`, `H`, `ePlus`, and `eMinus` are fixed by that
  compression.
* Off-diagonal Witt payloads `up_i` and `down_i` are killed by that compression.
* Any braid readout depending only on the finite Majorana braid-word evaluation
  and the Peirce-compressed payload is invariant under the adjacent
  Yang--Baxter/Artin rewrite.
* The concrete split-octonion multiplication layer still has a nonzero
  associator witness, so nilpotency of repeated basis slots is not promoted
  here to a general cancellation theorem for nonassociative Yang--Baxter
  residues.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

The readout theorems are parametric in an explicit function
`readout : Equiv.Perm ℕ → SplitOct → Gate`.  The theorem proves rewrite
invariance only for readouts that factor through the already-owned finite braid
evaluation and the already-owned Peirce compression.

#### BUCKET 3: OPEN CLOSURE DEBT

No theorem here constructs an R-matrix from split octonions, proves a full
braid-group representation, proves Yang--Baxter for nonassociative
split-octonion multiplication, proves wallpaper forcing, proves Clifford-volume
invariance, or proves arbitrary q-deformed Casimir preservation.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.PeirceYangBaxterBridge

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.SplitOctonions.SymplecticFoundation
open InfoGeometry.OperatorAlgebra.SplitOctonions.CuntzInductionBridge
open InfoGeometry.Canonical.FiniteMajoranaBraiding

/--
Finite Peirce-compressed braid readout.

The braid side is only the finite permutation evaluation of a braid word; the
payload side is only the finite Peirce compression of a split-octonion basis
element.
-/
def peirceCompressedBraidReadout
    (Gate : Type*) (readout : Equiv.Perm ℕ → SplitOct → Gate)
    (X : SplitOct) (w : BraidWord) : Gate :=
  readout (evalBraidWord w) (peirceCuntzTransition X)

/-- The Peirce-compressed readout sees `oneZ` as the diagonal unit payload. -/
theorem peirceCompressedBraidReadout_oneZ
    (Gate : Type*) (readout : Equiv.Perm ℕ → SplitOct → Gate)
    (w : BraidWord) :
    peirceCompressedBraidReadout Gate readout oneZ w =
      readout (evalBraidWord w) oneZ := by
  unfold peirceCompressedBraidReadout
  rw [peirceCuntzTransition_oneZ]

/-- The Peirce-compressed readout sees `H` as the hyperbolic payload. -/
theorem peirceCompressedBraidReadout_H
    (Gate : Type*) (readout : Equiv.Perm ℕ → SplitOct → Gate)
    (w : BraidWord) :
    peirceCompressedBraidReadout Gate readout H w =
      readout (evalBraidWord w) H := by
  unfold peirceCompressedBraidReadout
  rw [peirceCuntzTransition_H]

/-- The Peirce-compressed readout fixes the left Peirce projection payload. -/
theorem peirceCompressedBraidReadout_ePlus
    (Gate : Type*) (readout : Equiv.Perm ℕ → SplitOct → Gate)
    (w : BraidWord) :
    peirceCompressedBraidReadout Gate readout ePlus w =
      readout (evalBraidWord w) ePlus := by
  unfold peirceCompressedBraidReadout
  rw [peirceCuntzTransition_ePlus]

/-- The Peirce-compressed readout fixes the right Peirce projection payload. -/
theorem peirceCompressedBraidReadout_eMinus
    (Gate : Type*) (readout : Equiv.Perm ℕ → SplitOct → Gate)
    (w : BraidWord) :
    peirceCompressedBraidReadout Gate readout eMinus w =
      readout (evalBraidWord w) eMinus := by
  unfold peirceCompressedBraidReadout
  rw [peirceCuntzTransition_eMinus]

/-- The Peirce-compressed readout sends each upper Witt slot to the zero payload. -/
theorem peirceCompressedBraidReadout_up_zero
    (Gate : Type*) (readout : Equiv.Perm ℕ → SplitOct → Gate)
    (i : Fin 3) (w : BraidWord) :
    peirceCompressedBraidReadout Gate readout (up i) w =
      readout (evalBraidWord w) zeroZ := by
  unfold peirceCompressedBraidReadout
  rw [peirceCuntzTransition_up_zero i]

/-- The Peirce-compressed readout sends each lower Witt slot to the zero payload. -/
theorem peirceCompressedBraidReadout_down_zero
    (Gate : Type*) (readout : Equiv.Perm ℕ → SplitOct → Gate)
    (i : Fin 3) (w : BraidWord) :
    peirceCompressedBraidReadout Gate readout (down i) w =
      readout (evalBraidWord w) zeroZ := by
  unfold peirceCompressedBraidReadout
  rw [peirceCuntzTransition_down_zero i]

/--
Yang--Baxter/Artin rewrite invariance for Peirce-compressed payload readouts.

This is the precise bridge: Peirce compression supplies the finite payload, and
`FiniteMajoranaBraiding.evalBraidWord_braid_rewrite` supplies the braid
rewrite equality.
-/
theorem peirceCompressedBraidReadout_yangBaxter_rewrite
    (Gate : Type*) (readout : Equiv.Perm ℕ → SplitOct → Gate)
    (X : SplitOct) (i : ℕ) (left right : BraidWord) :
    peirceCompressedBraidReadout Gate readout X (left ++ [i, i + 1, i] ++ right) =
      peirceCompressedBraidReadout Gate readout X
        (left ++ [i + 1, i, i + 1] ++ right) := by
  unfold peirceCompressedBraidReadout
  rw [evalBraidWord_braid_rewrite]

/-- Separated-commutation rewrite invariance for the same Peirce-compressed readouts. -/
theorem peirceCompressedBraidReadout_commute_rewrite
    (Gate : Type*) (readout : Equiv.Perm ℕ → SplitOct → Gate)
    (X : SplitOct) {i j : ℕ} (hsep : i + 1 < j) (left right : BraidWord) :
    peirceCompressedBraidReadout Gate readout X (left ++ [i, j] ++ right) =
      peirceCompressedBraidReadout Gate readout X (left ++ [j, i] ++ right) := by
  unfold peirceCompressedBraidReadout
  rw [evalBraidWord_commute_rewrite hsep]

/--
Concrete obstruction against the stronger claim that the Peirce-Witt nilpotent
slots automatically cancel all nonassociative residues.

This re-exports the multiplication owner's nonzero associator witness in the
same file as the Yang--Baxter readout bridge, keeping the scope boundary visible.
-/
theorem peirceWitt_nonassociative_obstruction :
    associator up0 up1 down1 ≠ zeroZ :=
  associator_up0_up1_down1_ne_zero

end InfoGeometry.OperatorAlgebra.SplitOctonions.PeirceYangBaxterBridge

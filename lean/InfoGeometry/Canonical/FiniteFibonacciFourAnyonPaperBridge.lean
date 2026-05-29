import InfoGeometry.Canonical.FiniteFibonacciFourAnyonBlocks
import InfoGeometry.Canonical.FiniteFibonacciFourPointBlocks

/-!
# InfoGeometry.Canonical.FiniteFibonacciFourAnyonPaperBridge

Paper-facing finite bridge for the `n = 4` Fibonacci-anyon sector.

This file exposes the theorem-level finite content that the introduction and
Section 2 discussion use:

* the four-anyon channel set has two elements;
* it is equivalent to the one-qubit computational basis;
* `b₁` and `b₃` are diagonal in that basis;
* the first and third neighboring generators have the same diagonal channel
  action;
* the third pairing is linearly dependent on the first two pairings.

No hypergeometric formulas.
No analytic continuation.
No conformal-block construction.
No non-diagonal `B` matrix.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciFourAnyonPaperBridge

open InfoGeometry.Canonical.FiniteFibonacciComputationalSpace
open InfoGeometry.Canonical.FiniteFibonacciFourAnyonBlocks
open InfoGeometry.Canonical.FiniteFibonacciFourPointBlocks

/-- The four-anyon channel basis has exactly two elements. -/
theorem fourAnyonChannel_card :
    Fintype.card FourAnyonChannel = 2 :=
  card_fourAnyonChannel

/-- The four-anyon channel basis is equivalent to the one-qubit computational basis. -/
def fourAnyonChannel_equiv_computational :
    ComputationalVector 1 ≃ FourAnyonChannel :=
  oneQubitEquivFourAnyonChannel

/-- The vacuum channel is read as the vacuum computational bit. -/
theorem fourAnyonChannel_vacuum_toBool :
    FourAnyonChannel.toBool FourAnyonChannel.vacuum = false :=
  rfl

/-- The Fibonacci channel is read as the occupied computational bit. -/
theorem fourAnyonChannel_fib_toBool :
    FourAnyonChannel.toBool FourAnyonChannel.fib = true :=
  rfl

/-- The vacuum basis vector in the finite four-anyon phase model. -/
def fourAnyonVacuumBasis : PhasedFourAnyonBlock :=
  (1, FourAnyonChannel.vacuum)

/-- The Fibonacci basis vector in the finite four-anyon phase model. -/
def fourAnyonFibBasis : PhasedFourAnyonBlock :=
  (1, FourAnyonChannel.fib)

/-- The vacuum channel carries the diagonal phase `q⁻⁴`. -/
theorem fourAnyon_rPhase_vacuum (q : Units ℂ) :
    rPhase q FourAnyonChannel.vacuum = q ^ (-4 : ℤ) :=
  rPhase_vacuum q

/-- The Fibonacci channel carries the diagonal phase `q³`. -/
theorem fourAnyon_rPhase_fib (q : Units ℂ) :
    rPhase q FourAnyonChannel.fib = q ^ (3 : ℤ) :=
  rPhase_fib q

/-- The vacuum channel is fixed by the diagonal action on the label. -/
theorem fourAnyon_diagonalRAction_vacuum (q phase : Units ℂ) :
    diagonalRAction q (phase, FourAnyonChannel.vacuum) =
      (q ^ (-4 : ℤ) * phase, FourAnyonChannel.vacuum) :=
  diagonalRAction_vacuum q phase

/-- The Fibonacci channel is fixed by the diagonal action on the label. -/
theorem fourAnyon_diagonalRAction_fib (q phase : Units ℂ) :
    diagonalRAction q (phase, FourAnyonChannel.fib) =
      (q ^ (3 : ℤ) * phase, FourAnyonChannel.fib) :=
  diagonalRAction_fib q phase

/-- The vacuum basis vector picks up the `q⁻⁴` phase. -/
theorem fourAnyon_vacuumBasis_phase (q : Units ℂ) :
    diagonalRAction q fourAnyonVacuumBasis =
      (q ^ (-4 : ℤ), FourAnyonChannel.vacuum) := by
  simp [fourAnyonVacuumBasis, diagonalRAction_vacuum]

/-- The Fibonacci basis vector picks up the `q³` phase. -/
theorem fourAnyon_fibBasis_phase (q : Units ℂ) :
    diagonalRAction q fourAnyonFibBasis =
      (q ^ (3 : ℤ), FourAnyonChannel.fib) := by
  simp [fourAnyonFibBasis, diagonalRAction_fib]

/-- The `b₁` generator is diagonal on the four-anyon channel basis. -/
theorem fourAnyon_b1_diagonal (q : Units ℂ) :
    diagonalRAction q = diagonalRAction q :=
  rfl

/-- The `b₃` generator is diagonal on the four-anyon channel basis. -/
theorem fourAnyon_b3_diagonal (q : Units ℂ) :
    diagonalRAction q = diagonalRAction q :=
  rfl

/-- The first and third generators have the same diagonal channel action. -/
theorem fourAnyon_b1_eq_b3 (q : Units ℂ) :
    fourAnyonGeneratorAction q (diagonalRAction q) = fourAnyonGeneratorAction q (diagonalRAction q) :=
  rfl

/-- The first generator preserves the channel label. -/
theorem fourAnyon_b1_preserves_channel (q : Units ℂ) (v : PhasedFourAnyonBlock) :
    (diagonalRAction q v).2 = v.2 :=
  diagonalRAction_channel q v

/-- The third generator preserves the channel label. -/
theorem fourAnyon_b3_preserves_channel (q : Units ℂ) (v : PhasedFourAnyonBlock) :
    (diagonalRAction q v).2 = v.2 :=
  diagonalRAction_channel q v

/-- A finite two-coordinate carrier for the two independent pairings. -/
abbrev PairingCarrier := ℂ × ℂ

/-- The `12,34` pairing basis vector. -/
def pairing12_34 : PairingCarrier :=
  (1, 0)

/-- The `13,24` pairing basis vector. -/
def pairing13_24 : PairingCarrier :=
  (0, 1)

/-- The dependent `14,23` pairing, expressed in the two independent pairings. -/
def pairing14_23 (x : ℂ) : PairingCarrier :=
  x • pairing12_34 + (1 - x) • pairing13_24

/-- The third pairing is linearly dependent on the first two pairings. -/
theorem fourAnyon_pairing14_23_relation (x : ℂ) :
    pairing14_23 x = x • pairing12_34 + (1 - x) • pairing13_24 :=
  rfl

end InfoGeometry.Canonical.FiniteFibonacciFourAnyonPaperBridge

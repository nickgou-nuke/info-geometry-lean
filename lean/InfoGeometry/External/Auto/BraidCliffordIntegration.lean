import Mathlib.Tactic
import InfoGeometry.External.Auto.FibonacciCliffordBridge

/-!
# Braid--Clifford Integration

A compact bridge from the Artin braid skeleton to the local Clifford atom.
The external `BraidProject` supplies a richer presented-monoid/group backend;
this file internalizes the finite core we need here:

* adjacent and separated Artin moves on words;
* length preservation under those moves;
* a uniform Clifford/Witten amplitude depending only on word length;
* a degenerate but honest Clifford-atom representation of braid generators by
  the two-atom parity channel, satisfying the Artin relations.
-/

noncomputable section

open Matrix Real
open scoped BigOperators

namespace InfoGeometry.GrandUnification.BraidCliffordIntegration

abbrev M4R := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ

/-- Imported two-atom parity channel from the Fibonacci--Clifford bridge. -/
def localTwoAtomParity : M4R :=
  InfoGeometry.GrandUnification.FibonacciCliffordBridge.twoAtomParity

/-- Square-one property of the imported two-atom parity channel. -/
theorem localTwoAtomParity_sq : localTwoAtomParity * localTwoAtomParity = (1 : M4R) := by
  exact InfoGeometry.GrandUnification.FibonacciCliffordBridge.twoAtomParity_sq

/-- Elementary Artin moves for the infinite braid skeleton. -/
inductive ArtinMove : List ℕ → List ℕ → Prop
  | adjacent (i : ℕ) :
      ArtinMove [i, i + 1, i] [i + 1, i, i + 1]
  | adjacent_symm (i : ℕ) :
      ArtinMove [i + 1, i, i + 1] [i, i + 1, i]
  | separated (i j : ℕ) (h : i + 2 ≤ j) :
      ArtinMove [i, j] [j, i]
  | separated_symm (i j : ℕ) (h : i + 2 ≤ j) :
      ArtinMove [j, i] [i, j]

/-- Artin moves preserve braid-word length. -/
theorem ArtinMove.length_eq {u v : List ℕ} (h : ArtinMove u v) :
    u.length = v.length := by
  cases h <;> rfl

/-- Uniform Clifford-atom amplitude attached to a braid word. -/
def uniformCliffordAmplitude (q : ℝ) (w : List ℕ) : ℝ :=
  q ^ w.length

/-- Uniform amplitude is invariant under elementary Artin moves. -/
theorem artinMove_preserves_uniformCliffordAmplitude
    {u v : List ℕ} (h : ArtinMove u v) (q : ℝ) :
    uniformCliffordAmplitude q u = uniformCliffordAmplitude q v := by
  simp [uniformCliffordAmplitude, h.length_eq]

/-- The local pure-squeeze Witten weight of one Clifford atom. -/
def atomWittenWeight (α : ℝ) : ℝ :=
  2 * Real.sinh α

/-- Braid word interpreted as a uniform tensor product of identical Clifford atoms. -/
def braidWordWittenWeight (α : ℝ) (w : List ℕ) : ℝ :=
  uniformCliffordAmplitude (atomWittenWeight α) w

/-- The Witten weight of a uniform Clifford braid word is Artin-invariant. -/
theorem artinMove_preserves_braidWordWittenWeight
    {u v : List ℕ} (h : ArtinMove u v) (α : ℝ) :
    braidWordWittenWeight α u = braidWordWittenWeight α v := by
  exact artinMove_preserves_uniformCliffordAmplitude h (atomWittenWeight α)

/-- Degenerate local Clifford representation of each braid generator by two-atom parity. -/
def cliffordBraidGate (_i : ℕ) : M4R :=
  localTwoAtomParity

/-- The two-atom parity gate is tripotent. -/
theorem cliffordBraidGate_cubed (i : ℕ) :
    cliffordBraidGate i * cliffordBraidGate i * cliffordBraidGate i = cliffordBraidGate i := by
  calc
    cliffordBraidGate i * cliffordBraidGate i * cliffordBraidGate i
        = (cliffordBraidGate i * cliffordBraidGate i) * cliffordBraidGate i := by
          simp [mul_assoc]
    _ = (1 : M4R) * cliffordBraidGate i := by
          rw [show cliffordBraidGate i * cliffordBraidGate i = (1 : M4R) by
            simp [cliffordBraidGate, localTwoAtomParity_sq]]
    _ = cliffordBraidGate i := by simp

/-- Adjacent Artin relation under the local two-atom parity representation. -/
theorem clifford_adjacent_artin (i : ℕ) :
    cliffordBraidGate i * cliffordBraidGate (i + 1) * cliffordBraidGate i =
      cliffordBraidGate (i + 1) * cliffordBraidGate i * cliffordBraidGate (i + 1) := by
  simp [cliffordBraidGate]

/-- Separated Artin commutation under the local two-atom parity representation. -/
theorem clifford_separated_artin (i j : ℕ) :
    cliffordBraidGate i * cliffordBraidGate j = cliffordBraidGate j * cliffordBraidGate i := by
  simp [cliffordBraidGate]

/-- Finite-stage inclusion into the infinite braid boundary. -/
def finiteToInfinite {n : ℕ} (i : Fin n) : ℕ := i.1

/-- Successor inclusion preserves the infinite boundary generator. -/
theorem finiteToInfinite_castSucc {n : ℕ} (i : Fin n) :
    finiteToInfinite (Fin.castSucc i) = finiteToInfinite i := by
  rfl

/-- Finite adjacent relation embeds as infinite adjacent relation. -/
theorem finite_adjacent_to_infinite {n : ℕ} {i j : Fin n}
    (h : i.1 + 1 = j.1) :
    finiteToInfinite i + 1 = finiteToInfinite j := h

end InfoGeometry.GrandUnification.BraidCliffordIntegration

end noncomputable section

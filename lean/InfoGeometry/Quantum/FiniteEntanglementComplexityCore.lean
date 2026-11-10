/-
InfoGeometry/Quantum/FiniteEntanglementComplexityCore.lean

Finite quantum-information anchors for the ER/EPR and complexity branches.

This file does not prove ER = EPR.
It does not prove complexity = wormhole volume.
It does not assert black-hole geometry.

It kills the finite shadows first:

* Bell support correlations are explicit finite amplitude facts.
* GHZ support correlations are explicit finite amplitude facts.
* A measurement/copy register transforms Bell support into GHZ support.
* Classical single-flip complexity is the Hamming weight and is bounded by `n`.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Quantum.FiniteEntanglementComplexityCore

/-! ## 1. Bits and finite amplitudes -/

/-- A computational bit. -/
abbrev Bit : Type :=
  Bool

/-- Two-qubit amplitude table. -/
abbrev TwoQubitAmplitude : Type :=
  Bit × Bit → ℂ

/-- A three-bit/qubit index. -/
structure TripleBit where
  a : Bit
  b : Bit
  c : Bit
deriving DecidableEq, Repr

/-- Three-qubit amplitude table. -/
abbrev ThreeQubitAmplitude : Type :=
  TripleBit → ℂ

/-! ## 2. Bell support patterns -/

/--
Unnormalized Bell-same amplitude.

Support: `00` and `11`.
-/
def bellSameAmplitude : TwoQubitAmplitude :=
  fun x => if x.1 = x.2 then 1 else 0

/--
Unnormalized Bell-opposite amplitude.

Support: `01` and `10`.
-/
def bellOppAmplitude : TwoQubitAmplitude :=
  fun x => if x.2 = !x.1 then 1 else 0

/-- The Bell-same amplitude is nonzero exactly on equal bits. -/
theorem bellSame_nonzero_iff
    (x : Bit × Bit) :
    bellSameAmplitude x ≠ 0 ↔ x.1 = x.2 := by
  unfold bellSameAmplitude
  by_cases h : x.1 = x.2
  · simp [h]
  · simp [h]

/-- The Bell-opposite amplitude is nonzero exactly on opposite bits. -/
theorem bellOpp_nonzero_iff
    (x : Bit × Bit) :
    bellOppAmplitude x ≠ 0 ↔ x.2 = !x.1 := by
  unfold bellOppAmplitude
  by_cases h : x.2 = !x.1
  · simp [h]
  · simp [h]

/-- On Bell-same support, the second bit is determined by the first. -/
theorem bellSame_second_eq_first
    {x : Bit × Bit}
    (h : bellSameAmplitude x ≠ 0) :
    x.2 = x.1 := by
  exact (bellSame_nonzero_iff x).mp h |>.symm

/-- On Bell-opposite support, the second bit is the Boolean complement of the first. -/
theorem bellOpp_second_eq_not_first
    {x : Bit × Bit}
    (h : bellOppAmplitude x ≠ 0) :
    x.2 = !x.1 :=
  (bellOpp_nonzero_iff x).mp h

/-! ## 3. GHZ support pattern -/

/--
Unnormalized GHZ amplitude.

Support: `000` and `111`.
-/
def ghzAmplitude : ThreeQubitAmplitude :=
  fun x =>
    if x.a = x.b ∧ x.b = x.c then 1 else 0

/-- The GHZ amplitude is nonzero exactly when all three bits are equal. -/
theorem ghz_nonzero_iff
    (x : TripleBit) :
    ghzAmplitude x ≠ 0 ↔ x.a = x.b ∧ x.b = x.c := by
  unfold ghzAmplitude
  by_cases h : x.a = x.b ∧ x.b = x.c
  · simp [h]
  · simp [h]

/-- On GHZ support, `a = b`. -/
theorem ghz_a_eq_b
    {x : TripleBit}
    (h : ghzAmplitude x ≠ 0) :
    x.a = x.b :=
  (ghz_nonzero_iff x).mp h |>.1

/-- On GHZ support, `b = c`. -/
theorem ghz_b_eq_c
    {x : TripleBit}
    (h : ghzAmplitude x ≠ 0) :
    x.b = x.c :=
  (ghz_nonzero_iff x).mp h |>.2

/-- On GHZ support, `a = c`. -/
theorem ghz_a_eq_c
    {x : TripleBit}
    (h : ghzAmplitude x ≠ 0) :
    x.a = x.c := by
  exact Eq.trans (ghz_a_eq_b h) (ghz_b_eq_c h)

/-! ## 4. Measurement/copy register: Bell to GHZ support -/

/--
Copy Bob's bit into Charlie's register.

This is a finite support-level model of a classical measurement register.
No claim about density matrices or quantum measurement theory is made here.
-/
def copyBobToCharlie
    (x : Bit × Bit) : TripleBit where
  a := x.1
  b := x.2
  c := x.2

/-- Copying the second bit preserves support exactly: the copied triple is
GHZ-supported precisely when the original pair is Bell-same-supported. -/
theorem copyBobToCharlie_support_iff
    (x : Bit × Bit) :
    ghzAmplitude (copyBobToCharlie x) ≠ 0 ↔ bellSameAmplitude x ≠ 0 := by
  rw [ghz_nonzero_iff, bellSame_nonzero_iff]
  simp [copyBobToCharlie]

/-- If the copied state is GHZ-supported, Alice equals Charlie. -/
theorem copyBobToCharlie_GHZ_a_eq_c
    {x : Bit × Bit}
    (h : ghzAmplitude (copyBobToCharlie x) ≠ 0) :
    (copyBobToCharlie x).a = (copyBobToCharlie x).c :=
  ghz_a_eq_c h

/-! ## 5. Classical single-flip complexity anchor -/

/-- A classical `n`-bit string. -/
abbrev BitString
    (n : ℕ) : Type :=
  Fin n → Bool

/-- The simple all-false bit string. -/
def simpleString
    {n : ℕ} : BitString n :=
  fun _ => false

/-- Hamming weight: number of true bits. -/
def hammingWeight
    {n : ℕ}
    (s : BitString n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => s i = true)).card

/-- The simple string has Hamming weight zero. -/
@[simp]
theorem hammingWeight_simpleString
    {n : ℕ} :
    hammingWeight (simpleString : BitString n) = 0 := by
  simp [hammingWeight, simpleString]

/-- Hamming weight is bounded by the number of bits. -/
theorem hammingWeight_le
    {n : ℕ}
    (s : BitString n) :
    hammingWeight s ≤ n := by
  have h :
      (Finset.univ.filter (fun i : Fin n => s i = true)).card
        ≤ (Finset.univ : Finset (Fin n)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  simpa [hammingWeight] using h

/-- Flip one bit. -/
def flipAt
    {n : ℕ}
    (s : BitString n)
    (i : Fin n) : BitString n :=
  fun j => if j = i then !s j else s j

/-- Flipping one bit of the simple string gives Hamming weight one. -/
theorem hammingWeight_flipAt_simpleString
    {n : ℕ}
    (i : Fin n) :
    hammingWeight (flipAt (simpleString : BitString n) i) = 1 := by
  have hset :
      Finset.univ.filter
          (fun j : Fin n =>
            flipAt (simpleString : BitString n) i j = true)
        =
      ({i} : Finset (Fin n)) := by
    ext j
    by_cases hji : j = i
    · simp [flipAt, simpleString, hji]
    · simp [flipAt, simpleString, hji]
  simp [hammingWeight, hset]

/--
Classical single-flip complexity is represented here by Hamming weight.

This is not a theorem about quantum circuit complexity. It is the finite
classical anchor from which the quantum circuit layer must later diverge.
-/
def classicalSingleFlipComplexity
    {n : ℕ}
    (s : BitString n) : ℕ :=
  hammingWeight s

/-- Classical single-flip complexity is bounded by the number of bits. -/
theorem classicalSingleFlipComplexity_le
    {n : ℕ}
    (s : BitString n) :
    classicalSingleFlipComplexity s ≤ n :=
  hammingWeight_le s

/-! ## 6. Finite quantum circuit gate accounting -/

universe u

/--
A finite gate acts on one or two wires.

No unitary semantics are asserted here. This is only the finite accounting
substrate for later circuit-complexity witnesses.
-/
inductive Gate
    (Wire : Type u) : Type u where
  /-- A one-wire gate. -/
  | one : Wire → Gate Wire

  /-- A two-wire gate. -/
  | two : Wire → Wire → Gate Wire
deriving Repr

/--
A finite circuit is a list of gates.
-/
abbrev Circuit
    (Wire : Type u) : Type u :=
  List (Gate Wire)

namespace Circuit

variable {Wire : Type u}

/--
Finite circuit cost: the number of gates in the explicit list.
-/
def cost
    (C : Circuit Wire) : ℕ :=
  C.length

/--
The empty circuit has zero cost.
-/
@[simp]
theorem cost_nil :
    cost ([] : Circuit Wire) = 0 :=
  rfl

/--
A one-gate circuit has cost one.
-/
@[simp]
theorem cost_singleton
    (g : Gate Wire) :
    cost ([g] : Circuit Wire) = 1 :=
  rfl

/--
Appending a gate increases cost by one.
-/
theorem cost_append_gate
    (C : Circuit Wire)
    (g : Gate Wire) :
    cost (C ++ [g]) = cost C + 1 := by
  simp [cost]

/--
Circuit cost is additive under concatenation.
-/
theorem cost_append
    (C₁ C₂ : Circuit Wire) :
    cost (C₁ ++ C₂) = cost C₁ + cost C₂ := by
  simp [cost]

/--
A nonempty circuit has positive cost.
-/
theorem cost_pos_of_ne_nil
    {C : Circuit Wire}
    (hC : C ≠ []) :
    0 < cost C := by
  cases C with
  | nil =>
      exact False.elim (hC rfl)
  | cons _ _ =>
      simp [cost]

end Circuit

/-! ## 7. Derived finite support and circuit-cost consequences -/

/-- The copy-register map retains both input bits and is therefore injective. -/
theorem copyBobToCharlie_injective
    {x y : Bit × Bit}
    (h : copyBobToCharlie x = copyBobToCharlie y) :
    x = y := by
  have ha := congrArg (fun z : TripleBit => z.a) h
  have hb := congrArg (fun z : TripleBit => z.b) h
  cases x with
  | mk xa xb =>
    cases y with
    | mk ya yb =>
      change xa = ya at ha
      change xb = yb at hb
      subst ya
      subst yb
      rfl

/-- Appending a circuit cannot reduce its gate cost. -/
theorem Circuit.cost_le_append_right
    {Wire : Type*}
    (C D : Circuit Wire) :
    Circuit.cost C ≤ Circuit.cost (C ++ D) := by
  rw [Circuit.cost_append]
  omega

/-- Appending a nonempty circuit strictly increases the gate cost. -/
theorem Circuit.cost_lt_append_of_ne_nil
    {Wire : Type*}
    (C : Circuit Wire)
    {D : Circuit Wire}
    (hD : D ≠ []) :
    Circuit.cost C < Circuit.cost (C ++ D) := by
  rw [Circuit.cost_append]
  have hpos := Circuit.cost_pos_of_ne_nil hD
  omega

end InfoGeometry.Quantum.FiniteEntanglementComplexityCore

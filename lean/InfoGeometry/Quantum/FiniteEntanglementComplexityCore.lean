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
import InfoGeometry.Meta.OwnerTarget

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

/-- A Bell-same support element copied into Charlie's register lands on GHZ support. -/
theorem copyBellSame_to_GHZ
    {x : Bit × Bit}
    (h : bellSameAmplitude x ≠ 0) :
    ghzAmplitude (copyBobToCharlie x) ≠ 0 := by
  apply (ghz_nonzero_iff (copyBobToCharlie x)).mpr
  constructor
  · exact (bellSame_nonzero_iff x).mp h
  · rfl

/-- The copied register has Bob and Charlie equal by construction. -/
theorem copyBobToCharlie_b_eq_c
    (x : Bit × Bit) :
    (copyBobToCharlie x).b = (copyBobToCharlie x).c :=
  rfl

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

/-- The simple state has zero classical single-flip complexity. -/
@[simp]
theorem classicalSingleFlipComplexity_simple
    {n : ℕ} :
    classicalSingleFlipComplexity (simpleString : BitString n) = 0 := by
  simp [classicalSingleFlipComplexity]

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

/--
Cost is bounded by an explicit list length exactly because it is that length.
-/
theorem cost_eq_length
    (C : Circuit Wire) :
    cost C = C.length :=
  rfl

end Circuit

/-! ## 7. Owner theorems discharged constructively -/

/-- Constructive proof of Bell-same support correlation. -/
theorem bellSameSupportOwnerTarget :
    ∀ x : Bit × Bit,
      bellSameAmplitude x ≠ 0 ↔ x.1 = x.2 :=
  bellSame_nonzero_iff

/-- Constructive proof of GHZ support correlation. -/
theorem ghzSupportOwnerTarget :
    ∀ x : TripleBit,
      ghzAmplitude x ≠ 0 ↔ x.a = x.b ∧ x.b = x.c :=
  ghz_nonzero_iff

/-- Constructive proof of the finite Bell-to-GHZ support transition. -/
theorem bellToGHZCopyOwnerTarget :
    ∀ x : Bit × Bit,
      bellSameAmplitude x ≠ 0 →
        ghzAmplitude (copyBobToCharlie x) ≠ 0 := by
  intro x h
  exact copyBellSame_to_GHZ h

/-- Constructive proof of the classical single-flip complexity bound. -/
theorem classicalSingleFlipComplexityOwnerTarget :
    ∀ (n : ℕ) (s : BitString n),
      classicalSingleFlipComplexity s ≤ n := by
  intro n s
  exact classicalSingleFlipComplexity_le s

/--
Constructive proof of finite circuit gate-accounting additivity.
-/
theorem circuitCostAppendOwnerTarget :
    ∀ (Wire : Type*) (C₁ C₂ : Circuit Wire),
      Circuit.cost (C₁ ++ C₂) =
        Circuit.cost C₁ + Circuit.cost C₂ := by
  intro Wire C₁ C₂
  exact Circuit.cost_append C₁ C₂

@[owner_target_tag]
theorem finiteEntanglementComplexity_packet :
    (∀ x : Bit × Bit, bellSameAmplitude x ≠ 0 ↔ x.1 = x.2) ∧
      (∀ x : TripleBit, ghzAmplitude x ≠ 0 ↔ x.a = x.b ∧ x.b = x.c) ∧
      (∀ x : Bit × Bit, bellSameAmplitude x ≠ 0 →
        ghzAmplitude (copyBobToCharlie x) ≠ 0) ∧
      (∀ (n : ℕ) (s : BitString n), classicalSingleFlipComplexity s ≤ n) ∧
      (∀ (Wire : Type*) (C₁ C₂ : Circuit Wire),
        Circuit.cost (C₁ ++ C₂) =
          Circuit.cost C₁ + Circuit.cost C₂) := by
  exact ⟨bellSameSupportOwnerTarget,
    ghzSupportOwnerTarget,
    bellToGHZCopyOwnerTarget,
    classicalSingleFlipComplexityOwnerTarget,
    circuitCostAppendOwnerTarget⟩

end InfoGeometry.Quantum.FiniteEntanglementComplexityCore

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11KleinTwist
import Mathlib.Data.Fintype.Sum

/-!
# Recursive split Clifford generator families over a noncommutative ring

The doubling operation adjoins one positive and one negative generator and
inserts the Klein factor into every old generator. Its pairwise theorem is
valid for any index type. Iteration constructs all `2n` signed generators in
the full nested matrix ring over the original coefficient ring.

These are explicit representation relations. An isomorphism with a native
Clifford algebra is a separate statement, proved over real quadratic modules
in `Cl11GradedTensorUntwist`.
-/

namespace InfoGeometry.Clifford.Cl11BrauerWeylGenerators

open SplitAtomDoubling

variable {A : Type*} [Ring A] {ι : Type*}

/-- Adjoin the two outer split generators and twist every inner generator. -/
def doubleGenerator (e : ι → A) : Bool ⊕ ι → Block2 A
  | .inl false => positive
  | .inl true => omega
  | .inr i => twisted (e i)

/-- `true` marks a negative-square generator. -/
def doubleSign (s : ι → Bool) : Bool ⊕ ι → Bool
  | .inl b => b
  | .inr i => s i

theorem doubleGenerator_square (e : ι → A) (s : ι → Bool)
    (hsq : ∀ i, e i * e i = if s i then -1 else 1) (i : Bool ⊕ ι) :
    doubleGenerator e i * doubleGenerator e i =
      if doubleSign s i then -1 else 1 := by
  rcases i with b | i
  · cases b <;> simp [doubleGenerator, doubleSign]
  · change twisted (e i) * twisted (e i) = if s i then -1 else 1
    rw [twisted_mul, hsq]
    cases s i <;> simp

theorem doubleGenerator_pairwise (e : ι → A)
    (hanti : Pairwise fun i j => e i * e j + e j * e i = 0) :
    Pairwise fun i j =>
      doubleGenerator e i * doubleGenerator e j +
        doubleGenerator e j * doubleGenerator e i = 0 := by
  intro i j hij
  rcases i with b | i <;> rcases j with c | j
  · cases b <;> cases c
    · exact False.elim (hij rfl)
    · exact positive_omega_anticommutator
    · simpa [doubleGenerator, add_comm] using
        (positive_omega_anticommutator (A := A))
    · exact False.elim (hij rfl)
  · cases b
    · simpa [doubleGenerator, add_comm] using twisted_positive_anticommutator (e j)
    · simpa [doubleGenerator, add_comm] using twisted_omega_anticommutator (e j)
  · cases c
    · exact twisted_positive_anticommutator (e i)
    · exact twisted_omega_anticommutator (e i)
  · change twisted (e i) * twisted (e j) + twisted (e j) * twisted (e i) = 0
    rw [twisted_anticommutator, hanti (fun h => hij (congrArg Sum.inr h)), repeated_zero]

/-- Full nested block rings; the coefficient ring is retained at every stage. -/
def Nested (A : Type*) : ℕ → Type _ :=
  Nat.rec A (fun _ T => Block2 T)

instance nestedRing (A : Type*) [Ring A] : (n : ℕ) → Ring (Nested A n) :=
  Nat.rec (motive := fun n => Ring (Nested A n))
    (inferInstanceAs (Ring A))
    (fun n ih =>
      let _ : Ring (Nested A n) := ih
      inferInstanceAs (Ring (Block2 (Nested A n))))

/-- A structural index for the two generators adjoined at each step. -/
def GeneratorIndex : ℕ → Type :=
  Nat.rec Empty (fun _ I => Bool ⊕ I)

instance generatorIndexFintype : (n : ℕ) → Fintype (GeneratorIndex n) :=
  Nat.rec (motive := fun n => Fintype (GeneratorIndex n))
    (inferInstanceAs (Fintype Empty))
    (fun n ih =>
      let _ : Fintype (GeneratorIndex n) := ih
      inferInstanceAs (Fintype (Bool ⊕ GeneratorIndex n)))

theorem generatorIndex_card (n : ℕ) : Fintype.card (GeneratorIndex n) = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Fintype.card (Bool ⊕ GeneratorIndex n) = 2 * (n + 1)
      rw [Fintype.card_sum, Fintype.card_bool, ih]
      omega

/-- The recursively propagated split signs. -/
def generatorSign : (n : ℕ) → GeneratorIndex n → Bool :=
  Nat.rec (motive := fun n => GeneratorIndex n → Bool)
    (fun i => Empty.elim i) (fun _ previous => doubleSign previous)

/-- The recursive Jordan–Wigner family in full nested operator matrices. -/
def generator (A : Type*) [Ring A] : (n : ℕ) → GeneratorIndex n → Nested A n :=
  Nat.rec (motive := fun n => GeneratorIndex n → Nested A n)
    (fun i => Empty.elim i)
    (fun n previous =>
      @doubleGenerator (Nested A n) (nestedRing A n) (GeneratorIndex n) previous)

theorem generator_square (n : ℕ) (i : GeneratorIndex n) :
    generator A n i * generator A n i = if generatorSign n i then -1 else 1 := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
      exact doubleGenerator_square (generator A n) (generatorSign n) ih i

theorem generator_pairwise (n : ℕ) :
    Pairwise fun i j => generator A n i * generator A n j +
      generator A n j * generator A n i = 0 := by
  induction n with
  | zero => intro i; exact Empty.elim i
  | succ n ih => exact doubleGenerator_pairwise (generator A n) ih

/-- At the second stage, inner generators carry the outer chirality factor. -/
theorem generator_two_inner (b : Bool) :
    generator A 2 (.inr (.inl b)) =
      twisted (if b then (omega : Block2 A) else positive) := by
  cases b <;> rfl

end InfoGeometry.Clifford.Cl11BrauerWeylGenerators

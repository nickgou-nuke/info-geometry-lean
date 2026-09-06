import Mathlib

/-!
# Finite Prime Fock Cutoff

This file proves the finite algebraic layer behind the arithmetic Fock
dictionary.

For a finite list of prime-mode weights `xᵢ = pᵢ^{-s}`:

* ordinary fermion occupation `kᵢ ∈ {0,1}` gives local factor `1 + xᵢ`;
* parity insertion `(-1)^F` gives local factor `1 - xᵢ`;
* bosonic occupation `kᵢ ∈ ℕ` is represented by the local reciprocal
  `(1 - xᵢ)⁻¹`;
* the finite bosonic determinant cancels the finite graded superdeterminant
  away from local singular factors.

This is the finite cutoff theorem.  The infinite Euler product and analytic
continuation are separate analytic tasks.
-/

noncomputable section

namespace FinitePrimeFock

/-- One prime mode with formal Dirichlet weight `x = p^{-s}`. -/
structure PrimeMode where
  p : ℕ
  isPrime : Nat.Prime p
  weight : ℂ

/-- Local ordinary fermion factor: empty plus occupied. -/
def ordinaryFermionLocal (x : ℂ) : ℂ :=
  1 + x

/-- Local graded fermion factor: empty minus occupied. -/
def gradedFermionLocal (x : ℂ) : ℂ :=
  1 - x

/-- Local boson factor, encoded as the reciprocal determinant. -/
def bosonLocal (x : ℂ) : ℂ :=
  (1 - x)⁻¹

/-- Finite ordinary fermion Fock trace over a cutoff list of weights. -/
def ordinaryFermionTrace (xs : List ℂ) : ℂ :=
  xs.map ordinaryFermionLocal |>.prod

/-- Finite graded Fock supertrace over a cutoff list of weights. -/
def gradedFockSupertrace (xs : List ℂ) : ℂ :=
  xs.map gradedFermionLocal |>.prod

/-- Finite bosonic reciprocal determinant over a cutoff list of weights. -/
def bosonicFockDeterminant (xs : List ℂ) : ℂ :=
  xs.map bosonLocal |>.prod

theorem ordinaryFermionTrace_nil :
    ordinaryFermionTrace [] = 1 := by
  rfl

theorem gradedFockSupertrace_nil :
    gradedFockSupertrace [] = 1 := by
  rfl

theorem bosonicFockDeterminant_nil :
    bosonicFockDeterminant [] = 1 := by
  rfl

theorem ordinaryFermionTrace_cons (x : ℂ) (xs : List ℂ) :
    ordinaryFermionTrace (x :: xs) =
      (1 + x) * ordinaryFermionTrace xs := by
  rfl

theorem gradedFockSupertrace_cons (x : ℂ) (xs : List ℂ) :
    gradedFockSupertrace (x :: xs) =
      (1 - x) * gradedFockSupertrace xs := by
  rfl

theorem bosonicFockDeterminant_cons (x : ℂ) (xs : List ℂ) :
    bosonicFockDeterminant (x :: xs) =
      (1 - x)⁻¹ * bosonicFockDeterminant xs := by
  rfl

/-- One-mode parity trace: empty state minus occupied state. -/
theorem one_mode_graded_supertrace (x : ℂ) :
    1 + (-x) = gradedFermionLocal x := by
  simp [gradedFermionLocal]
  ring

/-- Two-mode graded Fock expansion. -/
theorem two_mode_graded_supertrace (x y : ℂ) :
    gradedFockSupertrace [x, y] = 1 - x - y + x * y := by
  simp [gradedFockSupertrace, gradedFermionLocal]
  ring

/-- Three-mode graded Fock expansion: even occupations minus odd occupations. -/
theorem three_mode_graded_supertrace (x y z : ℂ) :
    gradedFockSupertrace [x, y, z] =
      1 - (x + y + z) + (x * y + x * z + y * z) - x * y * z := by
  simp [gradedFockSupertrace, gradedFermionLocal]
  ring

/-- One-mode ordinary fermion trace: empty plus occupied. -/
theorem one_mode_ordinary_trace (x : ℂ) :
    ordinaryFermionTrace [x] = 1 + x := by
  simp [ordinaryFermionTrace, ordinaryFermionLocal]

/-- Two-mode ordinary fermion expansion. -/
theorem two_mode_ordinary_trace (x y : ℂ) :
    ordinaryFermionTrace [x, y] = 1 + x + y + x * y := by
  simp [ordinaryFermionTrace, ordinaryFermionLocal]
  ring

/-- A single bosonic reciprocal determinant cancels the graded local factor. -/
theorem local_boson_cancels_graded {x : ℂ} (hx : x ≠ 1) :
    bosonLocal x * gradedFermionLocal x = 1 := by
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  simp [bosonLocal, gradedFermionLocal, hden]

/-- Finite cutoff cancellation over a list of nonsingular local weights. -/
theorem finite_boson_cancels_graded
    (xs : List ℂ) (hxs : ∀ x ∈ xs, x ≠ 1) :
    bosonicFockDeterminant xs * gradedFockSupertrace xs = 1 := by
  induction xs with
  | nil =>
      simp [bosonicFockDeterminant, gradedFockSupertrace]
  | cons x xs ih =>
      have hx : x ≠ 1 := hxs x (by simp)
      have htail : ∀ y ∈ xs, y ≠ 1 := by
        intro y hy
        exact hxs y (by simp [hy])
      calc
        bosonicFockDeterminant (x :: xs) * gradedFockSupertrace (x :: xs)
            =
          ((1 - x)⁻¹ * bosonicFockDeterminant xs) *
            ((1 - x) * gradedFockSupertrace xs) := by
              rfl
        _ =
          ((1 - x)⁻¹ * (1 - x)) *
            (bosonicFockDeterminant xs * gradedFockSupertrace xs) := by
              ring
        _ = 1 * 1 := by
              rw [ih htail]
              exact congrArg (fun a => a * 1) (by
                have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
                simp [hden])
        _ = 1 := by ring

/-- Finite prime cutoff uses the mode weights only. -/
def weightsOfModes (modes : List PrimeMode) : List ℂ :=
  modes.map (fun mode => mode.weight)

def finitePrimeGradedIndex (modes : List PrimeMode) : ℂ :=
  gradedFockSupertrace (weightsOfModes modes)

def finitePrimeBosonicPartition (modes : List PrimeMode) : ℂ :=
  bosonicFockDeterminant (weightsOfModes modes)

theorem finite_prime_boson_cancels_graded
    (modes : List PrimeMode)
    (h : ∀ mode ∈ modes, mode.weight ≠ 1) :
    finitePrimeBosonicPartition modes * finitePrimeGradedIndex modes = 1 := by
  unfold finitePrimeBosonicPartition finitePrimeGradedIndex weightsOfModes
  apply finite_boson_cancels_graded
  intro x hx
  rcases List.mem_map.mp hx with ⟨mode, hmode, hweight⟩
  rw [← hweight]
  exact h mode hmode

/--
Finite Fock synthesis: local parity factors, finite determinant cancellation,
and the three-prime even-minus-odd expansion.
-/
theorem finite_prime_fock_synthesis :
    (∀ x : ℂ, 1 + (-x) = gradedFermionLocal x) ∧
    (∀ x y z : ℂ,
      gradedFockSupertrace [x, y, z] =
        1 - (x + y + z) + (x * y + x * z + y * z) - x * y * z) ∧
    (∀ x : ℂ, x ≠ 1 → bosonLocal x * gradedFermionLocal x = 1) ∧
    (∀ xs : List ℂ, (∀ x ∈ xs, x ≠ 1) →
      bosonicFockDeterminant xs * gradedFockSupertrace xs = 1) ∧
    (∀ modes : List PrimeMode, (∀ mode ∈ modes, mode.weight ≠ 1) →
      finitePrimeBosonicPartition modes * finitePrimeGradedIndex modes = 1) := by
  exact ⟨one_mode_graded_supertrace,
    three_mode_graded_supertrace,
    fun x hx => local_boson_cancels_graded hx,
    finite_boson_cancels_graded,
    finite_prime_boson_cancels_graded⟩

end FinitePrimeFock

end noncomputable section

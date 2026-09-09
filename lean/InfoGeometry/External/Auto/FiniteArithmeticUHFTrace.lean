import Mathlib.Tactic

/-!
# Finite Arithmetic UHF Trace

This layer attaches the finite UHF Boolean trace to arithmetic prime modes.

For a finite cutoff list `modes : List ℕ` and an abstract Dirichlet weight
`weight : ℕ → ℂ`, the finite arithmetic supertrace is

`Trace(modes) = finiteBooleanTrace (modes.map weight)`.

When `weight p` is later specialized to `p^{-s}`, this is the finite Euler
superdeterminant `∏_{p in modes} (1 - p^{-s})`.  No infinite product or
analytic continuation is asserted here.
-/

noncomputable section

namespace FiniteArithmeticUHFTrace

/-- Local graded boundary selector: empty bit gives `1`, occupied bit gives `-x`. -/
def gradedBitSelector (bit : Bool) (x : ℂ) : ℂ :=
  if bit then -x else 1

/-- Recursive finite Boolean trace over UHF diagonal bits. -/
def finiteBooleanTrace : List ℂ → ℂ
  | [] => 1
  | x :: xs => finiteBooleanTrace xs + (-x) * finiteBooleanTrace xs

/-- Finite graded product/determinant. -/
def gradedProduct (xs : List ℂ) : ℂ :=
  xs.map (fun x => 1 - x) |>.prod

theorem finiteBooleanTrace_eq_gradedProduct (xs : List ℂ) :
    finiteBooleanTrace xs = gradedProduct xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [finiteBooleanTrace, gradedProduct, ih]
      ring

theorem finiteBooleanTrace_snoc (xs : List ℂ) (x : ℂ) :
    finiteBooleanTrace (xs ++ [x]) =
      finiteBooleanTrace xs * (1 - x) := by
  rw [finiteBooleanTrace_eq_gradedProduct xs]
  rw [finiteBooleanTrace_eq_gradedProduct (xs ++ [x])]
  induction xs with
  | nil =>
      simp [gradedProduct]
  | cons y ys ih =>
      simp [gradedProduct]
      ring

/-- A finite prime/arithmetic cutoff with an abstract complex weight. -/
def finiteArithmeticSupertrace (weight : ℕ → ℂ) (modes : List ℕ) : ℂ :=
  finiteBooleanTrace (modes.map weight)

/-- The matching finite Euler superdeterminant. -/
def finiteEulerSuperdeterminant (weight : ℕ → ℂ) (modes : List ℕ) : ℂ :=
  gradedProduct (modes.map weight)

theorem finiteArithmeticSupertrace_eq_euler
    (weight : ℕ → ℂ) (modes : List ℕ) :
    finiteArithmeticSupertrace weight modes =
      finiteEulerSuperdeterminant weight modes := by
  simp [finiteArithmeticSupertrace, finiteEulerSuperdeterminant,
    finiteBooleanTrace_eq_gradedProduct]

theorem finiteArithmeticSupertrace_snoc
    (weight : ℕ → ℂ) (modes : List ℕ) (p : ℕ) :
    finiteArithmeticSupertrace weight (modes ++ [p]) =
      finiteArithmeticSupertrace weight modes * (1 - weight p) := by
  simp [finiteArithmeticSupertrace, List.map_append, finiteBooleanTrace_snoc]

/-- Occupied-prime product for a Boolean word over a cutoff list. -/
def occupiedInteger : List ℕ → List Bool → ℕ
  | [], _ => 1
  | _, [] => 1
  | p :: ps, bit :: bits =>
      (if bit then p else 1) * occupiedInteger ps bits

/-- Number of occupied modes in a Boolean word. -/
def occupationNumber : List Bool → ℕ
  | [] => 0
  | bit :: bits => (if bit then 1 else 0) + occupationNumber bits

/-- Finite Mobius/Fock parity of a Boolean word. -/
def wordParity (bits : List Bool) : ℂ :=
  (-1 : ℂ) ^ occupationNumber bits

theorem occupiedInteger_nil_modes (bits : List Bool) :
    occupiedInteger [] bits = 1 := by
  cases bits <;> rfl

theorem occupiedInteger_nil_bits (modes : List ℕ) :
    occupiedInteger modes [] = 1 := by
  cases modes <;> rfl

theorem occupiedInteger_cons_false (p : ℕ) (ps : List ℕ) (bits : List Bool) :
    occupiedInteger (p :: ps) (false :: bits) =
      occupiedInteger ps bits := by
  simp [occupiedInteger]

theorem occupiedInteger_cons_true (p : ℕ) (ps : List ℕ) (bits : List Bool) :
    occupiedInteger (p :: ps) (true :: bits) =
      p * occupiedInteger ps bits := by
  simp [occupiedInteger]

theorem occupationNumber_cons_false (bits : List Bool) :
    occupationNumber (false :: bits) = occupationNumber bits := by
  simp [occupationNumber]

theorem occupationNumber_cons_true (bits : List Bool) :
    occupationNumber (true :: bits) = occupationNumber bits + 1 := by
  simp [occupationNumber]
  omega

theorem wordParity_cons_false (bits : List Bool) :
    wordParity (false :: bits) = wordParity bits := by
  simp [wordParity, occupationNumber]

theorem wordParity_cons_true (bits : List Bool) :
    wordParity (true :: bits) = -wordParity bits := by
  simp [wordParity, occupationNumber]
  rw [show (1 + occupationNumber bits) = occupationNumber bits + 1 by omega]
  simp [pow_succ]

/--
Consolidated arithmetic-UHF trace package:
the finite UHF Boolean trace over prime weights is exactly the finite Euler
superdeterminant, and appending a prime appends one graded Euler factor.
-/
theorem finite_arithmetic_uhf_trace_synthesis :
    (∀ weight : ℕ → ℂ, ∀ modes : List ℕ,
      finiteArithmeticSupertrace weight modes =
        finiteEulerSuperdeterminant weight modes) ∧
    (∀ weight : ℕ → ℂ, ∀ modes : List ℕ, ∀ p : ℕ,
      finiteArithmeticSupertrace weight (modes ++ [p]) =
        finiteArithmeticSupertrace weight modes * (1 - weight p)) ∧
    (∀ p : ℕ, ∀ ps : List ℕ, ∀ bits : List Bool,
      occupiedInteger (p :: ps) (false :: bits) = occupiedInteger ps bits) ∧
    (∀ p : ℕ, ∀ ps : List ℕ, ∀ bits : List Bool,
      occupiedInteger (p :: ps) (true :: bits) =
        p * occupiedInteger ps bits) ∧
    (∀ bits : List Bool, wordParity (false :: bits) = wordParity bits) ∧
    (∀ bits : List Bool, wordParity (true :: bits) = -wordParity bits) := by
  exact ⟨finiteArithmeticSupertrace_eq_euler,
    finiteArithmeticSupertrace_snoc,
    occupiedInteger_cons_false,
    occupiedInteger_cons_true,
    wordParity_cons_false,
    wordParity_cons_true⟩

end FiniteArithmeticUHFTrace

end noncomputable section

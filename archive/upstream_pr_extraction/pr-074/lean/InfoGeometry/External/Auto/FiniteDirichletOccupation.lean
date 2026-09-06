import Mathlib.Tactic

/-!
# Finite Dirichlet Occupation Bridge

This layer connects the UHF/Fock Boolean word to the arithmetic Dirichlet
monomial.

For a cutoff list of prime modes and a Boolean occupation word:

* `occupiedInteger modes bits` multiplies exactly the occupied modes;
* `selectedWeightProduct weight modes bits` multiplies the selected local
  weights;
* if `weight` is multiplicative, then the selected product is the weight of
  the occupied integer.

Specializing `weight n = n^{-s}` gives the finite Dirichlet monomials in the
Möbius supertrace.
-/

noncomputable section

namespace FiniteDirichletOccupation

/-- Occupied-prime product for a Boolean word over a cutoff list. -/
def occupiedInteger : List ℕ → List Bool → ℕ
  | [], _ => 1
  | _, [] => 1
  | p :: ps, bit :: bits =>
      (if bit then p else 1) * occupiedInteger ps bits

/-- Product of selected local weights along an occupation word. -/
def selectedWeightProduct (weight : ℕ → ℂ) : List ℕ → List Bool → ℂ
  | [], _ => 1
  | _, [] => 1
  | p :: ps, bit :: bits =>
      (if bit then weight p else 1) * selectedWeightProduct weight ps bits

/-- Number of occupied modes. -/
def occupationNumber : List Bool → ℕ
  | [] => 0
  | bit :: bits => (if bit then 1 else 0) + occupationNumber bits

/-- Finite Möbius/Fock parity of a Boolean word. -/
def wordParity (bits : List Bool) : ℂ :=
  (-1 : ℂ) ^ occupationNumber bits

theorem selectedWeightProduct_nil_modes
    (weight : ℕ → ℂ) (bits : List Bool) :
    selectedWeightProduct weight [] bits = 1 := by
  cases bits <;> rfl

theorem selectedWeightProduct_nil_bits
    (weight : ℕ → ℂ) (modes : List ℕ) :
    selectedWeightProduct weight modes [] = 1 := by
  cases modes <;> rfl

theorem selectedWeightProduct_cons_false
    (weight : ℕ → ℂ) (p : ℕ) (ps : List ℕ) (bits : List Bool) :
    selectedWeightProduct weight (p :: ps) (false :: bits) =
      selectedWeightProduct weight ps bits := by
  simp [selectedWeightProduct]

theorem selectedWeightProduct_cons_true
    (weight : ℕ → ℂ) (p : ℕ) (ps : List ℕ) (bits : List Bool) :
    selectedWeightProduct weight (p :: ps) (true :: bits) =
      weight p * selectedWeightProduct weight ps bits := by
  simp [selectedWeightProduct]

theorem occupiedInteger_cons_false
    (p : ℕ) (ps : List ℕ) (bits : List Bool) :
    occupiedInteger (p :: ps) (false :: bits) =
      occupiedInteger ps bits := by
  simp [occupiedInteger]

theorem occupiedInteger_cons_true
    (p : ℕ) (ps : List ℕ) (bits : List Bool) :
    occupiedInteger (p :: ps) (true :: bits) =
      p * occupiedInteger ps bits := by
  simp [occupiedInteger]

/--
Selected local weights equal the weight of the occupied integer, provided the
weight is multiplicative on the products under consideration.
-/
theorem selectedWeightProduct_eq_weight_occupied
    (weight : ℕ → ℂ)
    (h_one : weight 1 = 1)
    (h_mul : ∀ a b : ℕ, weight (a * b) = weight a * weight b)
    (modes : List ℕ) (bits : List Bool) :
    selectedWeightProduct weight modes bits =
      weight (occupiedInteger modes bits) := by
  induction modes generalizing bits with
  | nil =>
      cases bits <;> simp [selectedWeightProduct, occupiedInteger, h_one]
  | cons p ps ih =>
      cases bits with
      | nil =>
          simp [selectedWeightProduct, occupiedInteger, h_one]
      | cons bit bits =>
          cases bit
          · simp [selectedWeightProduct, occupiedInteger, ih]
          · simp [selectedWeightProduct, occupiedInteger, ih, h_mul]

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

/-- Word contribution written with selected local weights. -/
def selectedWordContribution
    (weight : ℕ → ℂ) (modes : List ℕ) (bits : List Bool) : ℂ :=
  wordParity bits * selectedWeightProduct weight modes bits

/-- Word contribution written as a Dirichlet monomial of the occupied integer. -/
def dirichletWordContribution
    (weight : ℕ → ℂ) (modes : List ℕ) (bits : List Bool) : ℂ :=
  wordParity bits * weight (occupiedInteger modes bits)

theorem selectedWordContribution_eq_dirichlet
    (weight : ℕ → ℂ)
    (h_one : weight 1 = 1)
    (h_mul : ∀ a b : ℕ, weight (a * b) = weight a * weight b)
    (modes : List ℕ) (bits : List Bool) :
    selectedWordContribution weight modes bits =
      dirichletWordContribution weight modes bits := by
  simp [selectedWordContribution, dirichletWordContribution,
    selectedWeightProduct_eq_weight_occupied weight h_one h_mul modes bits]

end FiniteDirichletOccupation

end noncomputable section

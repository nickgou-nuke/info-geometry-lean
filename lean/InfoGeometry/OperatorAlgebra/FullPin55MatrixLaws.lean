import Mathlib.Tactic

/-!
# Finite Pin(5,5) matrix laws

This module is the Lean twin of `tools/sympy/full_pin55_matrix_laws.py`.
It gives a native finite owner surface for the ten non-null basis-generator
Pin reflections in the split form `η = diag(1,1,1,1,1,-1,-1,-1,-1,-1)`.

#### BUCKET 1: CLOSED FINITE THEOREMS
The declarations below kernel-check:

* the ten coordinate Pin reflection readouts `pinReflect k` all preserve `η`;
* every `pinReflect k` is involutive;
* finite products of two basis reflections preserve `η`;
* basis-vector action matches the Clifford sandwich convention verified by the
  Python `clifford` lane: the reflected coordinate is negated and all others are fixed;
* the split-sign Clifford coefficient shadow has five `+1` and five `-1` squares;
* the full finite packet combines the above into a reusable theorem surface.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not construct the topological group `Pin(5,5)`, a spinor bundle,
or a continuum proof that every non-null unit vector acts by Clifford sandwich.
It closes the finite basis-generator matrix-law surface used by this repository.
-/

namespace InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws

open Matrix

abbrev M10Z := Matrix (Fin 10) (Fin 10) ℤ
abbrev V10Z := Fin 10 → ℤ

/-- Split `O(5,5)` metric `diag(1,1,1,1,1,-1,-1,-1,-1,-1)`. -/
def eta : M10Z :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, -1]

/-- Orthogonal group predicate for the fixed split form. -/
def IsO55 (A : M10Z) : Prop := Aᵀ * eta * A = eta

/--
Off-diagonal `O(5,5)` metric `[[0, I₅], [I₅, 0]]`.

This is the exact finite matrix instantiated from the symbolic CAS witness
`sympy_t_duality_cascade.py`.
-/
def etaOff : M10Z :=
  !![0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0]

/-- Orthogonal group predicate for the off-diagonal split form. -/
def IsO55Off (A : M10Z) : Prop := Aᵀ * etaOff * A = etaOff

/-- Coordinate vector `e_i`. -/
def basisVec (i : Fin 10) : V10Z := fun r => if r = i then 1 else 0

/--
Buscher first-cell momentum/winding swap, exchanging coordinates `0` and `5`.

This is the exact finite matrix from `sympy_t_duality_cascade.py`.
-/
def buscherSwapFirst : M10Z :=
  !![0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- Basis-generator Pin reflection readout: flip coordinate `k`. -/
def pinReflect (k : Fin 10) : M10Z :=
  fun i j => if i = j then if i = k then -1 else 1 else 0

/-- Product readout of two basis-generator Pin reflections. -/
def pinProduct (i j : Fin 10) : M10Z := pinReflect i * pinReflect j

/-- Split-sign Clifford square coefficient for the ten basis vectors. -/
def cliffordSquareSign (i : Fin 10) : ℤ := if i.val < 5 then 1 else -1

/-- The Clifford anticommutator coefficient shadow on basis vectors. -/
def cliffordAnticommCoeff (i j : Fin 10) : ℤ :=
  if i = j then 2 * cliffordSquareSign i else 0

/-- The first five basis generators have square `+1`. -/
theorem positive_square_signs : ∀ i : Fin 5, cliffordSquareSign ⟨i.val, by omega⟩ = 1 := by
  intro i
  fin_cases i <;> decide

/-- The last five basis generators have square `-1`. -/
theorem negative_square_signs :
    ∀ i : Fin 5, cliffordSquareSign ⟨i.val + 5, by omega⟩ = -1 := by
  intro i
  fin_cases i <;> decide

/-- Distinct basis generators have zero Clifford anticommutator coefficient. -/
theorem distinct_anticomm_zero :
    ∀ i j : Fin 10, i ≠ j → cliffordAnticommCoeff i j = 0 := by
  intro i j h
  unfold cliffordAnticommCoeff
  simp [h]

/-- Every basis-generator Pin reflection is an `O(5,5)` matrix. -/
theorem pinReflect_all_o55 : ∀ k : Fin 10, IsO55 (pinReflect k) := by
  intro k
  fin_cases k <;> unfold IsO55 pinReflect eta <;> decide

/-- Every basis-generator Pin reflection is involutive. -/
theorem pinReflect_all_involutive : ∀ k : Fin 10, pinReflect k * pinReflect k = 1 := by
  intro k
  fin_cases k <;> unfold pinReflect <;> decide

/-- Products of two finite `O(5,5)` readout matrices remain `O(5,5)`. -/
theorem IsO55_mul {A B : M10Z} (hA : IsO55 A) (hB : IsO55 B) : IsO55 (A * B) := by
  unfold IsO55 at hA hB ⊢
  rw [transpose_mul]
  calc
    (Bᵀ * Aᵀ) * eta * (A * B) = Bᵀ * (Aᵀ * eta * A) * B := by
      simp only [mul_assoc]
    _ = Bᵀ * eta * B := by rw [hA]
    _ = eta := hB

/-- Every product of two basis-generator Pin reflections is an `O(5,5)` matrix. -/
theorem pinProduct_all_o55 : ∀ i j : Fin 10, IsO55 (pinProduct i j) := by
  intro i j
  exact IsO55_mul (pinReflect_all_o55 i) (pinReflect_all_o55 j)

/-! ## Off-diagonal `O(5,5)` Buscher-swap instantiation from CAS -/

/-- The first-cell Buscher momentum/winding swap preserves `[[0,I₅],[I₅,0]]`. -/
theorem buscherSwapFirst_o55Off : IsO55Off buscherSwapFirst := by
  unfold IsO55Off buscherSwapFirst etaOff
  decide

/-- The first-cell Buscher momentum/winding swap is an involution. -/
theorem buscherSwapFirst_involutive : buscherSwapFirst * buscherSwapFirst = 1 := by
  unfold buscherSwapFirst
  decide

/-- The first-cell Buscher swap sends the first momentum basis vector to its winding partner. -/
theorem buscherSwapFirst_basis_zero :
    buscherSwapFirst.mulVec (basisVec 0) = basisVec 5 := by
  unfold buscherSwapFirst basisVec
  decide

/-- The first-cell Buscher swap sends the first winding basis vector back to momentum. -/
theorem buscherSwapFirst_basis_five :
    buscherSwapFirst.mulVec (basisVec 5) = basisVec 0 := by
  unfold buscherSwapFirst basisVec
  decide

/-- The first-cell Buscher swap is nontrivial on the finite coordinate carrier. -/
theorem buscherSwapFirst_nontrivial :
    buscherSwapFirst.mulVec (basisVec 0) ≠ basisVec 0 := by
  rw [buscherSwapFirst_basis_zero]
  decide

/-- Closed finite packet for the off-diagonal `O(5,5)` Buscher-swap surface. -/
theorem buscherSwapFirst_packet :
    IsO55Off buscherSwapFirst ∧
      buscherSwapFirst * buscherSwapFirst = 1 ∧
      buscherSwapFirst.mulVec (basisVec 0) = basisVec 5 ∧
      buscherSwapFirst.mulVec (basisVec 5) = basisVec 0 ∧
      buscherSwapFirst.mulVec (basisVec 0) ≠ basisVec 0 := by
  exact ⟨buscherSwapFirst_o55Off, buscherSwapFirst_involutive,
    buscherSwapFirst_basis_zero, buscherSwapFirst_basis_five,
    buscherSwapFirst_nontrivial⟩

/-- A basis Pin reflection negates its own coordinate basis vector. -/
theorem pinReflect_self_action :
    ∀ k : Fin 10, (pinReflect k).mulVec (basisVec k) = -basisVec k := by
  intro k
  fin_cases k <;> unfold pinReflect basisVec <;> decide

/-- A basis Pin reflection fixes every other coordinate basis vector. -/
theorem pinReflect_other_action :
    ∀ k j : Fin 10, k ≠ j → (pinReflect k).mulVec (basisVec j) = basisVec j := by
  intro k j h
  fin_cases k <;> fin_cases j <;> simp at h <;>
    unfold pinReflect basisVec <;> decide

/-- The Pin reflection action has the expected Clifford sandwich readout on basis vectors. -/
theorem pinReflect_basis_action :
    ∀ k j : Fin 10,
      (pinReflect k).mulVec (basisVec j) = if k = j then -basisVec j else basisVec j := by
  intro k j
  by_cases h : k = j
  · subst j
    simp [pinReflect_self_action]
  · simp [h, pinReflect_other_action k j h]

/-- Clifford algebra dimension shadow: `dim Cl(5,5) = 2^10 = 1024`. -/
theorem cl55_dimension_shadow : 2 ^ 10 = (1024 : ℕ) := by
  decide

/-- Even/odd parity shadow: each parity half has `2^9 = 512` basis blades. -/
theorem pin_parity_half_shadow : 2 ^ 9 = (512 : ℕ) := by
  decide

/-- Bivector/Spin Lie algebra dimension shadow: `10 choose 2 = 45`. -/
theorem spin55_bivector_count_shadow : 10 * 9 / 2 = (45 : ℕ) := by
  decide

/-- Closed finite packet for the basis-generator `Pin(5,5)` matrix-law surface. -/
theorem full_pin55_basis_packet :
    (∀ k : Fin 10, IsO55 (pinReflect k)) ∧
      (∀ k : Fin 10, pinReflect k * pinReflect k = 1) ∧
      (∀ i j : Fin 10, IsO55 (pinProduct i j)) ∧
      (∀ k j : Fin 10,
        (pinReflect k).mulVec (basisVec j) = if k = j then -basisVec j else basisVec j) ∧
      (∀ i : Fin 5, cliffordSquareSign ⟨i.val, by omega⟩ = 1) ∧
      (∀ i : Fin 5, cliffordSquareSign ⟨i.val + 5, by omega⟩ = -1) := by
  exact ⟨pinReflect_all_o55, pinReflect_all_involutive, pinProduct_all_o55,
    pinReflect_basis_action, positive_square_signs, negative_square_signs⟩

end InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws

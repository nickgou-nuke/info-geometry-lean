import Mathlib.Tactic

/-!
# InfoGeometry.Algebra.HypercomplexTriadMatrix

Concrete `2 × 2` matrix realization of the elliptic/hyperbolic/parabolic triad.

This file proves:

* elliptic unit `I` satisfies `I² = -1`;
* split/hyperbolic unit `E` satisfies `E² = 1`;
* parabolic/nilpotent unit `N` satisfies `N² = 0`;
* `N` has no left or right inverse over a nontrivial ring;
* the unipotent shifts `1 ± N` are mutual inverses;
* the split idempotents `P₊ = (1+E)/2`, `P₋ = (1-E)/2` are orthogonal projectors.

No wrappers.
No `sorry`.
-/

namespace InfoGeometry.Algebra.HypercomplexTriadMatrix

open Matrix

/-- Concrete elliptic unit: matrix model of `i`, satisfying `I² = -1`. -/
def I (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, -1;
     1,  0]

/-- Concrete hyperbolic/split unit: matrix model of `e`, satisfying `E² = 1`. -/
def E (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1;
     1, 0]

/-- Concrete parabolic/dual nilpotent unit: matrix model of `N`, satisfying `N² = 0`. -/
def N (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1;
     0, 0]

/-- Elliptic sector: `I² = -1`. -/
theorem I_sq
    {R : Type*} [CommRing R] :
    I R * I R = -(1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j <;> fin_cases i <;> fin_cases j
    <;> simp [I, Matrix.mul_apply, Fin.sum_univ_two]

/-- Hyperbolic/split sector: `E² = 1`. -/
theorem E_sq
    {R : Type*} [CommRing R] :
    E R * E R = (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j <;> fin_cases i <;> fin_cases j
    <;> simp [E, Matrix.mul_apply, Fin.sum_univ_two]

/-- Parabolic/dual sector: `N² = 0`. -/
theorem N_sq
    {R : Type*} [CommRing R] :
    N R * N R = (0 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j <;> fin_cases i <;> fin_cases j
    <;> simp [N, Matrix.mul_apply, Fin.sum_univ_two]

/-- The nilpotent unit `N` has no left inverse over a nontrivial ring. -/
theorem N_no_left_inverse
    {R : Type*} [CommRing R] [Nontrivial R] :
    ¬ ∃ M : Matrix (Fin 2) (Fin 2) R,
      M * N R = (1 : Matrix (Fin 2) (Fin 2) R) := by
  rintro ⟨M, hM⟩
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) R =>
    A (0 : Fin 2) (0 : Fin 2)) hM
  simp [N, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The nilpotent unit `N` has no right inverse over a nontrivial ring. -/
theorem N_no_right_inverse
    {R : Type*} [CommRing R] [Nontrivial R] :
    ¬ ∃ M : Matrix (Fin 2) (Fin 2) R,
      N R * M = (1 : Matrix (Fin 2) (Fin 2) R) := by
  rintro ⟨M, hM⟩
  have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) R =>
    A (1 : Fin 2) (1 : Fin 2)) hM
  simp [N, Matrix.mul_apply, Fin.sum_univ_two] at h11

/--
The parabolic nilpotent generates a unipotent shift:

`(1 + N)(1 - N) = 1`.
-/
theorem one_add_N_mul_one_sub_N
    {R : Type*} [CommRing R] :
    ((1 : Matrix (Fin 2) (Fin 2) R) + N R) *
      ((1 : Matrix (Fin 2) (Fin 2) R) - N R)
      =
    (1 : Matrix (Fin 2) (Fin 2) R) := by
  calc
    ((1 : Matrix (Fin 2) (Fin 2) R) + N R) *
        ((1 : Matrix (Fin 2) (Fin 2) R) - N R)
        =
      (1 : Matrix (Fin 2) (Fin 2) R) - N R * N R := by
        noncomm_ring
    _ = 1 := by
        rw [N_sq]
        simp

/--
Right-handed unipotent inverse identity:

`(1 - N)(1 + N) = 1`.
-/
theorem one_sub_N_mul_one_add_N
    {R : Type*} [CommRing R] :
    ((1 : Matrix (Fin 2) (Fin 2) R) - N R) *
      ((1 : Matrix (Fin 2) (Fin 2) R) + N R)
      =
    (1 : Matrix (Fin 2) (Fin 2) R) := by
  calc
    ((1 : Matrix (Fin 2) (Fin 2) R) - N R) *
        ((1 : Matrix (Fin 2) (Fin 2) R) + N R)
        =
      (1 : Matrix (Fin 2) (Fin 2) R) - N R * N R := by
        noncomm_ring
    _ = 1 := by
        rw [N_sq]
        simp

/--
Drazin inverse of the nilpotent unit is zero, encoded by the index-two Drazin
equations.

For a square-zero element `N`, the Drazin inverse is `0` with index `2`:

* `N³ * 0 = N²`;
* `0 * N * 0 = 0`;
* `N * 0 = 0 * N`.
-/
theorem N_drazin_zero_index_two
    {R : Type*} [CommRing R] :
    (N R) ^ 3 * (0 : Matrix (Fin 2) (Fin 2) R) = (N R) ^ 2
      ∧
    (0 : Matrix (Fin 2) (Fin 2) R) * N R *
        (0 : Matrix (Fin 2) (Fin 2) R)
      =
    (0 : Matrix (Fin 2) (Fin 2) R)
      ∧
    N R * (0 : Matrix (Fin 2) (Fin 2) R)
      =
    (0 : Matrix (Fin 2) (Fin 2) R) * N R := by
  constructor
  · rw [pow_two, N_sq]
    simp
  constructor
  · simp
  · simp

/-- Split idempotent `P₊ = (1/2)(1 + E)`. -/
def Pplus (R : Type*) [Field R] : Matrix (Fin 2) (Fin 2) R :=
  (1 / 2 : R) • ((1 : Matrix (Fin 2) (Fin 2) R) + E R)

/-- Split idempotent `P₋ = (1/2)(1 - E)`. -/
def Pminus (R : Type*) [Field R] : Matrix (Fin 2) (Fin 2) R :=
  (1 / 2 : R) • ((1 : Matrix (Fin 2) (Fin 2) R) - E R)

/-- The split projector `P₊` is idempotent. -/
theorem Pplus_idempotent
    {R : Type*} [Field R] [CharZero R] :
    Pplus R * Pplus R = Pplus R := by
  ext i j <;> fin_cases i <;> fin_cases j
    <;> simp [Pplus, E, Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring

/-- The split projector `P₋` is idempotent. -/
theorem Pminus_idempotent
    {R : Type*} [Field R] [CharZero R] :
    Pminus R * Pminus R = Pminus R := by
  ext i j <;> fin_cases i <;> fin_cases j
    <;> simp [Pminus, E, Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring

/-- The split projectors are orthogonal: `P₊P₋ = 0`. -/
theorem Pplus_mul_Pminus
    {R : Type*} [Field R] [CharZero R] :
    Pplus R * Pminus R = (0 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j <;> fin_cases i <;> fin_cases j
    <;> simp [Pplus, Pminus, E, Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring

/-- The split projectors are orthogonal in the other order: `P₋P₊ = 0`. -/
theorem Pminus_mul_Pplus
    {R : Type*} [Field R] [CharZero R] :
    Pminus R * Pplus R = (0 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j <;> fin_cases i <;> fin_cases j
    <;> simp [Pplus, Pminus, E, Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring

/-- The split projectors resolve the identity: `P₊ + P₋ = 1`. -/
theorem Pplus_add_Pminus
    {R : Type*} [Field R] [CharZero R] :
    Pplus R + Pminus R = (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j <;> fin_cases i <;> fin_cases j
    <;> simp [Pplus, Pminus, E]
    <;> ring

end InfoGeometry.Algebra.HypercomplexTriadMatrix

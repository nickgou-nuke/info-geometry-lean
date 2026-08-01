import Mathlib.Tactic

/-!
# Fermionic Primon Partition Function

Finite Euler-product layer for the fermionic Primon gas.

For each prime mode `p`, Pauli exclusion restricts the occupation to
`0` or `1`.  The one-prime factor is therefore

`1 + p^(-β)`.

For finitely many prime modes this expands as a sum over Boolean occupation
vectors, the finite algebraic core of the squarefree/fermionic Euler product.
-/

noncomputable section

def fermionPrimeBoltzmannWeight (p : ℕ) (β : ℝ) : ℝ :=
  (p : ℝ) ^ (-β)

def fermionOccupationWeight (p : ℕ) (β : ℝ) (occupied : Bool) : ℝ :=
  if occupied then fermionPrimeBoltzmannWeight p β else 1

def singlePrimeFermionPartition (p : ℕ) (β : ℝ) : ℝ :=
  (Finset.univ : Finset Bool).sum fun occupied =>
    fermionOccupationWeight p β occupied

def twoPrimeFermionPartition (p q : ℕ) (β : ℝ) : ℝ :=
  (Finset.univ : Finset Bool).sum fun bp =>
    (Finset.univ : Finset Bool).sum fun bq =>
      fermionOccupationWeight p β bp * fermionOccupationWeight q β bq

theorem fermionOccupationWeight_false (p : ℕ) (β : ℝ) :
    fermionOccupationWeight p β false = 1 := by
  simp [fermionOccupationWeight]

theorem fermionOccupationWeight_true (p : ℕ) (β : ℝ) :
    fermionOccupationWeight p β true = fermionPrimeBoltzmannWeight p β := by
  simp [fermionOccupationWeight]

theorem singlePrimeFermionPartition_eq (p : ℕ) (β : ℝ) :
    singlePrimeFermionPartition p β = 1 + fermionPrimeBoltzmannWeight p β := by
  simp [singlePrimeFermionPartition, fermionOccupationWeight, add_comm]

theorem fermion_factor_as_boson_ratio {x : ℝ} (hx : x ≠ 1) :
    1 + x = (1 - x ^ 2) / (1 - x) := by
  have hfac : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  rw [hfac]
  field_simp [hden]

theorem singlePrimeFermionPartition_as_zeta_ratio {p : ℕ} {β : ℝ}
    (h : fermionPrimeBoltzmannWeight p β ≠ 1) :
    singlePrimeFermionPartition p β =
      (1 - (fermionPrimeBoltzmannWeight p β) ^ 2) /
        (1 - fermionPrimeBoltzmannWeight p β) := by
  rw [singlePrimeFermionPartition_eq]
  exact fermion_factor_as_boson_ratio h

theorem finite_two_prime_fermion_euler_product (p q : ℕ) (β : ℝ) :
    singlePrimeFermionPartition p β * singlePrimeFermionPartition q β =
      twoPrimeFermionPartition p q β := by
  simp [singlePrimeFermionPartition, twoPrimeFermionPartition]
  ring

theorem finite_two_prime_fermion_expansion (p q : ℕ) (β : ℝ) :
    twoPrimeFermionPartition p q β =
      1 + fermionPrimeBoltzmannWeight p β +
        fermionPrimeBoltzmannWeight q β +
          fermionPrimeBoltzmannWeight p β * fermionPrimeBoltzmannWeight q β := by
  rw [← finite_two_prime_fermion_euler_product]
  rw [singlePrimeFermionPartition_eq, singlePrimeFermionPartition_eq]
  ring

/-- Concrete finite statement for the first two prime modes `2` and `3`. -/
theorem finite_2_3_fermionic_partition (β : ℝ) :
    singlePrimeFermionPartition 2 β * singlePrimeFermionPartition 3 β =
      twoPrimeFermionPartition 2 3 β :=
  finite_two_prime_fermion_euler_product 2 3 β

end noncomputable section

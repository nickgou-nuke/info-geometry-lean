import InfoGeometry.Arithmetic.HoradamIonMatrixMethods

/-!
# Horadam `2^k`-ion Binet slice

This module formalizes the next theorem-safe slice of
`preprints201906.0303.v1`, *Horadam 2^k-ions*.

Closed content:

* a conditional Binet core `A α^n - B β^n` satisfies the Horadam recurrence
  whenever `α` and `β` satisfy the characteristic equation
  `x^2 = p x + q`;
* the finite coordinate/`2^k`-ion lift satisfies the same recurrence;
* the paper's normalized constants `A=b-aβ`, `B=b-aα` give initial values
  after multiplication by `(α-β)`.

No Cayley-Dickson multiplication, noncommutative Catalan/Cassini identity,
radical/discriminant construction, or analytic generating-function convergence
is asserted here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.HoradamIonBinetSlice

open InfoGeometry.Arithmetic.HoradamIonMatrixMethods

variable {R : Type*} [CommRing R]

/-- Conditional Binet numerator/core `A α^n - B β^n`. -/
def binetCore (A B α β : R) (n : ℕ) : R := A * α ^ n - B * β ^ n

/-- A root of `x^2 - p x - q = 0` propagates the Horadam recurrence. -/
theorem pow_succ_succ_of_characteristic
    (x p q : R)
    (h : x ^ 2 = p * x + q)
    (n : ℕ) :
    x ^ (n + 2) = p * x ^ (n + 1) + q * x ^ n := by
  calc
    x ^ (n + 2) = x ^ n * x ^ 2 := by
      rw [pow_add]
    _ = x ^ n * (p * x + q) := by rw [h]
    _ = p * x ^ (n + 1) + q * x ^ n := by
      rw [show x ^ (n + 1) = x ^ n * x by rw [pow_add]; ring]
      ring

/-- The Binet core satisfies the Horadam recurrence under the characteristic-root hypotheses. -/
theorem binetCore_recurrence
    (A B α β p q : R)
    (hα : α ^ 2 = p * α + q)
    (hβ : β ^ 2 = p * β + q)
    (n : ℕ) :
    binetCore A B α β (n + 2) =
      p * binetCore A B α β (n + 1) + q * binetCore A B α β n := by
  unfold binetCore
  rw [pow_succ_succ_of_characteristic α p q hα n]
  rw [pow_succ_succ_of_characteristic β p q hβ n]
  ring

/-- Coordinate lift of the Binet core. -/
def binetIon {N : ℕ} (A B α β : R) (n : ℕ) : Ion N R :=
  fun s => binetCore A B α β (n + s.val)

/-- The Binet coordinate lift satisfies the componentwise Horadam recurrence. -/
theorem binetIon_recurrence {N : ℕ}
    (A B α β p q : R)
    (hα : α ^ 2 = p * α + q)
    (hβ : β ^ 2 = p * β + q)
    (n : ℕ) :
    binetIon (N := N) A B α β (n + 2) =
      ionScale p (binetIon (N := N) A B α β (n + 1)) +
        ionScale q (binetIon (N := N) A B α β n) := by
  ext s
  simp [binetIon, ionScale]
  rw [show n + 2 + s.val = n + s.val + 2 by omega]
  rw [show n + 1 + s.val = n + s.val + 1 by omega]
  exact binetCore_recurrence A B α β p q hα hβ (n + s.val)

/-- Paper's numerator constant `A=b-aβ`. -/
def paperA (a b β : R) : R := b - a * β

/-- Paper's numerator constant `B=b-aα`. -/
def paperB (a b α : R) : R := b - a * α

/-- The normalized Binet numerator has initial value `a` after clearing denominator. -/
theorem paper_binet_initial_zero_clear_denominator
    (a b α β : R) :
    binetCore (paperA a b β) (paperB a b α) α β 0 = a * (α - β) := by
  simp [binetCore, paperA, paperB]
  ring

/-- The normalized Binet numerator has initial value `b` after clearing denominator. -/
theorem paper_binet_initial_one_clear_denominator
    (a b α β : R) :
    binetCore (paperA a b β) (paperB a b α) α β 1 = b * (α - β) := by
  simp [binetCore, paperA, paperB]
  ring

/-- Consolidated finite Binet slice packet. -/
theorem horadam_ion_binet_slice_packet {N : ℕ}
    (A B α β p q : R)
    (hα : α ^ 2 = p * α + q)
    (hβ : β ^ 2 = p * β + q) :
    (∀ n : ℕ,
      binetCore A B α β (n + 2) =
        p * binetCore A B α β (n + 1) + q * binetCore A B α β n) ∧
    (∀ n : ℕ,
      binetIon (N := N) A B α β (n + 2) =
        ionScale p (binetIon (N := N) A B α β (n + 1)) +
          ionScale q (binetIon (N := N) A B α β n)) := by
  exact ⟨binetCore_recurrence A B α β p q hα hβ,
    binetIon_recurrence A B α β p q hα hβ⟩

end InfoGeometry.Arithmetic.HoradamIonBinetSlice

end noncomputable section

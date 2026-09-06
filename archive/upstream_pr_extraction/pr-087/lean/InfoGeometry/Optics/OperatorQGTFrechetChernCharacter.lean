import InfoGeometry.Canonical.SouriauOnsagerBKMIntegrability
import InfoGeometry.OperatorAlgebra.BianchiOperatorLift
import InfoGeometry.OperatorAlgebra.InnerConjugation
import InfoGeometry.Optics.OperatorDerivationForms

noncomputable section

namespace InfoGeometry.Optics.OperatorQGTFrechetChernCharacter

open scoped RightActions
open InfoGeometry.OperatorAlgebra
open SouriauOnsagerBKM

/-- The degree-`k` finite operator Chern character, before normalization by
the conventional scalar constants.  Its input is the repository's native
finite-dimensional C-star algebra of continuous endomorphisms. -/
def frechetChernCharacter (n k : ℕ) : FiniteOperatorAlgebra n → ℂ :=
  fun A => finiteOperatorTrace (A ^ k)

@[simp] theorem frechetChernCharacter_apply
    (n k : ℕ) (A : FiniteOperatorAlgebra n) :
    frechetChernCharacter n k A = finiteOperatorTrace (A ^ k) :=
  rfl

/-- The continuous linear differential of the traced power is the finite
trace composed with Mathlib's ordered noncommutative power derivative. -/
noncomputable def frechetChernCharacterDerivative
    (n k : ℕ) (A : FiniteOperatorAlgebra n) :
    FiniteOperatorAlgebra n →L[ℂ] ℂ :=
  (finiteOperatorTraceCLM n).comp (powerDerivative k A)

@[simp] theorem frechetChernCharacterDerivative_apply
    (n k : ℕ) (A H : FiniteOperatorAlgebra n) :
    frechetChernCharacterDerivative n k A H =
      finiteOperatorTrace (powerDerivative (𝕜 := ℂ) k A H) :=
  rfl

/-- Genuine Fréchet differentiability of every finite traced characteristic
power.  This is the analytic Chern-character bridge from the existing
noncommutative insertion derivative to the existing continuous trace. -/
theorem hasFDerivAt_frechetChernCharacter
    (n k : ℕ) (A : FiniteOperatorAlgebra n) :
    HasFDerivAt (frechetChernCharacter n k)
      (frechetChernCharacterDerivative n k A) A := by
  exact (finiteOperatorTraceCLM n).hasFDerivAt.comp A
    (hasFDerivAt_power_noncommutative k A)

theorem differentiable_frechetChernCharacter (n k : ℕ) :
    Differentiable ℂ (frechetChernCharacter n k) := by
  intro A
  exact (hasFDerivAt_frechetChernCharacter n k A).differentiableAt

/-- The native `fderiv` computes to the explicit trace of the ordered
insertion derivative. -/
theorem fderiv_frechetChernCharacter
    (n k : ℕ) (A : FiniteOperatorAlgebra n) :
    fderiv ℂ (frechetChernCharacter n k) A =
      frechetChernCharacterDerivative n k A :=
  (hasFDerivAt_frechetChernCharacter n k A).fderiv

@[simp] theorem frechetChernCharacterDerivative_zero
    (n : ℕ) (A : FiniteOperatorAlgebra n) :
    frechetChernCharacterDerivative n 0 A = 0 := by
  ext H
  simp [frechetChernCharacterDerivative]

@[simp] theorem frechetChernCharacterDerivative_one
    (n : ℕ) (A H : FiniteOperatorAlgebra n) :
    frechetChernCharacterDerivative n 1 A H = finiteOperatorTrace H := by
  simp [frechetChernCharacterDerivative]

/-! ## Cyclic reduction and infinitesimal gauge directions -/

/-- Cyclicity collapses every ordered insertion in the noncommutative power
derivative to the same traced monomial. -/
theorem finiteOperatorTrace_powerDerivative
    (n k : ℕ) (A H : FiniteOperatorAlgebra n) :
    finiteOperatorTrace (powerDerivative (𝕜 := ℂ) k A H) =
      (k : ℂ) * finiteOperatorTrace (H * A ^ k.pred) := by
  simp only [powerDerivative, ContinuousLinearMap.sum_apply]
  change finiteOperatorTraceLinear n
      (∑ x ∈ Finset.range k, A ^ (k.pred - x) * H * A ^ x) = _
  rw [map_sum]
  have hterm : ∀ x ∈ Finset.range k,
      finiteOperatorTrace (A ^ (k.pred - x) * H * A ^ x) =
        finiteOperatorTrace (H * A ^ k.pred) := by
    intro x hx
    have hxlt : x < k := Finset.mem_range.mp hx
    have hxle : x ≤ k.pred := Nat.le_pred_of_lt hxlt
    calc
      finiteOperatorTrace (A ^ (k.pred - x) * H * A ^ x) =
          finiteOperatorTrace (A ^ (k.pred - x) * (H * A ^ x)) := by
            rw [mul_assoc]
      _ = finiteOperatorTrace ((H * A ^ x) * A ^ (k.pred - x)) :=
        finiteOperatorTrace_mul_comm _ _
      _ = finiteOperatorTrace (H * (A ^ x * A ^ (k.pred - x))) := by
        rw [mul_assoc]
      _ = finiteOperatorTrace (H * A ^ k.pred) := by
        rw [← pow_add, Nat.add_sub_of_le hxle]
  simp only [finiteOperatorTraceLinear_apply]
  calc
    (∑ x ∈ Finset.range k,
        finiteOperatorTrace (A ^ (k.pred - x) * H * A ^ x)) =
        ∑ _x ∈ Finset.range k, finiteOperatorTrace (H * A ^ k.pred) := by
          exact Finset.sum_congr rfl (fun x hx => hterm x hx)
    _ = (k : ℂ) * finiteOperatorTrace (H * A ^ k.pred) := by simp

/-- Closed cyclic formula for the derivative of the finite traced
characteristic power. -/
theorem frechetChernCharacterDerivative_eq
    (n k : ℕ) (A H : FiniteOperatorAlgebra n) :
    frechetChernCharacterDerivative n k A H =
      (k : ℂ) * finiteOperatorTrace (H * A ^ k.pred) := by
  rw [frechetChernCharacterDerivative_apply,
    finiteOperatorTrace_powerDerivative]

/-- A commutator tangent followed by the matching power has zero finite
trace.  This is the elementary cyclic identity underlying infinitesimal
gauge invariance. -/
theorem finiteOperatorTrace_commutator_mul_pow_zero
    (n m : ℕ) (X A : FiniteOperatorAlgebra n) :
    finiteOperatorTrace ((X * A - A * X) * A ^ m) = 0 := by
  rw [sub_mul]
  change finiteOperatorTraceLinear n
      (X * A * A ^ m - A * X * A ^ m) = 0
  rw [map_sub]
  have hcyc : finiteOperatorTrace (A * (X * A ^ m)) =
      finiteOperatorTrace ((X * A ^ m) * A) :=
    finiteOperatorTrace_mul_comm _ _
  calc
      finiteOperatorTrace (X * A * A ^ m) -
        finiteOperatorTrace (A * X * A ^ m) =
      finiteOperatorTrace (X * A ^ (m + 1)) -
        finiteOperatorTrace (A * (X * A ^ m)) := by
          simp only [mul_assoc]
          rw [← pow_succ' A m]
    _ = finiteOperatorTrace (X * A ^ (m + 1)) -
        finiteOperatorTrace ((X * A ^ m) * A) := by rw [hcyc]
    _ = 0 := by rw [pow_succ]; exact sub_self _

/-- Infinitesimal inner-conjugation directions belong to the kernel of every
traced characteristic-power differential. -/
theorem frechetChernCharacterDerivative_commutator
    (n k : ℕ) (A X : FiniteOperatorAlgebra n) :
    frechetChernCharacterDerivative n k A (X * A - A * X) = 0 := by
  cases k with
  | zero => simp
  | succ m =>
      rw [frechetChernCharacterDerivative_eq]
      simp only [Nat.cast_add, Nat.cast_one, Nat.pred_succ]
      rw [finiteOperatorTrace_commutator_mul_pow_zero, mul_zero]

/-- The same kernel statement in the connection layer's canonical
`associativeCommutator` coordinates. -/
theorem frechetChernCharacterDerivative_associativeCommutator
    (n k : ℕ) (A X : FiniteOperatorAlgebra n) :
    frechetChernCharacterDerivative n k A
      (InfoGeometry.OperatorAlgebra.associativeCommutator X A) = 0 := by
  exact frechetChernCharacterDerivative_commutator n k A X

/-- Native `fderiv` form of infinitesimal gauge invariance: tangent vectors
generated by inner conjugation are annihilated at every operator. -/
theorem fderiv_frechetChernCharacter_associativeCommutator
    (n k : ℕ) (A X : FiniteOperatorAlgebra n) :
    (fderiv ℂ (frechetChernCharacter n k) A)
      (InfoGeometry.OperatorAlgebra.associativeCommutator X A) = 0 := by
  rw [fderiv_frechetChernCharacter]
  exact frechetChernCharacterDerivative_associativeCommutator n k A X

/-! ## Finite conjugation invariance -/

/-- The coordinate finite trace is invariant under the repository's native
inner-conjugation ring equivalence. -/
theorem finiteOperatorTrace_innerConjugation
    (n : ℕ) (u : (FiniteOperatorAlgebra n)ˣ)
    (A : FiniteOperatorAlgebra n) :
    finiteOperatorTrace (innerConjugation u A) = finiteOperatorTrace A := by
  unfold innerConjugation
  calc
    finiteOperatorTrace ((u : FiniteOperatorAlgebra n) * A *
        (↑(u⁻¹) : FiniteOperatorAlgebra n)) =
      finiteOperatorTrace ((↑(u⁻¹) : FiniteOperatorAlgebra n) *
        ((u : FiniteOperatorAlgebra n) * A)) := by
      exact finiteOperatorTrace_mul_comm
        ((u : FiniteOperatorAlgebra n) * A)
        (↑(u⁻¹) : FiniteOperatorAlgebra n)
    _ = finiteOperatorTrace
        (((↑(u⁻¹) : FiniteOperatorAlgebra n) *
          (u : FiniteOperatorAlgebra n)) * A) := by
      simp only [mul_assoc]
    _ = finiteOperatorTrace A := by
      rw [Units.inv_mul, one_mul]

/-- Every analytic finite Chern-character power is exactly invariant under
finite inner frame changes. -/
theorem frechetChernCharacter_innerConjugation
    (n k : ℕ) (u : (FiniteOperatorAlgebra n)ˣ)
    (A : FiniteOperatorAlgebra n) :
    frechetChernCharacter n k (innerConjugation u A) =
      frechetChernCharacter n k A := by
  change finiteOperatorTrace ((innerConjugation u A) ^ k) =
    finiteOperatorTrace (A ^ k)
  change finiteOperatorTrace (((innerConjugationRingEquiv u) A) ^ k) = _
  rw [← map_pow]
  exact finiteOperatorTrace_innerConjugation n u (A ^ k)

/-- Naturality of the explicit Fréchet differential under simultaneous
conjugation of its base operator and tangent operator. -/
theorem frechetChernCharacterDerivative_innerConjugation
    (n k : ℕ) (u : (FiniteOperatorAlgebra n)ˣ)
    (A H : FiniteOperatorAlgebra n) :
    frechetChernCharacterDerivative n k (innerConjugation u A)
        (innerConjugation u H) =
      frechetChernCharacterDerivative n k A H := by
  rw [frechetChernCharacterDerivative_eq,
    frechetChernCharacterDerivative_eq]
  congr 1
  change finiteOperatorTrace
      ((innerConjugationRingEquiv u H) *
        (innerConjugationRingEquiv u A) ^ k.pred) = _
  rw [← map_pow, ← map_mul]
  exact finiteOperatorTrace_innerConjugation n u (H * A ^ k.pred)

/-- Native `fderiv` naturality under a finite gauge-frame change. -/
theorem fderiv_frechetChernCharacter_innerConjugation
    (n k : ℕ) (u : (FiniteOperatorAlgebra n)ˣ)
    (A H : FiniteOperatorAlgebra n) :
    (fderiv ℂ (frechetChernCharacter n k) (innerConjugation u A))
        (innerConjugation u H) =
      (fderiv ℂ (frechetChernCharacter n k) A) H := by
  rw [fderiv_frechetChernCharacter, fderiv_frechetChernCharacter]
  exact frechetChernCharacterDerivative_innerConjugation n k u A H

end InfoGeometry.Optics.OperatorQGTFrechetChernCharacter

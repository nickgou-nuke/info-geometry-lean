import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Algebra.CliffordGA

open CliffordAlgebra

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- 
The core universal property of the Clifford Algebra:
The square of a basis vector equals the quadratic form evaluated on it.
This corresponds to the `e_i^2 = Q(e_i)` relation verified in SGAE/galgebra.
-/
theorem clifford_square_eq_quadratic_form (m : M) :
    (ι Q m) * (ι Q m) = algebraMap R (CliffordAlgebra Q) (Q m) := by
  exact ι_sq_scalar Q m

/-- Symmetric part of the product of two elements in a ring. -/
def symPart {A : Type*} [Ring A] [Invertible (2 : A)] (x y : A) : A :=
  ⅟(2 : A) * (x * y + y * x)

/-- Antisymmetric part of the product of two elements in a ring. -/
def antiPart {A : Type*} [Ring A] [Invertible (2 : A)] (x y : A) : A :=
  ⅟(2 : A) * (x * y - y * x)

/-- The Hestenes product decomposition: ab = a · b + a ∧ b. -/
theorem hestenes_decomposition {A : Type*} [Ring A] [Invertible (2 : A)] (x y : A) :
    x * y = symPart x y + antiPart x y := by
  unfold symPart antiPart
  rw [← mul_add]
  have h_add : (x * y + y * x) + (x * y - y * x) = (2 : A) * (x * y) := by
    calc
      (x * y + y * x) + (x * y - y * x) = (x * y + x * y) + (y * x - y * x) := by noncomm_ring
      _ = x * y + x * y := by
        rw [sub_self, add_zero]
      _ = (2 : A) * (x * y) := by
        have h2 : (2 : A) * (x * y) = (1 + 1) * (x * y) := by congr; norm_num
        rw [h2, add_mul, one_mul]
  rw [h_add]
  rw [← mul_assoc]
  rw [invOf_mul_self (2 : A)]
  rw [one_mul]

/-- The coordinate-free projection state mapping trace-free elements. -/
def IsTraceFree {A : Type*} [Ring A] [Invertible (2 : A)] (x y : A) : Prop :=
  symPart x y = 0

/-- An element product is trace-free if and only if it equals its antisymmetric (wedge) part. -/
theorem isTraceFree_iff_prod_eq_antiPart {A : Type*} [Ring A] [Invertible (2 : A)] (x y : A) :
    IsTraceFree x y ↔ x * y = antiPart x y := by
  unfold IsTraceFree
  constructor
  · intro h_sym
    rw [hestenes_decomposition x y, h_sym, zero_add]
  · intro h_prod
    have h_decomp := hestenes_decomposition x y
    rw [h_prod] at h_decomp
    have h_zero : symPart x y + antiPart x y - antiPart x y = 0 := by
      rw [← h_decomp, sub_self]
    rw [add_sub_cancel_right] at h_zero
    exact h_zero

/-- Two vectors are a light-like (null) pair if both square to 0 and their polar product is 2. -/
abbrev IsLightlikePair (u v : M) : Prop :=
  Q u = 0 ∧ Q v = 0 ∧ QuadraticMap.polar Q u v = 2

lemma commute_two {A : Type*} [Ring A] (x : A) : (2 : A) * x = x * (2 : A) := by
  rw [two_mul, mul_two]

lemma commute_invOf_two {A : Type*} [Ring A] [Invertible (2 : A)] (x : A) :
    ⅟(2 : A) * x = x * ⅟(2 : A) := by
  have hc : Commute (2 : A) x := by
    dsimp [Commute, SemiconjBy]
    exact commute_two x
  exact hc.invOf_left

/-- The vacuum projector P₀ constructed from a light-like pair is idempotent. -/
theorem vacuum_projector_idempotent [Invertible (2 : CliffordAlgebra Q)]
    {u v : M} (h : IsLightlikePair Q u v) :
    let P₀ := ⅟(2 : CliffordAlgebra Q) * (ι Q u * ι Q v)
    P₀ * P₀ = P₀ := by
  intro P₀
  dsimp [P₀]
  -- First prove the core product identity: (u v) * (u v) = 2 * (u v)
  have h_prod : (ι Q u * ι Q v) * (ι Q u * ι Q v) = (2 : CliffordAlgebra Q) * (ι Q u * ι Q v) := by
    have h_comm : ι Q v * ι Q u = algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q v u) - ι Q u * ι Q v := by
      exact ι_mul_ι_comm v u
    have h_symm : QuadraticMap.polar Q v u = QuadraticMap.polar Q u v := by
      exact (QuadraticMap.polar_comm Q u v).symm
    rw [h_symm, h.2.2] at h_comm
    have h_two : algebraMap R (CliffordAlgebra Q) 2 = (2 : CliffordAlgebra Q) := by
      exact map_ofNat (algebraMap R (CliffordAlgebra Q)) 2
    rw [h_two] at h_comm
    have h_nil : ι Q u * ι Q u = 0 := by
      rw [ι_sq_scalar, h.1, map_zero]
    rw [mul_assoc, ← mul_assoc (ι Q v), h_comm, sub_mul, mul_assoc, mul_sub, ← mul_assoc, ← mul_assoc]
    rw [h_nil, zero_mul, sub_zero]
    rw [← commute_two (ι Q u), mul_assoc]
  -- Now simplify P₀ * P₀:
  have h_assoc_inv : (⅟(2 : CliffordAlgebra Q) * (ι Q u * ι Q v)) * (⅟(2 : CliffordAlgebra Q) * (ι Q u * ι Q v)) =
      ⅟(2 : CliffordAlgebra Q) * (⅟(2 : CliffordAlgebra Q) * ((ι Q u * ι Q v) * (ι Q u * ι Q v))) := by
    rw [mul_assoc]
    rw [← mul_assoc (ι Q u * ι Q v) (⅟2) (ι Q u * ι Q v)]
    rw [← commute_invOf_two (ι Q u * ι Q v)]
    rw [mul_assoc]
  rw [h_assoc_inv, h_prod]
  have h_assoc_two : ⅟(2 : CliffordAlgebra Q) * (⅟(2 : CliffordAlgebra Q) * (2 * (ι Q u * ι Q v))) =
      (⅟(2 : CliffordAlgebra Q) * (⅟(2 : CliffordAlgebra Q) * 2)) * (ι Q u * ι Q v) := by
    rw [mul_assoc, mul_assoc]
  rw [h_assoc_two, invOf_mul_self (2 : CliffordAlgebra Q), mul_one]

end InfoGeometry.Algebra.CliffordGA

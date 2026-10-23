import Mathlib

/-!
# Canonical alternatives to counterexample-driven claims

The repository contains many finite witnesses showing that a stronger slogan
is false.  This owner file records general algebraic replacements.  The
statements use arbitrary associative rings or additive groups, rather than
scalar diagonal models.
-/

namespace InfoGeometry.Canonical.CounterexampleAlternatives

variable {A B : Type*}

theorem positive_entry_ne_zero_entry
    [Preorder A] [Zero A] (P Q : A) (hP : 0 < P) (hQ : Q = 0) : P ≠ Q := by
  intro h
  exact (ne_of_gt hP) (hQ ▸ h)

theorem star_symmetric_sum_of_self_adjoint
    [Ring A] [StarRing A] (x y : A)
    (hx : star x = x) (hy : star y = y) :
    star (x + y) = x + y := by
  rw [star_add, hx, hy]

theorem complement_idempotent_of_idempotent
    [Ring A] (e : A) (he : e * e = e) :
    (1 - e) * (1 - e) = 1 - e ∧ e * (1 - e) = 0 ∧ (1 - e) * e = 0 := by
  constructor
  · calc
      (1 - e) * (1 - e) = 1 - e - e + e * e := by noncomm_ring
      _ = 1 - e := by rw [he]; abel
  · constructor
    · rw [mul_sub, mul_one, he, sub_self]
    · rw [sub_mul, one_mul, he, sub_self]

theorem nonzero_idempotent_not_square_zero
    [MonoidWithZero A] (e : A) (he : e * e = e) (hne : e ≠ 0) :
    e * e ≠ 0 := by
  rw [he]
  exact hne

theorem orthogonal_idempotent_sum_idempotent
    [Ring A] (e f : A) (he : e * e = e) (hf : f * f = f)
    (hef : e * f = 0) (hfe : f * e = 0) :
    (e + f) * (e + f) = e + f := by
  calc
    (e + f) * (e + f) = e * e + e * f + (f * e + f * f) := by noncomm_ring
    _ = e + f := by rw [he, hef, hfe, hf]; abel

theorem orthogonal_idempotents_have_zero_jordan_product
    [Ring A] (e f : A) (hef : e * f = 0) (hfe : f * e = 0) :
    e * f + f * e = 0 := by
  rw [hef, hfe, add_zero]

theorem star_sandwich_of_self_adjoint
    [Ring A] [StarRing A] (e x : A) (he : star e = e) :
    star (e * x * e) = e * star x * e := by
  rw [star_mul, star_mul, he]
  simp only [mul_assoc]

theorem peirce_corner_square_zero
    [Semiring A] (p q x : A) (hqp : q * p = 0) :
    (p * x * q) * (p * x * q) = 0 := by
  calc
    (p * x * q) * (p * x * q) = p * x * (q * p) * x * q := by
      simp only [mul_assoc]
    _ = 0 := by rw [hqp, mul_zero, zero_mul, zero_mul]

theorem mismatched_peirce_product_zero
    [Semiring A] (p q r s x y : A) (hqr : q * r = 0) :
    (p * x * q) * (r * y * s) = 0 := by
  calc
    (p * x * q) * (r * y * s) = p * x * (q * r) * y * s := by
      simp only [mul_assoc]
    _ = 0 := by rw [hqr, mul_zero, zero_mul, zero_mul]

theorem finite_peirce_reconstruction
    [Semiring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → A) (hcomplete : ∑ i, p i = 1) (x : A) :
    (∑ i, ∑ j, p i * x * p j) = x := by
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  rw [hcomplete, one_mul, mul_one]

theorem ring_hom_preserves_associator
    [Ring A] [Ring B]
    (f : A →+* B) (x y z : A) :
    f ((x * y) * z - x * (y * z)) =
      (f x * f y) * f z - f x * (f y * f z) := by
  simp only [map_sub, map_mul]

theorem ring_hom_preserves_idempotent
    [Semiring A] [Semiring B] (f : A →+* B) (e : A)
    (he : e * e = e) : f e * f e = f e := by
  rw [← f.map_mul, he]

theorem ring_hom_preserves_orthogonal_pair
    [Semiring A] [Semiring B] (f : A →+* B) (e g : A)
    (heg : e * g = 0) (hge : g * e = 0) :
    f e * f g = 0 ∧ f g * f e = 0 := by
  constructor
  · rw [← f.map_mul, heg, map_zero]
  · rw [← f.map_mul, hge, map_zero]

theorem ring_hom_preserves_peirce_corner
    [Semiring A] [Semiring B] (f : A →+* B) (p q x : A) :
    f (p * x * q) = f p * f x * f q := by
  simp only [map_mul]

theorem cycle_sum_zero_of_potential
    [AddCommGroup A] (u v w : A) :
    ((v - u) + (w - v) + (u - w)) = 0 := by
  abel

theorem mp_range_idempotent
    [Semiring A] (x m : A) (hxm : x * m * x = x) :
    (x * m) * (x * m) = x * m := by
  calc
    (x * m) * (x * m) = (x * m * x) * m := by simp only [mul_assoc]
    _ = x * m := by rw [hxm]

theorem matrix_commutator_trace_zero
    {K : Type*} [CommRing K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (a b : Matrix n n K) :
    Matrix.trace (a * b - b * a) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

theorem square_zero_endomorphism_has_strict_kernel
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (N : Module.End R M) (hN : N * N = 0) (hN0 : N ≠ 0) :
    LinearMap.ker N ≤ LinearMap.ker (N * N) ∧
      LinearMap.ker N ≠ LinearMap.ker (N * N) := by
  constructor
  · intro x hx
    change N (N x) = 0
    rw [show N x = 0 from hx, map_zero]
  · intro hEq
    have hAll : ∀ x, N x = 0 := by
      intro x
      have hx : x ∈ LinearMap.ker (N * N) := by
        rw [hN]
        simp
      have hx' : x ∈ LinearMap.ker N := by
        rw [hEq]
        exact hx
      exact hx'
    apply hN0
    ext x
    exact hAll x

theorem idempotent_endomorphism_split
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (P : Module.End R M) (hP : P * P = P) (x : M) :
    P (P x) = P x ∧ P (x - P x) = 0 ∧ x = P x + (x - P x) := by
  have hP_apply : P (P x) = P x := by
    have hx := congrArg (fun T : Module.End R M => T x) hP
    simpa [Module.End.mul_apply] using hx
  refine ⟨hP_apply, ?_, ?_⟩
  · rw [map_sub, hP_apply, sub_self]
  · abel

theorem finite_matrix_ccr_impossible
    {K : Type*} [Field K] [CharZero K]
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (a b : Matrix n n K) : a * b - b * a ≠ (1 : Matrix n n K) := by
  intro h
  have ht := congrArg Matrix.trace h
  rw [matrix_commutator_trace_zero, Matrix.trace_one] at ht
  have hcard : (Fintype.card n : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card n))
  exact hcard ht.symm

theorem jordan_plus_lie_recovers_mul
    [Ring A] (x y : A) :
    (x * y + y * x + (x * y - y * x)) = 2 • (x * y) := by
  module

end InfoGeometry.Canonical.CounterexampleAlternatives

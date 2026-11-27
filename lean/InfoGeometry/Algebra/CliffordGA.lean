/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Algebra.CliffordGA

open CliffordAlgebra

section General

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

/-- Orthogonal generators anticommute in the Clifford algebra. -/
theorem clifford_orthogonal_vectors_anticommute
    (u v : M) (horth : QuadraticMap.polar Q u v = 0) :
    ι Q v * ι Q u = -(ι Q u * ι Q v) := by
  have h : ι Q v * ι Q u =
      algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q v u) -
        ι Q u * ι Q v := ι_mul_ι_comm v u
  rw [QuadraticMap.polar_comm, horth, map_zero, zero_sub] at h
  exact h

/-- In an orthonormal pair of positive unit vectors, the Clifford product
`ι(u) * ι(v)` squares to `-1`. This is the algebraic unit-bivector identity;
it does not identify the bivector with an external scalar imaginary unit. -/
theorem clifford_product_sq_eq_neg_one_of_orthonormal
    (u v : M) (hu : Q u = 1) (hv : Q v = 1)
    (horth : QuadraticMap.polar Q u v = 0) :
    (ι Q u * ι Q v) ^ 2 = -1 := by
  have hcomm := clifford_orthogonal_vectors_anticommute Q u v horth
  have huSq : ι Q u * ι Q u = (1 : CliffordAlgebra Q) := by
    rw [ι_sq_scalar, hu, map_one]
  have hvSq : ι Q v * ι Q v = (1 : CliffordAlgebra Q) := by
    rw [ι_sq_scalar, hv, map_one]
  calc
    (ι Q u * ι Q v) ^ 2 = ι Q u * (ι Q v * ι Q u) * ι Q v := by
      simp only [pow_two, mul_assoc]
    _ = ι Q u * (-(ι Q u * ι Q v)) * ι Q v := by rw [hcomm]
    _ = -((ι Q u * ι Q u) * (ι Q v * ι Q v)) := by noncomm_ring
    _ = -(1 * 1) := by rw [huSq, hvSq]
    _ = -1 := by simp

/-- The square of an oriented Clifford plane element records the product of
the two vector signatures. In particular, the plane squares to `-1` when the
vectors have equal unit signature and to `+1` when their unit signatures are
opposite. This is a statement about the Clifford algebra's real scalar image;
it does not identify that bivector with a central scalar imaginary unit. -/
theorem clifford_product_sq_eq_neg_quadratic_product_of_orthogonal
    (u v : M) (horth : QuadraticMap.polar Q u v = 0) :
    (ι Q u * ι Q v) ^ 2 =
      algebraMap R (CliffordAlgebra Q) (-(Q u * Q v)) := by
  have hcomm := clifford_orthogonal_vectors_anticommute Q u v horth
  calc
    (ι Q u * ι Q v) ^ 2 = ι Q u * (ι Q v * ι Q u) * ι Q v := by
      simp only [pow_two, mul_assoc]
    _ = -((ι Q u * ι Q u) * (ι Q v * ι Q v)) := by
      rw [hcomm]
      noncomm_ring
    _ = -(algebraMap R (CliffordAlgebra Q) (Q u) *
          algebraMap R (CliffordAlgebra Q) (Q v)) := by
      rw [ι_sq_scalar, ι_sq_scalar]
    _ = algebraMap R (CliffordAlgebra Q) (-(Q u * Q v)) := by
      simp only [map_mul, map_neg]

/-- Multiplication by a positive unit generator twice recovers the other
orthogonal unit generator; this is the first oriented-plane quarter-turn law. -/
theorem clifford_left_unit_vector_mul_bivector
    (u v : M) (hu : Q u = 1) :
    ι Q u * (ι Q u * ι Q v) = ι Q v := by
  rw [← mul_assoc, ι_sq_scalar, hu, map_one, one_mul]

/-- The other basis vector is sent to the negative first vector by left
multiplication by the oriented product `ι(u) * ι(v)`. -/
theorem clifford_right_unit_vector_mul_bivector
    (u v : M) (hv : Q v = 1)
    (horth : QuadraticMap.polar Q u v = 0) :
    ι Q v * (ι Q u * ι Q v) = -(ι Q u) := by
  have hcomm := clifford_orthogonal_vectors_anticommute Q u v horth
  calc
    ι Q v * (ι Q u * ι Q v) = (ι Q v * ι Q u) * ι Q v := by rw [mul_assoc]
    _ = -(ι Q u * ι Q v) * ι Q v := by rw [hcomm]
    _ = -(ι Q u) := by
      rw [neg_mul, mul_assoc, ι_sq_scalar, hv, map_one, mul_one]

/-- Symmetric part of the product of two elements in a ring. -/
def symPart {A : Type*} [Semiring A] [Invertible (2 : A)] (x y : A) : A :=
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
def IsTraceFree {A : Type*} [Semiring A] [Invertible (2 : A)] (x y : A) : Prop :=
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

lemma commute_two {A : Type*} [Semiring A] (x : A) : (2 : A) * x = x * (2 : A) := by
  rw [two_mul, mul_two]

lemma commute_invOf_two {A : Type*} [Semiring A] [Invertible (2 : A)] (x : A) :
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

/-- Reflection of `ι Q x` across the hyperplane perpendicular to a unit vector `n` (`Q n = 1`):
`-ι Q n * ι Q x * ι Q n = ι Q (x - QuadraticMap.polar Q n x • n)` (Gull–Lasenby–Doran §3 Eq. 3.1). -/
theorem clifford_unit_reflection (n x : M) (hn : Q n = 1) :
    -(ι Q n * ι Q x * ι Q n) = ι Q (x - QuadraticMap.polar Q n x • n) := by
  rw [ι_mul_ι_mul_ι, hn, one_smul, ← map_neg, neg_sub]

end General

/-- Concrete real `Cl(2, 0)` quadratic form on `Fin 2 → ℝ`. -/
def cl20Form : QuadraticForm ℝ (Fin 2 → ℝ) :=
  QuadraticMap.sq.comp (LinearMap.proj 0) + QuadraticMap.sq.comp (LinearMap.proj 1)

/-- First basis vector in `Cl(2, 0)`. -/
def cl20_e0 : CliffordAlgebra cl20Form := ι cl20Form ![1, 0]

/-- Second basis vector in `Cl(2, 0)`. -/
def cl20_e1 : CliffordAlgebra cl20Form := ι cl20Form ![0, 1]

/-- Closed `T16` non-commutativity witness in real `Cl(2, 0)` via a faithful lift into
`InfoGeometry.Algebra.FiniteSpin.Mat2R`. -/
theorem cliffordGA_cl20_noncomm_witness :
    ι cl20Form ![1, 0] * ι cl20Form ![0, 1] ≠
      ι cl20Form ![0, 1] * ι cl20Form ![1, 0] := by
  let E0 : InfoGeometry.Algebra.FiniteSpin.Mat2R := !![1, 0; 0, -1]
  let E1 : InfoGeometry.Algebra.FiniteSpin.Mat2R := !![0, 1; 1, 0]
  let f : (Fin 2 → ℝ) →ₗ[ℝ] InfoGeometry.Algebra.FiniteSpin.Mat2R :=
    { toFun := fun v => v 0 • E0 + v 1 • E1
      map_add' := fun u v => by simp [add_smul]; abel
      map_smul' := fun r v => by simp [smul_add, smul_smul] }
  have hf_sq : ∀ v : Fin 2 → ℝ,
      f v * f v = algebraMap ℝ InfoGeometry.Algebra.FiniteSpin.Mat2R (cl20Form v) := by
    intro v
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [f, E0, E1, cl20Form, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one];
       try ring)
  let φ : CliffordAlgebra cl20Form →ₐ[ℝ] InfoGeometry.Algebra.FiniteSpin.Mat2R :=
    CliffordAlgebra.lift cl20Form ⟨f, hf_sq⟩
  intro hcomm
  have hm := congrArg φ hcomm
  simp only [φ, map_mul, CliffordAlgebra.lift_ι_apply] at hm
  have h01 := congrArg (fun M : InfoGeometry.Algebra.FiniteSpin.Mat2R => M 0 1) hm
  simp [f, E0, E1, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

theorem cliffordGA_cl20_e0_e1_noncomm : cl20_e0 * cl20_e1 ≠ cl20_e1 * cl20_e0 :=
  cliffordGA_cl20_noncomm_witness

section RealRotors

private lemma scalar_inv_sqrt_mul_self {c : ℝ} (hc : 0 < c) :
    (1 / Real.sqrt c) * (1 / Real.sqrt c) * c = 1 := by
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  have hne : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  field_simp [hne]
  rw [pow_two, hsq]

private lemma scalar_half_add_half (θ₁ θ₂ : ℝ) : (θ₁ + θ₂) / 2 = θ₁ / 2 + θ₂ / 2 := by
  ring

private lemma scalar_add_two_pi_div_two (θ : ℝ) : (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi := by
  ring

private lemma scalar_two_mul_div_two (θ : ℝ) : (2 * θ) / 2 = θ := by
  ring

private lemma scalar_add_self_eq_two_mul (θ : ℝ) : θ + θ = 2 * θ := by
  ring

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private lemma cliffordGA_algebraMap_injective (Q : QuadraticForm ℝ V) :
    Function.Injective (algebraMap ℝ (CliffordAlgebra Q)) := by
  intro r₁ r₂ h
  have h1 := congrArg
    (fun x => ExteriorAlgebra.algebraMapInv (CliffordAlgebra.equivExterior Q x)) h
  simpa [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply,
    CliffordAlgebra.changeForm_algebraMap, AlgHom.commutes] using h1

theorem cliffordGA_neg_one_ne_one (Q : QuadraticForm ℝ V) :
    (-1 : CliffordAlgebra Q) ≠ 1 := by
  intro h
  have h2 : algebraMap ℝ (CliffordAlgebra Q) (2 : ℝ) =
      algebraMap ℝ (CliffordAlgebra Q) (0 : ℝ) := by
    rw [map_zero, show (2 : ℝ) = 1 + 1 by norm_num, map_add, map_one]
    calc
      (1 : CliffordAlgebra Q) + 1 = (-1 : CliffordAlgebra Q) + 1 := by rw [h]
      _ = 0 := neg_add_cancel 1
  have h20 : (2 : ℝ) = 0 := cliffordGA_algebraMap_injective Q h2
  norm_num at h20

/-! #### Simple Rotors (Gull–Lasenby–Doran §3 Eqs. 3.3–3.8) -/

/-- Simple rotor rotating unit vector `a` to unit vector `b` in the `a ∧ b` plane:
`R = (1 / √(2 + polar Q b a)) • (1 + ι Q b * ι Q a) = (1 + ba) / √(2(1 + b · a))`
(Gull–Lasenby–Doran §3 Eq. 3.5). -/
noncomputable def simpleRotor (Q : QuadraticForm ℝ V) (a b : V) : CliffordAlgebra Q :=
  (1 / Real.sqrt (2 + QuadraticMap.polar Q b a)) • (1 + ι Q b * ι Q a)

theorem two_add_polar_eq_two_mul_one_add_associated (Q : QuadraticForm ℝ V)
    [Invertible (2 : ℝ)] (a b : V) :
    2 + QuadraticMap.polar Q b a = 2 * (1 + QuadraticMap.associated (R := ℝ) Q b a) := by
  have hpol : QuadraticMap.polar Q b a = 2 * QuadraticMap.associated (R := ℝ) Q b a := by
    have h2 : (2 : ℕ) • (QuadraticMap.associated (R := ℝ) Q b a) = QuadraticMap.polar Q b a :=
      congrArg (fun B => B b a) (QuadraticMap.two_nsmul_associated (R := ℝ) ℝ Q)
    rw [nsmul_eq_mul, Nat.cast_ofNat] at h2
    exact h2.symm
  rw [hpol]
  ring

theorem simpleRotor_eq_associated (Q : QuadraticForm ℝ V) [Invertible (2 : ℝ)] (a b : V) :
    simpleRotor Q a b =
      (1 / Real.sqrt (2 * (1 + QuadraticMap.associated (R := ℝ) Q b a))) •
        (1 + ι Q b * ι Q a) := by
  rw [simpleRotor, two_add_polar_eq_two_mul_one_add_associated]

theorem two_add_polar_eq_add_sq (Q : QuadraticForm ℝ V) {a b : V}
    (ha : Q a = 1) (hb : Q b = 1) :
    2 + QuadraticMap.polar Q b a = Q (a + b) := by
  rw [QuadraticMap.map_add Q a b, ha, hb, QuadraticMap.polar_comm]
  ring

theorem simpleRotor_mem_even (Q : QuadraticForm ℝ V) (a b : V) :
    simpleRotor Q a b ∈ CliffordAlgebra.even Q := by
  unfold simpleRotor
  refine Subalgebra.smul_mem _ ?_ _
  exact Subalgebra.add_mem _ (Subalgebra.one_mem _) (ι_mul_ι_mem_evenOdd_zero Q b a)

theorem reverse_simpleRotor_eq_swap (Q : QuadraticForm ℝ V) (a b : V) :
    CliffordAlgebra.reverse (simpleRotor Q a b) = simpleRotor Q b a := by
  unfold simpleRotor
  simp only [map_smul, map_add, CliffordAlgebra.reverse.map_one, CliffordAlgebra.reverse.map_mul,
    CliffordAlgebra.reverse_ι, QuadraticMap.polar_comm]

theorem simpleRotor_mul_reverse (Q : QuadraticForm ℝ V) {a b : V}
    (ha : Q a = 1) (hb : Q b = 1) (hpos : 0 < 2 + QuadraticMap.polar Q b a) :
    simpleRotor Q a b * CliffordAlgebra.reverse (simpleRotor Q a b) = 1 := by
  rw [reverse_simpleRotor_eq_swap]
  unfold simpleRotor
  rw [QuadraticMap.polar_comm Q a b]
  set c : ℝ := 2 + QuadraticMap.polar Q b a
  set s : ℝ := 1 / Real.sqrt c
  have haSq : ι Q a * ι Q a = (1 : CliffordAlgebra Q) := by
    rw [ι_sq_scalar, ha, map_one]
  have hbSq : ι Q b * ι Q b = (1 : CliffordAlgebra Q) := by
    rw [ι_sq_scalar, hb, map_one]
  have hswap : ι Q b * ι Q a + ι Q a * ι Q b = QuadraticMap.polar Q b a • (1 : CliffordAlgebra Q) := by
    rw [ι_mul_ι_add_swap, Algebra.algebraMap_eq_smul_one]
  have hcore : (1 + ι Q b * ι Q a) * (1 + ι Q a * ι Q b) = c • (1 : CliffordAlgebra Q) := by
    calc
      (1 + ι Q b * ι Q a) * (1 + ι Q a * ι Q b)
          = (1 + 1) + (ι Q b * ι Q a + ι Q a * ι Q b) +
              ι Q b * (ι Q a * ι Q a) * ι Q b - 1 := by noncomm_ring
      _ = (1 + 1) + QuadraticMap.polar Q b a • (1 : CliffordAlgebra Q) +
              ι Q b * ι Q b - 1 := by rw [hswap, haSq, mul_one]
      _ = (2 : ℝ) • (1 : CliffordAlgebra Q) +
              QuadraticMap.polar Q b a • (1 : CliffordAlgebra Q) := by
            rw [hbSq, two_smul]
            noncomm_ring
      _ = c • (1 : CliffordAlgebra Q) := by rw [← add_smul]
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hcore, smul_smul,
    scalar_inv_sqrt_mul_self hpos, one_smul]

theorem reverse_mul_simpleRotor (Q : QuadraticForm ℝ V) {a b : V}
    (ha : Q a = 1) (hb : Q b = 1) (hpos : 0 < 2 + QuadraticMap.polar Q b a) :
    CliffordAlgebra.reverse (simpleRotor Q a b) * simpleRotor Q a b = 1 := by
  rw [reverse_simpleRotor_eq_swap]
  have hpos' : 0 < 2 + QuadraticMap.polar Q a b := by
    rw [QuadraticMap.polar_comm]
    exact hpos
  have h := simpleRotor_mul_reverse Q hb ha hpos'
  rwa [reverse_simpleRotor_eq_swap] at h

theorem simple_rotor_rotation_formula (Q : QuadraticForm ℝ V) {a b : V}
    (ha : Q a = 1) (hb : Q b = 1) (hpos : 0 < 2 + QuadraticMap.polar Q b a) :
    simpleRotor Q a b * ι Q a * CliffordAlgebra.reverse (simpleRotor Q a b) = ι Q b := by
  rw [reverse_simpleRotor_eq_swap]
  unfold simpleRotor
  rw [QuadraticMap.polar_comm Q a b]
  set c : ℝ := 2 + QuadraticMap.polar Q b a
  set s : ℝ := 1 / Real.sqrt c
  have haSq : ι Q a * ι Q a = (1 : CliffordAlgebra Q) := by
    rw [ι_sq_scalar, ha, map_one]
  have hbab : ι Q b * ι Q a * ι Q b = QuadraticMap.polar Q b a • ι Q b - ι Q a := by
    rw [ι_mul_ι_mul_ι, hb, one_smul, map_sub, map_smul]
  have hcore :
      (1 + ι Q b * ι Q a) * ι Q a * (1 + ι Q a * ι Q b) = c • ι Q b := by
    calc
      (1 + ι Q b * ι Q a) * ι Q a * (1 + ι Q a * ι Q b)
          = (ι Q a + ι Q b * (ι Q a * ι Q a)) * (1 + ι Q a * ι Q b) := by noncomm_ring
      _ = (ι Q a + ι Q b) * (1 + ι Q a * ι Q b) := by rw [haSq, mul_one]
      _ = ι Q a + (ι Q a * ι Q a) * ι Q b + ι Q b + ι Q b * ι Q a * ι Q b := by noncomm_ring
      _ = ι Q a + ι Q b + ι Q b + (QuadraticMap.polar Q b a • ι Q b - ι Q a) := by
            rw [haSq, one_mul, hbab]
      _ = (2 : ℝ) • ι Q b + QuadraticMap.polar Q b a • ι Q b := by
            rw [two_smul]
            abel
      _ = c • ι Q b := by rw [← add_smul]
  rw [Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul,
    hcore, smul_smul, scalar_inv_sqrt_mul_self hpos, one_smul]

theorem simple_rotor_inverse_rotation_formula (Q : QuadraticForm ℝ V) {a b : V}
    (ha : Q a = 1) (hb : Q b = 1) (hpos : 0 < 2 + QuadraticMap.polar Q b a) :
    CliffordAlgebra.reverse (simpleRotor Q a b) * ι Q b * simpleRotor Q a b = ι Q a := by
  have hpos' : 0 < 2 + QuadraticMap.polar Q a b := by
    rw [QuadraticMap.polar_comm]
    exact hpos
  have h := simple_rotor_rotation_formula Q hb ha hpos'
  rw [reverse_simpleRotor_eq_swap] at h
  rw [reverse_simpleRotor_eq_swap]
  exact h

theorem simple_rotor_preserves_orthogonal_vector (Q : QuadraticForm ℝ V) {a b v : V}
    (ha : Q a = 1) (hb : Q b = 1) (hpos : 0 < 2 + QuadraticMap.polar Q b a)
    (hva : Q.IsOrtho a v) (hvb : Q.IsOrtho b v) :
    simpleRotor Q a b * ι Q v * CliffordAlgebra.reverse (simpleRotor Q a b) = ι Q v := by
  have hcomm_av : ι Q a * ι Q v = -(ι Q v * ι Q a) := ι_mul_ι_comm_of_isOrtho hva
  have hcomm_bv : ι Q b * ι Q v = -(ι Q v * ι Q b) := ι_mul_ι_comm_of_isOrtho hvb
  have hcomm_ba : (1 + ι Q b * ι Q a) * ι Q v = ι Q v * (1 + ι Q b * ι Q a) := by
    calc
      (1 + ι Q b * ι Q a) * ι Q v = ι Q v + ι Q b * (ι Q a * ι Q v) := by noncomm_ring
      _ = ι Q v + ι Q b * (-(ι Q v * ι Q a)) := by rw [hcomm_av]
      _ = ι Q v - (ι Q b * ι Q v) * ι Q a := by noncomm_ring
      _ = ι Q v - (-(ι Q v * ι Q b)) * ι Q a := by rw [hcomm_bv]
      _ = ι Q v * (1 + ι Q b * ι Q a) := by noncomm_ring
  have hcomm_R : simpleRotor Q a b * ι Q v = ι Q v * simpleRotor Q a b := by
    unfold simpleRotor
    rw [Algebra.smul_mul_assoc, hcomm_ba, Algebra.mul_smul_comm]
  calc
    simpleRotor Q a b * ι Q v * CliffordAlgebra.reverse (simpleRotor Q a b)
        = (ι Q v * simpleRotor Q a b) * CliffordAlgebra.reverse (simpleRotor Q a b) := by
          rw [hcomm_R]
    _ = ι Q v * (simpleRotor Q a b * CliffordAlgebra.reverse (simpleRotor Q a b)) := by
          rw [mul_assoc]
    _ = ι Q v := by rw [simpleRotor_mul_reverse Q ha hb hpos, mul_one]

theorem simpleRotor_eq_mul_bisector (Q : QuadraticForm ℝ V) {a b : V}
    (hb : Q b = 1) :
    let n : V := (1 / Real.sqrt (2 + QuadraticMap.polar Q b a)) • (a + b)
    simpleRotor Q a b = ι Q b * ι Q n := by
  intro n
  have hbSq : ι Q b * ι Q b = (1 : CliffordAlgebra Q) := by
    rw [ι_sq_scalar, hb, map_one]
  dsimp [n, simpleRotor]
  rw [map_smul, map_add, Algebra.mul_smul_comm, mul_add, hbSq, add_comm 1 (ι Q b * ι Q a)]

theorem rotor_preserves_geometric_product (Q : QuadraticForm ℝ V)
    (R x y : CliffordAlgebra Q) (hR : CliffordAlgebra.reverse R * R = 1) :
    (R * x * CliffordAlgebra.reverse R) * (R * y * CliffordAlgebra.reverse R) =
      R * (x * y) * CliffordAlgebra.reverse R := by
  calc
    (R * x * CliffordAlgebra.reverse R) * (R * y * CliffordAlgebra.reverse R)
        = R * x * (CliffordAlgebra.reverse R * R) * y * CliffordAlgebra.reverse R := by
          noncomm_ring
    _ = R * (x * y) * CliffordAlgebra.reverse R := by rw [hR]; noncomm_ring

/-! #### Exponential Rotors & 2π Spinor Double-Cover Sign Flip (Eqs. 3.10–3.18) -/

/-- Exponential rotor generated by unit bivector `B` (`B^2 = -1`, `reverse B = -B`):
`expRotor B θ = cos(θ / 2) • 1 - sin(θ / 2) • B` (Gull–Lasenby–Doran §3 Eq. 3.10). -/
noncomputable def expRotor {Q : QuadraticForm ℝ V}
    (B : CliffordAlgebra Q) (θ : ℝ) : CliffordAlgebra Q :=
  (Real.cos (θ / 2)) • (1 : CliffordAlgebra Q) - (Real.sin (θ / 2)) • B

theorem expRotor_mem_even {Q : QuadraticForm ℝ V} {B : CliffordAlgebra Q}
    (hB : B ∈ CliffordAlgebra.even Q) (θ : ℝ) :
    expRotor B θ ∈ CliffordAlgebra.even Q := by
  unfold expRotor
  exact Subalgebra.sub_mem _ (Subalgebra.smul_mem _ (Subalgebra.one_mem _) _)
    (Subalgebra.smul_mem _ hB _)

@[simp]
theorem expRotor_zero {Q : QuadraticForm ℝ V} (B : CliffordAlgebra Q) :
    expRotor B 0 = 1 := by
  simp [expRotor]

theorem expRotor_reverse {Q : QuadraticForm ℝ V} {B : CliffordAlgebra Q}
    (hBrev : CliffordAlgebra.reverse B = -B) (θ : ℝ) :
    CliffordAlgebra.reverse (expRotor B θ) = expRotor B (-θ) := by
  unfold expRotor
  rw [map_sub, map_smul, map_smul, CliffordAlgebra.reverse.map_one, hBrev,
    smul_neg, sub_neg_eq_add, neg_div, Real.cos_neg, Real.sin_neg, neg_smul, sub_neg_eq_add]

theorem expRotor_add {Q : QuadraticForm ℝ V} {B : CliffordAlgebra Q}
    (hBsq : B * B = -1) (θ₁ θ₂ : ℝ) :
    expRotor B (θ₁ + θ₂) = expRotor B θ₁ * expRotor B θ₂ := by
  unfold expRotor
  rw [scalar_half_add_half, Real.cos_add, Real.sin_add]
  have hmul :
      (Real.cos (θ₁ / 2) • (1 : CliffordAlgebra Q) - Real.sin (θ₁ / 2) • B) *
          (Real.cos (θ₂ / 2) • (1 : CliffordAlgebra Q) - Real.sin (θ₂ / 2) • B) =
        (Real.cos (θ₁ / 2) * Real.cos (θ₂ / 2) - Real.sin (θ₁ / 2) * Real.sin (θ₂ / 2)) •
            (1 : CliffordAlgebra Q) -
          (Real.sin (θ₁ / 2) * Real.cos (θ₂ / 2) + Real.cos (θ₁ / 2) * Real.sin (θ₂ / 2)) • B := by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one, hBsq, smul_neg,
      smul_smul]
    rw [sub_smul, add_smul, mul_comm (Real.cos (θ₂ / 2)) (Real.cos (θ₁ / 2)),
      mul_comm (Real.sin (θ₂ / 2)) (Real.sin (θ₁ / 2)),
      mul_comm (Real.cos (θ₂ / 2)) (Real.sin (θ₁ / 2)),
      mul_comm (Real.sin (θ₂ / 2)) (Real.cos (θ₁ / 2))]
    abel
  exact hmul.symm

theorem expRotor_mul_reverse_eq_one {Q : QuadraticForm ℝ V} {B : CliffordAlgebra Q}
    (hBsq : B * B = -1) (hBrev : CliffordAlgebra.reverse B = -B) (θ : ℝ) :
    expRotor B θ * CliffordAlgebra.reverse (expRotor B θ) = 1 := by
  rw [expRotor_reverse hBrev, ← expRotor_add hBsq, add_neg_cancel, expRotor_zero]

theorem reverse_mul_expRotor_eq_one {Q : QuadraticForm ℝ V} {B : CliffordAlgebra Q}
    (hBsq : B * B = -1) (hBrev : CliffordAlgebra.reverse B = -B) (θ : ℝ) :
    CliffordAlgebra.reverse (expRotor B θ) * expRotor B θ = 1 := by
  rw [expRotor_reverse hBrev, ← expRotor_add hBsq, neg_add_cancel, expRotor_zero]

theorem expRotor_sandwich_of_anticomm {Q : QuadraticForm ℝ V} {B x : CliffordAlgebra Q}
    (hBsq : B * B = -1) (hBrev : CliffordAlgebra.reverse B = -B)
    (hanti : x * B = -(B * x)) (θ : ℝ) :
    expRotor B θ * x * CliffordAlgebra.reverse (expRotor B θ) =
      (Real.cos θ • (1 : CliffordAlgebra Q) - Real.sin θ • B) * x := by
  have hcomm : x * expRotor B (-θ) = expRotor B θ * x := by
    unfold expRotor
    rw [neg_div, Real.cos_neg, Real.sin_neg, neg_smul, sub_neg_eq_add]
    rw [mul_add, sub_mul]
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_one, one_mul, hanti, smul_neg,
      sub_eq_add_neg]
  calc
    expRotor B θ * x * CliffordAlgebra.reverse (expRotor B θ)
        = expRotor B θ * (x * expRotor B (-θ)) := by rw [expRotor_reverse hBrev, mul_assoc]
    _ = (expRotor B θ * expRotor B θ) * x := by rw [hcomm, mul_assoc]
    _ = expRotor B (θ + θ) * x := by rw [← expRotor_add hBsq]
    _ = (Real.cos θ • (1 : CliffordAlgebra Q) - Real.sin θ • B) * x := by
          unfold expRotor
          rw [scalar_add_self_eq_two_mul, scalar_two_mul_div_two]

theorem expRotor_sandwich_of_comm {Q : QuadraticForm ℝ V} {B x : CliffordAlgebra Q}
    (hBsq : B * B = -1) (hBrev : CliffordAlgebra.reverse B = -B)
    (hcomm : x * B = B * x) (θ : ℝ) :
    expRotor B θ * x * CliffordAlgebra.reverse (expRotor B θ) = x := by
  have hR : x * expRotor B (-θ) = expRotor B (-θ) * x := by
    unfold expRotor
    rw [mul_sub, sub_mul]
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_one, one_mul, hcomm]
  calc
    expRotor B θ * x * CliffordAlgebra.reverse (expRotor B θ)
        = expRotor B θ * (x * expRotor B (-θ)) := by rw [expRotor_reverse hBrev, mul_assoc]
    _ = (expRotor B θ * expRotor B (-θ)) * x := by rw [hR, mul_assoc]
    _ = x := by rw [← expRotor_add hBsq, add_neg_cancel, expRotor_zero, one_mul]

theorem expRotor_orthonormal_plane_rotation (Q : QuadraticForm ℝ V) {u v : V}
    (hu : Q u = 1) (hv : Q v = 1) (horth : QuadraticMap.polar Q u v = 0) (θ : ℝ) :
    let B := ι Q u * ι Q v
    expRotor B θ * ι Q u * CliffordAlgebra.reverse (expRotor B θ) =
        Real.cos θ • ι Q u + Real.sin θ • ι Q v ∧
      expRotor B θ * ι Q v * CliffordAlgebra.reverse (expRotor B θ) =
        -(Real.sin θ • ι Q u) + Real.cos θ • ι Q v := by
  intro B
  have hBsq : B * B = -1 := by
    rw [← pow_two]
    exact clifford_product_sq_eq_neg_one_of_orthonormal Q u v hu hv horth
  have hcomm_uv : ι Q v * ι Q u = -(ι Q u * ι Q v) :=
    clifford_orthogonal_vectors_anticommute Q u v horth
  have hBrev : CliffordAlgebra.reverse B = -B := by
    dsimp [B]
    rw [CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_ι, CliffordAlgebra.reverse_ι]
    exact hcomm_uv
  have hBu : B * ι Q u = -(ι Q v) := by
    dsimp [B]
    calc
      (ι Q u * ι Q v) * ι Q u = ι Q u * (ι Q v * ι Q u) := by rw [mul_assoc]
      _ = ι Q u * (-(ι Q u * ι Q v)) := by rw [hcomm_uv]
      _ = -(ι Q u * (ι Q u * ι Q v)) := by rw [mul_neg]
      _ = -(ι Q v) := by rw [clifford_left_unit_vector_mul_bivector Q u v hu]
  have huB : ι Q u * B = -(B * ι Q u) := by
    dsimp [B]
    rw [clifford_left_unit_vector_mul_bivector Q u v hu]
    dsimp [B] at hBu
    rw [hBu, neg_neg]
  have hBv : B * ι Q v = ι Q u := by
    dsimp [B]
    rw [mul_assoc, ι_sq_scalar, hv, map_one, mul_one]
  have hvB : ι Q v * B = -(B * ι Q v) := by
    dsimp [B]
    rw [clifford_right_unit_vector_mul_bivector Q u v hv horth]
    dsimp [B] at hBv
    rw [hBv]
  refine ⟨?_, ?_⟩
  · rw [expRotor_sandwich_of_anticomm hBsq hBrev huB θ, sub_mul,
      Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, one_mul, hBu, smul_neg, sub_neg_eq_add]
  · rw [expRotor_sandwich_of_anticomm hBsq hBrev hvB θ, sub_mul,
      Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, one_mul, hBv, sub_eq_add_neg, add_comm]

/-- Spinor `2π` double-cover sign flip (Gull–Lasenby–Doran §3 Eq. 3.18):
rotating by `θ + 2π` negates the spinor/rotor `expRotor B (θ + 2π) = -expRotor B θ`. -/
theorem expRotor_add_two_pi {Q : QuadraticForm ℝ V} (B : CliffordAlgebra Q) (θ : ℝ) :
    expRotor B (θ + 2 * Real.pi) = -expRotor B θ := by
  unfold expRotor
  rw [scalar_add_two_pi_div_two, Real.cos_add_pi, Real.sin_add_pi, neg_smul, neg_smul,
    sub_neg_eq_add, neg_sub]
  abel

/-- The bilinear sandwich transformation `x ↦ R x R̃` is invariant under the `2π` spinor
sign flip (Eqs. 3.2, 3.18). -/
theorem expRotor_add_two_pi_sandwich {Q : QuadraticForm ℝ V}
    (B x : CliffordAlgebra Q) (θ : ℝ) :
    expRotor B (θ + 2 * Real.pi) * x *
        CliffordAlgebra.reverse (expRotor B (θ + 2 * Real.pi)) =
      expRotor B θ * x * CliffordAlgebra.reverse (expRotor B θ) := by
  rw [expRotor_add_two_pi, map_neg]
  noncomm_ring

theorem expRotor_two_pi_ne_one {Q : QuadraticForm ℝ V} (B : CliffordAlgebra Q) :
    expRotor B (2 * Real.pi) ≠ 1 := by
  have h := expRotor_add_two_pi B 0
  rw [zero_add, expRotor_zero] at h
  rw [h]
  exact cliffordGA_neg_one_ne_one Q

end RealRotors

end InfoGeometry.Algebra.CliffordGA

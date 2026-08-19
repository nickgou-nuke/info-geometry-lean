import Mathlib.Tactic
import InfoGeometry.Canonical.CantorCuntzBasis
import InfoGeometry.Meta.Architecture

noncomputable section

namespace InfoGeometry.Canonical.CantorKMSCylinderState

open InfoGeometry.Canonical.CantorCuntzBasis

/-!
# Cantor KMS Cylinder State

This module isolates the finite-cylinder substrate for the Cuntz/KMS boundary
state.  It constructs the algebraic GNS quotient and its positive-definite
Hermitian pairing, but not a completed Hilbert space.  It proves the exact
finite-word scaling, cross-branch orthogonality, and finite partition laws
that a later completion and GNS representation should consume.

For a binary cylinder word `w`, the uniform KMS cylinder weight is `2^-|w|`.
For matrix-unit-style word pairs, the diagonal coefficient is this weight and
off-diagonal coefficients are zero.

#### BUCKET 1: CLOSED FINITE THEOREMS

[Fully verified lemmas with zero remaining dependencies or open goals. Fully
checked by the kernel.]

* `cylinderKMSWeight_nonneg`
* `cylinderKMSWeight_cons`
* `cylinderKMSWeight_cons_false`
* `cylinderKMSWeight_cons_true`
* `cylinderKMSCoeff_self`
* `cylinderKMSCoeff_ne`
* `cylinderKMSCoeff_self_nonneg`
* `cylinderKMSCoeff_cons_same`
* `cylinderKMSCoeff_cons_false_false`
* `cylinderKMSCoeff_cons_true_true`
* `cylinderKMSCoeff_cons_false_true`
* `cylinderKMSCoeff_cons_true_false`
* `cylinderKMSGNSQuadraticForm_prefixWordQuotient_children_add`
* `cylinderKMSPrefixWordQuotientLinearMap_children_add`
* `cylinderKMSGNSQuadraticForm_prefixWordQuotient_sum_bitWord`
* `cylinderKMSIsometricPrefixQuotient_range_inter_eq_singleton_zero`
* `cylinderKMSGNSRelation_iff_eq`
* `cylinderKMSGNSQuotientLinearEquiv`
* `cylinderKMSGNSHermitianPairing_self_eq_zero_iff`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

[Theorems that compile from explicitly named theorem parameters or imported
verified premises.]

* None.

#### BUCKET 3: OPEN CLOSURE DEBT

[Exact theorem statements that remain unproved. No wrappers, interfaces, fields,
witnesses, certificates, or renamed placeholders.]

* Identify that completion with the concrete `PiLp`/`lp` Cantor-boundary
  Hilbert carrier.
* Transport the Cuntz generators and phase-axis commutation through that GNS
  representation.
-/

/-- The uniform binary KMS weight of a finite cylinder word: `2^-|w|`. -/
@[rep_depth operator]
def cylinderKMSWeight (w : List Bool) : ℝ :=
  ((1 / 2 : ℝ) ^ w.length)

@[rep_depth operator]
theorem cylinderKMSWeight_nonneg (w : List Bool) :
    0 ≤ cylinderKMSWeight w := by
  unfold cylinderKMSWeight
  exact pow_nonneg (by norm_num) w.length

theorem cylinderKMSWeight_pos (w : List Bool) :
    0 < cylinderKMSWeight w := by
  unfold cylinderKMSWeight
  exact pow_pos (by norm_num) w.length

def cylinderKMSQuadratic
    (n : ℕ) (f : (Fin n → Bool) → ℂ) : ℝ :=
  ∑ w : (Fin n → Bool),
    cylinderKMSWeight (List.ofFn w) * ‖f w‖ ^ 2

theorem cylinderKMSQuadratic_nonneg
    (n : ℕ) (f : (Fin n → Bool) → ℂ) :
    0 ≤ cylinderKMSQuadratic n f := by
  unfold cylinderKMSQuadratic
  apply Finset.sum_nonneg
  intro w hw
  exact mul_nonneg
    (cylinderKMSWeight_nonneg (List.ofFn w))
    (sq_nonneg _)

theorem cylinderKMSQuadratic_pos_of_exists_ne
    (n : ℕ) (f : (Fin n → Bool) → ℂ)
    (hf : ∃ w, f w ≠ 0) :
    0 < cylinderKMSQuadratic n f := by
  rcases hf with ⟨w, hw⟩
  unfold cylinderKMSQuadratic
  apply Finset.sum_pos'
  · intro v hv
    exact mul_nonneg
      (cylinderKMSWeight_nonneg (List.ofFn v))
      (sq_nonneg _)
  · refine ⟨w, Finset.mem_univ w, ?_⟩
    have hnorm : 0 < ‖f w‖ := norm_pos_iff.mpr hw
    exact mul_pos
      (cylinderKMSWeight_pos (List.ofFn w))
      (sq_pos_of_pos hnorm)

theorem cylinderKMSQuadratic_eq_zero_iff
    (n : ℕ) (f : (Fin n → Bool) → ℂ) :
    cylinderKMSQuadratic n f = 0 ↔ ∀ w, f w = 0 := by
  constructor
  · intro h w
    by_contra hw
    have hpos := cylinderKMSQuadratic_pos_of_exists_ne n f ⟨w, hw⟩
    linarith
  · intro hf
    unfold cylinderKMSQuadratic
    apply Finset.sum_eq_zero
    intro w hw
    simp [hf w]

theorem cylinderKMSQuadratic_eq_zero_iff_fun_eq_zero
    (n : ℕ) (f : (Fin n → Bool) → ℂ) :
    cylinderKMSQuadratic n f = 0 ↔ f = 0 := by
  constructor
  · intro h
    funext w
    exact (cylinderKMSQuadratic_eq_zero_iff n f).mp h w
  · intro h
    subst f
    simp [cylinderKMSQuadratic]

theorem cylinderKMSQuadratic_pos_iff_exists_ne
    (n : ℕ) (f : (Fin n → Bool) → ℂ) :
    0 < cylinderKMSQuadratic n f ↔ ∃ w, f w ≠ 0 := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have hf : f = 0 := by
      funext w
      exact hne w
    subst f
    simp [cylinderKMSQuadratic] at h
  · rintro ⟨w, hw⟩
    exact cylinderKMSQuadratic_pos_of_exists_ne n f ⟨w, hw⟩

/-- Prefixing either binary branch halves the cylinder KMS weight. -/
@[rep_depth operator]
theorem cylinderKMSWeight_cons (b : Bool) (w : List Bool) :
    cylinderKMSWeight (b :: w) = (1 / 2 : ℝ) * cylinderKMSWeight w := by
  simp [cylinderKMSWeight, pow_succ, mul_comm]

@[rep_depth operator]
theorem cylinderKMSWeight_cons_false (w : List Bool) :
    cylinderKMSWeight (false :: w) = (1 / 2 : ℝ) * cylinderKMSWeight w :=
  cylinderKMSWeight_cons false w

@[rep_depth operator]
theorem cylinderKMSWeight_cons_true (w : List Bool) :
    cylinderKMSWeight (true :: w) = (1 / 2 : ℝ) * cylinderKMSWeight w :=
  cylinderKMSWeight_cons true w

theorem cylinderKMSWeight_append (u v : List Bool) :
    cylinderKMSWeight (u ++ v) =
      cylinderKMSWeight u * cylinderKMSWeight v := by
  unfold cylinderKMSWeight
  rw [List.length_append, pow_add]

@[simp] theorem cylinderKMSWeight_ofFn
    (n : ℕ) (w : Fin n → Bool) :
    cylinderKMSWeight (List.ofFn w) = (1 / 2 : ℝ) ^ n := by
  simp [cylinderKMSWeight]

theorem cylinderKMSWeight_sum_bitWord (n : ℕ) :
    ∑ w : (Fin n → Bool), cylinderKMSWeight (List.ofFn w) = 1 := by
  simp [cylinderKMSWeight, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_pow]

theorem cylinderKMSWeight_sum_append_bitWord
    (u : List Bool) (n : ℕ) :
    ∑ w : (Fin n → Bool),
      cylinderKMSWeight (u ++ List.ofFn w) = cylinderKMSWeight u := by
  calc
    ∑ w : (Fin n → Bool),
        cylinderKMSWeight (u ++ List.ofFn w) =
        ∑ w : (Fin n → Bool),
          cylinderKMSWeight u * cylinderKMSWeight (List.ofFn w) := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [cylinderKMSWeight_append]
    _ = cylinderKMSWeight u *
          (∑ w : (Fin n → Bool), cylinderKMSWeight (List.ofFn w)) := by
            rw [Finset.mul_sum]
    _ = cylinderKMSWeight u := by
          rw [cylinderKMSWeight_sum_bitWord]
          ring

/--
The two depth-one children of a cylinder split the parent weight evenly.

This is the finite algebraic version of the shard/whole readout: each branch
contains exactly half of the cylinder mass, and the two children sum back to the
parent.
-/
@[rep_depth operator]
theorem cylinderKMSWeight_children_sum (w : List Bool) :
    cylinderKMSWeight (false :: w) + cylinderKMSWeight (true :: w) =
      cylinderKMSWeight w := by
  rw [cylinderKMSWeight_cons_false, cylinderKMSWeight_cons_true]
  ring

@[rep_depth operator]
theorem cylinderKMSWeight_bool_sum (w : List Bool) :
    ∑ b : Bool, cylinderKMSWeight (b :: w) = cylinderKMSWeight w := by
  rw [Fintype.sum_bool]
  exact cylinderKMSWeight_children_sum w

/--
Diagonal finite-cylinder coefficient for the uniform KMS state.

This is the matrix-unit shadow of `φ(S_u S_v*)`: diagonal pairs receive the
cylinder weight, off-diagonal pairs vanish.
-/
@[rep_depth operator]
def cylinderKMSCoeff (u v : List Bool) : ℝ :=
  if u = v then cylinderKMSWeight u else 0

@[simp, rep_depth operator]
theorem cylinderKMSCoeff_self (w : List Bool) :
    cylinderKMSCoeff w w = cylinderKMSWeight w := by
  simp [cylinderKMSCoeff]

theorem cylinderKMSCoeff_sum_diag_bitWord (n : ℕ) :
    ∑ w : (Fin n → Bool),
      cylinderKMSCoeff (List.ofFn w) (List.ofFn w) = 1 := by
  simpa only [cylinderKMSCoeff_self] using cylinderKMSWeight_sum_bitWord n

@[rep_depth operator]
theorem cylinderKMSCoeff_ne {u v : List Bool} (h : u ≠ v) :
    cylinderKMSCoeff u v = 0 := by
  simp [cylinderKMSCoeff, h]

theorem cylinderKMSCoeff_eq_zero_iff (u v : List Bool) :
    cylinderKMSCoeff u v = 0 ↔ u ≠ v := by
  constructor
  · intro hzero huv
    subst v
    rw [cylinderKMSCoeff_self] at hzero
    exact (ne_of_gt (cylinderKMSWeight_pos u)) hzero
  · exact cylinderKMSCoeff_ne

@[rep_depth operator]
theorem cylinderKMSCoeff_self_nonneg (w : List Bool) :
    0 ≤ cylinderKMSCoeff w w := by
  simp [cylinderKMSCoeff_self, cylinderKMSWeight_nonneg]

theorem cylinderKMSCoeff_nonneg (u v : List Bool) :
    0 ≤ cylinderKMSCoeff u v := by
  by_cases h : u = v
  · subst v
    exact cylinderKMSCoeff_self_nonneg u
  · rw [cylinderKMSCoeff_ne h]

theorem cylinderKMSCoeff_append_right
    (u v w : List Bool) :
    cylinderKMSCoeff (u ++ w) (v ++ w) =
      if u = v then cylinderKMSWeight u * cylinderKMSWeight w else 0 := by
  by_cases h : u = v
  · subst v
    simp [cylinderKMSCoeff_self, cylinderKMSWeight_append]
  · have h' : u ++ w ≠ v ++ w := by
      intro huv
      exact h (List.append_left_injective w huv)
    rw [cylinderKMSCoeff_ne h', if_neg h]

theorem cylinderKMSCoeff_append_right_factor
    (u v w : List Bool) :
    cylinderKMSCoeff (u ++ w) (v ++ w) =
      cylinderKMSCoeff u v * cylinderKMSWeight w := by
  by_cases h : u = v
  · subst v
    rw [cylinderKMSCoeff_append_right]
    simp [cylinderKMSCoeff_self]
  · rw [cylinderKMSCoeff_append_right, if_neg h,
      cylinderKMSCoeff_ne h]
    simp

theorem cylinderKMSCoeff_append_left
    (w u v : List Bool) :
    cylinderKMSCoeff (w ++ u) (w ++ v) =
      if u = v then cylinderKMSWeight w * cylinderKMSWeight u else 0 := by
  by_cases h : u = v
  · subst v
    simp [cylinderKMSCoeff_self, cylinderKMSWeight_append]
  · have h' : w ++ u ≠ w ++ v := by
      intro huv
      exact h (List.append_right_injective w huv)
    rw [cylinderKMSCoeff_ne h', if_neg h]

theorem cylinderKMSCoeff_append_left_factor
    (w u v : List Bool) :
    cylinderKMSCoeff (w ++ u) (w ++ v) =
      cylinderKMSWeight w * cylinderKMSCoeff u v := by
  by_cases h : u = v
  · subst v
    rw [cylinderKMSCoeff_append_left]
    simp [cylinderKMSCoeff_self]
  · rw [cylinderKMSCoeff_append_left, if_neg h,
      cylinderKMSCoeff_ne h]
    simp

theorem cylinderKMSCoeff_quadratic_nonneg
    (s : Finset (List Bool)) (f : List Bool → ℝ) :
    0 ≤ s.sum (fun u => s.sum (fun v =>
      f u * cylinderKMSCoeff u v * f v)) := by
  classical
  refine Finset.sum_nonneg fun u hu => ?_
  rw [Finset.sum_eq_single u]
  · rw [cylinderKMSCoeff_self]
    calc
      f u * cylinderKMSWeight u * f u =
          (f u) ^ 2 * cylinderKMSWeight u := by ring
      _ ≥ 0 := mul_nonneg (sq_nonneg (f u))
        (cylinderKMSWeight_nonneg u)
  · intro v hv hne
    have hne' : u ≠ v := Ne.symm hne
    simp [cylinderKMSCoeff, hne']
  · intro hu'
    exact (hu' hu).elim

theorem cylinderKMSCoeff_complex_quadratic_nonneg
    (s : Finset (List Bool)) (f : List Bool → ℂ) :
    0 ≤ (s.sum (fun u => s.sum (fun v =>
      star (f u) * (cylinderKMSCoeff u v : ℂ) * f v))).re := by
  classical
  have hinner (u : List Bool) (hu_mem : u ∈ s) :
      s.sum (fun v =>
        star (f u) * (cylinderKMSCoeff u v : ℂ) * f v) =
        (cylinderKMSCoeff u u : ℂ) * Complex.normSq (f u) := by
    rw [Finset.sum_eq_single u]
    · rw [cylinderKMSCoeff_self]
      calc
        star (f u) * (cylinderKMSWeight u : ℂ) * f u =
            (cylinderKMSWeight u : ℂ) *
              (f u * star (f u)) := by ring
        _ = (cylinderKMSWeight u : ℂ) * Complex.normSq (f u) := by
          have hnorm : f u * star (f u) =
              (Complex.normSq (f u) : ℂ) := by
            simpa only [starRingEnd_apply] using Complex.mul_conj (f u)
          rw [hnorm]
    · intro v hv hne
      rw [cylinderKMSCoeff_ne (Ne.symm hne)]
      simp
    · intro hu_not
      exact (hu_not hu_mem).elim
  have hreal (u : List Bool) (hu : u ∈ s) :
      (s.sum (fun v =>
        star (f u) * (cylinderKMSCoeff u v : ℂ) * f v)).re =
        cylinderKMSCoeff u u * Complex.normSq (f u) := by
    rw [hinner u hu]
    simp [Complex.mul_re]
  calc
    0 ≤ s.sum (fun u => cylinderKMSCoeff u u * Complex.normSq (f u)) := by
      exact Finset.sum_nonneg fun u hu =>
        mul_nonneg (cylinderKMSCoeff_nonneg u u)
          (Complex.normSq_nonneg (f u))
    _ = (s.sum (fun u => s.sum (fun v =>
        star (f u) * (cylinderKMSCoeff u v : ℂ) * f v))).re := by
      rw [← Complex.reCLM_apply, map_sum]
      apply Finset.sum_congr rfl
      intro u hu
      exact (hreal u hu).symm

theorem cylinderKMSCoeff_complex_quadratic_eq_diag
    (s : Finset (List Bool)) (f : List Bool → ℂ) :
    (s.sum (fun u => s.sum (fun v =>
      star (f u) * (cylinderKMSCoeff u v : ℂ) * f v))).re =
        s.sum (fun u => cylinderKMSCoeff u u * Complex.normSq (f u)) := by
  classical
  rw [← Complex.reCLM_apply, map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_eq_single u]
  · rw [cylinderKMSCoeff_self]
    have hnorm : f u * star (f u) =
        (Complex.normSq (f u) : ℂ) := by
      simpa only [starRingEnd_apply] using Complex.mul_conj (f u)
    calc
      (star (f u) * (cylinderKMSWeight u : ℂ) * f u).re =
          ((cylinderKMSWeight u : ℂ) * Complex.normSq (f u)).re := by
            rw [show star (f u) * (cylinderKMSWeight u : ℂ) * f u =
              (cylinderKMSWeight u : ℂ) * (f u * star (f u)) by ring]
            rw [hnorm]
      _ = cylinderKMSWeight u * Complex.normSq (f u) := by
            simp [Complex.mul_re]
  · intro v hv hne
    rw [cylinderKMSCoeff_ne (Ne.symm hne)]
    simp
  · intro hu_not
    exact (hu_not hu).elim

theorem cylinderKMSCoeff_complex_quadratic_eq_zero_iff
    (s : Finset (List Bool)) (f : List Bool → ℂ) :
    (s.sum (fun u => s.sum (fun v =>
      star (f u) * (cylinderKMSCoeff u v : ℂ) * f v))).re = 0 ↔
        ∀ u ∈ s, f u = 0 := by
  classical
  have hinner (u : List Bool) (hu_mem : u ∈ s) :
      s.sum (fun v =>
        star (f u) * (cylinderKMSCoeff u v : ℂ) * f v) =
        (cylinderKMSCoeff u u : ℂ) * Complex.normSq (f u) := by
    rw [Finset.sum_eq_single u]
    · rw [cylinderKMSCoeff_self]
      calc
        star (f u) * (cylinderKMSWeight u : ℂ) * f u =
            (cylinderKMSWeight u : ℂ) *
              (f u * star (f u)) := by ring
        _ = (cylinderKMSWeight u : ℂ) * Complex.normSq (f u) := by
          have hnorm : f u * star (f u) =
              (Complex.normSq (f u) : ℂ) := by
            simpa only [starRingEnd_apply] using Complex.mul_conj (f u)
          rw [hnorm]
    · intro v hv hne
      rw [cylinderKMSCoeff_ne (Ne.symm hne)]
      simp
    · intro hu_not
      exact (hu_not hu_mem).elim
  have hsum :
      (s.sum (fun u => s.sum (fun v =>
        star (f u) * (cylinderKMSCoeff u v : ℂ) * f v))).re =
        s.sum (fun u => cylinderKMSCoeff u u * Complex.normSq (f u)) := by
    rw [← Complex.reCLM_apply, map_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [hinner u hu]
    simp [Complex.mul_re]
  rw [hsum]
  constructor
  · intro hzero u hu
    have hterms :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun v hv =>
        mul_nonneg (cylinderKMSCoeff_nonneg v v)
          (Complex.normSq_nonneg (f v)))).mp hzero
    have hterm := hterms u hu
    have hnorm : Complex.normSq (f u) = 0 :=
      (mul_eq_zero.mp hterm).resolve_left
        (ne_of_gt (by
          rw [cylinderKMSCoeff_self]
          exact cylinderKMSWeight_pos u))
    exact Complex.normSq_eq_zero.mp hnorm
  · intro hf
    apply Finset.sum_eq_zero
    intro u hu
    rw [hf u hu]
    simp

theorem cylinderKMSCoeff_complex_quadratic_pos
    (s : Finset (List Bool)) (f : List Bool → ℂ)
    (hf : ∃ u ∈ s, f u ≠ 0) :
    0 < (s.sum (fun u => s.sum (fun v =>
      star (f u) * (cylinderKMSCoeff u v : ℂ) * f v))).re := by
  have hnonneg := cylinderKMSCoeff_complex_quadratic_nonneg s f
  have hzero :
      (s.sum (fun u => s.sum (fun v =>
        star (f u) * (cylinderKMSCoeff u v : ℂ) * f v))).re ≠ 0 := by
    intro h
    have hvanish : ∀ u ∈ s, f u = 0 :=
      (cylinderKMSCoeff_complex_quadratic_eq_zero_iff s f).mp h
    obtain ⟨u, hu, hfu⟩ := hf
    exact hfu (hvanish u hu)
  exact lt_of_le_of_ne hnonneg (Ne.symm hzero)

theorem cylinderKMSCoeff_singleton_quadratic_pos
    (u : List Bool) {x : ℝ} (hx : x ≠ 0) :
    0 < ({u} : Finset (List Bool)).sum (fun a =>
      ({u} : Finset (List Bool)).sum (fun b =>
        x * cylinderKMSCoeff a b * x)) := by
  simp only [Finset.sum_singleton, cylinderKMSCoeff, if_pos]
  calc
    0 < x ^ 2 * cylinderKMSWeight u :=
      mul_pos (sq_pos_of_ne_zero hx) (cylinderKMSWeight_pos u)
    _ = x * cylinderKMSWeight u * x := by ring

theorem cylinderKMSCoeff_singleton_quadratic_eq_zero_iff
    (u : List Bool) (x : ℝ) :
    ({u} : Finset (List Bool)).sum (fun a =>
      ({u} : Finset (List Bool)).sum (fun b =>
        x * cylinderKMSCoeff a b * x)) = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    have hpos := cylinderKMSCoeff_singleton_quadratic_pos u hx
    rw [h] at hpos
    exact (lt_irrefl 0 hpos)
  · intro hx
    subst x
    simp

theorem cylinderKMSCoeff_quadratic_eq_zero_iff
    (s : Finset (List Bool)) (f : List Bool → ℝ) :
    s.sum (fun u => s.sum (fun v =>
      f u * cylinderKMSCoeff u v * f v)) = 0 ↔
        ∀ u ∈ s, f u = 0 := by
  classical
  have hdiag :
      s.sum (fun u => s.sum (fun v =>
        f u * cylinderKMSCoeff u v * f v)) =
        s.sum (fun u => (f u) ^ 2 * cylinderKMSWeight u) := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.sum_eq_single u]
    · rw [cylinderKMSCoeff_self]
      ring
    · intro v hv hne
      have hne' : u ≠ v := Ne.symm hne
      simp [cylinderKMSCoeff, hne']
    · intro hnot
      exact (hnot hu).elim
  rw [hdiag]
  constructor
  · intro h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun u hu =>
      mul_nonneg (sq_nonneg (f u)) (cylinderKMSWeight_nonneg u))).mp h
    intro u hu
    have hu0 := hz u hu
    have hsq : (f u) ^ 2 = 0 := by
      exact (mul_eq_zero.mp hu0).resolve_right
        (ne_of_gt (cylinderKMSWeight_pos u))
    exact sq_eq_zero_iff.mp hsq
  · intro hf
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun u hu =>
      mul_nonneg (sq_nonneg (f u)) (cylinderKMSWeight_nonneg u))).mpr
    intro u hu
    rw [hf u hu]
    simp

theorem cylinderKMSCoeff_quadratic_pos
    (s : Finset (List Bool)) (f : List Bool → ℝ)
    (hf : ∃ u ∈ s, f u ≠ 0) :
    0 < s.sum (fun u => s.sum (fun v =>
      f u * cylinderKMSCoeff u v * f v)) := by
  have hnonneg := cylinderKMSCoeff_quadratic_nonneg s f
  have hne : s.sum (fun u => s.sum (fun v =>
      f u * cylinderKMSCoeff u v * f v)) ≠ 0 := by
    intro hzero
    have hz := (cylinderKMSCoeff_quadratic_eq_zero_iff s f).mp hzero
    obtain ⟨u, hu, hfu⟩ := hf
    exact hfu (hz u hu)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem cylinderKMSCoeff_symm (u v : List Bool) :
    cylinderKMSCoeff u v = cylinderKMSCoeff v u := by
  by_cases h : u = v
  · subst v
    rfl
  · rw [cylinderKMSCoeff_ne h, cylinderKMSCoeff_ne (Ne.symm h)]

theorem cylinderKMSCoeff_complex_hermitian (u v : List Bool) :
    star (cylinderKMSCoeff u v : ℂ) =
      (cylinderKMSCoeff v u : ℂ) := by
  rw [cylinderKMSCoeff_symm]
  simp

noncomputable def cylinderKMSFinsuppQuadraticForm
    (f : List Bool →₀ ℂ) : ℝ :=
  (f.support.sum (fun u => f.support.sum (fun v =>
    star (f u) * (cylinderKMSCoeff u v : ℂ) * f v))).re

theorem cylinderKMSFinsuppQuadraticForm_eq_weighted_normSq
    (f : List Bool →₀ ℂ) :
    cylinderKMSFinsuppQuadraticForm f =
      f.support.sum (fun u =>
        cylinderKMSWeight u * Complex.normSq (f u)) := by
  classical
  unfold cylinderKMSFinsuppQuadraticForm
  have hinner (u : List Bool) (hu : u ∈ f.support) :
      f.support.sum (fun v =>
        star (f u) * (cylinderKMSCoeff u v : ℂ) * f v) =
        (cylinderKMSCoeff u u : ℂ) * Complex.normSq (f u) := by
    rw [Finset.sum_eq_single u]
    · rw [cylinderKMSCoeff_self]
      calc
        star (f u) * (cylinderKMSWeight u : ℂ) * f u =
            (cylinderKMSWeight u : ℂ) *
              (f u * star (f u)) := by ring
        _ = (cylinderKMSWeight u : ℂ) * Complex.normSq (f u) := by
          have hnorm : f u * star (f u) =
              (Complex.normSq (f u) : ℂ) := by
            simpa only [starRingEnd_apply] using Complex.mul_conj (f u)
          rw [hnorm]
    · intro v hv hne
      rw [cylinderKMSCoeff_ne (Ne.symm hne)]
      simp
    · intro hu_not
      exact (hu_not hu).elim
  rw [← Complex.reCLM_apply, map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [hinner u hu]
  simp [Complex.mul_re]

noncomputable def cylinderKMSHermitianPairing
    (f g : List Bool →₀ ℂ) : ℂ :=
  (f.support ∪ g.support).sum (fun u =>
    (cylinderKMSWeight u : ℂ) * star (f u) * g u)

theorem cylinderKMSHermitianPairing_self_re
    (f : List Bool →₀ ℂ) :
    (cylinderKMSHermitianPairing f f).re =
      cylinderKMSFinsuppQuadraticForm f := by
  rw [cylinderKMSFinsuppQuadraticForm_eq_weighted_normSq]
  unfold cylinderKMSHermitianPairing
  rw [Finset.union_self]
  rw [← Complex.reCLM_apply, map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hnorm : star (f u) * f u =
      (Complex.normSq (f u) : ℂ) := by
    calc
      star (f u) * f u = f u * star (f u) := by ring
      _ = (Complex.normSq (f u) : ℂ) := by
        simpa only [starRingEnd_apply] using Complex.mul_conj (f u)
  calc
    ((cylinderKMSWeight u : ℂ) * star (f u) * f u).re =
        ((cylinderKMSWeight u : ℂ) * (star (f u) * f u)).re := by
          congr 1 <;> ring
    _ = cylinderKMSWeight u * Complex.normSq (f u) := by
      rw [hnorm]
      simp [Complex.mul_re]

theorem cylinderKMSHermitianPairing_conj_symm
    (f g : List Bool →₀ ℂ) :
    star (cylinderKMSHermitianPairing f g) =
      cylinderKMSHermitianPairing g f := by
  unfold cylinderKMSHermitianPairing
  change starRingEnd ℂ
      ((f.support ∪ g.support).sum (fun u =>
        (cylinderKMSWeight u : ℂ) * star (f u) * g u)) = _
  rw [map_sum, Finset.union_comm]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [map_mul, starRingEnd_apply, star_star]
  have hw : star (cylinderKMSWeight u : ℂ) =
      (cylinderKMSWeight u : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [hw]
  ring

noncomputable def cylinderKMSPrefix (b : Bool) :
    (List Bool →₀ ℂ) →ₗ[ℂ] (List Bool →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ (fun w => b :: w)

noncomputable def cylinderKMSPrefixWord (w : List Bool) :
    (List Bool →₀ ℂ) →ₗ[ℂ] (List Bool →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ (fun v => w ++ v)

theorem cylinderKMSPrefixWord_nil :
    cylinderKMSPrefixWord [] = LinearMap.id := by
  apply LinearMap.ext
  intro f
  change Finsupp.mapDomain id f = f
  exact Finsupp.mapDomain_id

theorem cylinderKMSPrefixWord_append
    (u v : List Bool) :
    (cylinderKMSPrefixWord u).comp (cylinderKMSPrefixWord v) =
      cylinderKMSPrefixWord (u ++ v) := by
  apply LinearMap.ext
  intro f
  change Finsupp.mapDomain (fun x => u ++ x)
      (Finsupp.mapDomain (fun x => v ++ x) f) =
    Finsupp.mapDomain (fun x => (u ++ v) ++ x) f
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext x
  simp [List.append_assoc]

theorem cylinderKMSPrefixWord_cons
    (b : Bool) (w : List Bool) :
    cylinderKMSPrefixWord (b :: w) =
      (cylinderKMSPrefix b).comp (cylinderKMSPrefixWord w) := by
  apply LinearMap.ext
  intro f
  change Finsupp.mapDomain (fun v => (b :: w) ++ v) f =
    Finsupp.mapDomain (fun v => b :: v)
      (Finsupp.mapDomain (fun v => w ++ v) f)
  rw [← Finsupp.mapDomain_comp]
  congr 1

theorem cylinderKMSPrefixWord_support
    (w : List Bool) (f : List Bool →₀ ℂ) :
    (cylinderKMSPrefixWord w f).support =
      f.support.image (fun v => w ++ v) := by
  classical
  change (Finsupp.mapDomain (fun v => w ++ v) f).support = _
  exact Finsupp.mapDomain_support_of_injective
    (by
      intro u v h
      exact List.append_right_injective w h) f

theorem cylinderKMSFinsuppQuadraticForm_prefixWord
    (w : List Bool) (f : List Bool →₀ ℂ) :
    cylinderKMSFinsuppQuadraticForm (cylinderKMSPrefixWord w f) =
      cylinderKMSWeight w * cylinderKMSFinsuppQuadraticForm f := by
  classical
  rw [cylinderKMSFinsuppQuadraticForm_eq_weighted_normSq,
    cylinderKMSFinsuppQuadraticForm_eq_weighted_normSq,
    cylinderKMSPrefixWord_support]
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    have hinj : Function.Injective (fun u : List Bool => w ++ u) := by
      intro u v h
      exact List.append_right_injective w h
    change cylinderKMSWeight (w ++ v) *
        Complex.normSq ((Finsupp.mapDomain (fun u => w ++ u) f) (w ++ v)) =
      cylinderKMSWeight w *
        (cylinderKMSWeight v * Complex.normSq (f v))
    rw [Finsupp.mapDomain_apply hinj f v, cylinderKMSWeight_append]
    ring
  · intro u hu v hv huv
    exact List.append_right_injective w huv

theorem cylinderKMSPrefix_apply
    (b : Bool) (f : List Bool →₀ ℂ) :
    cylinderKMSPrefix b f = Finsupp.mapDomain (fun w => b :: w) f :=
  rfl

theorem cylinderKMSPrefix_injective (b : Bool) :
    Function.Injective (cylinderKMSPrefix b) := by
  intro f g h
  change Finsupp.mapDomain (fun w => b :: w) f =
    Finsupp.mapDomain (fun w => b :: w) g at h
  exact Finsupp.mapDomain_injective
    (by
      intro u v huv
      cases huv
      rfl) h

theorem cylinderKMSPrefix_false_eq_true_iff
    (f g : List Bool →₀ ℂ) :
    cylinderKMSPrefix false f = cylinderKMSPrefix true g ↔
      f = 0 ∧ g = 0 := by
  constructor
  · intro h
    change Finsupp.mapDomain (fun w => false :: w) f =
      Finsupp.mapDomain (fun w => true :: w) g at h
    constructor
    · apply Finsupp.ext
      intro u
      have hu := congrArg (fun z : List Bool →₀ ℂ => z (false :: u)) h
      change (Finsupp.mapDomain (fun w => false :: w) f) (false :: u) =
        (Finsupp.mapDomain (fun w => true :: w) g) (false :: u) at hu
      have hfalse : Function.Injective (fun w : List Bool => false :: w) := by
        intro v w hvw
        cases hvw
        rfl
      rw [Finsupp.mapDomain_apply hfalse f u] at hu
      have hnot : false :: u ∉ Set.range (fun w : List Bool => true :: w) := by
        rintro ⟨v, hv⟩
        cases hv
      rw [Finsupp.mapDomain_notin_range g (false :: u) hnot] at hu
      exact hu
    · apply Finsupp.ext
      intro u
      have hu := congrArg (fun z : List Bool →₀ ℂ => z (true :: u)) h
      change (Finsupp.mapDomain (fun w => false :: w) f) (true :: u) =
        (Finsupp.mapDomain (fun w => true :: w) g) (true :: u) at hu
      have htrue : Function.Injective (fun w : List Bool => true :: w) := by
        intro v w hvw
        cases hvw
        rfl
      have hnot : true :: u ∉ Set.range (fun w : List Bool => false :: w) := by
        rintro ⟨v, hv⟩
        cases hv
      rw [Finsupp.mapDomain_notin_range f (true :: u) hnot] at hu
      rw [Finsupp.mapDomain_apply htrue g u] at hu
      exact hu.symm
  · rintro ⟨rfl, rfl⟩
    simp [cylinderKMSPrefix]

theorem cylinderKMSPrefix_support
    (b : Bool) (f : List Bool →₀ ℂ) :
    (cylinderKMSPrefix b f).support =
      f.support.image (fun w => b :: w) := by
  classical
  change (Finsupp.mapDomain (fun w => b :: w) f).support = _
  exact Finsupp.mapDomain_support_of_injective
    (by
      intro u v h
      cases h
      rfl) f

theorem cylinderKMSFinsuppQuadraticForm_prefix
    (b : Bool) (f : List Bool →₀ ℂ) :
    cylinderKMSFinsuppQuadraticForm (cylinderKMSPrefix b f) =
      (1 / 2 : ℝ) * cylinderKMSFinsuppQuadraticForm f := by
  classical
  rw [cylinderKMSFinsuppQuadraticForm_eq_weighted_normSq,
    cylinderKMSFinsuppQuadraticForm_eq_weighted_normSq,
    cylinderKMSPrefix_support]
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have hinj : Function.Injective (fun w : List Bool => b :: w) := by
      intro v w h
      cases h
      rfl
    change cylinderKMSWeight (b :: u) *
        Complex.normSq ((Finsupp.mapDomain (fun w => b :: w) f) (b :: u)) =
      (1 / 2 : ℝ) * (cylinderKMSWeight u * Complex.normSq (f u))
    rw [Finsupp.mapDomain_apply hinj f u, cylinderKMSWeight_cons]
    ring
  · intro u hu v hv huv
    cases huv
    rfl

theorem cylinderKMSHermitianPairing_prefix
    (b : Bool) (f g : List Bool →₀ ℂ) :
    cylinderKMSHermitianPairing
        (cylinderKMSPrefix b f) (cylinderKMSPrefix b g) =
      (1 / 2 : ℂ) * cylinderKMSHermitianPairing f g := by
  classical
  unfold cylinderKMSHermitianPairing
  rw [cylinderKMSPrefix_support, cylinderKMSPrefix_support]
  rw [← Finset.image_union]
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have hinj : Function.Injective (fun w : List Bool => b :: w) := by
      intro v w h
      cases h
      rfl
    rw [cylinderKMSPrefix_apply, cylinderKMSPrefix_apply]
    change cylinderKMSWeight (b :: u) *
        star ((Finsupp.mapDomain (fun w => b :: w) f) (b :: u)) *
        (Finsupp.mapDomain (fun w => b :: w) g) (b :: u) =
      (1 / 2 : ℂ) *
        ((cylinderKMSWeight u : ℂ) * star (f u) * g u)
    rw [Finsupp.mapDomain_apply hinj f u,
      Finsupp.mapDomain_apply hinj g u,
      cylinderKMSWeight_cons]
    norm_num
    ring
  · intro u hu v hv huv
    exact List.cons.inj huv |>.2

theorem cylinderKMSHermitianPairing_prefix_false_true
    (f g : List Bool →₀ ℂ) :
    cylinderKMSHermitianPairing
        (cylinderKMSPrefix false f) (cylinderKMSPrefix true g) = 0 := by
  classical
  unfold cylinderKMSHermitianPairing
  apply Finset.sum_eq_zero
  intro u hu
  cases u with
  | nil =>
      have hfalse : [] ∉ Set.range (fun w : List Bool => false :: w) := by
        rintro ⟨v, hv⟩
        cases hv
      have htrue : [] ∉ Set.range (fun w : List Bool => true :: w) := by
        rintro ⟨v, hv⟩
        cases hv
      rw [cylinderKMSPrefix_apply false f,
        cylinderKMSPrefix_apply true g,
        Finsupp.mapDomain_notin_range f [] hfalse,
        Finsupp.mapDomain_notin_range g [] htrue]
      simp
  | cons b u =>
      cases b with
      | false =>
          have hnot : false :: u ∉ Set.range (fun w : List Bool => true :: w) := by
            rintro ⟨v, hv⟩
            cases hv
          rw [cylinderKMSPrefix_apply true g,
            Finsupp.mapDomain_notin_range g (false :: u) hnot]
          simp
      | true =>
          have hnot : true :: u ∉ Set.range (fun w : List Bool => false :: w) := by
            rintro ⟨v, hv⟩
            cases hv
          rw [cylinderKMSPrefix_apply false f,
            Finsupp.mapDomain_notin_range f (true :: u) hnot]
          simp

theorem cylinderKMSFinsuppQuadraticForm_nonneg
    (f : List Bool →₀ ℂ) :
    0 ≤ cylinderKMSFinsuppQuadraticForm f := by
  unfold cylinderKMSFinsuppQuadraticForm
  exact cylinderKMSCoeff_complex_quadratic_nonneg
    f.support (fun u => f u)

theorem cylinderKMSFinsuppQuadraticForm_eq_zero_iff
    (f : List Bool →₀ ℂ) :
    cylinderKMSFinsuppQuadraticForm f = 0 ↔ f = 0 := by
  unfold cylinderKMSFinsuppQuadraticForm
  constructor
  · intro h
    apply Finsupp.ext
    intro u
    by_cases hu : u ∈ f.support
    · exact cylinderKMSCoeff_complex_quadratic_eq_zero_iff
        f.support (fun v => f v) |>.mp h u hu
    · by_contra hfu
      exact hu (Finsupp.mem_support_iff.mpr hfu)
  · intro h
    subst f
    simp

theorem cylinderKMSFinsuppQuadraticForm_pos_of_ne_zero
    (f : List Bool →₀ ℂ) (hf : f ≠ 0) :
    0 < cylinderKMSFinsuppQuadraticForm f := by
  have hnonneg := cylinderKMSFinsuppQuadraticForm_nonneg f
  have hne : cylinderKMSFinsuppQuadraticForm f ≠ 0 := by
    intro hzero
    exact hf (cylinderKMSFinsuppQuadraticForm_eq_zero_iff f |>.mp hzero)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem cylinderKMSHermitianPairing_self_nonneg
    (f : List Bool →₀ ℂ) :
    0 ≤ (cylinderKMSHermitianPairing f f).re := by
  rw [cylinderKMSHermitianPairing_self_re]
  exact cylinderKMSFinsuppQuadraticForm_nonneg f

theorem cylinderKMSHermitianPairing_self_pos_of_ne_zero
    {f : List Bool →₀ ℂ} (hf : f ≠ 0) :
    0 < (cylinderKMSHermitianPairing f f).re := by
  rw [cylinderKMSHermitianPairing_self_re]
  exact cylinderKMSFinsuppQuadraticForm_pos_of_ne_zero f hf

/-- Same-branch prefixing halves the finite-cylinder KMS coefficient. -/
@[rep_depth operator]
theorem cylinderKMSCoeff_cons_same (b : Bool) (u v : List Bool) :
    cylinderKMSCoeff (b :: u) (b :: v) =
      (1 / 2 : ℝ) * cylinderKMSCoeff u v := by
  by_cases h : u = v
  · subst v
    simp [cylinderKMSCoeff_self, cylinderKMSWeight_cons]
  · have hcons : b :: u ≠ b :: v := by
      intro hc
      cases hc
      exact h rfl
    simp [cylinderKMSCoeff, h, hcons]

@[rep_depth operator]
theorem cylinderKMSCoeff_cons_false_false (u v : List Bool) :
    cylinderKMSCoeff (false :: u) (false :: v) =
      (1 / 2 : ℝ) * cylinderKMSCoeff u v :=
  cylinderKMSCoeff_cons_same false u v

@[rep_depth operator]
theorem cylinderKMSCoeff_cons_true_true (u v : List Bool) :
    cylinderKMSCoeff (true :: u) (true :: v) =
      (1 / 2 : ℝ) * cylinderKMSCoeff u v :=
  cylinderKMSCoeff_cons_same true u v

@[rep_depth operator]
theorem cylinderKMSCoeff_cons_false_true (u v : List Bool) :
    cylinderKMSCoeff (false :: u) (true :: v) = 0 := by
  have h : false :: u ≠ true :: v := by
    intro hc
    cases hc
  exact cylinderKMSCoeff_ne h

@[rep_depth operator]
theorem cylinderKMSCoeff_cons_true_false (u v : List Bool) :
    cylinderKMSCoeff (true :: u) (false :: v) = 0 := by
  have h : true :: u ≠ false :: v := by
    intro hc
    cases hc
  exact cylinderKMSCoeff_ne h

theorem cylinderKMSCoeff_children_sum (u v : List Bool) :
    cylinderKMSCoeff (false :: u) (false :: v) +
        cylinderKMSCoeff (true :: u) (true :: v) =
      cylinderKMSCoeff u v := by
  rw [cylinderKMSCoeff_cons_false_false,
    cylinderKMSCoeff_cons_true_true]
  ring

theorem cylinderKMSCoeff_children_cross_sum (u v : List Bool) :
    cylinderKMSCoeff (false :: u) (true :: v) +
        cylinderKMSCoeff (true :: u) (false :: v) = 0 := by
  rw [cylinderKMSCoeff_cons_false_true,
    cylinderKMSCoeff_cons_true_false]
  simp

def cylinderKMSGNSRelation
    (f g : List Bool →₀ ℂ) : Prop :=
  cylinderKMSFinsuppQuadraticForm (f - g) = 0

theorem cylinderKMSGNSRelation_iff_eq
    (f g : List Bool →₀ ℂ) :
    cylinderKMSGNSRelation f g ↔ f = g := by
  constructor
  · intro h
    have hzero : f - g = 0 :=
      cylinderKMSFinsuppQuadraticForm_eq_zero_iff (f - g) |>.mp h
    exact sub_eq_zero.mp hzero
  · intro h
    subst g
    simp [cylinderKMSGNSRelation, cylinderKMSFinsuppQuadraticForm]

instance cylinderKMSGNSSetoid : Setoid (List Bool →₀ ℂ) where
  r := cylinderKMSGNSRelation
  iseqv :=
    { refl := by
        intro f
        exact cylinderKMSGNSRelation_iff_eq f f |>.2 rfl
      symm := by
        intro f g h
        exact cylinderKMSGNSRelation_iff_eq g f |>.2
          (cylinderKMSGNSRelation_iff_eq f g |>.1 h).symm
      trans := by
        intro f g h hfg hgh
        exact cylinderKMSGNSRelation_iff_eq f h |>.2
          ((cylinderKMSGNSRelation_iff_eq f g |>.1 hfg).trans
            (cylinderKMSGNSRelation_iff_eq g h |>.1 hgh)) }

def cylinderKMSGNSModuleCon : ModuleCon ℂ (List Bool →₀ ℂ) where
  toAddCon :=
    { toSetoid := cylinderKMSGNSSetoid
      add' := by
        intro w x y z hwx hyz
        exact cylinderKMSGNSRelation_iff_eq _ _ |>.2 <|
          congrArg₂ (· + ·)
            (cylinderKMSGNSRelation_iff_eq _ _ |>.1 hwx)
            (cylinderKMSGNSRelation_iff_eq _ _ |>.1 hyz) }
  smul := by
    intro c x y hxy
    exact cylinderKMSGNSRelation_iff_eq _ _ |>.2 <|
      congrArg (c • ·) (cylinderKMSGNSRelation_iff_eq _ _ |>.1 hxy)

abbrev cylinderKMSGNSQuotient :=
  cylinderKMSGNSModuleCon.Quotient

noncomputable def cylinderKMSGNSQuotient_mkLinearMap :
    (List Bool →₀ ℂ) →ₗ[ℂ] cylinderKMSGNSQuotient where
  toFun := Quotient.mk'
  map_add' := by
    intro f g
    apply Quotient.sound
    exact cylinderKMSGNSRelation_iff_eq _ _ |>.2 rfl
  map_smul' := by
    intro c f
    apply Quotient.sound
    exact cylinderKMSGNSRelation_iff_eq _ _ |>.2 rfl

theorem cylinderKMSGNSQuotient_mk_eq_iff
    (f g : List Bool →₀ ℂ) :
    Quotient.mk' f = Quotient.mk' g ↔ f = g := by
  constructor
  · intro h
    exact cylinderKMSGNSRelation_iff_eq f g |>.1 (Quotient.exact h)
  · intro h
    subst g
    rfl

theorem cylinderKMSGNSQuotient_mk_bijective :
    Function.Bijective (fun f : List Bool →₀ ℂ => Quotient.mk' f) := by
  constructor
  · intro f g h
    exact cylinderKMSGNSQuotient_mk_eq_iff f g |>.mp h
  · intro x
    exact Quotient.inductionOn x (fun f => ⟨f, rfl⟩)

noncomputable def cylinderKMSGNSQuotientLinearEquiv :
    (List Bool →₀ ℂ) ≃ₗ[ℂ] cylinderKMSGNSQuotient :=
  LinearEquiv.ofBijective cylinderKMSGNSQuotient_mkLinearMap
    cylinderKMSGNSQuotient_mk_bijective

@[simp] theorem cylinderKMSGNSQuotientLinearEquiv_apply
    (f : List Bool →₀ ℂ) :
    cylinderKMSGNSQuotientLinearEquiv f = Quotient.mk' f := rfl

noncomputable def cylinderKMSGNSQuotient_equiv :
    (List Bool →₀ ℂ) ≃ cylinderKMSGNSQuotient :=
  Equiv.ofBijective (fun f : List Bool →₀ ℂ => Quotient.mk' f)
    cylinderKMSGNSQuotient_mk_bijective

@[simp] theorem cylinderKMSGNSQuotient_equiv_apply
    (f : List Bool →₀ ℂ) :
    cylinderKMSGNSQuotient_equiv f = Quotient.mk' f := rfl

noncomputable def cylinderKMSGNSQuadraticForm
    (x : cylinderKMSGNSQuotient) : ℝ :=
  Quotient.lift cylinderKMSFinsuppQuadraticForm
    (fun f g h => by
      rw [cylinderKMSGNSRelation_iff_eq f g |>.1 h]) x

theorem cylinderKMSGNSQuadraticForm_mk
    (f : List Bool →₀ ℂ) :
    cylinderKMSGNSQuadraticForm (Quotient.mk' f) =
      cylinderKMSFinsuppQuadraticForm f := rfl

noncomputable def cylinderKMSGNSHermitianPairing
    (x y : cylinderKMSGNSQuotient) : ℂ :=
  cylinderKMSHermitianPairing
    (cylinderKMSGNSQuotientLinearEquiv.symm x)
    (cylinderKMSGNSQuotientLinearEquiv.symm y)

@[simp] theorem cylinderKMSGNSHermitianPairing_mk
    (f g : List Bool →₀ ℂ) :
    cylinderKMSGNSHermitianPairing (Quotient.mk' f) (Quotient.mk' g) =
      cylinderKMSHermitianPairing f g := by
  have hf : cylinderKMSGNSQuotientLinearEquiv.symm (Quotient.mk' f) = f := by
    rw [← cylinderKMSGNSQuotientLinearEquiv_apply f]
    exact cylinderKMSGNSQuotientLinearEquiv.symm_apply_apply f
  have hg : cylinderKMSGNSQuotientLinearEquiv.symm (Quotient.mk' g) = g := by
    rw [← cylinderKMSGNSQuotientLinearEquiv_apply g]
    exact cylinderKMSGNSQuotientLinearEquiv.symm_apply_apply g
  simp [cylinderKMSGNSHermitianPairing, hf, hg]

theorem cylinderKMSGNSQuadraticForm_linearEquiv
    (f : List Bool →₀ ℂ) :
    cylinderKMSGNSQuadraticForm
        (cylinderKMSGNSQuotientLinearEquiv f) =
      cylinderKMSFinsuppQuadraticForm f := by
  rw [cylinderKMSGNSQuotientLinearEquiv_apply,
    cylinderKMSGNSQuadraticForm_mk]

theorem cylinderKMSGNSHermitianPairing_linearEquiv
    (f g : List Bool →₀ ℂ) :
    cylinderKMSGNSHermitianPairing
        (cylinderKMSGNSQuotientLinearEquiv f)
        (cylinderKMSGNSQuotientLinearEquiv g) =
      cylinderKMSHermitianPairing f g := by
  rw [cylinderKMSGNSQuotientLinearEquiv_apply,
    cylinderKMSGNSQuotientLinearEquiv_apply,
    cylinderKMSGNSHermitianPairing_mk]

theorem cylinderKMSGNSHermitianPairing_conj_symm
    (x y : cylinderKMSGNSQuotient) :
    star (cylinderKMSGNSHermitianPairing x y) =
      cylinderKMSGNSHermitianPairing y x := by
  refine Quotient.inductionOn₂ x y ?_
  intro f g
  change star (cylinderKMSGNSHermitianPairing (Quotient.mk' f) (Quotient.mk' g)) =
    cylinderKMSGNSHermitianPairing (Quotient.mk' g) (Quotient.mk' f)
  rw [cylinderKMSGNSHermitianPairing_mk,
    cylinderKMSGNSHermitianPairing_mk]
  exact cylinderKMSHermitianPairing_conj_symm f g

theorem cylinderKMSGNSHermitianPairing_self_re
    (x : cylinderKMSGNSQuotient) :
    (cylinderKMSGNSHermitianPairing x x).re =
      cylinderKMSGNSQuadraticForm x := by
  refine Quotient.inductionOn x ?_
  intro f
  change
    (cylinderKMSGNSHermitianPairing (Quotient.mk' f) (Quotient.mk' f)).re =
      cylinderKMSGNSQuadraticForm (Quotient.mk' f)
  rw [cylinderKMSGNSHermitianPairing_mk,
    cylinderKMSGNSQuadraticForm_mk]
  exact cylinderKMSHermitianPairing_self_re f

theorem cylinderKMSGNSQuadraticForm_nonneg
    (x : cylinderKMSGNSQuotient) :
    0 ≤ cylinderKMSGNSQuadraticForm x := by
  refine Quotient.inductionOn x ?_
  intro f
  change 0 ≤ cylinderKMSGNSQuadraticForm (Quotient.mk' f)
  rw [cylinderKMSGNSQuadraticForm_mk]
  exact cylinderKMSFinsuppQuadraticForm_nonneg f

theorem cylinderKMSGNSHermitianPairing_self_nonneg
    (x : cylinderKMSGNSQuotient) :
    0 ≤ (cylinderKMSGNSHermitianPairing x x).re := by
  rw [cylinderKMSGNSHermitianPairing_self_re]
  exact cylinderKMSGNSQuadraticForm_nonneg x

theorem cylinderKMSGNSQuadraticForm_eq_zero_iff
    (x : cylinderKMSGNSQuotient) :
    cylinderKMSGNSQuadraticForm x = 0 ↔
      x = Quotient.mk' (0 : List Bool →₀ ℂ) := by
  refine Quotient.inductionOn x ?_
  intro f
  change cylinderKMSGNSQuadraticForm (Quotient.mk' f) = 0 ↔
    Quotient.mk' f = Quotient.mk' (0 : List Bool →₀ ℂ)
  rw [cylinderKMSGNSQuadraticForm_mk]
  rw [cylinderKMSFinsuppQuadraticForm_eq_zero_iff]
  exact (cylinderKMSGNSQuotient_mk_eq_iff f 0).symm

theorem cylinderKMSGNSHermitianPairing_self_eq_zero_iff
    (x : cylinderKMSGNSQuotient) :
    cylinderKMSGNSHermitianPairing x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply (cylinderKMSGNSQuadraticForm_eq_zero_iff x).mp
    rw [← cylinderKMSGNSHermitianPairing_self_re x, h]
    simp
  · intro h
    subst x
    change cylinderKMSGNSHermitianPairing
      (Quotient.mk' (0 : List Bool →₀ ℂ))
      (Quotient.mk' (0 : List Bool →₀ ℂ)) = 0
    rw [cylinderKMSGNSHermitianPairing_mk]
    simp [cylinderKMSHermitianPairing]

theorem cylinderKMSGNSQuadraticForm_pos_of_ne_zero
    (x : cylinderKMSGNSQuotient)
    (hx : x ≠ Quotient.mk' (0 : List Bool →₀ ℂ)) :
    0 < cylinderKMSGNSQuadraticForm x := by
  have hnonneg := cylinderKMSGNSQuadraticForm_nonneg x
  have hne : cylinderKMSGNSQuadraticForm x ≠ 0 := by
    intro hzero
    exact hx (cylinderKMSGNSQuadraticForm_eq_zero_iff x |>.mp hzero)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

noncomputable def cylinderKMSPrefixQuotient (b : Bool) :
    cylinderKMSGNSQuotient → cylinderKMSGNSQuotient :=
  Quotient.lift (fun f => Quotient.mk' (cylinderKMSPrefix b f)) (by
    intro f g h
    apply Quotient.sound
    exact cylinderKMSGNSRelation_iff_eq _ _ |>.2
      (congrArg (cylinderKMSPrefix b)
        (cylinderKMSGNSRelation_iff_eq f g |>.mp h)))

@[simp] theorem cylinderKMSPrefixQuotient_mk (b : Bool)
    (f : List Bool →₀ ℂ) :
    cylinderKMSPrefixQuotient b (Quotient.mk' f) =
      Quotient.mk' (cylinderKMSPrefix b f) := rfl

noncomputable def cylinderKMSPrefixQuotientLinearMap (b : Bool) :
    cylinderKMSGNSQuotient →ₗ[ℂ] cylinderKMSGNSQuotient :=
  { toFun := Quotient.lift
      (fun f => Quotient.mk' (cylinderKMSPrefix b f)) (by
        intro f g h
        apply Quotient.sound
        exact cylinderKMSGNSRelation_iff_eq _ _ |>.2
          (congrArg (cylinderKMSPrefix b)
            (cylinderKMSGNSRelation_iff_eq _ _ |>.mp h)))
    map_add' := by
      intro x y
      refine Quotient.inductionOn₂ x y ?_
      intro f g
      apply Quotient.sound
      exact cylinderKMSGNSRelation_iff_eq _ _ |>.2 <|
        by simp only [cylinderKMSPrefix_apply, Finsupp.mapDomain_add]
    map_smul' := by
      intro c x
      refine Quotient.inductionOn x ?_
      intro f
      apply Quotient.sound
      exact cylinderKMSGNSRelation_iff_eq _ _ |>.2 <|
        by simp [cylinderKMSPrefix_apply] }

@[simp] theorem cylinderKMSPrefixQuotientLinearMap_mk (b : Bool)
    (f : List Bool →₀ ℂ) :
    cylinderKMSPrefixQuotientLinearMap b (Quotient.mk' f) =
      Quotient.mk' (cylinderKMSPrefix b f) := rfl

theorem cylinderKMSPrefixQuotientLinearMap_injective (b : Bool) :
    Function.Injective (cylinderKMSPrefixQuotientLinearMap b) := by
  intro x y hxy
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro f g hfg
  apply Quotient.sound
  exact cylinderKMSGNSRelation_iff_eq _ _ |>.2 <|
      cylinderKMSPrefix_injective b <|
      cylinderKMSGNSQuotient_mk_eq_iff _ _ |>.mp hfg

theorem cylinderKMSPrefixQuotientLinearMap_quadraticForm
    (b : Bool) (x : cylinderKMSGNSQuotient) :
    cylinderKMSGNSQuadraticForm
        (cylinderKMSPrefixQuotientLinearMap b x) =
      (1 / 2 : ℝ) * cylinderKMSGNSQuadraticForm x := by
  refine Quotient.inductionOn x ?_
  intro f
  change cylinderKMSGNSQuadraticForm
      (Quotient.mk' (cylinderKMSPrefix b f)) =
    (1 / 2 : ℝ) * cylinderKMSGNSQuadraticForm (Quotient.mk' f)
  rw [
    cylinderKMSGNSQuadraticForm_mk,
    cylinderKMSFinsuppQuadraticForm_prefix,
    cylinderKMSGNSQuadraticForm_mk]

theorem cylinderKMSPrefixQuotientLinearMap_hermitianPairing
    (b : Bool) (x y : cylinderKMSGNSQuotient) :
    cylinderKMSGNSHermitianPairing
        (cylinderKMSPrefixQuotientLinearMap b x)
        (cylinderKMSPrefixQuotientLinearMap b y) =
      (1 / 2 : ℂ) * cylinderKMSGNSHermitianPairing x y := by
  refine Quotient.inductionOn₂ x y ?_
  intro f g
  change cylinderKMSGNSHermitianPairing
      (Quotient.mk' (cylinderKMSPrefix b f))
      (Quotient.mk' (cylinderKMSPrefix b g)) =
    (1 / 2 : ℂ) * cylinderKMSGNSHermitianPairing
      (Quotient.mk' f) (Quotient.mk' g)
  simpa only [cylinderKMSGNSHermitianPairing_mk] using
    (cylinderKMSHermitianPairing_prefix b f g)

noncomputable def cylinderKMSIsometricPrefixQuotientLinearMap (b : Bool) :
    cylinderKMSGNSQuotient →ₗ[ℂ] cylinderKMSGNSQuotient :=
  (Real.sqrt 2 : ℂ) • cylinderKMSPrefixQuotientLinearMap b

theorem cylinderKMSIsometricPrefixQuotientLinearMap_injective (b : Bool) :
    Function.Injective (cylinderKMSIsometricPrefixQuotientLinearMap b) := by
  intro x y hxy
  unfold cylinderKMSIsometricPrefixQuotientLinearMap at hxy
  apply cylinderKMSPrefixQuotientLinearMap_injective b
  exact (smul_right_injective _
    (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.2 (by norm_num))))) hxy

theorem cylinderKMSIsometricPrefixQuotientLinearMap_hermitianPairing
    (b : Bool) (x y : cylinderKMSGNSQuotient) :
    cylinderKMSGNSHermitianPairing
        (cylinderKMSIsometricPrefixQuotientLinearMap b x)
        (cylinderKMSIsometricPrefixQuotientLinearMap b y) =
      cylinderKMSGNSHermitianPairing x y := by
  have hsmul (c d : ℂ) (hc : c ≠ 0) (hd : d ≠ 0)
      (x y : cylinderKMSGNSQuotient) :
      cylinderKMSGNSHermitianPairing (c • x) (d • y) =
        star c * d * cylinderKMSGNSHermitianPairing x y := by
    refine Quotient.inductionOn₂ x y ?_
    intro f g
    unfold cylinderKMSGNSHermitianPairing
    rw [map_smul, map_smul]
    change cylinderKMSHermitianPairing
        (c • cylinderKMSGNSQuotientLinearEquiv.symm
          (cylinderKMSGNSQuotientLinearEquiv f))
        (d • cylinderKMSGNSQuotientLinearEquiv.symm
          (cylinderKMSGNSQuotientLinearEquiv g)) =
      star c * d * cylinderKMSHermitianPairing
        (cylinderKMSGNSQuotientLinearEquiv.symm
          (cylinderKMSGNSQuotientLinearEquiv f))
        (cylinderKMSGNSQuotientLinearEquiv.symm
          (cylinderKMSGNSQuotientLinearEquiv g))
    rw [cylinderKMSGNSQuotientLinearEquiv.symm_apply_apply,
      cylinderKMSGNSQuotientLinearEquiv.symm_apply_apply]
    have hcf_support : (c • f).support = f.support := by
      apply Finset.Subset.antisymm Finsupp.support_smul
      intro u hu
      rw [Finsupp.mem_support_iff] at hu ⊢
      rw [Finsupp.smul_apply]
      exact smul_ne_zero hc hu
    have hdg_support : (d • g).support = g.support := by
      apply Finset.Subset.antisymm Finsupp.support_smul
      intro u hu
      rw [Finsupp.mem_support_iff] at hu ⊢
      rw [Finsupp.smul_apply]
      exact smul_ne_zero hd hu
    unfold cylinderKMSHermitianPairing
    rw [hcf_support, hdg_support]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    simp only [Finsupp.smul_apply, smul_eq_mul, map_mul,
      starRingEnd_apply, star_mul]
    ring
  unfold cylinderKMSIsometricPrefixQuotientLinearMap
  have hsqrt_ne : Real.sqrt (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hsmul _ _
    (Complex.ofReal_ne_zero.mpr hsqrt_ne)
    (Complex.ofReal_ne_zero.mpr hsqrt_ne),
    cylinderKMSPrefixQuotientLinearMap_hermitianPairing]
  have hstar : star (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) := by
    exact Complex.conj_ofReal _
  have hsqrt : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hstar, hsqrt]
  ring_nf

theorem cylinderKMSIsometricPrefixQuotientLinearMap_quadraticForm
    (b : Bool) (x : cylinderKMSGNSQuotient) :
    cylinderKMSGNSQuadraticForm
        (cylinderKMSIsometricPrefixQuotientLinearMap b x) =
      cylinderKMSGNSQuadraticForm x := by
  rw [← cylinderKMSGNSHermitianPairing_self_re]
  rw [cylinderKMSIsometricPrefixQuotientLinearMap_hermitianPairing]
  exact cylinderKMSGNSHermitianPairing_self_re x

noncomputable def cylinderKMSIsometricPrefixWordQuotientLinearMap :
    List Bool → cylinderKMSGNSQuotient →ₗ[ℂ] cylinderKMSGNSQuotient
  | [] => LinearMap.id
  | b :: w =>
      (cylinderKMSIsometricPrefixQuotientLinearMap b).comp
        (cylinderKMSIsometricPrefixWordQuotientLinearMap w)

theorem cylinderKMSIsometricPrefixWordQuotientLinearMap_injective
    (w : List Bool) :
    Function.Injective
      (cylinderKMSIsometricPrefixWordQuotientLinearMap w) := by
  induction w with
  | nil =>
      intro x y h
      exact h
  | cons b w ih =>
      exact (cylinderKMSIsometricPrefixQuotientLinearMap_injective b).comp ih

theorem cylinderKMSIsometricPrefixWordQuotientLinearMap_hermitianPairing
    (w : List Bool) (x y : cylinderKMSGNSQuotient) :
    cylinderKMSGNSHermitianPairing
        (cylinderKMSIsometricPrefixWordQuotientLinearMap w x)
        (cylinderKMSIsometricPrefixWordQuotientLinearMap w y) =
      cylinderKMSGNSHermitianPairing x y := by
  induction w with
  | nil =>
      simp [cylinderKMSIsometricPrefixWordQuotientLinearMap]
  | cons b w ih =>
      simp only [cylinderKMSIsometricPrefixWordQuotientLinearMap,
        LinearMap.comp_apply]
      rw [cylinderKMSIsometricPrefixQuotientLinearMap_hermitianPairing,
        ih]

theorem cylinderKMSIsometricPrefixWordQuotientLinearMap_quadraticForm
    (w : List Bool) (x : cylinderKMSGNSQuotient) :
    cylinderKMSGNSQuadraticForm
        (cylinderKMSIsometricPrefixWordQuotientLinearMap w x) =
      cylinderKMSGNSQuadraticForm x := by
  rw [← cylinderKMSGNSHermitianPairing_self_re]
  rw [cylinderKMSIsometricPrefixWordQuotientLinearMap_hermitianPairing]
  exact cylinderKMSGNSHermitianPairing_self_re x

theorem cylinderKMSIsometricPrefixWordQuotientLinearMap_append
    (u v : List Bool) :
    cylinderKMSIsometricPrefixWordQuotientLinearMap (u ++ v) =
      (cylinderKMSIsometricPrefixWordQuotientLinearMap u).comp
        (cylinderKMSIsometricPrefixWordQuotientLinearMap v) := by
  induction u with
  | nil =>
      simp [cylinderKMSIsometricPrefixWordQuotientLinearMap]
  | cons b u ih =>
      simp only [List.cons_append,
        cylinderKMSIsometricPrefixWordQuotientLinearMap]
      rw [ih]
      rfl

theorem cylinderKMSGNSHermitianPairing_smul
    (c d : ℂ) (hc : c ≠ 0) (hd : d ≠ 0)
    (x y : cylinderKMSGNSQuotient) :
    cylinderKMSGNSHermitianPairing (c • x) (d • y) =
      star c * d * cylinderKMSGNSHermitianPairing x y := by
  refine Quotient.inductionOn₂ x y ?_
  intro f g
  unfold cylinderKMSGNSHermitianPairing
  rw [map_smul, map_smul]
  change cylinderKMSHermitianPairing
      (c • cylinderKMSGNSQuotientLinearEquiv.symm
        (cylinderKMSGNSQuotientLinearEquiv f))
      (d • cylinderKMSGNSQuotientLinearEquiv.symm
        (cylinderKMSGNSQuotientLinearEquiv g)) =
    star c * d * cylinderKMSHermitianPairing
      (cylinderKMSGNSQuotientLinearEquiv.symm
        (cylinderKMSGNSQuotientLinearEquiv f))
      (cylinderKMSGNSQuotientLinearEquiv.symm
        (cylinderKMSGNSQuotientLinearEquiv g))
  rw [cylinderKMSGNSQuotientLinearEquiv.symm_apply_apply,
    cylinderKMSGNSQuotientLinearEquiv.symm_apply_apply]
  have hcf_support : (c • f).support = f.support := by
    apply Finset.Subset.antisymm Finsupp.support_smul
    intro u hu
    rw [Finsupp.mem_support_iff] at hu ⊢
    rw [Finsupp.smul_apply]
    exact smul_ne_zero hc hu
  have hdg_support : (d • g).support = g.support := by
    apply Finset.Subset.antisymm Finsupp.support_smul
    intro u hu
    rw [Finsupp.mem_support_iff] at hu ⊢
    rw [Finsupp.smul_apply]
    exact smul_ne_zero hd hu
  unfold cylinderKMSHermitianPairing
  rw [hcf_support, hdg_support, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [Finsupp.smul_apply, smul_eq_mul, map_mul,
    starRingEnd_apply, star_mul]
  ring

theorem cylinderKMSPrefixQuotient_false_true_hermitianPairing
    (x y : cylinderKMSGNSQuotient) :
    cylinderKMSGNSHermitianPairing
        (cylinderKMSPrefixQuotientLinearMap false x)
        (cylinderKMSPrefixQuotientLinearMap true y) = 0 := by
  refine Quotient.inductionOn₂ x y ?_
  intro f g
  change cylinderKMSGNSHermitianPairing
      (Quotient.mk' (cylinderKMSPrefix false f))
      (Quotient.mk' (cylinderKMSPrefix true g)) = 0
  simpa only [cylinderKMSGNSHermitianPairing_mk] using
    (cylinderKMSHermitianPairing_prefix_false_true f g)

theorem cylinderKMSPrefixQuotient_true_false_hermitianPairing
    (x y : cylinderKMSGNSQuotient) :
    cylinderKMSGNSHermitianPairing
        (cylinderKMSPrefixQuotientLinearMap true x)
        (cylinderKMSPrefixQuotientLinearMap false y) = 0 := by
  rw [← cylinderKMSGNSHermitianPairing_conj_symm]
  rw [cylinderKMSPrefixQuotient_false_true_hermitianPairing]
  simp

theorem cylinderKMSIsometricPrefixQuotient_false_true_hermitianPairing
    (x y : cylinderKMSGNSQuotient) :
    cylinderKMSGNSHermitianPairing
        (cylinderKMSIsometricPrefixQuotientLinearMap false x)
        (cylinderKMSIsometricPrefixQuotientLinearMap true y) = 0 := by
  unfold cylinderKMSIsometricPrefixQuotientLinearMap
  rw [LinearMap.smul_apply, LinearMap.smul_apply]
  have hsqrt_ne : Real.sqrt (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [cylinderKMSGNSHermitianPairing_smul _ _
    (Complex.ofReal_ne_zero.mpr hsqrt_ne)
    (Complex.ofReal_ne_zero.mpr hsqrt_ne),
    cylinderKMSPrefixQuotient_false_true_hermitianPairing]
  simp

theorem cylinderKMSIsometricPrefixQuotient_true_false_hermitianPairing
    (x y : cylinderKMSGNSQuotient) :
    cylinderKMSGNSHermitianPairing
        (cylinderKMSIsometricPrefixQuotientLinearMap true x)
        (cylinderKMSIsometricPrefixQuotientLinearMap false y) = 0 := by
  rw [← cylinderKMSGNSHermitianPairing_conj_symm]
  rw [cylinderKMSIsometricPrefixQuotient_false_true_hermitianPairing]
  simp

theorem cylinderKMSGNSHermitianPairing_isometricPrefixQuotient_add
    (x y : cylinderKMSGNSQuotient) :
    cylinderKMSGNSHermitianPairing
          (cylinderKMSIsometricPrefixQuotientLinearMap false x)
          (cylinderKMSIsometricPrefixQuotientLinearMap false y) +
        cylinderKMSGNSHermitianPairing
          (cylinderKMSIsometricPrefixQuotientLinearMap true x)
          (cylinderKMSIsometricPrefixQuotientLinearMap true y) =
      2 * cylinderKMSGNSHermitianPairing x y := by
  rw [cylinderKMSIsometricPrefixQuotientLinearMap_hermitianPairing,
    cylinderKMSIsometricPrefixQuotientLinearMap_hermitianPairing]
  ring

theorem cylinderKMSIsometricPrefixQuotient_eq_zero_of_false_eq_true
    (x y : cylinderKMSGNSQuotient)
    (hxy : cylinderKMSIsometricPrefixQuotientLinearMap false x =
      cylinderKMSIsometricPrefixQuotientLinearMap true y) :
    x = 0 ∧ y = 0 := by
  have hfalse :
      cylinderKMSGNSHermitianPairing
          (cylinderKMSIsometricPrefixQuotientLinearMap false x)
          (cylinderKMSIsometricPrefixQuotientLinearMap false x) = 0 := by
    calc
      cylinderKMSGNSHermitianPairing
          (cylinderKMSIsometricPrefixQuotientLinearMap false x)
          (cylinderKMSIsometricPrefixQuotientLinearMap false x) =
          cylinderKMSGNSHermitianPairing
            (cylinderKMSIsometricPrefixQuotientLinearMap true y)
            (cylinderKMSIsometricPrefixQuotientLinearMap false x) := by
              rw [hxy]
      _ = 0 := cylinderKMSIsometricPrefixQuotient_true_false_hermitianPairing y x
  have htrue :
      cylinderKMSGNSHermitianPairing
          (cylinderKMSIsometricPrefixQuotientLinearMap true y)
          (cylinderKMSIsometricPrefixQuotientLinearMap true y) = 0 := by
    calc
      cylinderKMSGNSHermitianPairing
          (cylinderKMSIsometricPrefixQuotientLinearMap true y)
          (cylinderKMSIsometricPrefixQuotientLinearMap true y) =
          cylinderKMSGNSHermitianPairing
            (cylinderKMSIsometricPrefixQuotientLinearMap true y)
            (cylinderKMSIsometricPrefixQuotientLinearMap false x) := by
              rw [← hxy]
      _ = 0 := cylinderKMSIsometricPrefixQuotient_true_false_hermitianPairing y x
  constructor
  · apply (cylinderKMSGNSHermitianPairing_self_eq_zero_iff x).mp
    calc
      cylinderKMSGNSHermitianPairing x x =
          cylinderKMSGNSHermitianPairing
            (cylinderKMSIsometricPrefixQuotientLinearMap false x)
            (cylinderKMSIsometricPrefixQuotientLinearMap false x) := by
              symm
              exact cylinderKMSIsometricPrefixQuotientLinearMap_hermitianPairing
                false x x
      _ = 0 := hfalse
  · apply (cylinderKMSGNSHermitianPairing_self_eq_zero_iff y).mp
    calc
      cylinderKMSGNSHermitianPairing y y =
          cylinderKMSGNSHermitianPairing
            (cylinderKMSIsometricPrefixQuotientLinearMap true y)
            (cylinderKMSIsometricPrefixQuotientLinearMap true y) := by
              symm
              exact cylinderKMSIsometricPrefixQuotientLinearMap_hermitianPairing
                true y y
      _ = 0 := htrue

theorem cylinderKMSIsometricPrefixWordQuotient_eq_zero_of_head_ne
    {u v : List Bool} {x y : cylinderKMSGNSQuotient}
    {b c : Bool} (hbc : b ≠ c)
    (hxy : cylinderKMSIsometricPrefixWordQuotientLinearMap (b :: u) x =
      cylinderKMSIsometricPrefixWordQuotientLinearMap (c :: v) y) :
    x = 0 ∧ y = 0 := by
  cases b <;> cases c
  · exact False.elim (hbc rfl)
  · have htails :
        cylinderKMSIsometricPrefixWordQuotientLinearMap u x = 0 ∧
          cylinderKMSIsometricPrefixWordQuotientLinearMap v y = 0 := by
      apply cylinderKMSIsometricPrefixQuotient_eq_zero_of_false_eq_true
      simpa [cylinderKMSIsometricPrefixWordQuotientLinearMap] using hxy
    have hx : x = 0 := by
      apply cylinderKMSIsometricPrefixWordQuotientLinearMap_injective u
      simpa using htails.1
    have hy : y = 0 := by
      apply cylinderKMSIsometricPrefixWordQuotientLinearMap_injective v
      simpa using htails.2
    exact ⟨hx, hy⟩
  · have htails :
        cylinderKMSIsometricPrefixWordQuotientLinearMap v y = 0 ∧
          cylinderKMSIsometricPrefixWordQuotientLinearMap u x = 0 := by
      apply cylinderKMSIsometricPrefixQuotient_eq_zero_of_false_eq_true
      simpa [cylinderKMSIsometricPrefixWordQuotientLinearMap] using hxy.symm
    have hx : x = 0 := by
      apply cylinderKMSIsometricPrefixWordQuotientLinearMap_injective u
      simpa using htails.2
    have hy : y = 0 := by
      apply cylinderKMSIsometricPrefixWordQuotientLinearMap_injective v
      simpa using htails.1
    exact ⟨hx, hy⟩
  · exact False.elim (hbc rfl)

theorem cylinderKMSIsometricPrefixWordQuotient_eq_zero_of_ne_of_length_eq
    {u v : List Bool} (hlen : u.length = v.length) (hne : u ≠ v)
    {x y : cylinderKMSGNSQuotient}
    (hxy : cylinderKMSIsometricPrefixWordQuotientLinearMap u x =
      cylinderKMSIsometricPrefixWordQuotientLinearMap v y) :
    x = 0 ∧ y = 0 := by
  induction u generalizing v x y with
  | nil =>
      cases v with
      | nil => exact False.elim (hne rfl)
      | cons c v => simp at hlen
  | cons b u ih =>
      cases v with
      | nil => simp at hlen
      | cons c v =>
          have hlen' : u.length = v.length := by
            simpa using Nat.succ.inj hlen
          by_cases hbc : b = c
          · subst c
            have htail :
                cylinderKMSIsometricPrefixWordQuotientLinearMap u x =
                  cylinderKMSIsometricPrefixWordQuotientLinearMap v y := by
              apply cylinderKMSIsometricPrefixQuotientLinearMap_injective b
              simpa [cylinderKMSIsometricPrefixWordQuotientLinearMap] using hxy
            have hne' : u ≠ v := by
              intro huv
              apply hne
              simp [huv]
            exact ih hlen' hne' htail
          · exact cylinderKMSIsometricPrefixWordQuotient_eq_zero_of_head_ne
              hbc hxy

theorem cylinderKMSIsometricPrefixWordQuotient_hermitianPairing_eq_zero_of_ne_of_length_eq
    {u v : List Bool} (hlen : u.length = v.length) (hne : u ≠ v)
    (x y : cylinderKMSGNSQuotient) :
    cylinderKMSGNSHermitianPairing
        (cylinderKMSIsometricPrefixWordQuotientLinearMap u x)
        (cylinderKMSIsometricPrefixWordQuotientLinearMap v y) = 0 := by
  induction u generalizing v x y with
  | nil =>
      cases v with
      | nil => exact False.elim (hne rfl)
      | cons c v => simp at hlen
  | cons b u ih =>
      cases v with
      | nil => simp at hlen
      | cons c v =>
          have hlen' : u.length = v.length := by
            simpa using Nat.succ.inj hlen
          by_cases hbc : b = c
          · subst c
            have hne' : u ≠ v := by
              intro huv
              apply hne
              simp [huv]
            simp only [cylinderKMSIsometricPrefixWordQuotientLinearMap]
            simp only [LinearMap.comp_apply]
            rw [cylinderKMSIsometricPrefixQuotientLinearMap_hermitianPairing]
            exact ih hlen' hne' x y
          · cases b <;> cases c
            · exact False.elim (hbc rfl)
            · simpa [cylinderKMSIsometricPrefixWordQuotientLinearMap] using
                cylinderKMSIsometricPrefixQuotient_false_true_hermitianPairing
                  (cylinderKMSIsometricPrefixWordQuotientLinearMap u x)
                  (cylinderKMSIsometricPrefixWordQuotientLinearMap v y)
            · simpa [cylinderKMSIsometricPrefixWordQuotientLinearMap] using
                cylinderKMSIsometricPrefixQuotient_true_false_hermitianPairing
                  (cylinderKMSIsometricPrefixWordQuotientLinearMap u x)
                  (cylinderKMSIsometricPrefixWordQuotientLinearMap v y)
            · exact False.elim (hbc rfl)

noncomputable def cylinderKMSPrefixWordQuotientLinearMap :
    List Bool → cylinderKMSGNSQuotient →ₗ[ℂ] cylinderKMSGNSQuotient
  | [] => LinearMap.id
  | b :: w =>
      (cylinderKMSPrefixQuotientLinearMap b).comp
        (cylinderKMSPrefixWordQuotientLinearMap w)

@[simp] theorem cylinderKMSPrefixWordQuotientLinearMap_mk
    (w : List Bool) (f : List Bool →₀ ℂ) :
    cylinderKMSPrefixWordQuotientLinearMap w (Quotient.mk' f) =
      Quotient.mk' (cylinderKMSPrefixWord w f) := by
  induction w with
  | nil => simp [cylinderKMSPrefixWordQuotientLinearMap,
      cylinderKMSPrefixWord_nil]
  | cons b w ih =>
      simp [cylinderKMSPrefixWordQuotientLinearMap,
        cylinderKMSPrefixWord_cons, ih, LinearMap.comp_apply]

theorem cylinderKMSPrefixWordQuotientLinearMap_hermitianPairing
    (w : List Bool) (x y : cylinderKMSGNSQuotient) :
    cylinderKMSGNSHermitianPairing
        (cylinderKMSPrefixWordQuotientLinearMap w x)
        (cylinderKMSPrefixWordQuotientLinearMap w y) =
      (cylinderKMSWeight w : ℂ) *
        cylinderKMSGNSHermitianPairing x y := by
  induction w with
  | nil =>
      simp [cylinderKMSPrefixWordQuotientLinearMap,
        cylinderKMSWeight]
  | cons b w ih =>
      simp only [cylinderKMSPrefixWordQuotientLinearMap,
        LinearMap.comp_apply]
      rw [cylinderKMSPrefixQuotientLinearMap_hermitianPairing,
        ih, cylinderKMSWeight_cons]
      norm_num
      ring

theorem cylinderKMSPrefixWordQuotientLinearMap_quadraticForm
    (w : List Bool) (x : cylinderKMSGNSQuotient) :
    cylinderKMSGNSQuadraticForm
        (cylinderKMSPrefixWordQuotientLinearMap w x) =
      cylinderKMSWeight w * cylinderKMSGNSQuadraticForm x := by
  refine Quotient.inductionOn x ?_
  intro f
  calc
    cylinderKMSGNSQuadraticForm
        (cylinderKMSPrefixWordQuotientLinearMap w (Quotient.mk' f)) =
        cylinderKMSGNSQuadraticForm
          (Quotient.mk' (cylinderKMSPrefixWord w f)) := by
            rw [cylinderKMSPrefixWordQuotientLinearMap_mk]
    _ = cylinderKMSWeight w *
          cylinderKMSGNSQuadraticForm (Quotient.mk' f) := by
      rw [cylinderKMSGNSQuadraticForm_mk,
        cylinderKMSFinsuppQuadraticForm_prefixWord,
        cylinderKMSGNSQuadraticForm_mk]

theorem cylinderKMSPrefixWordQuotientLinearMap_append
    (u v : List Bool) :
    cylinderKMSPrefixWordQuotientLinearMap (u ++ v) =
      (cylinderKMSPrefixWordQuotientLinearMap u).comp
        (cylinderKMSPrefixWordQuotientLinearMap v) := by
  induction u with
  | nil => simp [cylinderKMSPrefixWordQuotientLinearMap]
  | cons b u ih =>
      simp only [List.cons_append,
        cylinderKMSPrefixWordQuotientLinearMap,
        LinearMap.comp_assoc, ih]

theorem cylinderKMSPrefixWordQuotientLinearMap_injective
    (w : List Bool) :
    Function.Injective (cylinderKMSPrefixWordQuotientLinearMap w) := by
  induction w with
  | nil =>
      intro x y hxy
      exact hxy
  | cons b w ih =>
      exact (cylinderKMSPrefixQuotientLinearMap_injective b).comp ih

theorem cylinderKMSPrefixQuotient_zero (b : Bool) :
    cylinderKMSPrefixQuotient b (Quotient.mk' (0 : List Bool →₀ ℂ)) =
      Quotient.mk' (0 : List Bool →₀ ℂ) := by
  rw [cylinderKMSPrefixQuotient_mk]
  apply Quotient.sound
  apply cylinderKMSGNSRelation_iff_eq _ _ |>.2
  simp [cylinderKMSPrefix_apply]

theorem cylinderKMSPrefixQuotient_injective (b : Bool) :
    Function.Injective (cylinderKMSPrefixQuotient b) := by
  intro x
  refine Quotient.inductionOn x ?_
  intro f y
  refine Quotient.inductionOn y ?_
  intro g hfg
  change Quotient.mk' (cylinderKMSPrefix b f) =
    Quotient.mk' (cylinderKMSPrefix b g) at hfg
  apply Quotient.sound
  exact cylinderKMSGNSRelation_iff_eq _ _ |>.2
    (cylinderKMSPrefix_injective b
      (cylinderKMSGNSQuotient_mk_eq_iff _ _ |>.mp hfg))

theorem cylinderKMSPrefixQuotient_false_eq_true_iff
    (x y : cylinderKMSGNSQuotient) :
    cylinderKMSPrefixQuotient false x =
        cylinderKMSPrefixQuotient true y ↔
      x = Quotient.mk' (0 : List Bool →₀ ℂ) ∧
        y = Quotient.mk' (0 : List Bool →₀ ℂ) := by
  constructor
  · intro hxy
    refine Quotient.inductionOn₂ x y ?_ hxy
    intro f g hfg
    change Quotient.mk' (cylinderKMSPrefix false f) =
      Quotient.mk' (cylinderKMSPrefix true g) at hfg
    have hsource : cylinderKMSPrefix false f =
        cylinderKMSPrefix true g :=
      cylinderKMSGNSQuotient_mk_eq_iff _ _ |>.mp hfg
    have hzero := (cylinderKMSPrefix_false_eq_true_iff f g).mp hsource
    exact ⟨
      cylinderKMSGNSQuotient_mk_eq_iff _ _ |>.2 hzero.1,
      cylinderKMSGNSQuotient_mk_eq_iff _ _ |>.2 hzero.2⟩
  · rintro ⟨hx, hy⟩
    rw [hx, hy, cylinderKMSPrefixQuotient_zero,
      cylinderKMSPrefixQuotient_zero]

theorem cylinderKMSPrefixQuotient_false_ne_true
    (x : cylinderKMSGNSQuotient)
    (hx : x ≠ Quotient.mk' (0 : List Bool →₀ ℂ)) :
    cylinderKMSPrefixQuotient false x ≠
      cylinderKMSPrefixQuotient true x := by
  intro hxy
  exact hx ((cylinderKMSPrefixQuotient_false_eq_true_iff x x).mp hxy).1

noncomputable def cylinderKMSPrefixWordQuotient (w : List Bool) :
    cylinderKMSGNSQuotient → cylinderKMSGNSQuotient :=
  Quotient.lift (fun f => Quotient.mk' (cylinderKMSPrefixWord w f)) (by
    intro f g h
    apply Quotient.sound
    exact cylinderKMSGNSRelation_iff_eq _ _ |>.2
      (congrArg (cylinderKMSPrefixWord w)
        (cylinderKMSGNSRelation_iff_eq f g |>.mp h)))

@[simp] theorem cylinderKMSPrefixWordQuotient_mk (w : List Bool)
    (f : List Bool →₀ ℂ) :
    cylinderKMSPrefixWordQuotient w (Quotient.mk' f) =
      Quotient.mk' (cylinderKMSPrefixWord w f) := rfl

theorem cylinderKMSPrefixWordQuotient_nil :
    cylinderKMSPrefixWordQuotient [] = id := by
  funext x
  refine Quotient.inductionOn x ?_
  intro f
  change Quotient.mk' (cylinderKMSPrefixWord [] f) = Quotient.mk' f
  rw [cylinderKMSPrefixWord_nil]
  rfl

theorem cylinderKMSPrefixWordQuotient_append
    (u v : List Bool) :
    (cylinderKMSPrefixWordQuotient u) ∘
        (cylinderKMSPrefixWordQuotient v) =
      cylinderKMSPrefixWordQuotient (u ++ v) := by
  funext x
  refine Quotient.inductionOn x ?_
  intro f
  change Quotient.mk'
      ((cylinderKMSPrefixWord u) (cylinderKMSPrefixWord v f)) =
    Quotient.mk' ((cylinderKMSPrefixWord (u ++ v)) f)
  apply congrArg Quotient.mk'
  simpa [Function.comp_apply] using
    congrArg (fun L => L f) (cylinderKMSPrefixWord_append u v)

theorem cylinderKMSPrefixWord_injective (w : List Bool) :
    Function.Injective (cylinderKMSPrefixWord w) := by
  induction w with
  | nil =>
      simpa [cylinderKMSPrefixWord_nil] using
        (Function.injective_id : Function.Injective
          (LinearMap.id : (List Bool →₀ ℂ) →ₗ[ℂ] (List Bool →₀ ℂ)))
  | cons b w ih =>
      rw [cylinderKMSPrefixWord_cons]
      exact (cylinderKMSPrefix_injective b).comp ih

theorem cylinderKMSPrefixWordQuotient_injective (w : List Bool) :
    Function.Injective (cylinderKMSPrefixWordQuotient w) := by
  intro x y hxy
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro f g hfg
  change Quotient.mk' (cylinderKMSPrefixWord w f) =
    Quotient.mk' (cylinderKMSPrefixWord w g) at hfg
  apply Quotient.sound
  exact cylinderKMSGNSRelation_iff_eq _ _ |>.2
    (cylinderKMSPrefixWord_injective w
      (cylinderKMSGNSQuotient_mk_eq_iff _ _ |>.mp hfg))

theorem cylinderKMSGNSQuadraticForm_prefixWordQuotient
    (w : List Bool) (x : cylinderKMSGNSQuotient) :
    cylinderKMSGNSQuadraticForm
        (cylinderKMSPrefixWordQuotient w x) =
      cylinderKMSWeight w * cylinderKMSGNSQuadraticForm x := by
  refine Quotient.inductionOn x ?_
  intro f
  change cylinderKMSGNSQuadraticForm
      (Quotient.mk' (cylinderKMSPrefixWord w f)) =
    cylinderKMSWeight w * cylinderKMSGNSQuadraticForm (Quotient.mk' f)
  rw [cylinderKMSGNSQuadraticForm_mk,
    cylinderKMSGNSQuadraticForm_mk,
    cylinderKMSFinsuppQuadraticForm_prefixWord]

theorem cylinderKMSGNSQuadraticForm_prefixWordQuotient_append
    (u v : List Bool) (x : cylinderKMSGNSQuotient) :
    cylinderKMSGNSQuadraticForm
        (cylinderKMSPrefixWordQuotient (u ++ v) x) =
      cylinderKMSWeight u * cylinderKMSWeight v *
        cylinderKMSGNSQuadraticForm x := by
  rw [← congrFun (cylinderKMSPrefixWordQuotient_append u v) x]
  rw [Function.comp_apply,
    cylinderKMSGNSQuadraticForm_prefixWordQuotient,
    cylinderKMSGNSQuadraticForm_prefixWordQuotient]
  ring

theorem cylinderKMSGNSQuadraticForm_prefixWordQuotient_pos_of_ne_zero
    (w : List Bool) (x : cylinderKMSGNSQuotient)
    (hx : x ≠ Quotient.mk' (0 : List Bool →₀ ℂ)) :
    0 < cylinderKMSGNSQuadraticForm
      (cylinderKMSPrefixWordQuotient w x) := by
  rw [cylinderKMSGNSQuadraticForm_prefixWordQuotient]
  exact mul_pos (cylinderKMSWeight_pos w)
    (cylinderKMSGNSQuadraticForm_pos_of_ne_zero x hx)

theorem cylinderKMSGNSQuadraticForm_prefixWordQuotient_eq_zero_iff
    (w : List Bool) (x : cylinderKMSGNSQuotient) :
    cylinderKMSGNSQuadraticForm
        (cylinderKMSPrefixWordQuotient w x) = 0 ↔
      x = Quotient.mk' (0 : List Bool →₀ ℂ) := by
  rw [cylinderKMSGNSQuadraticForm_prefixWordQuotient]
  constructor
  · intro h
    apply cylinderKMSGNSQuadraticForm_eq_zero_iff x |>.mp
    exact (mul_eq_zero.mp h).resolve_left
      (ne_of_gt (cylinderKMSWeight_pos w))
  · intro hx
    subst x
    simp [cylinderKMSGNSQuadraticForm_eq_zero_iff]

theorem cylinderKMSGNSQuadraticForm_prefixQuotient
    (b : Bool) (x : cylinderKMSGNSQuotient) :
    cylinderKMSGNSQuadraticForm (cylinderKMSPrefixQuotient b x) =
      (1 / 2 : ℝ) * cylinderKMSGNSQuadraticForm x := by
  refine Quotient.inductionOn x ?_
  intro f
  change cylinderKMSGNSQuadraticForm
      (Quotient.mk' (cylinderKMSPrefix b f)) =
    (1 / 2 : ℝ) * cylinderKMSGNSQuadraticForm (Quotient.mk' f)
  rw [cylinderKMSGNSQuadraticForm_mk,
    cylinderKMSGNSQuadraticForm_mk,
    cylinderKMSFinsuppQuadraticForm_prefix]

theorem cylinderKMSGNSQuadraticForm_prefixQuotient_pos_of_ne_zero
    (b : Bool) (x : cylinderKMSGNSQuotient)
    (hx : x ≠ Quotient.mk' (0 : List Bool →₀ ℂ)) :
    0 < cylinderKMSGNSQuadraticForm (cylinderKMSPrefixQuotient b x) := by
  rw [cylinderKMSGNSQuadraticForm_prefixQuotient]
  exact mul_pos (by norm_num)
    (cylinderKMSGNSQuadraticForm_pos_of_ne_zero x hx)

noncomputable def cylinderKMSKernel :
    Matrix (List Bool) (List Bool) ℝ :=
  fun u v => cylinderKMSCoeff u v

theorem cylinderKMSKernel_isHermitian :
    (cylinderKMSKernel).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro u v
  simpa [cylinderKMSKernel] using cylinderKMSCoeff_symm v u

theorem cylinderKMSKernel_posDef :
    (cylinderKMSKernel).PosDef := by
  refine ⟨cylinderKMSKernel_isHermitian, ?_⟩
  intro f hf
  have hnonneg :
      0 ≤ f.sum (fun u fu => f.sum (fun v fv =>
        fu * cylinderKMSKernel u v * fv)) := by
    simpa [cylinderKMSKernel] using
      cylinderKMSCoeff_quadratic_nonneg f.support (fun u => f u)
  have hne :
      f.sum (fun u fu => f.sum (fun v fv =>
        fu * cylinderKMSKernel u v * fv)) ≠ 0 := by
    intro hzero
    have hzero' :
        f.support.sum (fun u => f.support.sum (fun v =>
          f u * cylinderKMSCoeff u v * f v)) = 0 := by
      simpa [cylinderKMSKernel] using hzero
    have hvanishes :=
      (cylinderKMSCoeff_quadratic_eq_zero_iff f.support (fun u => f u)).mp hzero'
    apply hf
    apply Finsupp.ext
    intro u
    by_cases hu : u ∈ f.support
    · exact hvanishes u hu
    · by_contra hfu
      exact hu (Finsupp.mem_support_iff.mpr hfu)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem cylinderKMSGNSQuadraticForm_prefixQuotient_add
    (x : cylinderKMSGNSQuotient) :
    cylinderKMSGNSQuadraticForm
          (cylinderKMSPrefixQuotient false x) +
        cylinderKMSGNSQuadraticForm
          (cylinderKMSPrefixQuotient true x) =
      cylinderKMSGNSQuadraticForm x := by
  rw [cylinderKMSGNSQuadraticForm_prefixQuotient,
    cylinderKMSGNSQuadraticForm_prefixQuotient]
  ring

theorem cylinderKMSGNSHermitianPairing_prefixQuotientLinearMap_add
    (x y : cylinderKMSGNSQuotient) :
    cylinderKMSGNSHermitianPairing
          (cylinderKMSPrefixQuotientLinearMap false x)
          (cylinderKMSPrefixQuotientLinearMap false y) +
        cylinderKMSGNSHermitianPairing
          (cylinderKMSPrefixQuotientLinearMap true x)
          (cylinderKMSPrefixQuotientLinearMap true y) =
      cylinderKMSGNSHermitianPairing x y := by
  rw [cylinderKMSPrefixQuotientLinearMap_hermitianPairing,
    cylinderKMSPrefixQuotientLinearMap_hermitianPairing]
  ring

theorem cylinderKMSGNSQuadraticForm_prefixWordQuotient_children_add
    (w : List Bool) (x : cylinderKMSGNSQuotient) :
    cylinderKMSGNSQuadraticForm
          (cylinderKMSPrefixWordQuotient (w ++ [false]) x) +
        cylinderKMSGNSQuadraticForm
          (cylinderKMSPrefixWordQuotient (w ++ [true]) x) =
      cylinderKMSGNSQuadraticForm
        (cylinderKMSPrefixWordQuotient w x) := by
  rw [cylinderKMSGNSQuadraticForm_prefixWordQuotient_append,
    cylinderKMSGNSQuadraticForm_prefixWordQuotient_append,
    cylinderKMSGNSQuadraticForm_prefixWordQuotient]
  simp [cylinderKMSWeight]
  ring

theorem cylinderKMSGNSQuadraticForm_prefixWordQuotient_sum_bitWord
    (n : ℕ) (x : cylinderKMSGNSQuotient) :
    ∑ w : (Fin n → Bool),
      cylinderKMSGNSQuadraticForm
        (cylinderKMSPrefixWordQuotient (List.ofFn w) x) =
      cylinderKMSGNSQuadraticForm x := by
  calc
    ∑ w : (Fin n → Bool),
        cylinderKMSGNSQuadraticForm
          (cylinderKMSPrefixWordQuotient (List.ofFn w) x) =
      ∑ w : (Fin n → Bool),
        cylinderKMSWeight (List.ofFn w) *
          cylinderKMSGNSQuadraticForm x := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [cylinderKMSGNSQuadraticForm_prefixWordQuotient]
    _ = (∑ w : (Fin n → Bool),
          cylinderKMSWeight (List.ofFn w)) *
        cylinderKMSGNSQuadraticForm x := by
      rw [Finset.sum_mul]
    _ = cylinderKMSGNSQuadraticForm x := by
      rw [cylinderKMSWeight_sum_bitWord]
      simp

theorem cylinderKMSPrefixWordQuotientLinearMap_hermitianPairing_sum_bitWord
    (n : ℕ) (x y : cylinderKMSGNSQuotient) :
    ∑ w : (Fin n → Bool),
      cylinderKMSGNSHermitianPairing
        (cylinderKMSPrefixWordQuotientLinearMap (List.ofFn w) x)
        (cylinderKMSPrefixWordQuotientLinearMap (List.ofFn w) y) =
      cylinderKMSGNSHermitianPairing x y := by
  have hweight :
      ∑ w : (Fin n → Bool),
          (cylinderKMSWeight (List.ofFn w) : ℂ) = 1 := by
    exact_mod_cast cylinderKMSWeight_sum_bitWord n
  calc
    ∑ w : (Fin n → Bool),
        cylinderKMSGNSHermitianPairing
          (cylinderKMSPrefixWordQuotientLinearMap (List.ofFn w) x)
          (cylinderKMSPrefixWordQuotientLinearMap (List.ofFn w) y) =
      ∑ w : (Fin n → Bool),
        (cylinderKMSWeight (List.ofFn w) : ℂ) *
          cylinderKMSGNSHermitianPairing x y := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [cylinderKMSPrefixWordQuotientLinearMap_hermitianPairing]
    _ = (∑ w : (Fin n → Bool),
          (cylinderKMSWeight (List.ofFn w) : ℂ)) *
        cylinderKMSGNSHermitianPairing x y := by
      rw [Finset.sum_mul]
    _ = cylinderKMSGNSHermitianPairing x y := by
      rw [hweight]
      simp

theorem cylinderKMSPrefixWordQuotientLinearMap_children_add
    (w : List Bool) (x y : cylinderKMSGNSQuotient) :
    cylinderKMSGNSHermitianPairing
          (cylinderKMSPrefixWordQuotientLinearMap (w ++ [false]) x)
          (cylinderKMSPrefixWordQuotientLinearMap (w ++ [false]) y) +
        cylinderKMSGNSHermitianPairing
          (cylinderKMSPrefixWordQuotientLinearMap (w ++ [true]) x)
          (cylinderKMSPrefixWordQuotientLinearMap (w ++ [true]) y) =
      cylinderKMSGNSHermitianPairing
        (cylinderKMSPrefixWordQuotientLinearMap w x)
        (cylinderKMSPrefixWordQuotientLinearMap w y) := by
  rw [cylinderKMSPrefixWordQuotientLinearMap_hermitianPairing,
    cylinderKMSPrefixWordQuotientLinearMap_hermitianPairing,
    cylinderKMSPrefixWordQuotientLinearMap_hermitianPairing]
  simp [cylinderKMSWeight]
  ring

theorem cylinderKMSIsometricPrefixQuotient_range_inter_eq_singleton_zero :
    Set.range (cylinderKMSIsometricPrefixQuotientLinearMap false) ∩
        Set.range (cylinderKMSIsometricPrefixQuotientLinearMap true) =
      ({0} : Set cylinderKMSGNSQuotient) := by
  ext z
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hxy :
        cylinderKMSIsometricPrefixQuotientLinearMap false x =
          cylinderKMSIsometricPrefixQuotientLinearMap true y :=
      hx.trans hy.symm
    have hzero :=
      cylinderKMSIsometricPrefixQuotient_eq_zero_of_false_eq_true x y hxy
    rcases hzero with ⟨hx0, hy0⟩
    have hz0 : z = 0 := by
      simpa [hx0] using hx.symm
    exact hz0
  · intro hz
    have hz0 : z = 0 := by simpa using hz
    subst z
    exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩

theorem cylinderKMSIsometricPrefixQuotient_range_inf_eq_bot :
    LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap false) ⊓
        LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap true) =
      (⊥ : Submodule ℂ cylinderKMSGNSQuotient) := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨hxFalse, hxTrue⟩
    rcases hxFalse with ⟨p, hp⟩
    rcases hxTrue with ⟨q, hq⟩
    have hxset : x ∈
        Set.range (cylinderKMSIsometricPrefixQuotientLinearMap false) ∩
          Set.range (cylinderKMSIsometricPrefixQuotientLinearMap true) :=
      ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    have hxzero : x ∈ ({0} : Set cylinderKMSGNSQuotient) := by
      have hset := hxset
      rw [cylinderKMSIsometricPrefixQuotient_range_inter_eq_singleton_zero] at hset
      exact hset
    simpa using hxzero
  · intro x hx
    have hxzero : x = 0 := by simpa using hx
    subst x
    exact ⟨by simp, by simp⟩

noncomputable def cylinderKMSVacuumCoefficient :
    cylinderKMSGNSQuotient →ₗ[ℂ] ℂ :=
  (Finsupp.lapply ([] : List Bool)).comp
    cylinderKMSGNSQuotientLinearEquiv.symm.toLinearMap

theorem cylinderKMSVacuumCoefficient_prefix
    (b : Bool) (x : cylinderKMSGNSQuotient) :
    cylinderKMSVacuumCoefficient
        (cylinderKMSIsometricPrefixQuotientLinearMap b x) = 0 := by
  refine Quotient.inductionOn x ?_
  intro f
  have hnot : [] ∉ Set.range (fun w : List Bool => b :: w) := by
    rintro ⟨w, hw⟩
    cases hw
  simp only [cylinderKMSVacuumCoefficient, LinearMap.comp_apply,
    cylinderKMSIsometricPrefixQuotientLinearMap,
    LinearMap.smul_apply, map_smul, Finsupp.lapply_apply]
  have hprefix :
      cylinderKMSGNSQuotientLinearEquiv.symm
          (cylinderKMSPrefixQuotientLinearMap b (Quotient.mk' f)) =
        cylinderKMSPrefix b f := by
    rw [cylinderKMSPrefixQuotientLinearMap_mk,
      ← cylinderKMSGNSQuotientLinearEquiv_apply,
      cylinderKMSGNSQuotientLinearEquiv.symm_apply_apply]
  change (↑(Real.sqrt 2) : ℂ) •
      (cylinderKMSGNSQuotientLinearEquiv.symm
        (cylinderKMSPrefixQuotientLinearMap b (Quotient.mk' f))) [] = 0
  rw [hprefix,
    cylinderKMSPrefix_apply,
    Finsupp.mapDomain_notin_range f [] hnot]
  simp

theorem cylinderKMSVacuumCoefficient_vacuum :
      cylinderKMSVacuumCoefficient
        (Quotient.mk' (Finsupp.single ([] : List Bool) (1 : ℂ))) = 1 := by
  change
    (cylinderKMSGNSQuotientLinearEquiv.symm
      (Quotient.mk' (Finsupp.single ([] : List Bool) (1 : ℂ)))) [] = 1
  rw [← cylinderKMSGNSQuotientLinearEquiv_apply,
    cylinderKMSGNSQuotientLinearEquiv.symm_apply_apply]
  simp

theorem cylinderKMSVacuumCoefficient_vacuumClass_ne_zero :
    Quotient.mk' (Finsupp.single ([] : List Bool) (1 : ℂ)) ≠
      (0 : cylinderKMSGNSQuotient) := by
  intro hzero
  have hcoeff := congrArg cylinderKMSVacuumCoefficient hzero
  rw [map_zero, cylinderKMSVacuumCoefficient_vacuum] at hcoeff
  exact one_ne_zero hcoeff

theorem cylinderKMSIsometricPrefixQuotient_range_sup_le_vacuumCoefficient_ker :
    LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap false) ⊔
        LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap true) ≤
      LinearMap.ker cylinderKMSVacuumCoefficient := by
  apply sup_le
  · intro z hz
    rcases hz with ⟨p, rfl⟩
    exact LinearMap.mem_ker.mpr
      (cylinderKMSVacuumCoefficient_prefix false p)
  · intro z hz
    rcases hz with ⟨p, rfl⟩
    exact LinearMap.mem_ker.mpr
      (cylinderKMSVacuumCoefficient_prefix true p)

theorem cylinderKMSVacuumCoefficient_single_empty (c : ℂ) :
    cylinderKMSVacuumCoefficient
        (cylinderKMSGNSQuotientLinearEquiv
          (Finsupp.single ([] : List Bool) c)) = c := by
  change (Finsupp.lapply (R := ℂ) (M := ℂ) ([] : List Bool))
      (cylinderKMSGNSQuotientLinearEquiv.symm
        (cylinderKMSGNSQuotientLinearEquiv
          (Finsupp.single ([] : List Bool) c))) = c
  rw [cylinderKMSGNSQuotientLinearEquiv.symm_apply_apply]
  simp

theorem cylinderKMSPrefix_false_injective :
    Function.Injective (fun w : List Bool => false :: w) := by
  intro u v huv
  injection huv

theorem cylinderKMSPrefix_true_injective :
    Function.Injective (fun w : List Bool => true :: w) := by
  intro u v huv
  injection huv

theorem cylinderKMSPrefix_false_add_true_comap_of_empty_eq_zero
    (f : List Bool →₀ ℂ) (hf : f [] = 0) :
    cylinderKMSPrefix false
        (Finsupp.comapDomain (fun w : List Bool => false :: w) f
          cylinderKMSPrefix_false_injective.injOn) +
      cylinderKMSPrefix true
        (Finsupp.comapDomain (fun w : List Bool => true :: w) f
          cylinderKMSPrefix_true_injective.injOn) = f := by
  change
    Finsupp.mapDomain (fun w : List Bool => false :: w)
        (Finsupp.comapDomain (fun w : List Bool => false :: w) f
          cylinderKMSPrefix_false_injective.injOn) +
      Finsupp.mapDomain (fun w : List Bool => true :: w)
        (Finsupp.comapDomain (fun w : List Bool => true :: w) f
          cylinderKMSPrefix_true_injective.injOn) = f
  apply Finsupp.ext
  intro u
  cases u with
  | nil =>
      simp [Finsupp.mapDomain_notin_range, hf]
  | cons b u =>
      simp only [Finsupp.add_apply]
      cases b
      · rw [Finsupp.mapDomain_apply cylinderKMSPrefix_false_injective,
          Finsupp.mapDomain_notin_range _ _ (by
            rintro ⟨v, hv⟩
            cases hv)]
        simp [Finsupp.comapDomain_apply]
      · rw [Finsupp.mapDomain_notin_range _ _ (by
            rintro ⟨v, hv⟩
            cases hv), Finsupp.mapDomain_apply cylinderKMSPrefix_true_injective]
        simp [Finsupp.comapDomain_apply]

theorem cylinderKMSPrefixQuotient_reconstruct_of_empty_eq_zero
    (f : List Bool →₀ ℂ) (hf : f [] = 0) :
    let fFalse := Finsupp.comapDomain
      (fun w : List Bool => false :: w) f
        cylinderKMSPrefix_false_injective.injOn
    let fTrue := Finsupp.comapDomain
      (fun w : List Bool => true :: w) f
        cylinderKMSPrefix_true_injective.injOn
    Quotient.mk'
        (cylinderKMSPrefix false fFalse + cylinderKMSPrefix true fTrue) =
      Quotient.mk' f := by
  dsimp
  exact congrArg Quotient.mk'
    (cylinderKMSPrefix_false_add_true_comap_of_empty_eq_zero f hf)

theorem cylinderKMSGNSQuotient_smul_inv_smul₀
    (a : ℂ) (ha : a ≠ 0) (x : cylinderKMSGNSQuotient) :
    a • a⁻¹ • x = x := by
  refine Quotient.inductionOn x ?_
  intro f
  change Quotient.mk' (a • (a⁻¹ • f)) = Quotient.mk' f
  apply Quotient.sound
  apply cylinderKMSGNSRelation_iff_eq _ _ |>.2
  apply Finsupp.ext
  intro i
  simp [Finsupp.smul_apply, smul_eq_mul, mul_assoc, ha]

theorem cylinderKMSIsometricPrefixQuotient_range_sup_eq_vacuumCoefficient_ker :
    LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap false) ⊔
        LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap true) =
      LinearMap.ker cylinderKMSVacuumCoefficient := by
  apply le_antisymm
  · exact cylinderKMSIsometricPrefixQuotient_range_sup_le_vacuumCoefficient_ker
  · intro x hx
    refine Quotient.inductionOn x ?_ hx
    intro f hf
    have hf' : cylinderKMSVacuumCoefficient (Quotient.mk' f) = 0 :=
      LinearMap.mem_ker.mp hf
    change
      (Finsupp.lapply (R := ℂ) (M := ℂ) ([] : List Bool))
          (cylinderKMSGNSQuotientLinearEquiv.symm (Quotient.mk' f)) = 0 at hf'
    rw [← cylinderKMSGNSQuotientLinearEquiv_apply,
      cylinderKMSGNSQuotientLinearEquiv.symm_apply_apply,
      Finsupp.lapply_apply] at hf'
    have hf0 : f [] = 0 := hf'
    let fFalse := Finsupp.comapDomain
      (fun w : List Bool => false :: w) f
        cylinderKMSPrefix_false_injective.injOn
    let fTrue := Finsupp.comapDomain
      (fun w : List Bool => true :: w) f
        cylinderKMSPrefix_true_injective.injOn
    have hdecomp :
        cylinderKMSPrefix false fFalse + cylinderKMSPrefix true fTrue = f := by
      exact cylinderKMSPrefix_false_add_true_comap_of_empty_eq_zero f hf0
    have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
    let qFalse : cylinderKMSGNSQuotient := Quotient.mk' (cylinderKMSPrefix false fFalse)
    let qTrue : cylinderKMSGNSQuotient := Quotient.mk' (cylinderKMSPrefix true fTrue)
    let qFalseSource : cylinderKMSGNSQuotient := Quotient.mk' fFalse
    let qTrueSource : cylinderKMSGNSQuotient := Quotient.mk' fTrue
    have hfalse_mem :
        qFalse ∈
          LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap false) := by
      refine ⟨(↑(Real.sqrt 2) : ℂ)⁻¹ • qFalseSource, ?_⟩
      change (Real.sqrt 2 : ℂ) •
          cylinderKMSPrefixQuotientLinearMap false
            ((↑(Real.sqrt 2) : ℂ)⁻¹ • qFalseSource) = _
      rw [map_smul]
      rw [cylinderKMSGNSQuotient_smul_inv_smul₀ _ hsqrt]
      rfl
    have htrue_mem :
        qTrue ∈
          LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap true) := by
      refine ⟨(↑(Real.sqrt 2) : ℂ)⁻¹ • qTrueSource, ?_⟩
      change (Real.sqrt 2 : ℂ) •
          cylinderKMSPrefixQuotientLinearMap true
            ((↑(Real.sqrt 2) : ℂ)⁻¹ • qTrueSource) = _
      rw [map_smul]
      rw [cylinderKMSGNSQuotient_smul_inv_smul₀ _ hsqrt]
      rfl
    have hsum :
        qFalse + qTrue = Quotient.mk' f := by
      change Quotient.mk'
          (cylinderKMSPrefix false fFalse + cylinderKMSPrefix true fTrue) =
        Quotient.mk' f
      exact congrArg Quotient.mk' hdecomp
    change (Quotient.mk' f : cylinderKMSGNSQuotient) ∈ _
    rw [← hsum]
    change qFalse + qTrue ∈
      LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap false) ⊔
        LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap true)
    exact Submodule.add_mem_sup
      (S := LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap false))
      (T := LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap true))
      hfalse_mem htrue_mem

theorem cylinderKMSGNSQuotient_vacuum_children_decomposition
    (x : cylinderKMSGNSQuotient) :
    ∃ c : ℂ,
      ∃ xFalse xTrue : cylinderKMSGNSQuotient,
        x = cylinderKMSGNSQuotientLinearEquiv
              (Finsupp.single ([] : List Bool) c) +
          cylinderKMSIsometricPrefixQuotientLinearMap false xFalse +
          cylinderKMSIsometricPrefixQuotientLinearMap true xTrue := by
  let c : ℂ := cylinderKMSVacuumCoefficient x
  let vacuum : cylinderKMSGNSQuotient := cylinderKMSGNSQuotientLinearEquiv
    (Finsupp.single ([] : List Bool) c)
  let x₀ : cylinderKMSGNSQuotient := x - vacuum
  have hvac : cylinderKMSVacuumCoefficient vacuum = c := by
    exact cylinderKMSVacuumCoefficient_single_empty c
  have hx₀ : x₀ ∈ LinearMap.ker cylinderKMSVacuumCoefficient := by
    apply LinearMap.mem_ker.mpr
    dsimp [x₀]
    rw [map_sub, hvac]
    simp [c]
  have hx₀sup : x₀ ∈
      LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap false) ⊔
        LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap true) := by
    rw [cylinderKMSIsometricPrefixQuotient_range_sup_eq_vacuumCoefficient_ker]
    exact hx₀
  rcases Submodule.mem_sup.mp hx₀sup with ⟨y, hy, z, hz, hsum⟩
  rcases hy with ⟨xFalse, hFalse⟩
  rcases hz with ⟨xTrue, hTrue⟩
  refine ⟨c, xFalse, xTrue, ?_⟩
  calc
    x = vacuum + x₀ := by
      dsimp [x₀]
      abel
    _ = vacuum + (y + z) := by rw [← hsum]
    _ = vacuum +
        cylinderKMSIsometricPrefixQuotientLinearMap false xFalse +
        cylinderKMSIsometricPrefixQuotientLinearMap true xTrue := by
      rw [← hFalse, ← hTrue]
      abel
    _ = cylinderKMSGNSQuotientLinearEquiv
          (Finsupp.single ([] : List Bool) c) +
        cylinderKMSIsometricPrefixQuotientLinearMap false xFalse +
        cylinderKMSIsometricPrefixQuotientLinearMap true xTrue := by
      rfl

theorem cylinderKMSGNSQuotient_vacuum_coefficient_unique
    (c d : ℂ) (xFalse xTrue yFalse yTrue : cylinderKMSGNSQuotient)
    (h : cylinderKMSGNSQuotientLinearEquiv
          (Finsupp.single ([] : List Bool) c) +
          cylinderKMSIsometricPrefixQuotientLinearMap false xFalse +
          cylinderKMSIsometricPrefixQuotientLinearMap true xTrue =
        cylinderKMSGNSQuotientLinearEquiv
          (Finsupp.single ([] : List Bool) d) +
          cylinderKMSIsometricPrefixQuotientLinearMap false yFalse +
          cylinderKMSIsometricPrefixQuotientLinearMap true yTrue) :
    c = d := by
  have hcoeff :
      cylinderKMSVacuumCoefficient
          (cylinderKMSGNSQuotientLinearEquiv
            (Finsupp.single ([] : List Bool) c) +
            cylinderKMSIsometricPrefixQuotientLinearMap false xFalse +
            cylinderKMSIsometricPrefixQuotientLinearMap true xTrue) =
        cylinderKMSVacuumCoefficient
          (cylinderKMSGNSQuotientLinearEquiv
            (Finsupp.single ([] : List Bool) d) +
            cylinderKMSIsometricPrefixQuotientLinearMap false yFalse +
            cylinderKMSIsometricPrefixQuotientLinearMap true yTrue) :=
    congrArg cylinderKMSVacuumCoefficient h
  have hleft :
      cylinderKMSVacuumCoefficient
          (cylinderKMSGNSQuotientLinearEquiv
            (Finsupp.single ([] : List Bool) c) +
            cylinderKMSIsometricPrefixQuotientLinearMap false xFalse +
            cylinderKMSIsometricPrefixQuotientLinearMap true xTrue) = c := by
    rw [map_add, map_add, cylinderKMSVacuumCoefficient_single_empty,
      cylinderKMSVacuumCoefficient_prefix,
      cylinderKMSVacuumCoefficient_prefix]
    simp
  have hright :
      cylinderKMSVacuumCoefficient
          (cylinderKMSGNSQuotientLinearEquiv
            (Finsupp.single ([] : List Bool) d) +
            cylinderKMSIsometricPrefixQuotientLinearMap false yFalse +
            cylinderKMSIsometricPrefixQuotientLinearMap true yTrue) = d := by
    rw [map_add, map_add, cylinderKMSVacuumCoefficient_single_empty,
      cylinderKMSVacuumCoefficient_prefix,
      cylinderKMSVacuumCoefficient_prefix]
    simp
  calc
    c = cylinderKMSVacuumCoefficient
        (cylinderKMSGNSQuotientLinearEquiv
          (Finsupp.single ([] : List Bool) c) +
          cylinderKMSIsometricPrefixQuotientLinearMap false xFalse +
          cylinderKMSIsometricPrefixQuotientLinearMap true xTrue) := hleft.symm
    _ = cylinderKMSVacuumCoefficient
        (cylinderKMSGNSQuotientLinearEquiv
          (Finsupp.single ([] : List Bool) d) +
          cylinderKMSIsometricPrefixQuotientLinearMap false yFalse +
          cylinderKMSIsometricPrefixQuotientLinearMap true yTrue) := hcoeff
    _ = d := hright

theorem cylinderKMSIsometricPrefixQuotient_range_sup_ne_top :
    LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap false) ⊔
        LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap true) ≠
      (⊤ : Submodule ℂ cylinderKMSGNSQuotient) := by
  intro htop
  have hvac_mem :
      Quotient.mk' (Finsupp.single ([] : List Bool) (1 : ℂ)) ∈
        LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap false) ⊔
          LinearMap.range (cylinderKMSIsometricPrefixQuotientLinearMap true) := by
    have hmem :
        Quotient.mk' (Finsupp.single ([] : List Bool) (1 : ℂ)) ∈
          (⊤ : Submodule ℂ cylinderKMSGNSQuotient) :=
      by simp
    exact htop.symm ▸ hmem
  have hkernel :
      Quotient.mk' (Finsupp.single ([] : List Bool) (1 : ℂ)) ∈
        LinearMap.ker cylinderKMSVacuumCoefficient :=
    cylinderKMSIsometricPrefixQuotient_range_sup_le_vacuumCoefficient_ker
      hvac_mem
  have hzero : cylinderKMSVacuumCoefficient
      (Quotient.mk' (Finsupp.single ([] : List Bool) (1 : ℂ))) = 0 :=
    hkernel
  exact one_ne_zero
    ((cylinderKMSVacuumCoefficient_vacuum).symm.trans hzero)

end InfoGeometry.Canonical.CantorKMSCylinderState

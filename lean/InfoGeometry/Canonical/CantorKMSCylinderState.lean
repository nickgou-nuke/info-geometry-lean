import Mathlib.Tactic
import InfoGeometry.Canonical.CantorCuntzBasis
import InfoGeometry.Meta.Architecture

noncomputable section

namespace InfoGeometry.Canonical.CantorKMSCylinderState

open InfoGeometry.Canonical.CantorCuntzBasis

/-!
# Cantor KMS Cylinder State

This module isolates the finite-cylinder substrate for the Cuntz/KMS boundary
state.  It does not construct a GNS Hilbert space.  It proves the exact
finite-word scaling and cross-branch orthogonality laws that a later GNS
construction should consume.

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

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

[Theorems that compile from explicitly named theorem parameters or imported
verified premises.]

* None.

#### BUCKET 3: OPEN CLOSURE DEBT

[Exact theorem statements that remain unproved. No wrappers, sockets, fields,
witnesses, certificates, or renamed placeholders.]

* Construct the GNS quotient and completion from these finite-cylinder
  coefficients.
* Identify that completion with the concrete `PiLp`/`lp` Cantor-boundary
  Hilbert carrier.
* Transport the Cuntz generators and phase-axis commutation through that GNS
  representation.
-/

/-- The uniform binary KMS weight of a finite cylinder word: `2^-|w|`. -/
@[rep_depth operator]
def cylinderKMSWeight (w : BinaryWord) : ℝ :=
  ((1 / 2 : ℝ) ^ w.length)

@[rep_depth operator]
theorem cylinderKMSWeight_nonneg (w : BinaryWord) :
    0 ≤ cylinderKMSWeight w := by
  unfold cylinderKMSWeight
  exact pow_nonneg (by norm_num) w.length

theorem cylinderKMSWeight_pos (w : BinaryWord) :
    0 < cylinderKMSWeight w := by
  unfold cylinderKMSWeight
  exact pow_pos (by norm_num) w.length

/-- Prefixing either binary branch halves the cylinder KMS weight. -/
@[rep_depth operator]
theorem cylinderKMSWeight_cons (b : Bool) (w : BinaryWord) :
    cylinderKMSWeight (b :: w) = (1 / 2 : ℝ) * cylinderKMSWeight w := by
  simp [cylinderKMSWeight, pow_succ, mul_comm]

@[rep_depth operator]
theorem cylinderKMSWeight_cons_false (w : BinaryWord) :
    cylinderKMSWeight (false :: w) = (1 / 2 : ℝ) * cylinderKMSWeight w :=
  cylinderKMSWeight_cons false w

@[rep_depth operator]
theorem cylinderKMSWeight_cons_true (w : BinaryWord) :
    cylinderKMSWeight (true :: w) = (1 / 2 : ℝ) * cylinderKMSWeight w :=
  cylinderKMSWeight_cons true w

theorem cylinderKMSWeight_append (u v : BinaryWord) :
    cylinderKMSWeight (u ++ v) =
      cylinderKMSWeight u * cylinderKMSWeight v := by
  unfold cylinderKMSWeight
  rw [List.length_append, pow_add]

/--
The two depth-one children of a cylinder split the parent weight evenly.

This is the finite algebraic version of the shard/whole readout: each branch
contains exactly half of the cylinder mass, and the two children sum back to the
parent.
-/
@[rep_depth operator]
theorem cylinderKMSWeight_children_sum (w : BinaryWord) :
    cylinderKMSWeight (false :: w) + cylinderKMSWeight (true :: w) =
      cylinderKMSWeight w := by
  rw [cylinderKMSWeight_cons_false, cylinderKMSWeight_cons_true]
  ring

@[rep_depth operator]
theorem cylinderKMSWeight_bool_sum (w : BinaryWord) :
    ∑ b : Bool, cylinderKMSWeight (b :: w) = cylinderKMSWeight w := by
  rw [Fintype.sum_bool]
  exact cylinderKMSWeight_children_sum w

/--
Diagonal finite-cylinder coefficient for the uniform KMS state.

This is the matrix-unit shadow of `φ(S_u S_v*)`: diagonal pairs receive the
cylinder weight, off-diagonal pairs vanish.
-/
@[rep_depth operator]
def cylinderKMSCoeff (u v : BinaryWord) : ℝ :=
  if u = v then cylinderKMSWeight u else 0

@[simp, rep_depth operator]
theorem cylinderKMSCoeff_self (w : BinaryWord) :
    cylinderKMSCoeff w w = cylinderKMSWeight w := by
  simp [cylinderKMSCoeff]

@[rep_depth operator]
theorem cylinderKMSCoeff_ne {u v : BinaryWord} (h : u ≠ v) :
    cylinderKMSCoeff u v = 0 := by
  simp [cylinderKMSCoeff, h]

@[rep_depth operator]
theorem cylinderKMSCoeff_self_nonneg (w : BinaryWord) :
    0 ≤ cylinderKMSCoeff w w := by
  simp [cylinderKMSCoeff_self, cylinderKMSWeight_nonneg]

theorem cylinderKMSCoeff_nonneg (u v : BinaryWord) :
    0 ≤ cylinderKMSCoeff u v := by
  by_cases h : u = v
  · subst v
    exact cylinderKMSCoeff_self_nonneg u
  · rw [cylinderKMSCoeff_ne h]

theorem cylinderKMSCoeff_append_right
    (u v w : BinaryWord) :
    cylinderKMSCoeff (u ++ w) (v ++ w) =
      if u = v then cylinderKMSWeight u * cylinderKMSWeight w else 0 := by
  by_cases h : u = v
  · subst v
    simp [cylinderKMSCoeff_self, cylinderKMSWeight_append]
  · have h' : u ++ w ≠ v ++ w := by
      intro huv
      exact h (List.append_left_injective w huv)
    rw [cylinderKMSCoeff_ne h', if_neg h]

theorem cylinderKMSCoeff_append_left
    (w u v : BinaryWord) :
    cylinderKMSCoeff (w ++ u) (w ++ v) =
      if u = v then cylinderKMSWeight w * cylinderKMSWeight u else 0 := by
  by_cases h : u = v
  · subst v
    simp [cylinderKMSCoeff_self, cylinderKMSWeight_append]
  · have h' : w ++ u ≠ w ++ v := by
      intro huv
      exact h (List.append_right_injective w huv)
    rw [cylinderKMSCoeff_ne h', if_neg h]

theorem cylinderKMSCoeff_quadratic_nonneg
    (s : Finset BinaryWord) (f : BinaryWord → ℝ) :
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

theorem cylinderKMSCoeff_singleton_quadratic_pos
    (u : BinaryWord) {x : ℝ} (hx : x ≠ 0) :
    0 < ({u} : Finset BinaryWord).sum (fun a =>
      ({u} : Finset BinaryWord).sum (fun b =>
        x * cylinderKMSCoeff a b * x)) := by
  simp only [Finset.sum_singleton, cylinderKMSCoeff, if_pos]
  calc
    0 < x ^ 2 * cylinderKMSWeight u :=
      mul_pos (sq_pos_of_ne_zero hx) (cylinderKMSWeight_pos u)
    _ = x * cylinderKMSWeight u * x := by ring

theorem cylinderKMSCoeff_singleton_quadratic_eq_zero_iff
    (u : BinaryWord) (x : ℝ) :
    ({u} : Finset BinaryWord).sum (fun a =>
      ({u} : Finset BinaryWord).sum (fun b =>
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
    (s : Finset BinaryWord) (f : BinaryWord → ℝ) :
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

theorem cylinderKMSCoeff_symm (u v : BinaryWord) :
    cylinderKMSCoeff u v = cylinderKMSCoeff v u := by
  by_cases h : u = v
  · subst v
    rfl
  · rw [cylinderKMSCoeff_ne h, cylinderKMSCoeff_ne (Ne.symm h)]

/-- Same-branch prefixing halves the finite-cylinder KMS coefficient. -/
@[rep_depth operator]
theorem cylinderKMSCoeff_cons_same (b : Bool) (u v : BinaryWord) :
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
theorem cylinderKMSCoeff_cons_false_false (u v : BinaryWord) :
    cylinderKMSCoeff (false :: u) (false :: v) =
      (1 / 2 : ℝ) * cylinderKMSCoeff u v :=
  cylinderKMSCoeff_cons_same false u v

@[rep_depth operator]
theorem cylinderKMSCoeff_cons_true_true (u v : BinaryWord) :
    cylinderKMSCoeff (true :: u) (true :: v) =
      (1 / 2 : ℝ) * cylinderKMSCoeff u v :=
  cylinderKMSCoeff_cons_same true u v

@[rep_depth operator]
theorem cylinderKMSCoeff_cons_false_true (u v : BinaryWord) :
    cylinderKMSCoeff (false :: u) (true :: v) = 0 := by
  have h : false :: u ≠ true :: v := by
    intro hc
    cases hc
  exact cylinderKMSCoeff_ne h

@[rep_depth operator]
theorem cylinderKMSCoeff_cons_true_false (u v : BinaryWord) :
    cylinderKMSCoeff (true :: u) (false :: v) = 0 := by
  have h : true :: u ≠ false :: v := by
    intro hc
    cases hc
  exact cylinderKMSCoeff_ne h

theorem cylinderKMSCoeff_children_sum (u v : BinaryWord) :
    cylinderKMSCoeff (false :: u) (false :: v) +
        cylinderKMSCoeff (true :: u) (true :: v) =
      cylinderKMSCoeff u v := by
  rw [cylinderKMSCoeff_cons_false_false,
    cylinderKMSCoeff_cons_true_true]
  ring

theorem cylinderKMSCoeff_children_cross_sum (u v : BinaryWord) :
    cylinderKMSCoeff (false :: u) (true :: v) +
        cylinderKMSCoeff (true :: u) (false :: v) = 0 := by
  rw [cylinderKMSCoeff_cons_false_true,
    cylinderKMSCoeff_cons_true_false]
  simp

end InfoGeometry.Canonical.CantorKMSCylinderState

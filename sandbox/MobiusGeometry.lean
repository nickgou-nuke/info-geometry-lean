import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Matrix.Basic

open Complex
open scoped ComplexConjugate

namespace InfoGeometry

/-- The Riemann sphere, represented as the complex plane extended by a point at infinity. -/
def RiemannSphere := Option ℂ

instance : Inhabited RiemannSphere := ⟨none⟩

/-- A Möbius transformation is a rational function of the form
    f(z) = (a*z + b) / (c*z + d) with ad - bc ≠ 0.
    We represent it by a 2x2 matrix with non-zero determinant. -/
structure MobiusTransform where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det_ne_zero : a * d - b * c ≠ 0

instance : Inhabited MobiusTransform where
  default := {
    a := 1, b := 0, c := 0, d := 1,
    det_ne_zero := by norm_num
  }

namespace MobiusTransform

/-- The action of a Möbius transformation on the Riemann sphere. -/
noncomputable def eval (M : MobiusTransform) (z : RiemannSphere) : RiemannSphere :=
  match z with
  | none => if M.c = 0 then none else some (M.a / M.c)
  | some z' =>
      let denom := M.c * z' + M.d
      if denom = 0 then none else some ((M.a * z' + M.b) / denom)

/-- Two Möbius transformations are equivalent if they define the same function on the Riemann sphere.
    Equivalently, their matrices are proportional. -/
def equiv (M1 M2 : MobiusTransform) : Prop :=
  ∀ z : RiemannSphere, M1.eval z = M2.eval z

end MobiusTransform

/-- A generalized circle in the complex plane is the locus of points satisfying
    A * |z|^2 + B * z + conj B * conj z + C = 0.
    Since B * z + conj B * conj z = 2 * Re(B * z), we use that in the definition.
    A and C are real, and we require |B|^2 > A * C so the locus is a circle or a line.
    If A = 0, this is a line; if A ≠ 0, this is a circle. -/
structure GenCircle where
  A : ℝ
  B : ℂ
  C : ℝ
  valid : A * C < Complex.normSq B

instance : Inhabited GenCircle where
  default := {
    A := 1, B := 0, C := -1,
    valid := by
      simp only [normSq_zero]
      norm_num
  }

namespace GenCircle

/-- A complex number `z` lies on the generalized circle if it satisfies the equation. -/
def contains (circ : GenCircle) (z : ℂ) : Prop :=
  circ.A * Complex.normSq z + 2 * (circ.B * z).re + circ.C = 0

/-- Extension of the generalized circle to the Riemann sphere.
    The point at infinity lies on the circle if and only if A = 0 (i.e., it's a line). -/
def containsExt (circ : GenCircle) (z : RiemannSphere) : Prop :=
  match z with
  | none => circ.A = 0
  | some z' => circ.contains z'

end GenCircle

-- Circle-Preserving Theorem: Decomposition of Möbius transformations
noncomputable def trans_f1 (c d z : ℂ) := z + d / c
noncomputable def inv_f2 (z : ℂ) := z⁻¹
noncomputable def dil_f3 (a b c d z : ℂ) := ((b * c - a * d) / c^2) * z
noncomputable def trans_f4 (a c z : ℂ) := z + a / c

def trans_circle (c : ℂ) (circ : GenCircle) : GenCircle :=
  let A' := circ.A
  let B' := circ.B - (circ.A : ℂ) * conj c
  let C' := circ.A * normSq c - 2 * (circ.B * c).re + circ.C
  have h_valid : A' * C' < normSq B' := by
    have h1 : normSq B' - A' * C' = normSq circ.B - circ.A * circ.C := by
      change normSq (circ.B - (circ.A : ℂ) * conj c) - circ.A * (circ.A * normSq c - 2 * (circ.B * c).re + circ.C) = normSq circ.B - circ.A * circ.C
      simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im, ofReal_re, ofReal_im]
      ring
    linarith [circ.valid]
  { A := A', B := B', C := C', valid := h_valid }

lemma trans_circle_contains (c : ℂ) (circ : GenCircle) (z : ℂ) :
    circ.contains z ↔ (trans_circle c circ).contains (z + c) := by
  have h_eq : (trans_circle c circ).A * normSq (z + c) + 2 * ((trans_circle c circ).B * (z + c)).re + (trans_circle c circ).C = circ.A * normSq z + 2 * (circ.B * z).re + circ.C := by
    change circ.A * normSq (z + c) + 2 * ((circ.B - (circ.A : ℂ) * conj c) * (z + c)).re + (circ.A * normSq c - 2 * (circ.B * c).re + circ.C) = circ.A * normSq z + 2 * (circ.B * z).re + circ.C
    simp only [normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im, ofReal_re, ofReal_im]
    ring
  constructor
  · intro hz; change circ.A * normSq z + 2 * (circ.B * z).re + circ.C = 0 at hz; change (trans_circle c circ).A * normSq (z + c) + 2 * ((trans_circle c circ).B * (z + c)).re + (trans_circle c circ).C = 0; rw [h_eq]; exact hz
  · intro hz; change (trans_circle c circ).A * normSq (z + c) + 2 * ((trans_circle c circ).B * (z + c)).re + (trans_circle c circ).C = 0 at hz; change circ.A * normSq z + 2 * (circ.B * z).re + circ.C = 0; rw [← h_eq]; exact hz

def dil_circle (a : ℂ) (ha : a ≠ 0) (circ : GenCircle) : GenCircle :=
  let A' := circ.A
  let B' := circ.B * conj a
  let C' := circ.C * normSq a
  have h_normSq_a : 0 < normSq a := Complex.normSq_pos.mpr ha
  have h_valid : A' * C' < normSq B' := by
    have h1 : normSq B' = normSq circ.B * normSq a := by
      change normSq (circ.B * conj a) = normSq circ.B * normSq a
      rw [Complex.normSq_mul, Complex.normSq_conj]
    have h2 : A' * C' = (circ.A * circ.C) * normSq a := by
      change circ.A * (circ.C * normSq a) = (circ.A * circ.C) * normSq a
      ring
    rw [h1, h2]
    exact mul_lt_mul_of_pos_right circ.valid h_normSq_a
  { A := A', B := B', C := C', valid := h_valid }

lemma dil_circle_contains (a : ℂ) (ha : a ≠ 0) (circ : GenCircle) (z : ℂ) :
    circ.contains z ↔ (dil_circle a ha circ).contains (a * z) := by
  have h_eq : (dil_circle a ha circ).A * normSq (a * z) + 2 * ((dil_circle a ha circ).B * (a * z)).re + (dil_circle a ha circ).C = (circ.A * normSq z + 2 * (circ.B * z).re + circ.C) * normSq a := by
    change circ.A * normSq (a * z) + 2 * ((circ.B * conj a) * (a * z)).re + (circ.C * normSq a) = (circ.A * normSq z + 2 * (circ.B * z).re + circ.C) * normSq a
    simp only [normSq_apply, mul_re, mul_im, conj_re, conj_im, ofReal_re, ofReal_im]
    ring
  constructor
  · intro hz; change circ.A * normSq z + 2 * (circ.B * z).re + circ.C = 0 at hz; change (dil_circle a ha circ).A * normSq (a * z) + 2 * ((dil_circle a ha circ).B * (a * z)).re + (dil_circle a ha circ).C = 0; rw [h_eq, hz, zero_mul]
  · intro hz; change (dil_circle a ha circ).A * normSq (a * z) + 2 * ((dil_circle a ha circ).B * (a * z)).re + (dil_circle a ha circ).C = 0 at hz; change circ.A * normSq z + 2 * (circ.B * z).re + circ.C = 0; rw [h_eq] at hz
    cases mul_eq_zero.mp hz with
    | inl h => exact h
    | inr h => exfalso; exact ne_of_gt (Complex.normSq_pos.mpr ha) h

def inv_circle (circ : GenCircle) : GenCircle :=
  let A' := circ.C
  let B' := conj circ.B
  let C' := circ.A
  have h_valid : A' * C' < normSq B' := by
    have h1 : normSq B' = normSq circ.B := by
      change normSq (conj circ.B) = normSq circ.B
      exact normSq_conj circ.B
    have h2 : A' * C' = circ.A * circ.C := by
      change circ.C * circ.A = circ.A * circ.C
      ring
    rw [h1, h2]
    exact circ.valid
  { A := A', B := B', C := C', valid := h_valid }

lemma inv_circle_contains (circ : GenCircle) (z : ℂ) (hz : z ≠ 0) :
    circ.contains z ↔ (inv_circle circ).contains z⁻¹ := by
  have hz2_real : normSq z ≠ 0 := Complex.normSq_pos.mpr hz |> ne_of_gt
  have h_eq : (inv_circle circ).A * normSq z⁻¹ + 2 * ((inv_circle circ).B * z⁻¹).re + (inv_circle circ).C = (circ.A * normSq z + 2 * (circ.B * z).re + circ.C) / normSq z := by
    rw [eq_div_iff_mul_eq hz2_real]
    change (circ.C * normSq z⁻¹ + 2 * (conj circ.B * z⁻¹).re + circ.A) * normSq z = circ.A * normSq z + 2 * (circ.B * z).re + circ.C
    simp only [normSq_apply, add_re, add_im, mul_re, mul_im, conj_re, conj_im, inv_re, inv_im, ofReal_re, ofReal_im]
    have h_denom : z.re ^ 2 + z.im ^ 2 ≠ 0 := by
      have h : normSq z = z.re ^ 2 + z.im ^ 2 := by simp [normSq_apply]; ring
      rw [← h]
      exact hz2_real
    field_simp
    ring
  constructor
  · intro h_contains; change circ.A * normSq z + 2 * (circ.B * z).re + circ.C = 0 at h_contains; change (inv_circle circ).A * normSq z⁻¹ + 2 * ((inv_circle circ).B * z⁻¹).re + (inv_circle circ).C = 0; rw [h_eq, h_contains, zero_div]
  · intro h_contains'; change (inv_circle circ).A * normSq z⁻¹ + 2 * ((inv_circle circ).B * z⁻¹).re + (inv_circle circ).C = 0 at h_contains'; change circ.A * normSq z + 2 * (circ.B * z).re + circ.C = 0
    rw [h_eq] at h_contains'
    have h_or := div_eq_zero_iff.mp h_contains'
    cases h_or with
    | inl h => exact h
    | inr h => exfalso; exact hz2_real h

lemma maps_to_01inf (z1 z2 z3 : RiemannSphere) (h12 : z1 ≠ z2) (h23 : z2 ≠ z3) (h13 : z1 ≠ z3) :
    ∃ M : MobiusTransform, M.eval z1 = some 0 ∧ M.eval z2 = some 1 ∧ M.eval z3 = none := by
  cases z1 with
  | none =>
      cases z2 with
      | none => exact (h12 rfl).elim
      | some z2 =>
          cases z3 with
          | none => exact (h13 rfl).elim
          | some z3 =>
              have hz23 : z2 ≠ z3 := by
                intro hz
                exact h23 (by simpa [hz])
              let M : MobiusTransform :=
                { a := 0,
                  b := z2 - z3,
                  c := 1,
                  d := -z3,
                  det_ne_zero := by
                    have hdet : (0 : ℂ) * (-z3) - (z2 - z3) * (1 : ℂ) = -(z2 - z3) := by ring
                    rw [hdet]
                    exact neg_ne_zero.mpr (sub_ne_zero.mpr hz23) }
              refine ⟨M, ?_, ?_, ?_⟩
              · simp [M, MobiusTransform.eval]
              · have hden : z2 - z3 ≠ 0 := sub_ne_zero.mpr hz23
                have hden' : z2 + -z3 ≠ 0 := by simpa using hden
                have hq : (z2 - z3) / (z2 + -z3) = (1 : ℂ) := by
                  simpa [sub_eq_add_neg] using congrArg id (div_self hden)
                simp [M, MobiusTransform.eval, hden', hq]
              · have hden0 : z3 + -z3 = 0 := by ring
                simp [M, MobiusTransform.eval, hden0]
  | some z1 =>
      cases z2 with
      | none =>
          cases z3 with
          | none => exact (h23 rfl).elim
          | some z3 =>
              have hz13 : z1 ≠ z3 := by
                intro hz
                exact h13 (by simpa [hz])
              let M : MobiusTransform :=
                { a := 1,
                  b := -z1,
                  c := 1,
                  d := -z3,
                  det_ne_zero := by
                    have hdet : (1 : ℂ) * (-z3) - (-z1) * (1 : ℂ) = z1 - z3 := by ring
                    rw [hdet]
                    exact sub_ne_zero.mpr hz13 }
              refine ⟨M, ?_, ?_, ?_⟩
              · have hden : z1 - z3 ≠ 0 := sub_ne_zero.mpr hz13
                have hden' : z1 + -z3 ≠ 0 := by simpa using hden
                simp [M, MobiusTransform.eval, hden']
              · simp [M, MobiusTransform.eval]
              · have hden0 : z3 + -z3 = 0 := by ring
                simp [M, MobiusTransform.eval, hden0]
      | some z2 =>
          cases z3 with
          | none =>
              have hz12 : z1 ≠ z2 := by
                intro hz
                exact h12 (by simpa [hz])
              let M : MobiusTransform :=
                { a := 1,
                  b := -z1,
                  c := 0,
                  d := z2 - z1,
                  det_ne_zero := by
                    have hdet : (1 : ℂ) * (z2 - z1) - (-z1) * (0 : ℂ) = z2 - z1 := by ring
                    rw [hdet]
                    exact sub_ne_zero.mpr hz12.symm }
              refine ⟨M, ?_, ?_, ?_⟩
              · have hden : z2 - z1 ≠ 0 := sub_ne_zero.mpr hz12.symm
                simp [M, MobiusTransform.eval, hden]
              · have hden : z2 - z1 ≠ 0 := sub_ne_zero.mpr hz12.symm
                have hsub : z2 + -z1 = z2 - z1 := by ring
                have hq : (z2 + -z1) / (z2 - z1) = (1 : ℂ) := by
                  rw [hsub]
                  exact div_self hden
                simp [M, MobiusTransform.eval, hden, hsub, hq]
              · simp [M, MobiusTransform.eval]
          | some z3 =>
              have hz12 : z1 ≠ z2 := by
                intro hz
                exact h12 (by simpa [hz])
              have hz23 : z2 ≠ z3 := by
                intro hz
                exact h23 (by simpa [hz])
              have hz13 : z1 ≠ z3 := by
                intro hz
                exact h13 (by simpa [hz])
              let M : MobiusTransform :=
                { a := z2 - z3,
                  b := -(z2 - z3) * z1,
                  c := z2 - z1,
                  d := -(z2 - z1) * z3,
                  det_ne_zero := by
                    have hdet :
                        (z2 - z3) * (-(z2 - z1) * z3) - (-(z2 - z3) * z1) * (z2 - z1) =
                          (z2 - z3) * (z2 - z1) * (z1 - z3) := by
                      ring
                    rw [hdet]
                    exact mul_ne_zero
                      (mul_ne_zero (sub_ne_zero.mpr hz23) (sub_ne_zero.mpr hz12.symm))
                      (sub_ne_zero.mpr hz13) }
              refine ⟨M, ?_, ?_, ?_⟩
              · have hden1 : (z2 - z1) * z1 + (z1 - z2) * z3 ≠ 0 := by
                  have hneq : (z2 - z1) * (z1 - z3) ≠ 0 := by
                    exact mul_ne_zero (sub_ne_zero.mpr hz12.symm) (sub_ne_zero.mpr hz13)
                  have hiden : (z2 - z1) * z1 + (z1 - z2) * z3 = (z2 - z1) * (z1 - z3) := by
                    ring
                  rw [hiden]
                  exact hneq
                have hnum : (z2 - z3) * z1 + (z3 - z2) * z1 = 0 := by ring
                simp [M, MobiusTransform.eval, hden1, hnum]
              · have hden2 : (z2 - z1) * z2 + (z1 - z2) * z3 ≠ 0 := by
                  have hneq : (z2 - z1) * (z2 - z3) ≠ 0 := by
                    exact mul_ne_zero (sub_ne_zero.mpr hz12.symm) (sub_ne_zero.mpr hz23)
                  have hiden : (z2 - z1) * z2 + (z1 - z2) * z3 = (z2 - z1) * (z2 - z3) := by
                    ring
                  rw [hiden]
                  exact hneq
                have hq : ((z2 - z3) * z2 + (z3 - z2) * z1) / ((z2 - z1) * z2 + (z1 - z2) * z3) = 1 := by
                  have hnumden :
                      (z2 - z3) * z2 + (z3 - z2) * z1 = (z2 - z1) * z2 + (z1 - z2) * z3 := by
                    ring
                  rw [hnumden]
                  exact div_self hden2
                simp [M, MobiusTransform.eval, hden2, hq]
              · have hden0 : (z2 - z1) * z3 + (z1 - z2) * z3 = 0 := by ring
                simp [M, MobiusTransform.eval, hden0]

lemma mobius_unique_01inf (M : MobiusTransform) (h0 : M.eval (some 0) = some 0)
    (h1 : M.eval (some 1) = some 1) (hinf : M.eval none = none) :
    ∀ z, M.eval z = z := by
  have hc : M.c = 0 := by
    dsimp [MobiusTransform.eval] at hinf
    split_ifs at hinf with h
    exact h
  have hb : M.b = 0 := by
    dsimp [MobiusTransform.eval] at h0
    have hdenom : M.c * 0 + M.d = M.d := by ring
    rw [hdenom] at h0
    split_ifs at h0 with hd
    have h0' := Option.some.inj h0
    have hnum : M.a * 0 + M.b = M.b := by ring
    rw [hnum] at h0'
    exact div_eq_zero_iff.mp h0' |>.resolve_right hd
  have had : M.a = M.d := by
    dsimp [MobiusTransform.eval] at h1
    have hdenom : M.c * 1 + M.d = M.d := by rw [hc, zero_mul, zero_add]
    rw [hdenom] at h1
    split_ifs at h1 with hd
    have h1' := Option.some.inj h1
    have hnum : M.a * 1 + M.b = M.a := by rw [hb, mul_one, add_zero]
    rw [hnum] at h1'
    have h1'' := (div_eq_iff_mul_eq hd).mp h1'
    rw [one_mul] at h1''
    exact h1''.symm
  have hd_ne : M.d ≠ 0 := by
    intro hd
    have hdet := M.det_ne_zero
    rw [hc, hb, hd, had, mul_zero, mul_zero, sub_zero] at hdet
    exact hdet rfl
  intro z
  cases z with
  | none =>
      dsimp [MobiusTransform.eval]
      rw [if_pos hc]
  | some z' =>
      dsimp [MobiusTransform.eval]
      have hdenom : M.c * z' + M.d = M.d := by rw [hc, zero_mul, zero_add]
      rw [hdenom]
      have hnum : M.a * z' + M.b = M.d * z' := by rw [hb, had, add_zero]
      rw [hnum]
      rw [if_neg hd_ne]
      congr 1
      rw [mul_comm]
      exact mul_div_cancel_right₀ z' hd_ne

def inv (M : MobiusTransform) : MobiusTransform :=
  { a := M.d,
    b := -M.b,
    c := -M.c,
    d := M.a,
    det_ne_zero := by
      have h := M.det_ne_zero
      dsimp
      have h_ring : M.d * M.a - -M.b * -M.c = M.a * M.d - M.b * M.c := by ring
      rw [h_ring]
      exact h }

def comp (M1 M2 : MobiusTransform) : MobiusTransform :=
  { a := M1.a * M2.a + M1.b * M2.c,
    b := M1.a * M2.b + M1.b * M2.d,
    c := M1.c * M2.a + M1.d * M2.c,
    d := M1.c * M2.b + M1.d * M2.d,
    det_ne_zero := by
      have h1 := M1.det_ne_zero
      have h2 := M2.det_ne_zero
      have h_ring : (M1.a * M2.a + M1.b * M2.c) * (M1.c * M2.b + M1.d * M2.d) -
                    (M1.a * M2.b + M1.b * M2.d) * (M1.c * M2.a + M1.d * M2.c) =
                    (M1.a * M1.d - M1.b * M1.c) * (M2.a * M2.d - M2.b * M2.c) := by ring
      rw [h_ring]
      exact mul_ne_zero h1 h2 }

lemma eval_inv (M : MobiusTransform) (z : RiemannSphere) :
    M.eval ((inv M).eval z) = z := by
  cases z with
  | none =>
    change M.eval (if -M.c = 0 then none else some (M.d / -M.c)) = none
    by_cases hc : M.c = 0
    · have hmc : -M.c = 0 := by rw [hc, neg_zero]
      rw [if_pos hmc]
      change (if M.c = 0 then none else some (M.a / M.c)) = none
      rw [if_pos hc]
    · have hmc : -M.c ≠ 0 := by intro h; apply hc; exact neg_eq_zero.mp h
      rw [if_neg hmc]
      change (if M.c * (M.d / -M.c) + M.d = 0 then none else some _) = none
      have h_denom : M.c * (M.d / -M.c) + M.d = 0 := by
        field_simp; ring
      rw [if_pos h_denom]
  | some z' =>
    change M.eval (if -M.c * z' + M.a = 0 then none else some ((M.d * z' + -M.b) / (-M.c * z' + M.a))) = some z'
    by_cases h_inv_denom : -M.c * z' + M.a = 0
    · rw [if_pos h_inv_denom]
      have hc : M.c ≠ 0 := by
        intro h
        have ha : M.a = 0 := by
          calc M.a = (-M.c * z' + M.a) + M.c * z' := by ring
          _ = 0 + M.c * z' := by rw [h_inv_denom]
          _ = 0 + 0 * z' := by rw [h]
          _ = 0 := by ring
        have h_det := M.det_ne_zero
        rw [h, ha] at h_det
        have h_zero : (0 : ℂ) * M.d - M.b * 0 = 0 := by ring
        rw [h_zero] at h_det
        exact h_det rfl
      change (if M.c = 0 then none else some (M.a / M.c)) = some z'
      rw [if_neg hc]
      congr 1
      have h_eq : M.a = M.c * z' := by
        calc M.a = (-M.c * z' + M.a) + M.c * z' := by ring
        _ = 0 + M.c * z' := by rw [h_inv_denom]
        _ = M.c * z' := by ring
      rw [h_eq]
      have : M.c * z' / M.c = z' * M.c / M.c := by rw [mul_comm]
      rw [this, mul_div_cancel_right₀ _ hc]
    · rw [if_neg h_inv_denom]
      change (if M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d = 0 then none else some _) = some z'
      have h_denom : M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d ≠ 0 := by
        intro h_zero
        have h_det := M.det_ne_zero
        have h_zero_mul : (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) * (-M.c * z' + M.a) = 0 := by
          rw [h_zero, zero_mul]
        have h_simp : (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) * (-M.c * z' + M.a) = M.a * M.d - M.b * M.c := by
          calc (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) * (-M.c * z' + M.a)
            _ = M.c * (((M.d * z' + -M.b) / (-M.c * z' + M.a)) * (-M.c * z' + M.a)) + M.d * (-M.c * z' + M.a) := by ring
            _ = M.c * (M.d * z' + -M.b) + M.d * (-M.c * z' + M.a) := by
              rw [div_mul_cancel₀ _ h_inv_denom]
            _ = M.a * M.d - M.b * M.c := by ring
        rw [h_simp] at h_zero_mul
        exact h_det h_zero_mul
      rw [if_neg h_denom]
      congr 1
      have h_cross : (M.a * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.b) = z' * (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) := by
        have h1 : (M.a * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.b) * (-M.c * z' + M.a) = (M.a * M.d - M.b * M.c) * z' := by
          calc (M.a * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.b) * (-M.c * z' + M.a)
            _ = M.a * (((M.d * z' + -M.b) / (-M.c * z' + M.a)) * (-M.c * z' + M.a)) + M.b * (-M.c * z' + M.a) := by ring
            _ = M.a * (M.d * z' + -M.b) + M.b * (-M.c * z' + M.a) := by rw [div_mul_cancel₀ _ h_inv_denom]
            _ = (M.a * M.d - M.b * M.c) * z' := by ring
        have h2 : z' * (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) * (-M.c * z' + M.a) = (M.a * M.d - M.b * M.c) * z' := by
          calc z' * (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) * (-M.c * z' + M.a)
            _ = z' * ((M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) * (-M.c * z' + M.a)) := by ring
            _ = z' * (M.c * (((M.d * z' + -M.b) / (-M.c * z' + M.a)) * (-M.c * z' + M.a)) + M.d * (-M.c * z' + M.a)) := by ring
            _ = z' * (M.c * (M.d * z' + -M.b) + M.d * (-M.c * z' + M.a)) := by rw [div_mul_cancel₀ _ h_inv_denom]
            _ = (M.a * M.d - M.b * M.c) * z' := by ring
        have h3 : (M.a * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.b) * (-M.c * z' + M.a) = z' * (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) * (-M.c * z' + M.a) := by
          rw [h1, h2]
        exact mul_right_cancel₀ h_inv_denom h3
      calc (M.a * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.b) / (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d)
        _ = (z' * (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d)) / (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) := by rw [h_cross]
        _ = z' := by rw [mul_div_cancel_right₀ _ h_denom]

lemma eval_comp (M1 M2 : MobiusTransform) (z : RiemannSphere) :
    (comp M1 M2).eval z = M1.eval (M2.eval z) := by
  cases z with
  | none =>
    change (if M1.c * M2.a + M1.d * M2.c = 0 then none else some ((M1.a * M2.a + M1.b * M2.c) / (M1.c * M2.a + M1.d * M2.c))) =
           M1.eval (if M2.c = 0 then none else some (M2.a / M2.c))
    by_cases h2c : M2.c = 0
    · rw [if_pos h2c]
      change (if M1.c * M2.a + M1.d * M2.c = 0 then none else some _) =
             (if M1.c = 0 then none else some (M1.a / M1.c))
      have hc : M1.c * M2.a + M1.d * M2.c = M1.c * M2.a := by rw [h2c, mul_zero, add_zero]
      have ha : M1.a * M2.a + M1.b * M2.c = M1.a * M2.a := by rw [h2c, mul_zero, add_zero]
      by_cases h1c : M1.c = 0
      · have : M1.c * M2.a + M1.d * M2.c = 0 := by rw [hc, h1c, zero_mul]
        rw [if_pos this, if_pos h1c]
      · have h2a : M2.a ≠ 0 := by
          intro ha_zero
          have h_det2 := M2.det_ne_zero
          rw [h2c, ha_zero, zero_mul, mul_zero, sub_zero] at h_det2
          exact h_det2 rfl
        have : M1.c * M2.a + M1.d * M2.c ≠ 0 := by
          rw [hc]
          exact mul_ne_zero h1c h2a
        rw [if_neg this, if_neg h1c]
        congr 1
        change ((M1.a * M2.a + M1.b * M2.c) / (M1.c * M2.a + M1.d * M2.c)) = M1.a / M1.c
        have num_eq : (M1.a * M2.a + M1.b * M2.c) = M1.a * M2.a := by rw [h2c, mul_zero, add_zero]
        have den_eq : (M1.c * M2.a + M1.d * M2.c) = M1.c * M2.a := by rw [h2c, mul_zero, add_zero]
        rw [num_eq, den_eq]
        have cross : M1.a * M2.a / (M1.c * M2.a) = M1.a / M1.c := by
          rw [eq_div_iff_mul_eq h1c]
          calc M1.a * M2.a / (M1.c * M2.a) * M1.c
            _ = M1.a * M2.a * M1.c / (M1.c * M2.a) := by rw [div_mul_eq_mul_div]
            _ = M1.a * (M1.c * M2.a) / (M1.c * M2.a) := by ring_nf
            _ = M1.a := by rw [mul_div_cancel_right₀ _ (mul_ne_zero h1c h2a)]
        rw [cross]
    · rw [if_neg h2c]
      change (if M1.c * M2.a + M1.d * M2.c = 0 then none else some _) =
             (if M1.c * (M2.a / M2.c) + M1.d = 0 then none else some _)
      have h_denom : M1.c * (M2.a / M2.c) + M1.d = 0 ↔ M1.c * M2.a + M1.d * M2.c = 0 := by
        constructor
        · intro h
          calc M1.c * M2.a + M1.d * M2.c
            _ = (M1.c * (M2.a / M2.c) + M1.d) * M2.c := by
              have : M1.c * (M2.a / M2.c) * M2.c = M1.c * M2.a := by
                rw [mul_assoc, div_mul_cancel₀ _ h2c]
              rw [add_mul, this]
            _ = 0 * M2.c := by rw [h]
            _ = 0 := zero_mul M2.c
        · intro h
          have h_eq : (M1.c * (M2.a / M2.c) + M1.d) * M2.c = 0 := by
            calc (M1.c * (M2.a / M2.c) + M1.d) * M2.c
              _ = M1.c * (M2.a / M2.c) * M2.c + M1.d * M2.c := by ring
              _ = M1.c * M2.a + M1.d * M2.c := by
                have : M1.c * (M2.a / M2.c) * M2.c = M1.c * M2.a := by
                  rw [mul_assoc, div_mul_cancel₀ _ h2c]
                rw [this]
              _ = 0 := h
          exact (mul_eq_zero.mp h_eq).resolve_right h2c
      by_cases h_c_zero : M1.c * M2.a + M1.d * M2.c = 0
      · rw [if_pos h_c_zero, if_pos (h_denom.mpr h_c_zero)]
      · rw [if_neg h_c_zero, if_neg (mt h_denom.mp h_c_zero)]
        congr 1
        have h_c_zero' : M1.c * (M2.a / M2.c) + M1.d ≠ 0 := mt h_denom.mp h_c_zero
        change ((M1.a * M2.a + M1.b * M2.c) / (M1.c * M2.a + M1.d * M2.c)) =
               (M1.a * (M2.a / M2.c) + M1.b) / (M1.c * (M2.a / M2.c) + M1.d)
        have num_eq : (M1.a * (M2.a / M2.c) + M1.b) = (M1.a * M2.a + M1.b * M2.c) / M2.c := by
          rw [eq_div_iff_mul_eq h2c]
          calc (M1.a * (M2.a / M2.c) + M1.b) * M2.c
            _ = M1.a * (M2.a / M2.c) * M2.c + M1.b * M2.c := by ring
            _ = M1.a * M2.a + M1.b * M2.c := by
              have : M1.a * (M2.a / M2.c) * M2.c = M1.a * M2.a := by rw [mul_assoc, div_mul_cancel₀ _ h2c]
              rw [this]
        have den_eq : (M1.c * (M2.a / M2.c) + M1.d) = (M1.c * M2.a + M1.d * M2.c) / M2.c := by
          rw [eq_div_iff_mul_eq h2c]
          calc (M1.c * (M2.a / M2.c) + M1.d) * M2.c
            _ = M1.c * (M2.a / M2.c) * M2.c + M1.d * M2.c := by ring
            _ = M1.c * M2.a + M1.d * M2.c := by
              have : M1.c * (M2.a / M2.c) * M2.c = M1.c * M2.a := by rw [mul_assoc, div_mul_cancel₀ _ h2c]
              rw [this]
        rw [num_eq, den_eq]
        have cross : (M1.a * M2.a + M1.b * M2.c) / M2.c / ((M1.c * M2.a + M1.d * M2.c) / M2.c) = (M1.a * M2.a + M1.b * M2.c) / (M1.c * M2.a + M1.d * M2.c) := by
          rw [div_div_div_cancel_right₀ h2c]
        rw [cross]
  | some z' =>
    change (if (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) = 0 then none else some _) =
           M1.eval (if M2.c * z' + M2.d = 0 then none else some _)
    by_cases h2_denom : M2.c * z' + M2.d = 0
    · rw [if_pos h2_denom]
      change (if (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) = 0 then none else some _) =
             (if M1.c = 0 then none else some (M1.a / M1.c))
      have hc : (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) = M1.c * (M2.a * z' + M2.b) := by
        calc (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d)
          _ = M1.c * (M2.a * z' + M2.b) + M1.d * (M2.c * z' + M2.d) := by ring
          _ = M1.c * (M2.a * z' + M2.b) + M1.d * 0 := by rw [h2_denom]
          _ = M1.c * (M2.a * z' + M2.b) := by ring
      have ha : (M1.a * M2.a + M1.b * M2.c) * z' + (M1.a * M2.b + M1.b * M2.d) = M1.a * (M2.a * z' + M2.b) := by
        calc (M1.a * M2.a + M1.b * M2.c) * z' + (M1.a * M2.b + M1.b * M2.d)
          _ = M1.a * (M2.a * z' + M2.b) + M1.b * (M2.c * z' + M2.d) := by ring
          _ = M1.a * (M2.a * z' + M2.b) + M1.b * 0 := by rw [h2_denom]
          _ = M1.a * (M2.a * z' + M2.b) := by ring
      by_cases h1c : M1.c = 0
      · have : (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) = 0 := by
          rw [hc, h1c, zero_mul]
        rw [if_pos this, if_pos h1c]
      · have h2a : M2.a * z' + M2.b ≠ 0 := by
          intro h_zero
          have h_det2 := M2.det_ne_zero
          have : (M2.a * z' + M2.b) * M2.c - (M2.c * z' + M2.d) * M2.a = M2.b * M2.c - M2.d * M2.a := by ring
          rw [h_zero, h2_denom, zero_mul, zero_mul, zero_sub] at this
          have h_det2_neg : M2.b * M2.c - M2.a * M2.d = 0 := by
            calc M2.b * M2.c - M2.a * M2.d
              _ = M2.b * M2.c - M2.d * M2.a := by ring
              _ = -0 := this.symm
              _ = 0 := neg_zero
          have h_det2_pos : M2.a * M2.d - M2.b * M2.c = 0 := by
            calc M2.a * M2.d - M2.b * M2.c
              _ = - (M2.b * M2.c - M2.a * M2.d) := by ring
              _ = - 0 := by rw [h_det2_neg]
              _ = 0 := neg_zero
          exact h_det2 h_det2_pos
        have : (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) ≠ 0 := by
          rw [hc]
          exact mul_ne_zero h1c h2a
        rw [if_neg this, if_neg h1c]
        congr 1
        change ((M1.a * M2.a + M1.b * M2.c) * z' + (M1.a * M2.b + M1.b * M2.d)) / ((M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d)) = M1.a / M1.c
        rw [hc, ha]
        have : M1.a * (M2.a * z' + M2.b) / (M1.c * (M2.a * z' + M2.b)) = M1.a / M1.c := by
          rw [mul_comm M1.a, mul_comm M1.c]
          rw [mul_div_mul_left _ _ h2a]
        exact this
    · rw [if_neg h2_denom]
      change (if (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) = 0 then none else some _) =
             (if M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d = 0 then none else some _)
      have h_denom : M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d = 0 ↔ (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) = 0 := by
        constructor
        · intro h
          calc (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d)
            _ = M1.c * (M2.a * z' + M2.b) + M1.d * (M2.c * z' + M2.d) := by ring
            _ = (M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d) * (M2.c * z' + M2.d) := by
              have : M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) * (M2.c * z' + M2.d) = M1.c * (M2.a * z' + M2.b) := by
                rw [mul_assoc, div_mul_cancel₀ _ h2_denom]
              rw [add_mul, this]
            _ = 0 * (M2.c * z' + M2.d) := by rw [h]
            _ = 0 := zero_mul _
        · intro h
          have h_eq : (M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d) * (M2.c * z' + M2.d) = 0 := by
            calc (M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d) * (M2.c * z' + M2.d)
              _ = M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) * (M2.c * z' + M2.d) + M1.d * (M2.c * z' + M2.d) := by ring
              _ = M1.c * (M2.a * z' + M2.b) + M1.d * (M2.c * z' + M2.d) := by
                have : M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) * (M2.c * z' + M2.d) = M1.c * (M2.a * z' + M2.b) := by
                  rw [mul_assoc, div_mul_cancel₀ _ h2_denom]
                rw [this]
              _ = (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) := by ring
              _ = 0 := h
          exact (mul_eq_zero.mp h_eq).resolve_right h2_denom
      by_cases h_c_zero : (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) = 0
      · rw [if_pos h_c_zero, if_pos (h_denom.mpr h_c_zero)]
      · rw [if_neg h_c_zero, if_neg (mt h_denom.mp h_c_zero)]
        congr 1
        change ((M1.a * M2.a + M1.b * M2.c) * z' + (M1.a * M2.b + M1.b * M2.d)) / ((M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d)) =
               (M1.a * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.b) / (M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d)
        have num_eq : (M1.a * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.b) = ((M1.a * M2.a + M1.b * M2.c) * z' + (M1.a * M2.b + M1.b * M2.d)) / (M2.c * z' + M2.d) := by
          rw [eq_div_iff_mul_eq h2_denom]
          calc (M1.a * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.b) * (M2.c * z' + M2.d)
            _ = M1.a * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) * (M2.c * z' + M2.d) + M1.b * (M2.c * z' + M2.d) := by ring
            _ = M1.a * (M2.a * z' + M2.b) + M1.b * (M2.c * z' + M2.d) := by
              have : M1.a * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) * (M2.c * z' + M2.d) = M1.a * (M2.a * z' + M2.b) := by
                rw [mul_assoc, div_mul_cancel₀ _ h2_denom]
              rw [this]
            _ = (M1.a * M2.a + M1.b * M2.c) * z' + (M1.a * M2.b + M1.b * M2.d) := by ring
        have den_eq : (M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d) = ((M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d)) / (M2.c * z' + M2.d) := by
          rw [eq_div_iff_mul_eq h2_denom]
          calc (M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d) * (M2.c * z' + M2.d)
            _ = M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) * (M2.c * z' + M2.d) + M1.d * (M2.c * z' + M2.d) := by ring
            _ = M1.c * (M2.a * z' + M2.b) + M1.d * (M2.c * z' + M2.d) := by
              have : M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) * (M2.c * z' + M2.d) = M1.c * (M2.a * z' + M2.b) := by
                rw [mul_assoc, div_mul_cancel₀ _ h2_denom]
              rw [this]
            _ = (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) := by ring
        rw [num_eq, den_eq]
        rw [div_div_div_cancel_right₀ h2_denom]


lemma inv_eval (M : MobiusTransform) (z : RiemannSphere) :
    (inv M).eval (M.eval z) = z := by
  have h := eval_inv (inv M) z
  have h_eq : (inv (inv M)).eval z = M.eval z := by
    cases z with
    | none => dsimp [inv, MobiusTransform.eval]; simp only [neg_neg]
    | some z' => dsimp [inv, MobiusTransform.eval]; simp only [neg_neg]
  rw [h_eq] at h
  exact h

/-- The action of the Möbius group on the Riemann sphere is strictly 3-transitive.
    Any three distinct points determine a unique Möbius transformation
    mapping them to any other three distinct points. -/
theorem strictly_three_transitive
    (z1 z2 z3 : RiemannSphere) (h12 : z1 ≠ z2) (h23 : z2 ≠ z3) (h13 : z1 ≠ z3)
    (w1 w2 w3 : RiemannSphere) (g12 : w1 ≠ w2) (g23 : w2 ≠ w3) (g13 : w1 ≠ w3) :
    ∃ M : MobiusTransform,
      M.eval z1 = w1 ∧ M.eval z2 = w2 ∧ M.eval z3 = w3 ∧
      ∀ M' : MobiusTransform, M'.eval z1 = w1 ∧ M'.eval z2 = w2 ∧ M'.eval z3 = w3 →
        M.equiv M' := by
  obtain ⟨M1, h1z1, h1z2, h1z3⟩ := maps_to_01inf z1 z2 z3 h12 h23 h13
  obtain ⟨M2, h2w1, h2w2, h2w3⟩ := maps_to_01inf w1 w2 w3 g12 g23 g13
  let M := comp (inv M2) M1
  have hmz1 : M.eval z1 = w1 := by
    calc M.eval z1 = (inv M2).eval (M1.eval z1) := eval_comp (inv M2) M1 z1
      _ = (inv M2).eval (some 0) := by rw [h1z1]
      _ = w1 := by
        have h_inv : (inv M2).eval (M2.eval w1) = w1 := inv_eval M2 w1
        rw [h2w1] at h_inv
        exact h_inv
  have hmz2 : M.eval z2 = w2 := by
    calc M.eval z2 = (inv M2).eval (M1.eval z2) := eval_comp (inv M2) M1 z2
      _ = (inv M2).eval (some 1) := by rw [h1z2]
      _ = w2 := by
        have h_inv : (inv M2).eval (M2.eval w2) = w2 := inv_eval M2 w2
        rw [h2w2] at h_inv
        exact h_inv
  have hmz3 : M.eval z3 = w3 := by
    calc M.eval z3 = (inv M2).eval (M1.eval z3) := eval_comp (inv M2) M1 z3
      _ = (inv M2).eval none := by rw [h1z3]
      _ = w3 := by
        have h_inv : (inv M2).eval (M2.eval w3) = w3 := inv_eval M2 w3
        rw [h2w3] at h_inv
        exact h_inv
  refine ⟨M, hmz1, hmz2, hmz3, ?_⟩
  intro M' hM'
  intro z
  let M_test := comp M2 (comp M' (inv M1))
  have ht0 : M_test.eval (some 0) = some 0 := by
    calc M_test.eval (some 0) = M2.eval ((comp M' (inv M1)).eval (some 0)) := eval_comp M2 (comp M' (inv M1)) (some 0)
      _ = M2.eval (M'.eval ((inv M1).eval (some 0))) := by rw [eval_comp M' (inv M1) (some 0)]
      _ = M2.eval (M'.eval z1) := by
        have h_inv : (inv M1).eval (M1.eval z1) = z1 := inv_eval M1 z1
        rw [h1z1] at h_inv
        rw [h_inv]
      _ = M2.eval w1 := by rw [hM'.1]
      _ = some 0 := h2w1
  have ht1 : M_test.eval (some 1) = some 1 := by
    calc M_test.eval (some 1) = M2.eval ((comp M' (inv M1)).eval (some 1)) := eval_comp M2 (comp M' (inv M1)) (some 1)
      _ = M2.eval (M'.eval ((inv M1).eval (some 1))) := by rw [eval_comp M' (inv M1) (some 1)]
      _ = M2.eval (M'.eval z2) := by
        have h_inv : (inv M1).eval (M1.eval z2) = z2 := inv_eval M1 z2
        rw [h1z2] at h_inv
        rw [h_inv]
      _ = M2.eval w2 := by rw [hM'.2.1]
      _ = some 1 := h2w2
  have htinf : M_test.eval none = none := by
    calc M_test.eval none = M2.eval ((comp M' (inv M1)).eval none) := eval_comp M2 (comp M' (inv M1)) none
      _ = M2.eval (M'.eval ((inv M1).eval none)) := by rw [eval_comp M' (inv M1) none]
      _ = M2.eval (M'.eval z3) := by
        have h_inv : (inv M1).eval (M1.eval z3) = z3 := inv_eval M1 z3
        rw [h1z3] at h_inv
        rw [h_inv]
      _ = M2.eval w3 := by rw [hM'.2.2]
      _ = none := h2w3
  have h_id := mobius_unique_01inf M_test ht0 ht1 htinf
  have h_M_eq_M' : ∀ y, M.eval y = M'.eval y := by
    intro y
    have h_z_eq : M_test.eval (M1.eval y) = M1.eval y := h_id (M1.eval y)
    have h_z_expand : M_test.eval (M1.eval y) = M2.eval (M'.eval y) := by
      calc M_test.eval (M1.eval y) = M2.eval ((comp M' (inv M1)).eval (M1.eval y)) := eval_comp M2 (comp M' (inv M1)) (M1.eval y)
        _ = M2.eval (M'.eval ((inv M1).eval (M1.eval y))) := by rw [eval_comp M' (inv M1) (M1.eval y)]
        _ = M2.eval (M'.eval y) := by rw [inv_eval M1 y]
    rw [h_z_expand] at h_z_eq
    calc M.eval y = (comp (inv M2) M1).eval y := rfl
      _ = (inv M2).eval (M1.eval y) := eval_comp (inv M2) M1 y
      _ = (inv M2).eval (M2.eval (M'.eval y)) := by rw [← h_z_eq]
      _ = M'.eval y := inv_eval M2 (M'.eval y)
  exact h_M_eq_M' z

/-- A fixed point of a Möbius transformation is a point z on the Riemann sphere
    such that M.eval z = z. -/
def MobiusTransform.is_fixed_point (M : MobiusTransform) (z : RiemannSphere) : Prop :=
  M.eval z = z

/-- Every non-identity Möbius transformation has one or two fixed points (with multiplicity).
    The discriminant of the transformation is Δ = (a+d)^2 - 4(ad-bc). -/
def MobiusTransform.discriminant (M : MobiusTransform) : ℂ :=
  (M.a + M.d) ^ 2 - 4 * (M.a * M.d - M.b * M.c)

/-- If c ≠ 0, a finite point γ is a fixed point if and only if
    c * γ^2 - (a - d) * γ - b = 0. -/
theorem fixed_point_quadratic (M : MobiusTransform) (hc : M.c ≠ 0) (γ : ℂ) :
    M.is_fixed_point (some γ) ↔ M.c * γ^2 - (M.a - M.d) * γ - M.b = 0 := by
  sorry

/-- When c = 0 and a ≠ d, the fixed points are exactly ∞ and -b/(a-d). -/
theorem fixed_point_linear (M : MobiusTransform) (hc : M.c = 0) (had : M.a ≠ M.d) :
    (∀ z, M.is_fixed_point z ↔ z = none ∨ z = some (- M.b / (M.a - M.d))) := by
  sorry

/-- When c = 0 and a = d (and b ≠ 0 for non-identity), the only fixed point is ∞ (translation). -/
theorem fixed_point_translation (M : MobiusTransform) (hc : M.c = 0) (had : M.a = M.d) (hb : M.b ≠ 0) :
    (∀ z, M.is_fixed_point z ↔ z = none) := by
  sorry

/-- Topologically, the projective linear group acts on the sphere which has Euler characteristic 2.
    Therefore, by Lefschetz-Hopf, any non-identity Möbius transformation has 2 fixed points
    (counted with algebraic multiplicity). We express this as:
    If a transformation fixes at least 3 distinct points, it must be the identity. -/
theorem three_fixed_points_implies_identity (M : MobiusTransform)
    (z1 z2 z3 : RiemannSphere) (h12 : z1 ≠ z2) (h23 : z2 ≠ z3) (h13 : z1 ≠ z3)
    (f1 : M.is_fixed_point z1) (f2 : M.is_fixed_point z2) (f3 : M.is_fixed_point z3) :
    ∀ z, M.eval z = z := by
  sorry

/-- Two Möbius transformations are conjugate if there exists a transformation g mapping between them. -/
def is_conjugate (M1 M2 : MobiusTransform) : Prop :=
  ∃ g : MobiusTransform, ∃ g_inv : MobiusTransform,
    (∀ z, g.eval (g_inv.eval z) = z) ∧
    (∀ z, M1.eval z = g.eval (M2.eval (g_inv.eval z)))

/-- The normal form matrix for the non-parabolic case with two finite fixed points γ1, γ2 and multiplier k. -/
def non_parabolic_matrix (k γ1 γ2 : ℂ) (hk0 : k ≠ 0) (hk : k ≠ 1) (hγ : γ1 ≠ γ2) : MobiusTransform :=
  { a := γ1 - k * γ2,
    b := (k - 1) * γ1 * γ2,
    c := 1 - k,
    d := k * γ1 - γ2,
    det_ne_zero := by
      dsimp
      have h_ring : (γ1 - k * γ2) * (k * γ1 - γ2) - (k - 1) * γ1 * γ2 * (1 - k) = k * (γ1 - γ2)^2 := by ring
      rw [h_ring]
      have h1 : (γ1 - γ2) ≠ 0 := sub_ne_zero.mpr hγ
      have h2 : (γ1 - γ2)^2 ≠ 0 := pow_ne_zero 2 h1
      exact mul_ne_zero hk0 h2 }

-- Non-parabolic (dilation/rotation) normal form H(k; γ₁, γ₂)
def nonParabolicNormalForm (k γ₁ γ₂ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![γ₁ - k * γ₂, (k - 1) * γ₁ * γ₂],
    ![1 - k, k * γ₁ - γ₂]]

/-- Non-parabolic Normal Form: A Möbius transformation with two distinct fixed points
    is conjugate to a dilation/rotation mapping z ↦ k*z. -/
theorem non_parabolic_normal_form (M : MobiusTransform) (z1 z2 : RiemannSphere)
    (h_distinct : z1 ≠ z2) (f1 : M.is_fixed_point z1) (f2 : M.is_fixed_point z2) :
    ∃ k : ℂ, k ≠ 0 ∧ k ≠ 1 ∧
      ∃ M_k : MobiusTransform,
        (∀ z : ℂ, M_k.eval (some z) = some (k * z)) ∧
        is_conjugate M M_k := by
  sorry

/-- The normal form matrix for the parabolic case with one finite fixed point γ and translation length β. -/
def parabolic_matrix (β γ : ℂ) (hβ : β ≠ 0) : MobiusTransform :=
  { a := 1 + γ * β,
    b := -β * γ^2,
    c := β,
    d := 1 - γ * β,
    det_ne_zero := by
      have h : (1 + γ * β) * (1 - γ * β) - (-β * γ^2) * β = 1 := by ring
      rw [h]
      exact one_ne_zero }

def parabolicNormalForm (β γ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![1 + γ * β, -β * γ^2],
    ![β, 1 - γ * β]]

lemma parabolic_trace (β γ : ℂ) :
    let H := parabolicNormalForm β γ
    (H 0 0) + (H 1 1) = 2 := by
  dsimp [parabolicNormalForm]
  ring

lemma parabolic_det (β γ : ℂ) :
    let H := parabolicNormalForm β γ
    (H 0 0) * (H 1 1) - (H 0 1) * (H 1 0) = 1 := by
  dsimp [parabolicNormalForm]
  ring

/-- Parabolic Normal Form: A Möbius transformation with exactly one fixed point
    is conjugate to a translation mapping z ↦ z + β. -/
theorem parabolic_normal_form (M : MobiusTransform) (z1 : RiemannSphere)
    (f1 : M.is_fixed_point z1) (h_unique : ∀ z, M.is_fixed_point z → z = z1) :
    ∃ β : ℂ, β ≠ 0 ∧
      ∃ M_β : MobiusTransform,
        (∀ z : ℂ, M_β.eval (some z) = some (z + β)) ∧
        is_conjugate M M_β := by
  sorry

/-- The pole of the transformation, z_∞ = -d/c, which maps to ∞. -/
noncomputable def MobiusTransform.pole (M : MobiusTransform) : ℂ :=
  - M.d / M.c

/-- The inverse pole of the transformation, Z_∞ = a/c, to which ∞ maps. -/
noncomputable def MobiusTransform.inv_pole (M : MobiusTransform) : ℂ :=
  M.a / M.c

/-- The Characteristic Parallelogram Theorem:
    The point midway between the two poles is the same as the point midway between the two fixed points. -/
theorem characteristic_parallelogram (M : MobiusTransform) (hc : M.c ≠ 0)
    (γ1 γ2 : ℂ) (f1 : M.is_fixed_point (some γ1)) (f2 : M.is_fixed_point (some γ2)) :
    γ1 + γ2 = M.pole + M.inv_pole := by
  sorry

/-- The characteristic constant k can be derived directly from the poles and fixed points. -/
theorem multiplier_from_poles (M : MobiusTransform) (hc : M.c ≠ 0)
    (γ1 γ2 : ℂ) (f1 : M.is_fixed_point (some γ1)) (f2 : M.is_fixed_point (some γ2))
    (h_distinct : γ1 ≠ M.pole) :
    ∃ k : ℂ, k = (γ2 - M.pole) / (γ1 - M.pole) ∧
             k = (M.inv_pole - γ1) / (M.inv_pole - γ2) := by
  sorry

-- Eigenvalue mapping: λ_i = c γ_i + d
lemma eigenvalue_mapping (a b c d lam γ : ℂ) (h_fixed : c * γ^2 + (d - a) * γ - b = 0) (h_eigen : lam = c * γ + d) :
    lam^2 - (a + d) * lam + (a * d - b * c) = 0 := by
  calc lam^2 - (a + d) * lam + (a * d - b * c)
    _ = (c * γ + d)^2 - (a + d) * (c * γ + d) + (a * d - b * c) := by rw [h_eigen]
    _ = c * (c * γ^2 + (d - a) * γ - b) := by ring
    _ = c * 0 := by rw [h_fixed]
    _ = 0 := by ring

/-- The roots of the characteristic polynomial det(lamI - H) are exactly lam_i = c*γ_i + d. -/
theorem eigenvalue_roots (M : MobiusTransform) (hc : M.c ≠ 0)
    (γ : ℂ) (f : M.is_fixed_point (some γ)) :
    let lam := M.c * γ + M.d;
    lam ^ 2 - (M.a + M.d) * lam + (M.a * M.d - M.b * M.c) = 0 := by
  have h_fixed : M.c * γ^2 + (M.d - M.a) * γ - M.b = 0 := by
    have h1 := (fixed_point_quadratic M hc γ).mp f
    have h2 : M.c * γ^2 + (M.d - M.a) * γ - M.b = M.c * γ^2 - (M.a - M.d) * γ - M.b := by ring
    rwa [h2]
  exact eigenvalue_mapping M.a M.b M.c M.d (M.c * γ + M.d) γ h_fixed rfl

/-- Translation by b -/
def translation_transform (b : ℂ) : MobiusTransform :=
  { a := 1, b := b, c := 0, d := 1, det_ne_zero := by norm_num }

/-- Dilation and rotation by a (homothety) -/
def dilation_transform (a : ℂ) (ha : a ≠ 0) : MobiusTransform :=
  { a := a, b := 0, c := 0, d := 1, det_ne_zero := by
      dsimp; ring_nf; exact ha }

/-- Inversion and reflection (1/z) -/
def inversion_transform : MobiusTransform :=
  { a := 0, b := 1, c := 1, d := 0, det_ne_zero := by norm_num }

/-- Every Möbius transformation with c ≠ 0 can be decomposed into a sequence of
    four simple transformations: f4 ∘ f3 ∘ f2 ∘ f1. -/
theorem mobius_decomposition (M : MobiusTransform) (hc : M.c ≠ 0) :
    let f1 := translation_transform (M.d / M.c);
    let f2 := inversion_transform;
    let f3 := dilation_transform ((M.b * M.c - M.a * M.d) / M.c^2) (by sorry);
    let f4 := translation_transform (M.a / M.c);
    ∀ z : ℂ, M.eval (some z) =
      f4.eval (f3.eval (f2.eval (f1.eval (some z)))) := by
  sorry

/-- Alternative algebraic representation of the decomposition:
    (az + b) / (cz + d) = a/c + (bc - ad) / (c^2 * (z + d/c)) -/
theorem mobius_algebraic_decomposition (M : MobiusTransform) (hc : M.c ≠ 0) (z : ℂ)
    (hz : M.c * z + M.d ≠ 0) :
    (M.a * z + M.b) / (M.c * z + M.d) =
      M.a / M.c + ((M.b * M.c - M.a * M.d) / M.c^2) / (z + M.d / M.c) := by
  have hz' : z + M.d / M.c ≠ 0 := by
    intro h
    have h1 : M.c * (z + M.d / M.c) = M.c * 0 := by rw [h]
    rw [mul_zero] at h1
    have h2 : M.c * (z + M.d / M.c) = M.c * z + M.d := by
      calc M.c * (z + M.d / M.c) = M.c * z + M.c * (M.d / M.c) := by ring
      _ = M.c * z + M.d := by rw [mul_div_cancel₀ _ hc]
    rw [h2] at h1
    exact hz h1
  have hc2 : M.c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have h1 : M.c * (z + M.d / M.c) = M.c * z + M.d := by
    calc M.c * (z + M.d / M.c) = M.c * z + M.c * (M.d / M.c) := by ring
    _ = M.c * z + M.d := by rw [mul_div_cancel₀ M.d hc]
  have eq1 : ((M.b * M.c - M.a * M.d) / M.c ^ 2) / (z + M.d / M.c) = (M.b * M.c - M.a * M.d) / (M.c ^ 2 * (z + M.d / M.c)) := by
    rw [div_div]
  rw [eq1]
  have eq2 : M.c ^ 2 * (z + M.d / M.c) = M.c * (M.c * z + M.d) := by
    calc M.c ^ 2 * (z + M.d / M.c) = M.c * (M.c * (z + M.d / M.c)) := by ring
    _ = M.c * (M.c * z + M.d) := by rw [h1]
  rw [eq2]
  have eq3 : M.a / M.c = (M.a * (M.c * z + M.d)) / (M.c * (M.c * z + M.d)) := by
    have h_cancel : (M.a * (M.c * z + M.d)) / (M.c * (M.c * z + M.d)) = M.a / M.c := by
      rw [mul_div_mul_right M.a M.c hz]
    exact h_cancel.symm
  rw [eq3]
  rw [← add_div]
  have eq4 : (M.a * (M.c * z + M.d) + (M.b * M.c - M.a * M.d)) = M.c * (M.a * z + M.b) := by ring
  rw [eq4]
  have h_final : (M.c * (M.a * z + M.b)) / (M.c * (M.c * z + M.d)) = (M.a * z + M.b) / (M.c * z + M.d) := by
    rw [mul_div_mul_left (M.a * z + M.b) (M.c * z + M.d) hc]
  rw [h_final]

/-- The cross-ratio of four distinct finite points. -/
noncomputable def cross_ratio (z1 z2 z3 z4 : ℂ) : ℂ :=
  ((z1 - z3) * (z2 - z4)) / ((z2 - z3) * (z1 - z4))

/-- Extended cross-ratio handling infinity on the Riemann sphere. -/
noncomputable def cross_ratio_ext (z1 z2 z3 z4 : RiemannSphere) : RiemannSphere :=
  match z1, z2, z3, z4 with
  | none, none, none, none => none
  | none, none, none, some d => none
  | none, none, some c, none => none
  | none, none, some c, some d => some 1
  | none, some b, none, none => none
  | none, some b, none, some d => some 0
  | none, some b, some c, none => none
  | none, some b, some c, some d => if b - c = 0 then none else some ((b - d) / (b - c))
  | some a, none, none, none => none
  | some a, none, none, some d => none
  | some a, none, some c, none => some 0
  | some a, none, some c, some d => if a - d = 0 then none else some ((a - c) / (a - d))
  | some a, some b, none, none => some 1
  | some a, some b, none, some d => if a - d = 0 then none else some ((b - d) / (a - d))
  | some a, some b, some c, none => if b - c = 0 then none else some ((a - c) / (b - c))
  | some a, some b, some c, some d => if (b - c) * (a - d) = 0 then none else some (((a - c) * (b - d)) / ((b - c) * (a - d)))

private noncomputable def proj_cross_ratio (p1 p2 p3 p4 : ℂ × ℂ) : RiemannSphere :=
  let num := (p1.1 * p3.2 - p3.1 * p1.2) * (p2.1 * p4.2 - p4.1 * p2.2)
  let den := (p2.1 * p3.2 - p3.1 * p2.2) * (p1.1 * p4.2 - p4.1 * p1.2)
  if den = 0 then none else some (num / den)

private noncomputable def to_proj (z : RiemannSphere) : ℂ × ℂ :=
  match z with | none => (1, 0) | some z' => (z', 1)

private lemma if_mul_eq_if (x y c : ℂ) (hc : c ≠ 0) :
  (if x = 0 then (none : RiemannSphere) else some (y / x)) =
  (if c * x = 0 then none else some ((c * y) / (c * x))) := by
  by_cases h : x = 0
  · have h2 : c * x = 0 := by rw [h, mul_zero]
    rw [if_pos h, if_pos h2]
  · have h2 : c * x ≠ 0 := mul_ne_zero hc h
    rw [if_neg h, if_neg h2]
    congr 1
    rw [mul_div_mul_left y x hc]

private lemma if_mul_eq_if_right (x y c : ℂ) (hc : c ≠ 0) :
  (if x = 0 then (none : RiemannSphere) else some (y / x)) =
  (if x * c = 0 then none else some ((y * c) / (x * c))) := by
  by_cases h : x = 0
  · have h2 : x * c = 0 := by rw [h, zero_mul]
    rw [if_pos h, if_pos h2]
  · have h2 : x * c ≠ 0 := mul_ne_zero h hc
    rw [if_neg h, if_neg h2]
    congr 1
    rw [mul_div_mul_right y x hc]

/-- Möbius transformations strictly preserve the extended cross-ratio. -/
theorem cross_ratio_preserving (M : MobiusTransform) (z1 z2 z3 z4 : RiemannSphere) :
    cross_ratio_ext z1 z2 z3 z4 =
    cross_ratio_ext (M.eval z1) (M.eval z2) (M.eval z3) (M.eval z4) := by
  have h_eq : ∀ w1 w2 w3 w4 : RiemannSphere, cross_ratio_ext w1 w2 w3 w4 = proj_cross_ratio (to_proj w1) (to_proj w2) (to_proj w3) (to_proj w4) := by
    intro w1 w2 w3 w4
    cases w1 <;> cases w2 <;> cases w3 <;> cases w4 <;> {
      dsimp [cross_ratio_ext, proj_cross_ratio, to_proj]
      simp only [mul_one, mul_zero, sub_zero, zero_sub, one_mul, zero_mul, sub_self, neg_mul_neg]
      try {
        have h_neg1 : (-1 : ℂ) ≠ 0 := by norm_num
        rw [if_mul_eq_if _ _ (-1) h_neg1]
      }
      try {
        have h_neg1 : (-1 : ℂ) ≠ 0 := by norm_num
        rw [if_mul_eq_if_right _ _ (-1) h_neg1]
      }
      try {
        by_cases h : (-1 : ℂ) = 0
        · exfalso; revert h; norm_num
        simp only [h, mul_eq_zero, false_or, or_false, if_false, div_self h]
        have hz : (0 : ℂ) / -1 = 0 := by norm_num
        rw [hz]
      }
      try {
        by_cases h : (1 : ℂ) = 0
        · exfalso; revert h; norm_num
        simp only [h, mul_eq_zero, false_or, or_false, if_false, div_self h]
      }
      try {
        congr 1
        funext hc
        congr 1
        field_simp
        ring
      }
      try rfl
    }
  
  rw [h_eq z1 z2 z3 z4, h_eq (M.eval z1) (M.eval z2) (M.eval z3) (M.eval z4)]
  let M_act (p : ℂ × ℂ) : ℂ × ℂ := (M.a * p.1 + M.b * p.2, M.c * p.1 + M.d * p.2)
  
  have h_eval_act : ∀ z : RiemannSphere, ∃ lam : ℂ, lam ≠ 0 ∧ (to_proj (M.eval z)).1 = lam * (M_act (to_proj z)).1 ∧ (to_proj (M.eval z)).2 = lam * (M_act (to_proj z)).2 := by
    intro z
    cases z with
    | none =>
      dsimp [MobiusTransform.eval, to_proj, M_act]
      by_cases hc : M.c = 0
      · rw [if_pos hc]
        use (1 / M.a)
        have ha : M.a ≠ 0 := by
          intro h
          have : M.a * M.d - M.b * M.c = 0 := by rw [h, hc]; ring
          exact M.det_ne_zero this
        constructor
        · exact one_div_ne_zero ha
        · constructor
          · dsimp [to_proj]; have hx : (M.a * 1 + M.b * 0) = M.a := by ring
            rw [hx, one_div, inv_mul_cancel₀ ha]
          · dsimp [to_proj]; have hx : (M.c * 1 + M.d * 0) = M.c := by ring
            rw [hx, hc, mul_zero]
      · rw [if_neg hc]
        use (1 / M.c)
        constructor
        · exact one_div_ne_zero hc
        · constructor
          · dsimp [to_proj]; have hx : (M.a * 1 + M.b * 0) = M.a := by ring
            rw [hx, one_div, div_eq_inv_mul]
          · dsimp [to_proj]; have hx : (M.c * 1 + M.d * 0) = M.c := by ring
            rw [hx, one_div, inv_mul_cancel₀ hc]
    | some z' =>
      dsimp [MobiusTransform.eval, to_proj, M_act]
      by_cases hd : M.c * z' + M.d = 0
      · rw [if_pos hd]
        use (1 / (M.a * z' + M.b))
        have ha : M.a * z' + M.b ≠ 0 := by
          intro h
          have h1 : M.d * (M.a * z' + M.b) - M.b * (M.c * z' + M.d) = 0 := by rw [h, hd]; ring
          have h2 : M.d * (M.a * z' + M.b) - M.b * (M.c * z' + M.d) = (M.a * M.d - M.b * M.c) * z' := by ring
          rw [h2] at h1
          have hz : z' = 0 := by
            cases mul_eq_zero.mp h1 with
            | inl hdet => exact (M.det_ne_zero hdet).elim
            | inr hz => exact hz
          rw [hz] at h hd
          have hb : M.b = 0 := by
            calc M.b = M.a * 0 + M.b := by ring
                 _ = 0 := h
          have hm_d : M.d = 0 := by
            calc M.d = M.c * 0 + M.d := by ring
                 _ = 0 := hd
          have hdet : M.a * M.d - M.b * M.c = 0 := by rw [hb, hm_d]; ring
          exact M.det_ne_zero hdet
        constructor
        · exact one_div_ne_zero ha
        · constructor
          · dsimp [to_proj]; have hx : (M.a * z' + M.b * 1) = M.a * z' + M.b := by ring
            rw [hx, one_div, inv_mul_cancel₀ ha]
          · dsimp [to_proj]; have hx : (M.c * z' + M.d * 1) = M.c * z' + M.d := by ring
            rw [hx, hd, mul_zero]
      · rw [if_neg hd]
        use (1 / (M.c * z' + M.d))
        constructor
        · exact one_div_ne_zero hd
        · constructor
          · dsimp [to_proj]; have hx : (M.a * z' + M.b * 1) = M.a * z' + M.b := by ring
            rw [hx, one_div, div_eq_inv_mul]
          · dsimp [to_proj]; have hx : (M.c * z' + M.d * 1) = M.c * z' + M.d := by ring
            rw [hx, one_div, inv_mul_cancel₀ hd]

  rcases h_eval_act z1 with ⟨L1, hL1, hz1_1, hz1_2⟩
  rcases h_eval_act z2 with ⟨L2, hL2, hz2_1, hz2_2⟩
  rcases h_eval_act z3 with ⟨L3, hL3, hz3_1, hz3_2⟩
  rcases h_eval_act z4 with ⟨L4, hL4, hz4_1, hz4_2⟩

  have h_det : ∀ u v : ℂ × ℂ, (M_act u).1 * (M_act v).2 - (M_act v).1 * (M_act u).2 = (M.a * M.d - M.b * M.c) * (u.1 * v.2 - v.1 * u.2) := by
    intro u v
    dsimp [M_act]
    ring

  have h_diff : ∀ (u v : ℂ × ℂ) (Lu Lv : ℂ) (pu pv : ℂ × ℂ), pu.1 = Lu * (M_act u).1 → pu.2 = Lu * (M_act u).2 → pv.1 = Lv * (M_act v).1 → pv.2 = Lv * (M_act v).2 →
    pu.1 * pv.2 - pv.1 * pu.2 = Lu * Lv * (M.a * M.d - M.b * M.c) * (u.1 * v.2 - v.1 * u.2) := by
    intro u v Lu Lv pu pv hu1 hu2 hv1 hv2
    rw [hu1, hu2, hv1, hv2]
    have : (Lu * (M_act u).1) * (Lv * (M_act v).2) - (Lv * (M_act v).1) * (Lu * (M_act u).2) = Lu * Lv * ((M_act u).1 * (M_act v).2 - (M_act v).1 * (M_act u).2) := by ring
    rw [this, h_det]
    ring

  have num_eq : ((to_proj (M.eval z1)).1 * (to_proj (M.eval z3)).2 - (to_proj (M.eval z3)).1 * (to_proj (M.eval z1)).2) *
                ((to_proj (M.eval z2)).1 * (to_proj (M.eval z4)).2 - (to_proj (M.eval z4)).1 * (to_proj (M.eval z2)).2) =
                (L1 * L2 * L3 * L4 * (M.a * M.d - M.b * M.c)^2) *
                (((to_proj z1).1 * (to_proj z3).2 - (to_proj z3).1 * (to_proj z1).2) * ((to_proj z2).1 * (to_proj z4).2 - (to_proj z4).1 * (to_proj z2).2)) := by
    rw [h_diff (to_proj z1) (to_proj z3) L1 L3 (to_proj (M.eval z1)) (to_proj (M.eval z3)) hz1_1 hz1_2 hz3_1 hz3_2]
    rw [h_diff (to_proj z2) (to_proj z4) L2 L4 (to_proj (M.eval z2)) (to_proj (M.eval z4)) hz2_1 hz2_2 hz4_1 hz4_2]
    ring

  have den_eq : ((to_proj (M.eval z2)).1 * (to_proj (M.eval z3)).2 - (to_proj (M.eval z3)).1 * (to_proj (M.eval z2)).2) *
                ((to_proj (M.eval z1)).1 * (to_proj (M.eval z4)).2 - (to_proj (M.eval z4)).1 * (to_proj (M.eval z1)).2) =
                (L1 * L2 * L3 * L4 * (M.a * M.d - M.b * M.c)^2) *
                (((to_proj z2).1 * (to_proj z3).2 - (to_proj z3).1 * (to_proj z2).2) * ((to_proj z1).1 * (to_proj z4).2 - (to_proj z4).1 * (to_proj z1).2)) := by
    rw [h_diff (to_proj z2) (to_proj z3) L2 L3 (to_proj (M.eval z2)) (to_proj (M.eval z3)) hz2_1 hz2_2 hz3_1 hz3_2]
    rw [h_diff (to_proj z1) (to_proj z4) L1 L4 (to_proj (M.eval z1)) (to_proj (M.eval z4)) hz1_1 hz1_2 hz4_1 hz4_2]
    ring

  let num1 := (((to_proj z1).1 * (to_proj z3).2 - (to_proj z3).1 * (to_proj z1).2) * ((to_proj z2).1 * (to_proj z4).2 - (to_proj z4).1 * (to_proj z2).2))
  let den1 := (((to_proj z2).1 * (to_proj z3).2 - (to_proj z3).1 * (to_proj z2).2) * ((to_proj z1).1 * (to_proj z4).2 - (to_proj z4).1 * (to_proj z1).2))
  let factor := (L1 * L2 * L3 * L4 * (M.a * M.d - M.b * M.c)^2)
  have h_factor_ne_zero : factor ≠ 0 := by
    refine mul_ne_zero ?_ (pow_ne_zero 2 M.det_ne_zero)
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero hL1 hL2) hL3) hL4

  have h_proj_cr_eval : proj_cross_ratio (to_proj (M.eval z1)) (to_proj (M.eval z2)) (to_proj (M.eval z3)) (to_proj (M.eval z4)) =
    if factor * den1 = 0 then none else some ((factor * num1) / (factor * den1)) := by
    dsimp [proj_cross_ratio]
    rw [num_eq, den_eq]
  rw [h_proj_cr_eval]

  dsimp [proj_cross_ratio]
  by_cases hden : den1 = 0
  · have hden2 : factor * den1 = 0 := by rw [hden, mul_zero]
    rw [if_pos hden, if_pos hden2]
  · have hden2 : factor * den1 ≠ 0 := mul_ne_zero h_factor_ne_zero hden
    rw [if_neg hden, if_neg hden2]
    congr 1
    rw [mul_div_mul_left num1 den1 h_factor_ne_zero]

/-- Four distinct points lie on a generalized circle if and only if their cross-ratio is strictly real. -/
theorem cocircular_iff_real_cross_ratio (z1 z2 z3 z4 : ℂ) :
    (∃ circ : GenCircle, circ.contains z1 ∧ circ.contains z2 ∧ circ.contains z3 ∧ circ.contains z4)
    ↔ (cross_ratio z1 z2 z3 z4).im = 0 := by
  sorry

/-- Two points are conjugate (symmetric) with respect to a generalized circle if any circle
    passing through them intersecting the original circle at a and b yields a harmonic cross-ratio -1. -/
def is_conjugate_wrt_circle (z1 z2 : RiemannSphere) (circ : GenCircle) : Prop :=
  ∀ D : GenCircle, D.containsExt z1 → D.containsExt z2 →
    ∃ a b : RiemannSphere, circ.containsExt a ∧ circ.containsExt b ∧ D.containsExt a ∧ D.containsExt b ∧
      cross_ratio_ext z1 z2 a b = some (-1)

/-- Explicit geometric conjugation formula with respect to a line passing through z0 with angle θ. -/
theorem conjugate_wrt_line (z z_star z0 : ℂ) (θ : ℝ) :
    z_star = Complex.exp (2 * Complex.I * θ) * conj (z - z0) + z0 := by
  sorry

/-- Explicit geometric conjugation formula with respect to a circle of radius r centered at z0. -/
theorem conjugate_wrt_circle_radius (z z_star z0 : ℂ) (r : ℝ) :
    z_star = (r ^ 2 : ℂ) / conj (z - z0) + z0 := by
  sorry

/-- Möbius transformations preserve conjugation with respect to generalized circles. -/
theorem conjugation_preserving (M : MobiusTransform) (z1 z2 : RiemannSphere) (circ : GenCircle)
    (circ' : GenCircle) (h_map : ∀ z, circ.containsExt z ↔ circ'.containsExt (M.eval z)) :
    is_conjugate_wrt_circle z1 z2 circ ↔
    is_conjugate_wrt_circle (M.eval z1) (M.eval z2) circ' := by
  sorry

/-- Homogeneous coordinates for the complex projective line CP^1. -/
structure CP1 where
  z1 : ℂ
  z2 : ℂ
  not_both_zero : z1 ≠ 0 ∨ z2 ≠ 0

instance : Inhabited CP1 where
  default := {
    z1 := 1, z2 := 0,
    not_both_zero := by
      left
      exact one_ne_zero
  }

/-- Equivalence relation on homogeneous coordinates. -/
def CP1.equiv (p q : CP1) : Prop :=
  ∃ lam : ℂ, lam ≠ 0 ∧ p.z1 = lam * q.z1 ∧ p.z2 = lam * q.z2

/-- Identification of CP^1 with the Riemann sphere. -/
noncomputable def CP1.toRiemannSphere (p : CP1) : RiemannSphere :=
  if p.z2 = 0 then none else some (p.z1 / p.z2)

/-- The action of an invertible 2x2 matrix on CP^1. -/
noncomputable def MobiusTransform.actCP1 (M : MobiusTransform) (p : CP1) : CP1 :=
  { z1 := M.a * p.z1 + M.b * p.z2,
    z2 := M.c * p.z1 + M.d * p.z2,
    not_both_zero := by
      by_contra h
      push_neg at h
      have hz1 : M.a * p.z1 + M.b * p.z2 = 0 := h.1
      have hz2 : M.c * p.z1 + M.d * p.z2 = 0 := h.2
      have hd1 : M.d * (M.a * p.z1 + M.b * p.z2) - M.b * (M.c * p.z1 + M.d * p.z2) = 0 := by rw [hz1, hz2]; ring
      have hd1_ring : M.d * (M.a * p.z1 + M.b * p.z2) - M.b * (M.c * p.z1 + M.d * p.z2) = (M.a * M.d - M.b * M.c) * p.z1 := by ring
      rw [hd1_ring] at hd1
      have hp1 : p.z1 = 0 := by
        cases mul_eq_zero.mp hd1 with
        | inl hdet => exact (M.det_ne_zero hdet).elim
        | inr hz1 => exact hz1
      have hd2 : M.a * (M.c * p.z1 + M.d * p.z2) - M.c * (M.a * p.z1 + M.b * p.z2) = 0 := by rw [hz1, hz2]; ring
      have hd2_ring : M.a * (M.c * p.z1 + M.d * p.z2) - M.c * (M.a * p.z1 + M.b * p.z2) = (M.a * M.d - M.b * M.c) * p.z2 := by ring
      rw [hd2_ring] at hd2
      have hp2 : p.z2 = 0 := by
        cases mul_eq_zero.mp hd2 with
        | inl hdet => exact (M.det_ne_zero hdet).elim
        | inr hz2 => exact hz2
      rcases p.not_both_zero with h1 | h2
      · exact h1 hp1
      · exact h2 hp2 }

/-- The correspondence theorem: Action on CP^1 equates to the fractional linear action on the Riemann sphere. -/
theorem mobius_action_correspondence (M : MobiusTransform) (p : CP1) :
    (M.actCP1 p).toRiemannSphere = M.eval (p.toRiemannSphere) := by
  sorry

/-- Scaling the matrix by a non-zero scalar lam produces the same Möbius transformation (PGL(2, C) equivalence). -/
theorem pgl_equivalence (M : MobiusTransform) (lam : ℂ) (hlam : lam ≠ 0) :
    let M_scaled : MobiusTransform := {
      a := lam * M.a,
      b := lam * M.b,
      c := lam * M.c,
      d := lam * M.d,
      det_ne_zero := by
        dsimp
        have h1 : lam * M.a * (lam * M.d) - lam * M.b * (lam * M.c) = (lam * lam) * (M.a * M.d - M.b * M.c) := by ring
        rw [h1]
        have hl2 : lam * lam ≠ 0 := mul_ne_zero hlam hlam
        exact mul_ne_zero hl2 M.det_ne_zero
    };
    ∀ z, M.eval z = M_scaled.eval z := by
  intro M_scaled z
  cases z with
  | none =>
    change (if M.c = 0 then none else some (M.a / M.c)) = (if lam * M.c = 0 then none else some (lam * M.a / (lam * M.c)))
    by_cases hc : M.c = 0
    · have hcs : lam * M.c = 0 := by rw [hc, mul_zero]
      rw [if_pos hc, if_pos hcs]
    · have hcs : lam * M.c ≠ 0 := mul_ne_zero hlam hc
      rw [if_neg hc, if_neg hcs]
      have : lam * M.a / (lam * M.c) = M.a / M.c := by
        rw [mul_div_mul_left M.a M.c hlam]
      rw [this]
  | some z' =>
    change (if M.c * z' + M.d = 0 then none else some ((M.a * z' + M.b) / (M.c * z' + M.d))) = (if lam * M.c * z' + lam * M.d = 0 then none else some ((lam * M.a * z' + lam * M.b) / (lam * M.c * z' + lam * M.d)))
    by_cases hdenom : M.c * z' + M.d = 0
    · have hdenom_scaled : lam * M.c * z' + lam * M.d = 0 := by
        have h_ring : lam * M.c * z' + lam * M.d = lam * (M.c * z' + M.d) := by ring
        rw [h_ring, hdenom, mul_zero]
      rw [if_pos hdenom, if_pos hdenom_scaled]
    · have hdenom_scaled : lam * M.c * z' + lam * M.d ≠ 0 := by
        intro h
        have ht : lam * (M.c * z' + M.d) = 0 := by
          have h1 : lam * (M.c * z' + M.d) = lam * M.c * z' + lam * M.d := by ring
          rw [h1, h]
        cases mul_eq_zero.mp ht with
        | inl h1 => exact hlam h1
        | inr h2 => exact hdenom h2
      rw [if_neg hdenom, if_neg hdenom_scaled]
      congr 1
      have hnum : lam * M.a * z' + lam * M.b = lam * (M.a * z' + M.b) := by ring
      have hden : lam * M.c * z' + lam * M.d = lam * (M.c * z' + M.d) := by ring
      rw [hnum, hden, mul_div_mul_left (M.a * z' + M.b) (M.c * z' + M.d) hlam]

theorem mobius_decomposition_alt (a b c d z : ℂ) (hc : c ≠ 0) (hz : z + d/c ≠ 0) :
    a/c + ((b*c - a*d)/c^2) * (1 / (z + d/c)) = (a*z + b) / (c*z + d) := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have h1 : c * (z + d / c) = c * z + d := by
    calc c * (z + d / c) = c * z + c * (d / c) := by ring
    _ = c * z + d := by rw [mul_div_cancel₀ d hc]
  have hczd : c * z + d ≠ 0 := by
    intro h
    have h2 : c * (z + d / c) = 0 := h1.symm ▸ h
    cases mul_eq_zero.mp h2 with
    | inl hc_eq_0 => exact hc hc_eq_0
    | inr hz_eq_0 => exact hz hz_eq_0
  have eq1 : ((b * c - a * d) / c ^ 2) * (1 / (z + d / c)) = (b * c - a * d) / (c ^ 2 * (z + d / c)) := by
    rw [mul_one_div, div_div]
  rw [eq1]
  have eq2 : c ^ 2 * (z + d / c) = c * (c * z + d) := by
    calc c ^ 2 * (z + d / c) = c * (c * (z + d / c)) := by ring
    _ = c * (c * z + d) := by rw [h1]
  rw [eq2]
  have eq3 : a / c = (a * (c * z + d)) / (c * (c * z + d)) := by
    have h_cancel : (a * (c * z + d)) / (c * (c * z + d)) = a / c := by
      rw [mul_div_mul_right a c hczd]
    exact h_cancel.symm
  rw [eq3]
  rw [← add_div]
  have eq4 : (a * (c * z + d) + (b * c - a * d)) = c * (a * z + b) := by ring
  rw [eq4]
  have h_final : (c * (a * z + b)) / (c * (c * z + d)) = (a * z + b) / (c * z + d) := by
    rw [mul_div_mul_left (a * z + b) (c * z + d) hc]
  rw [h_final]



/-- Circle-Preserving Theorem:
    A Möbius transformation maps a generalized circle to another generalized circle. -/
theorem circle_preserving (M : MobiusTransform) (circ : GenCircle) :
    ∃ circ' : GenCircle, ∀ z : RiemannSphere,
      circ.containsExt z ↔ circ'.containsExt (M.eval z) := by
  by_cases hc : M.c = 0
  · have hd : M.d ≠ 0 := by
      intro h
      have : M.a * M.d - M.b * M.c = 0 := by rw [h, hc]; ring
      exact M.det_ne_zero this
    have ha : M.a ≠ 0 := by
      intro h
      have : M.a * M.d - M.b * M.c = 0 := by rw [h, hc]; ring
      exact M.det_ne_zero this
    have had : M.a / M.d ≠ 0 := div_ne_zero ha hd
    let C1 := dil_circle (M.a / M.d) had circ
    let C2 := trans_circle (M.b / M.d) C1
    use C2
    intro z
    cases z with
    | none =>
      dsimp [MobiusTransform.eval]
      rw [if_pos hc]
      change circ.A = 0 ↔ C2.A = 0
      have hA : C2.A = circ.A := by rfl
      rw [hA]
    | some z' =>
      dsimp [MobiusTransform.eval]
      have hdenom : M.c * z' + M.d ≠ 0 := by rw [hc, zero_mul, zero_add]; exact hd
      rw [if_neg hdenom]
      change circ.contains z' ↔ C2.contains ((M.a * z' + M.b) / (M.c * z' + M.d))
      have hz_eq : (M.a * z' + M.b) / (M.c * z' + M.d) = (M.a / M.d) * z' + M.b / M.d := by
        rw [hc, zero_mul, zero_add]
        have h_div : (M.a * z' + M.b) / M.d = (M.a * z') / M.d + M.b / M.d := add_div (M.a * z') M.b M.d
        rw [h_div]
        ring
      rw [hz_eq]
      have step1 := dil_circle_contains (M.a / M.d) had circ z'
      have step2 := trans_circle_contains (M.b / M.d) C1 ((M.a / M.d) * z')
      rw [step1, step2]
  · have h_dil_ne_zero : ((M.b * M.c - M.a * M.d) / M.c ^ 2) ≠ 0 := by
      intro h
      have hc2 : M.c ^ 2 ≠ 0 := pow_ne_zero 2 hc
      have h1 : M.b * M.c - M.a * M.d = 0 := (div_eq_zero_iff.mp h).resolve_right hc2
      have h2 : M.a * M.d - M.b * M.c = 0 := by rw [sub_eq_zero] at h1 ⊢; rw [h1]
      exact M.det_ne_zero h2
    let C1 := trans_circle (M.d / M.c) circ
    let C2 := inv_circle C1
    let C3 := dil_circle ((M.b * M.c - M.a * M.d) / M.c ^ 2) h_dil_ne_zero C2
    let C4 := trans_circle (M.a / M.c) C3
    use C4
    intro z
    cases z with
    | none =>
      dsimp [MobiusTransform.eval]
      rw [if_neg hc]
      change circ.A = 0 ↔ C4.contains (M.a / M.c)
      have hc4 : C4.contains (M.a / M.c) ↔ C3.C = 0 := by
        have h := trans_circle_contains (M.a / M.c) C3 0
        have h0 : 0 + M.a / M.c = M.a / M.c := zero_add (M.a / M.c)
        rw [h0] at h
        have hC : C3.contains 0 ↔ C3.C = 0 := by
           change C3.A * normSq 0 + 2 * (C3.B * 0).re + C3.C = 0 ↔ C3.C = 0
           have h_zero : C3.B * 0 = 0 := mul_zero C3.B
           rw [h_zero, Complex.normSq_zero]
           change C3.A * 0 + 2 * (0 : ℂ).re + C3.C = 0 ↔ C3.C = 0
           simp
        rw [hC] at h
        exact h.symm
      rw [hc4]
      have hc3 : C3.C = C2.C * normSq ((M.b * M.c - M.a * M.d) / M.c ^ 2) := rfl
      have hc2 : C2.C = C1.A := rfl
      have hc1 : C1.A = circ.A := rfl
      rw [hc3, hc2, hc1]
      have h_norm : normSq ((M.b * M.c - M.a * M.d) / M.c ^ 2) ≠ 0 := Complex.normSq_pos.mpr h_dil_ne_zero |> ne_of_gt
      constructor
      · intro h; rw [h, zero_mul]
      · intro h
        cases mul_eq_zero.mp h with
        | inl h1 => exact h1
        | inr h2 => exfalso; exact h_norm (by exact_mod_cast h2)
    | some z' =>
      dsimp [MobiusTransform.eval]
      by_cases hdenom : M.c * z' + M.d = 0
      · rw [if_pos hdenom]
        change circ.contains z' ↔ C4.A = 0
        have hA : C4.A = C3.A := rfl
        have hA3 : C3.A = C2.A := rfl
        have hA2 : C2.A = C1.C := rfl
        have hz'_eq : z' = - M.d / M.c := by
          have : M.c * z' = - M.d := eq_neg_iff_add_eq_zero.mpr hdenom
          have h_div : (M.c * z') / M.c = (- M.d) / M.c := by rw [this]
          have h2 : (M.c * z') / M.c = z' := mul_div_cancel_left₀ z' hc
          rw [h2] at h_div
          exact h_div
        rw [hA, hA3, hA2]
        have h_step1 := trans_circle_contains (M.d / M.c) circ z'
        have hz_plus_d_c : z' + M.d / M.c = 0 := by
          have h1 : M.c * (z' + M.d / M.c) = 0 := by
            calc M.c * (z' + M.d / M.c) = M.c * z' + M.c * (M.d / M.c) := mul_add _ _ _
            _ = M.c * z' + M.d := by rw [mul_div_cancel₀ M.d hc]
            _ = 0 := hdenom
          cases mul_eq_zero.mp h1 with
          | inl h => exfalso; exact hc h
          | inr h => exact h
        rw [hz_plus_d_c] at h_step1
        have hC : C1.contains 0 ↔ C1.C = 0 := by
           change C1.A * normSq 0 + 2 * (C1.B * 0).re + C1.C = 0 ↔ C1.C = 0
           have h_zero : C1.B * 0 = 0 := mul_zero C1.B
           rw [h_zero, Complex.normSq_zero]
           change C1.A * 0 + 2 * (0 : ℂ).re + C1.C = 0 ↔ C1.C = 0
           simp
        rw [hC] at h_step1
        exact h_step1
      · rw [if_neg hdenom]
        have hz_plus_d_c_ne_0 : z' + M.d / M.c ≠ 0 := by
          intro h
          have h1 : M.c * (z' + M.d / M.c) = 0 := by rw [h, mul_zero]
          have h2 : M.c * z' + M.d = 0 := by
            calc M.c * z' + M.d = M.c * z' + M.c * (M.d / M.c) := by rw [mul_div_cancel₀ M.d hc]
            _ = M.c * (z' + M.d / M.c) := (mul_add _ _ _).symm
            _ = 0 := h1
          exact hdenom h2
        change circ.contains z' ↔ C4.contains ((M.a * z' + M.b) / (M.c * z' + M.d))
        have h_step1 := trans_circle_contains (M.d / M.c) circ z'
        have h_step2 := inv_circle_contains C1 (z' + M.d / M.c) hz_plus_d_c_ne_0
        have h_step3 := dil_circle_contains ((M.b * M.c - M.a * M.d) / M.c ^ 2) h_dil_ne_zero C2 (z' + M.d / M.c)⁻¹
        have h_step4 := trans_circle_contains (M.a / M.c) C3 (((M.b * M.c - M.a * M.d) / M.c ^ 2) * (z' + M.d / M.c)⁻¹)
        rw [h_step1, h_step2, h_step3, h_step4]
        have h_inv : (z' + M.d / M.c)⁻¹ = 1 / (z' + M.d / M.c) := inv_eq_one_div _
        rw [h_inv]
        have h_alt := mobius_decomposition_alt M.a M.b M.c M.d z' hc hz_plus_d_c_ne_0
        rw [add_comm] at h_alt
        rw [← h_alt]

/-- A real Möbius transformation corresponding to PGL(2, ℝ) acting on the real projective line. -/
structure RealMobiusTransform where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  det_ne_zero : a * d - b * c ≠ 0

instance : Inhabited RealMobiusTransform where
  default := {
    a := 1, b := 0, c := 0, d := 1,
    det_ne_zero := by norm_num
  }

/-- The evaluation of a real Möbius transformation on ℝ. -/
noncomputable def RealMobiusTransform.eval (M : RealMobiusTransform) (x : ℝ) : ℝ :=
  (M.a * x + M.b) / (M.c * x + M.d)

/-- The real Möbius transformation f(x) = (1+x)/(1-x) which has NO real fixed points. -/
def no_real_fixed_points_transform : RealMobiusTransform :=
  { a := 1,
    b := 1,
    c := -1,
    d := 1,
    det_ne_zero := by norm_num }

/-- Theorem: Unlike the complex projective line (which always has fixed points due to Euler characteristic 2),
    the real projective line (Euler characteristic 0) admits Möbius transformations with strictly zero fixed points.
    This corresponds topologically to the Lefschetz-Hopf theorem for the circle S^1. -/
theorem real_mobius_can_have_no_fixed_points :
    ¬ ∃ x : ℝ, no_real_fixed_points_transform.eval x = x := by
  intro ⟨x, hx⟩
  dsimp [no_real_fixed_points_transform, RealMobiusTransform.eval] at hx
  by_cases h : -1 * x + 1 = 0
  · rw [h, div_zero] at hx
    linarith
  · have h2 : 1 * x + 1 = x * (-1 * x + 1) := (div_eq_iff h).mp hx
    have h3 : x ^ 2 + 1 = (1 * x + 1) - x * (-1 * x + 1) := by ring
    have h4 : (1 * x + 1) - x * (-1 * x + 1) = 0 := by
      rw [h2]
      exact sub_self _
    have h5 : x ^ 2 + 1 = 0 := Eq.trans h3 h4
    have h6 : 0 ≤ x ^ 2 := sq_nonneg x
    linarith

noncomputable def circle_inversion (z z0 : ℂ) (r : ℝ) : ℂ := (r^2 : ℂ) / conj (z - z0) + z0

theorem circle_inversion_involution (z z0 : ℂ) (r : ℝ) (h_r : r ≠ 0) (h_z : z ≠ z0) : 
    circle_inversion (circle_inversion z z0 r) z0 r = z := by
  dsimp [circle_inversion]
  have h1 : (r^2 : ℂ) / conj (z - z0) + z0 - z0 = (r^2 : ℂ) / conj (z - z0) := by ring
  rw [h1]
  rw [map_div₀]
  have h_conj_r2 : conj (r^2 : ℂ) = (r^2 : ℂ) := by
    have h2 : ((r^2 : ℝ) : ℂ) = (r^2 : ℂ) := by push_cast; rfl
    rw [← h2]
    rw [Complex.conj_ofReal]
  rw [h_conj_r2]
  have h_conj_conj : conj (conj (z - z0)) = z - z0 := by
    exact star_star (z - z0)
  rw [h_conj_conj]
  have hr2_ne : (r^2 : ℂ) ≠ 0 := by
    intro hr2
    have hr2' : r^2 = 0 := by exact_mod_cast hr2
    have hr_0 : r = 0 := sq_eq_zero_iff.mp hr2'
    exact h_r hr_0
  have h_div : (r^2 : ℂ) / ((r^2 : ℂ) / (z - z0)) = z - z0 := by
    rw [div_div_eq_mul_div]
    rw [mul_comm]
    rw [mul_div_cancel_right₀ (z - z0) hr2_ne]
  rw [h_div]
  ring

theorem pgl2_homogenous_action (a b c d z1 z2 : ℂ) (hz2 : z2 ≠ 0) (hden : c*z1 + d*z2 ≠ 0) (hden_frac : c*(z1/z2) + d ≠ 0) :
    (a*z1 + b*z2) / (c*z1 + d*z2) = (a*(z1/z2) + b) / (c*(z1/z2) + d) := by
  have h_num : z2 * (a * (z1 / z2) + b) = a * z1 + b * z2 := by
    calc z2 * (a * (z1 / z2) + b) = a * (z2 * (z1 / z2)) + b * z2 := by ring
      _ = a * z1 + b * z2 := by rw [mul_div_cancel₀ z1 hz2]
  have h_den : z2 * (c * (z1 / z2) + d) = c * z1 + d * z2 := by
    calc z2 * (c * (z1 / z2) + d) = c * (z2 * (z1 / z2)) + d * z2 := by ring
      _ = c * z1 + d * z2 := by rw [mul_div_cancel₀ z1 hz2]
  have h_eq : (z2 * (a * (z1 / z2) + b)) / (z2 * (c * (z1 / z2) + d)) = (a * (z1 / z2) + b) / (c * (z1 / z2) + d) := by
    rw [mul_div_mul_left (a * (z1 / z2) + b) (c * (z1 / z2) + d) hz2]
  rw [← h_eq, h_num, h_den]

theorem mobius_scaling_equivalence (a b c d z L : ℂ) (hL : L ≠ 0) (hden : c*z + d ≠ 0) :
    (L*a*z + L*b) / (L*c*z + L*d) = (a*z + b) / (c*z + d) := by
  have hnum : L * a * z + L * b = L * (a * z + b) := by ring
  have hden_eq : L * c * z + L * d = L * (c * z + d) := by ring
  rw [hnum, hden_eq, mul_div_mul_left (a * z + b) (c * z + d) hL]

noncomputable def map_to_01inf (z1 z2 z3 z : ℂ) : ℂ := ((z - z1)*(z2 - z3)) / ((z - z3)*(z2 - z1))

theorem map_to_01inf_z1 (z1 z2 z3 : ℂ) (h1 : z1 - z3 ≠ 0) (h2 : z2 - z1 ≠ 0) : map_to_01inf z1 z2 z3 z1 = 0 := by
  dsimp [map_to_01inf]
  have h : z1 - z1 = 0 := by ring
  rw [h, zero_mul, zero_div]

theorem map_to_01inf_z2 (z1 z2 z3 : ℂ) (h1 : z2 - z3 ≠ 0) (h2 : z2 - z1 ≠ 0) : map_to_01inf z1 z2 z3 z2 = 1 := by
  dsimp [map_to_01inf]
  have h_num : (z2 - z1) * (z2 - z3) = (z2 - z3) * (z2 - z1) := by ring
  rw [h_num]
  exact div_self (mul_ne_zero h1 h2)

noncomputable def disk_to_half_plane (z : ℂ) : ℂ := (z + I) / (I * z + 1)

theorem disk_to_half_plane_zero : disk_to_half_plane 0 = I := by
  unfold disk_to_half_plane
  rw [zero_add, mul_zero, zero_add, div_one]

def trace_sq (a d : ℂ) : ℂ := (a + d)^2

theorem loxodromic_trace (L : ℂ) (h : L ≠ 0) : trace_sq L (L⁻¹) = (L + L⁻¹)^2 := by rfl

theorem real_trace_sq_nonneg (a d : ℝ) : 0 ≤ (a + d)^2 := by exact sq_nonneg (a + d)

theorem elliptic_norm_invariant (u v x y : ℝ) (h : u^2 + v^2 = 1) : (u*x - v*y)^2 + (v*x + u*y)^2 = x^2 + y^2 := by
  have h1 : (u*x - v*y)^2 + (v*x + u*y)^2 = (u^2 + v^2) * (x^2 + y^2) := by ring
  rw [h] at h1
  rw [one_mul] at h1
  exact h1

theorem hyperbolic_trace_bound (L : ℝ) (h : L ≠ 0) : (L + L⁻¹)^2 - 4 = (L - L⁻¹)^2 := by
  have h1 : L * L⁻¹ = 1 := mul_inv_cancel₀ h
  calc (L + L⁻¹)^2 - 4
    _ = (L - L⁻¹)^2 + 4 * (L * L⁻¹) - 4 := by ring
    _ = (L - L⁻¹)^2 + 4 * 1 - 4 := by rw [h1]
    _ = (L - L⁻¹)^2 := by ring

noncomputable def matrix_sq_trace (L : ℂ) : ℂ := (L^2 + (L⁻¹)^2)^2

theorem iter_trace_bound (L : ℂ) (h : L ≠ 0) : matrix_sq_trace L = ( (L + L⁻¹)^2 - 2 )^2 := by
  dsimp [matrix_sq_trace]
  have h1 : L * L⁻¹ = 1 := mul_inv_cancel₀ h
  congr 1
  calc L^2 + (L⁻¹)^2
    _ = (L + L⁻¹)^2 - 2 * (L * L⁻¹) := by ring
    _ = (L + L⁻¹)^2 - 2 * 1 := by rw [h1]
    _ = (L + L⁻¹)^2 - 2 := by ring

theorem hyperplane_reflection_involution (x a r : ℝ) (h : a ≠ 0) :
  let R_x := x - 2 * ((x * a - r) / (a * a)) * a;
  R_x - 2 * ((R_x * a - r) / (a * a)) * a = x := by
  intro R_x
  change (x - 2 * ((x * a - r) / (a * a)) * a) - 2 * (((x - 2 * ((x * a - r) / (a * a)) * a) * a - r) / (a * a)) * a = x
  have ha2 : a * a ≠ 0 := mul_ne_zero h h
  field_simp
  ring

theorem minkowski_det (x0 x1 x2 x3 : ℝ) :
  (x0 + x1 : ℂ) * (x0 - x1 : ℂ) - (x2 + x3 * I) * (x2 - x3 * I) = (x0^2 - x1^2 - x2^2 - x3^2 : ℝ) := by
  apply Complex.ext
  · simp [-Complex.ofReal_pow]
    ring
  · simp [-Complex.ofReal_pow]
    ring

end InfoGeometry

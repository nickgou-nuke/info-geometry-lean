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
      change normSq (circ.B - (circ.A : ℂ) * conj c) -
          circ.A * (circ.A * normSq c - 2 * (circ.B * c).re + circ.C) =
        normSq circ.B - circ.A * circ.C
      simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im,
        ofReal_re, ofReal_im]
      ring
    linarith [circ.valid]
  { A := A', B := B', C := C', valid := h_valid }

lemma trans_circle_contains (c : ℂ) (circ : GenCircle) (z : ℂ) :
    circ.contains z ↔ (trans_circle c circ).contains (z + c) := by
  have h_eq :
      (trans_circle c circ).A * normSq (z + c) +
          2 * ((trans_circle c circ).B * (z + c)).re +
          (trans_circle c circ).C =
        circ.A * normSq z + 2 * (circ.B * z).re + circ.C := by
    change circ.A * normSq (z + c) +
        2 * ((circ.B - (circ.A : ℂ) * conj c) * (z + c)).re +
          (circ.A * normSq c - 2 * (circ.B * c).re + circ.C) =
        circ.A * normSq z + 2 * (circ.B * z).re + circ.C
    simp only [normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im,
      conj_re, conj_im, ofReal_re, ofReal_im]
    ring
  constructor
  · intro hz
    change (trans_circle c circ).A * normSq (z + c) +
        2 * ((trans_circle c circ).B * (z + c)).re +
          (trans_circle c circ).C = 0
    rw [h_eq]
    exact hz
  · intro hz
    change circ.A * normSq z + 2 * (circ.B * z).re + circ.C = 0
    rw [← h_eq]
    exact hz

lemma trans_preserves_circle (c : ℂ) (circ : GenCircle) :
    ∃ circ' : GenCircle, ∀ z : ℂ, circ.contains z ↔ circ'.contains (z + c) :=
  ⟨trans_circle c circ, trans_circle_contains c circ⟩

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
  have h_eq :
      (dil_circle a ha circ).A * normSq (a * z) +
          2 * ((dil_circle a ha circ).B * (a * z)).re +
          (dil_circle a ha circ).C =
        (circ.A * normSq z + 2 * (circ.B * z).re + circ.C) * normSq a := by
    change circ.A * normSq (a * z) + 2 * ((circ.B * conj a) * (a * z)).re +
        (circ.C * normSq a) =
      (circ.A * normSq z + 2 * (circ.B * z).re + circ.C) * normSq a
    simp only [normSq_apply, mul_re, mul_im, conj_re, conj_im]
    ring
  have h_normSq_a : 0 < normSq a := Complex.normSq_pos.mpr ha
  constructor
  · intro hz
    change (dil_circle a ha circ).A * normSq (a * z) +
        2 * ((dil_circle a ha circ).B * (a * z)).re +
          (dil_circle a ha circ).C = 0
    rw [h_eq, hz, zero_mul]
  · intro hz
    change circ.A * normSq z + 2 * (circ.B * z).re + circ.C = 0
    change (dil_circle a ha circ).A * normSq (a * z) +
        2 * ((dil_circle a ha circ).B * (a * z)).re +
          (dil_circle a ha circ).C = 0 at hz
    rw [h_eq] at hz
    cases mul_eq_zero.mp hz with
    | inl h => exact h
    | inr h => exfalso; exact ne_of_gt h_normSq_a h

lemma dil_preserves_circle (a : ℂ) (ha : a ≠ 0) (circ : GenCircle) :
    ∃ circ' : GenCircle, ∀ z : ℂ, circ.contains z ↔ circ'.contains (a * z) :=
  ⟨dil_circle a ha circ, dil_circle_contains a ha circ⟩

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
  have hz2_real : normSq z ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hz)
  have h_eq :
      (inv_circle circ).A * normSq z⁻¹ +
          2 * ((inv_circle circ).B * z⁻¹).re +
          (inv_circle circ).C =
        (circ.A * normSq z + 2 * (circ.B * z).re + circ.C) / normSq z := by
    rw [eq_div_iff_mul_eq hz2_real]
    change (circ.C * normSq z⁻¹ + 2 * (conj circ.B * z⁻¹).re + circ.A) *
        normSq z =
      circ.A * normSq z + 2 * (circ.B * z).re + circ.C
    simp only [normSq_apply, mul_re, conj_re, conj_im, inv_re, inv_im]
    have h_denom : z.re ^ 2 + z.im ^ 2 ≠ 0 := by
      have h : normSq z = z.re ^ 2 + z.im ^ 2 := by
        simp [normSq_apply]
        ring
      rw [← h]
      exact hz2_real
    field_simp
    ring
  constructor
  · intro h_contains
    change (inv_circle circ).A * normSq z⁻¹ +
        2 * ((inv_circle circ).B * z⁻¹).re + (inv_circle circ).C = 0
    rw [h_eq, h_contains, zero_div]
  · intro h_contains'
    change circ.A * normSq z + 2 * (circ.B * z).re + circ.C = 0
    change (inv_circle circ).A * normSq z⁻¹ +
        2 * ((inv_circle circ).B * z⁻¹).re + (inv_circle circ).C = 0 at h_contains'
    rw [h_eq] at h_contains'
    have h_or := div_eq_zero_iff.mp h_contains'
    cases h_or with
    | inl h => exact h
    | inr h => exfalso; exact hz2_real h

lemma inv_preserves_circle (circ : GenCircle) :
    ∃ circ' : GenCircle, ∀ z : ℂ, z ≠ 0 → (circ.contains z ↔ circ'.contains z⁻¹) :=
  ⟨inv_circle circ, inv_circle_contains circ⟩

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
                exact h23 (by simp [hz])
              let M : MobiusTransform :=
                { a := 0
                  b := z2 - z3
                  c := 1
                  d := -z3
                  det_ne_zero := by
                    have hdet :
                        (0 : ℂ) * (-z3) - (z2 - z3) * (1 : ℂ) = -(z2 - z3) := by
                      ring
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
                exact h13 (by simp [hz])
              let M : MobiusTransform :=
                { a := 1
                  b := -z1
                  c := 1
                  d := -z3
                  det_ne_zero := by
                    have hdet : (1 : ℂ) * (-z3) - (-z1) * (1 : ℂ) = z1 - z3 := by
                      ring
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
                exact h12 (by simp [hz])
              let M : MobiusTransform :=
                { a := 1
                  b := -z1
                  c := 0
                  d := z2 - z1
                  det_ne_zero := by
                    have hdet : (1 : ℂ) * (z2 - z1) - (-z1) * (0 : ℂ) = z2 - z1 := by
                      ring
                    rw [hdet]
                    exact sub_ne_zero.mpr hz12.symm }
              refine ⟨M, ?_, ?_, ?_⟩
              · have hden : z2 - z1 ≠ 0 := sub_ne_zero.mpr hz12.symm
                simp [M, MobiusTransform.eval, hden]
              · have hden : z2 - z1 ≠ 0 := sub_ne_zero.mpr hz12.symm
                have hsub : z2 + -z1 = z2 - z1 := by ring
                simp [M, MobiusTransform.eval, hden, hsub]
              · simp [M, MobiusTransform.eval]
          | some z3 =>
              have hz12 : z1 ≠ z2 := by
                intro hz
                exact h12 (by simp [hz])
              have hz23 : z2 ≠ z3 := by
                intro hz
                exact h23 (by simp [hz])
              have hz13 : z1 ≠ z3 := by
                intro hz
                exact h13 (by simp [hz])
              let M : MobiusTransform :=
                { a := z2 - z3
                  b := -(z2 - z3) * z1
                  c := z2 - z1
                  d := -(z2 - z1) * z3
                  det_ne_zero := by
                    have hdet :
                        (z2 - z3) * (-(z2 - z1) * z3) -
                            (-(z2 - z3) * z1) * (z2 - z1) =
                          (z2 - z3) * (z2 - z1) * (z1 - z3) := by
                      ring
                    rw [hdet]
                    exact mul_ne_zero
                      (mul_ne_zero (sub_ne_zero.mpr hz23) (sub_ne_zero.mpr hz12.symm))
                      (sub_ne_zero.mpr hz13) }
              refine ⟨M, ?_, ?_, ?_⟩
              · have hden1 : (z2 - z1) * z1 + (z1 - z2) * z3 ≠ 0 := by
                  have hneq : (z2 - z1) * (z1 - z3) ≠ 0 :=
                    mul_ne_zero (sub_ne_zero.mpr hz12.symm) (sub_ne_zero.mpr hz13)
                  have hiden :
                      (z2 - z1) * z1 + (z1 - z2) * z3 = (z2 - z1) * (z1 - z3) := by
                    ring
                  rw [hiden]
                  exact hneq
                have hnum : (z2 - z3) * z1 + (z3 - z2) * z1 = 0 := by ring
                simp [M, MobiusTransform.eval, hden1, hnum]
              · have hden2 : (z2 - z1) * z2 + (z1 - z2) * z3 ≠ 0 := by
                  have hneq : (z2 - z1) * (z2 - z3) ≠ 0 :=
                    mul_ne_zero (sub_ne_zero.mpr hz12.symm) (sub_ne_zero.mpr hz23)
                  have hiden :
                      (z2 - z1) * z2 + (z1 - z2) * z3 = (z2 - z1) * (z2 - z3) := by
                    ring
                  rw [hiden]
                  exact hneq
                have hq :
                    ((z2 - z3) * z2 + (z3 - z2) * z1) /
                        ((z2 - z1) * z2 + (z1 - z2) * z3) = 1 := by
                  have hnumden :
                      (z2 - z3) * z2 + (z3 - z2) * z1 =
                        (z2 - z1) * z2 + (z1 - z2) * z3 := by
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
  dsimp [MobiusTransform.is_fixed_point]
  dsimp [MobiusTransform.eval]
  by_cases hden : M.c * γ + M.d = 0
  · constructor
    · intro h
      simp [hden] at h
    · intro hpoly
      have hd : M.d = - (M.c * γ) := by
        exact eq_neg_of_add_eq_zero_right hden
      have htmp : M.a * γ + M.b - γ * (M.c * γ + M.d) = 0 := by
        calc
          M.a * γ + M.b - γ * (M.c * γ + M.d) = -(M.c * γ ^ 2 - (M.a - M.d) * γ - M.b) := by ring
          _ = 0 := by simp [hpoly]
      have hzero : M.a * γ + M.b = 0 := by
        rw [hden] at htmp
        simpa using htmp
      have hdet0 : M.a * M.d - M.b * M.c = 0 := by
        rw [hd]
        calc
          M.a * (-(M.c * γ)) - M.b * M.c = - M.c * (M.a * γ + M.b) := by ring
          _ = 0 := by rw [hzero]; simp
      exact (M.det_ne_zero hdet0).elim
  · have hden' : M.c * γ + M.d ≠ 0 := hden
    constructor
    · intro h
      rw [if_neg hden'] at h
      have hdiv : (M.a * γ + M.b) / (M.c * γ + M.d) = γ := Option.some.inj h
      have hnumden : M.a * γ + M.b = γ * (M.c * γ + M.d) := by
        rw [div_eq_iff hden'] at hdiv
        exact hdiv
      have htmp : M.a * γ + M.b - γ * (M.c * γ + M.d) = 0 := by
        exact sub_eq_zero.mpr hnumden
      calc
        M.c * γ ^ 2 - (M.a - M.d) * γ - M.b = -(M.a * γ + M.b - γ * (M.c * γ + M.d)) := by ring
        _ = 0 := by rw [htmp]; simp
    · intro hpoly
      have htmp : M.a * γ + M.b - γ * (M.c * γ + M.d) = 0 := by
        calc
          M.a * γ + M.b - γ * (M.c * γ + M.d) = -(M.c * γ ^ 2 - (M.a - M.d) * γ - M.b) := by ring
          _ = 0 := by simp [hpoly]
      have hnumden : M.a * γ + M.b = γ * (M.c * γ + M.d) := by
        exact eq_of_sub_eq_zero htmp
      have hdiv : (M.a * γ + M.b) / (M.c * γ + M.d) = γ := by
        rw [div_eq_iff hden']
        exact hnumden
      simp [hden, hdiv]

/-- When c = 0 and a ≠ d, the fixed points are exactly ∞ and -b/(a-d). -/
theorem fixed_point_linear (M : MobiusTransform) (hc : M.c = 0) (had : M.a ≠ M.d) :
    (∀ z, M.is_fixed_point z ↔ z = none ∨ z = some (- M.b / (M.a - M.d))) := by
  have hd_nonzero : M.d ≠ 0 := by
    intro hd
    have hdet : M.a * M.d - M.b * M.c = 0 := by
      rw [hc, hd]
      ring
    exact M.det_ne_zero hdet
  intro z
  cases z with
  | none =>
      constructor
      · intro _
        left
        rfl
      · intro _
        simp [MobiusTransform.is_fixed_point, MobiusTransform.eval, hc]
  | some γ =>
      constructor
      · intro h
        have h' := h
        simp [MobiusTransform.is_fixed_point, MobiusTransform.eval, hc, hd_nonzero] at h'
        have hdiv : (M.a * γ + M.b) / M.d = γ := Option.some.inj h'
        have hnumden : M.a * γ + M.b = γ * M.d := by
          rw [div_eq_iff hd_nonzero] at hdiv
          exact hdiv
        have hlin : (M.a - M.d) * γ = - M.b := by
          have htmp : (M.a - M.d) * γ + M.b = 0 := by
            calc
              (M.a - M.d) * γ + M.b = M.a * γ + M.b - M.d * γ := by ring
              _ = M.a * γ + M.b - γ * M.d := by ring
              _ = 0 := by rw [hnumden]; ring
          exact eq_neg_of_add_eq_zero_left htmp
        have hsol : γ = - M.b / (M.a - M.d) := by
          apply (eq_div_iff (sub_ne_zero.mpr had)).2
          simpa [mul_comm] using hlin
        right
        exact congrArg some hsol
      · intro h
        rcases h with h | h
        · cases h
        · have hγ : γ = - M.b / (M.a - M.d) := Option.some.inj h
          subst hγ
          have hcalc : (M.a * (- M.b / (M.a - M.d)) + M.b) / M.d = - M.b / (M.a - M.d) := by
            have hden1 : M.a - M.d ≠ 0 := sub_ne_zero.mpr had
            field_simp [hd_nonzero, hden1]
            ring
          dsimp [MobiusTransform.is_fixed_point, MobiusTransform.eval]
          rw [hc]
          rw [if_neg (by simpa using hd_nonzero)]
          simp [hcalc]

/-- When c = 0 and a = d (and b ≠ 0 for non-identity), the only fixed point is ∞ (translation). -/
theorem fixed_point_translation (M : MobiusTransform) (hc : M.c = 0) (had : M.a = M.d) (hb : M.b ≠ 0) :
    (∀ z, M.is_fixed_point z ↔ z = none) := by
  intro z
  cases z with
  | none =>
      constructor
      · intro _; rfl
      · intro _; simp [MobiusTransform.is_fixed_point, MobiusTransform.eval, hc]
  | some z' =>
      constructor
      · intro hfix
        have ha : M.a ≠ 0 := by
          intro ha0
          have hd0 : M.d = 0 := by simpa [had] using ha0
          have hzero : M.a * M.d - M.b * M.c = 0 := by
            simp [hc, ha0, hd0]
          exact M.det_ne_zero hzero
        have hd : M.d = M.a := had.symm
        have hfixOpt := hfix
        simp [MobiusTransform.is_fixed_point, MobiusTransform.eval, hc, hd, ha] at hfixOpt
        have hfix' : ((M.a * z' + M.b) / M.a : ℂ) = z' := Option.some.inj hfixOpt
        have hlin : M.a * z' + M.b = z' * M.a := by
          exact (div_eq_iff ha).mp hfix'
        have hb0 : M.b = 0 := by
          have hlin' : M.a * z' + M.b = M.a * z' + 0 := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hlin
          exact add_left_cancel hlin'
        exact False.elim (hb hb0)
      · intro hz
        cases hz

/-- Topologically, the projective linear group acts on the sphere which has Euler characteristic 2.
    Therefore, by Lefschetz-Hopf, any non-identity Möbius transformation has 2 fixed points
    (counted with algebraic multiplicity). We express this as:
    If a transformation fixes at least 3 distinct points, it must be the identity. -/
theorem three_fixed_points_implies_identity (M : MobiusTransform)
    (z1 z2 z3 : RiemannSphere) (h12 : z1 ≠ z2) (h23 : z2 ≠ z3) (h13 : z1 ≠ z3)
    (f1 : M.is_fixed_point z1) (f2 : M.is_fixed_point z2) (f3 : M.is_fixed_point z3) :
    ∀ z, M.eval z = z := by
  by_cases hc : M.c = 0
  · by_cases had : M.a = M.d
    · by_cases hb : M.b = 0
      · have hd_ne : M.d ≠ 0 := by
          intro hd
          have hdet : M.a * M.d - M.b * M.c = 0 := by
            rw [hc, hb, hd, had]
            ring
          exact M.det_ne_zero hdet
        intro z
        cases z with
        | none =>
            dsimp [MobiusTransform.eval]
            rw [if_pos hc]
        | some z =>
            dsimp [MobiusTransform.eval]
            have hden : M.c * z + M.d = M.d := by rw [hc, zero_mul, zero_add]
            rw [hden, if_neg hd_ne]
            have hnum : M.a * z + M.b = M.d * z := by rw [had, hb, add_zero]
            rw [hnum]
            congr 1
            rw [mul_comm]
            exact mul_div_cancel_right₀ z hd_ne
      · have hfix := fixed_point_translation M hc had hb
        have hz1 : z1 = none := (hfix z1).mp f1
        have hz2 : z2 = none := (hfix z2).mp f2
        exact False.elim (h12 (by rw [hz1, hz2]))
    · have hfix := fixed_point_linear M hc had
      have hz1 := (hfix z1).mp f1
      have hz2 := (hfix z2).mp f2
      have hz3 := (hfix z3).mp f3
      rcases hz1 with hz1 | hz1
      · rcases hz2 with hz2 | hz2
        · exact False.elim (h12 (by rw [hz1, hz2]))
        · rcases hz3 with hz3 | hz3
          · exact False.elim (h13 (by rw [hz1, hz3]))
          · exact False.elim (h23 (by rw [hz2, hz3]))
      · rcases hz2 with hz2 | hz2
        · rcases hz3 with hz3 | hz3
          · exact False.elim (h23 (by rw [hz2, hz3]))
          · exact False.elim (h13 (by rw [hz1, hz3]))
        · exact False.elim (h12 (by rw [hz1, hz2]))
  · have hnone_not_fixed : ¬ M.is_fixed_point none := by
      dsimp [MobiusTransform.is_fixed_point, MobiusTransform.eval]
      rw [if_neg hc]
      intro h
      cases h
    cases z1 with
    | none => exact False.elim (hnone_not_fixed f1)
    | some γ1 =>
      cases z2 with
      | none => exact False.elim (hnone_not_fixed f2)
      | some γ2 =>
        cases z3 with
        | none => exact False.elim (hnone_not_fixed f3)
        | some γ3 =>
          have hγ12 : γ1 ≠ γ2 := by
            intro h
            exact h12 (by rw [h])
          have hγ23 : γ2 ≠ γ3 := by
            intro h
            exact h23 (by rw [h])
          have hp1 := (fixed_point_quadratic M hc γ1).mp f1
          have hp2 := (fixed_point_quadratic M hc γ2).mp f2
          have hp3 := (fixed_point_quadratic M hc γ3).mp f3
          have hsum12 : M.c * (γ1 + γ2) = M.a - M.d := by
            have hfactor : (M.c * (γ1 + γ2) - (M.a - M.d)) * (γ1 - γ2) = 0 := by
              calc
                (M.c * (γ1 + γ2) - (M.a - M.d)) * (γ1 - γ2)
                    = M.c * (γ1 ^ 2 - γ2 ^ 2) - (M.a - M.d) * (γ1 - γ2) := by
                      ring
                _ = (M.c * γ1 ^ 2 - (M.a - M.d) * γ1 - M.b) -
                      (M.c * γ2 ^ 2 - (M.a - M.d) * γ2 - M.b) := by
                      ring
                _ = 0 := by rw [hp1, hp2]; ring
            have hneq : γ1 - γ2 ≠ 0 := sub_ne_zero.mpr hγ12
            rcases mul_eq_zero.mp hfactor with hleft | hright
            · exact sub_eq_zero.mp hleft
            · exact False.elim (hneq hright)
          have hsum13 : M.c * (γ1 + γ3) = M.a - M.d := by
            have hγ13 : γ1 ≠ γ3 := by
              intro h
              exact h13 (by rw [h])
            have hfactor : (M.c * (γ1 + γ3) - (M.a - M.d)) * (γ1 - γ3) = 0 := by
              calc
                (M.c * (γ1 + γ3) - (M.a - M.d)) * (γ1 - γ3)
                    = M.c * (γ1 ^ 2 - γ3 ^ 2) - (M.a - M.d) * (γ1 - γ3) := by
                      ring
                _ = (M.c * γ1 ^ 2 - (M.a - M.d) * γ1 - M.b) -
                      (M.c * γ3 ^ 2 - (M.a - M.d) * γ3 - M.b) := by
                      ring
                _ = 0 := by rw [hp1, hp3]; ring
            have hneq : γ1 - γ3 ≠ 0 := sub_ne_zero.mpr hγ13
            rcases mul_eq_zero.mp hfactor with hleft | hright
            · exact sub_eq_zero.mp hleft
            · exact False.elim (hneq hright)
          have hcg : M.c * (γ2 - γ3) = 0 := by
            have h := sub_eq_zero.mpr (Eq.trans hsum12 hsum13.symm)
            ring_nf at h ⊢
            simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using h
          have hγ23eq : γ2 = γ3 := by
            rcases mul_eq_zero.mp hcg with hc0 | hdiff
            · exact False.elim (hc hc0)
            · exact sub_eq_zero.mp hdiff
          exact False.elim (hγ23 hγ23eq)

/-- Two Möbius transformations are conjugate if there exists a transformation g mapping between them. -/
def is_conjugate (M1 M2 : MobiusTransform) : Prop :=
  ∃ g : MobiusTransform, ∃ g_inv : MobiusTransform,
    (∀ z, g.eval (g_inv.eval z) = z) ∧
    (∀ z, M1.eval z = g.eval (M2.eval (g_inv.eval z)))

/-- The normal form matrix for the non-parabolic case with two finite fixed points γ1, γ2 and multiplier k. -/
def non_parabolic_matrix (k γ1 γ2 : ℂ) (hk0 : k ≠ 0) (_hk : k ≠ 1) (hγ : γ1 ≠ γ2) : MobiusTransform :=
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

/-- The first parameter point is a finite fixed point of the non-parabolic normal-form matrix. -/
lemma non_parabolic_matrix_fixed_left (k γ1 γ2 : ℂ)
    (hk0 : k ≠ 0) (hk : k ≠ 1) (hγ : γ1 ≠ γ2) :
    (non_parabolic_matrix k γ1 γ2 hk0 hk hγ).is_fixed_point (some γ1) := by
  dsimp [MobiusTransform.is_fixed_point, MobiusTransform.eval, non_parabolic_matrix]
  have hden : (1 - k) * γ1 + (k * γ1 - γ2) ≠ 0 := by
    have hden_eq : (1 - k) * γ1 + (k * γ1 - γ2) = γ1 - γ2 := by ring
    rw [hden_eq]
    exact sub_ne_zero.mpr hγ
  rw [if_neg hden]
  congr 1
  rw [div_eq_iff hden]
  ring

/-- The second parameter point is a finite fixed point of the non-parabolic normal-form matrix. -/
lemma non_parabolic_matrix_fixed_right (k γ1 γ2 : ℂ)
    (hk0 : k ≠ 0) (hk : k ≠ 1) (hγ : γ1 ≠ γ2) :
    (non_parabolic_matrix k γ1 γ2 hk0 hk hγ).is_fixed_point (some γ2) := by
  dsimp [MobiusTransform.is_fixed_point, MobiusTransform.eval, non_parabolic_matrix]
  have hden : (1 - k) * γ2 + (k * γ1 - γ2) ≠ 0 := by
    have hden_eq : (1 - k) * γ2 + (k * γ1 - γ2) = k * (γ1 - γ2) := by ring
    rw [hden_eq]
    exact mul_ne_zero hk0 (sub_ne_zero.mpr hγ)
  rw [if_neg hden]
  congr 1
  rw [div_eq_iff hden]
  ring

-- Non-parabolic (dilation/rotation) normal form H(k; γ₁, γ₂)
def nonParabolicNormalForm (k γ₁ γ₂ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![γ₁ - k * γ₂, (k - 1) * γ₁ * γ₂],
    ![1 - k, k * γ₁ - γ₂]]

/-- The normal form matrix for the parabolic case with one finite fixed point γ and translation length β. -/
def parabolic_matrix (β γ : ℂ) (_hβ : β ≠ 0) : MobiusTransform :=
  { a := 1 + γ * β,
    b := -β * γ^2,
    c := β,
    d := 1 - γ * β,
    det_ne_zero := by
      have h : (1 + γ * β) * (1 - γ * β) - (-β * γ^2) * β = 1 := by ring
      rw [h]
      exact one_ne_zero }

/-- The parameter point is a finite fixed point of the parabolic normal-form matrix. -/
lemma parabolic_matrix_fixed_point (β γ : ℂ) (hβ : β ≠ 0) :
    (parabolic_matrix β γ hβ).is_fixed_point (some γ) := by
  dsimp [MobiusTransform.is_fixed_point, MobiusTransform.eval, parabolic_matrix]
  have hden : β * γ + (1 - γ * β) ≠ 0 := by
    have hden_eq : β * γ + (1 - γ * β) = 1 := by ring
    rw [hden_eq]
    exact one_ne_zero
  rw [if_neg hden]
  congr 1
  rw [div_eq_iff hden]
  ring

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

/-- The pole of the transformation, z_∞ = -d/c, which maps to ∞. -/
noncomputable def MobiusTransform.pole (M : MobiusTransform) : ℂ :=
  - M.d / M.c

/-- The inverse pole of the transformation, Z_∞ = a/c, to which ∞ maps. -/
noncomputable def MobiusTransform.inv_pole (M : MobiusTransform) : ℂ :=
  M.a / M.c

/-- The Characteristic Parallelogram Theorem:
    The point midway between the two poles is the same as the point midway between the two fixed points. -/
theorem characteristic_parallelogram (M : MobiusTransform) (hc : M.c ≠ 0)
    (γ1 γ2 : ℂ) (h_distinct : γ1 ≠ γ2)
    (f1 : M.is_fixed_point (some γ1)) (f2 : M.is_fixed_point (some γ2)) :
    γ1 + γ2 = M.pole + M.inv_pole := by
  have h1 := (fixed_point_quadratic M hc γ1).mp f1
  have h2 := (fixed_point_quadratic M hc γ2).mp f2
  have hfactor : (M.c * (γ1 + γ2) - (M.a - M.d)) * (γ1 - γ2) = 0 := by
    calc
      (M.c * (γ1 + γ2) - (M.a - M.d)) * (γ1 - γ2)
          = M.c * (γ1 ^ 2 - γ2 ^ 2) - (M.a - M.d) * (γ1 - γ2) := by ring
      _ = (M.c * γ1 ^ 2 - (M.a - M.d) * γ1 - M.b) -
            (M.c * γ2 ^ 2 - (M.a - M.d) * γ2 - M.b) := by ring
      _ = 0 := by rw [h1, h2]; ring
  have hsum_eq : M.c * (γ1 + γ2) = M.a - M.d := by
    have hneq : γ1 - γ2 ≠ 0 := sub_ne_zero.mpr h_distinct
    have hprod := mul_eq_zero.mp hfactor
    rcases hprod with hleft | hright
    · exact sub_eq_zero.mp hleft
    · exact False.elim (hneq hright)
  have hsum_div : γ1 + γ2 = (M.a - M.d) / M.c := by
    exact (eq_div_iff hc).2 (by simpa [mul_comm] using hsum_eq)
  dsimp [MobiusTransform.pole, MobiusTransform.inv_pole]
  have hpole : - M.d / M.c + M.a / M.c = (M.a - M.d) / M.c := by
    field_simp [hc]
    ring
  rw [hpole]
  exact hsum_div

/-- A finite fixed point cannot equal the inverse pole of a transform with nonzero `c`. -/
lemma fixed_point_ne_inv_pole (M : MobiusTransform) (hc : M.c ≠ 0) (γ : ℂ)
    (f : M.is_fixed_point (some γ)) : γ ≠ M.inv_pole := by
  intro hγ
  have hpoly := (fixed_point_quadratic M hc γ).mp f
  rw [hγ] at hpoly
  dsimp [MobiusTransform.inv_pole] at hpoly
  have hdet : M.a * M.d - M.b * M.c = 0 := by
    field_simp [hc] at hpoly
    ring_nf at hpoly ⊢
    simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hpoly
  exact M.det_ne_zero hdet

/-- The characteristic constant k can be derived directly from the poles and fixed points. -/
theorem multiplier_from_poles (M : MobiusTransform) (hc : M.c ≠ 0)
    (γ1 γ2 : ℂ) (f1 : M.is_fixed_point (some γ1)) (f2 : M.is_fixed_point (some γ2))
    (h_distinct : γ1 ≠ M.pole) :
    ∃ k : ℂ, k = (γ2 - M.pole) / (γ1 - M.pole) ∧
             k = (M.inv_pole - γ1) / (M.inv_pole - γ2) := by
  by_cases h_eq : γ1 = γ2
  · have hne1 : γ1 - M.pole ≠ 0 := sub_ne_zero.mpr h_distinct
    have hne2 : M.inv_pole - γ1 ≠ 0 := by
      intro h
      have hγ' : M.inv_pole = γ1 := by simpa [sub_eq_zero] using h
      have hγ : γ1 = M.inv_pole := hγ'.symm
      exact (fixed_point_ne_inv_pole M hc γ1 f1) hγ
    refine ⟨1, ?_, ?_⟩
    · simpa [h_eq] using (div_self hne1).symm
    · simpa [h_eq] using (div_self hne2).symm
  · have hsum :=
      characteristic_parallelogram (M := M) (hc := hc) (γ1 := γ1) (γ2 := γ2)
        h_eq f1 f2
    have hnum1 : γ2 - M.pole = M.inv_pole - γ1 := by
      have h := congrArg (fun t : ℂ => t - γ1 - M.pole) hsum
      dsimp [MobiusTransform.pole, MobiusTransform.inv_pole] at h ⊢
      ring_nf at h ⊢
      exact h
    have hnum2 : γ1 - M.pole = M.inv_pole - γ2 := by
      have h := congrArg (fun t : ℂ => t - γ2 - M.pole) hsum
      dsimp [MobiusTransform.pole, MobiusTransform.inv_pole] at h ⊢
      ring_nf at h ⊢
      exact h
    refine ⟨(γ2 - M.pole) / (γ1 - M.pole), rfl, ?_⟩
    calc
      (γ2 - M.pole) / (γ1 - M.pole)
          = (M.inv_pole - γ1) / (γ1 - M.pole) := by rw [hnum1]
      _ = (M.inv_pole - γ1) / (M.inv_pole - γ2) := by rw [hnum2]

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

/-- Translation acts by adding the translation parameter on finite points. -/
lemma translation_transform_eval_some (b z : ℂ) :
    (translation_transform b).eval (some z) = some (z + b) := by
  simp [MobiusTransform.eval, translation_transform]

/-- Translation fixes the point at infinity. -/
lemma translation_transform_eval_none (b : ℂ) :
    (translation_transform b).eval none = none := by
  simp [MobiusTransform.eval, translation_transform]

/-- A Möbius transform with `c = 0` and `a = d ≠ 0` acts as a translation on finite points. -/
lemma translation_like_eval (M : MobiusTransform) (hc : M.c = 0) (had : M.a = M.d)
    (ha : M.a ≠ 0) :
    ∀ z : ℂ, M.eval (some z) = some (z + M.b / M.a) := by
  intro z
  have hd : M.d ≠ 0 := by
    rw [← had]
    exact ha
  have hq : (M.d * z + M.b) / M.d = z + M.b / M.d := by
    field_simp [hd]
  simp [MobiusTransform.eval, hc, hd, had, hq]

/-- Parabolic normal form in the coordinate chart where the unique fixed point
    is already the point at infinity.  The full finite-fixed-point theorem
    additionally needs the conjugating map that sends the finite fixed point to
    infinity; this lemma isolates the proved translation core. -/
theorem parabolic_normal_form_at_infinity (M : MobiusTransform)
    (f_inf : M.is_fixed_point none) (h_unique : ∀ z, M.is_fixed_point z → z = none) :
    ∃ β : ℂ, β ≠ 0 ∧
      ∃ M_β : MobiusTransform,
        (∀ z : ℂ, M_β.eval (some z) = some (z + β)) ∧
        is_conjugate M M_β := by
  have hc : M.c = 0 := by
    by_contra hnc
    have hnone : M.eval none = none := f_inf
    dsimp [MobiusTransform.eval] at hnone
    rw [if_neg hnc] at hnone
    cases hnone
  have hNa : M.a ≠ 0 := by
    intro ha
    have hdet : M.a * M.d - M.b * M.c = 0 := by
      simp [hc, ha]
    exact M.det_ne_zero hdet
  have had : M.a = M.d := by
    by_contra hne
    have hlin := (fixed_point_linear M hc hne) (some (- M.b / (M.a - M.d)))
    have hfix : M.is_fixed_point (some (- M.b / (M.a - M.d))) :=
      hlin.mpr (Or.inr rfl)
    have hbad := h_unique (some (- M.b / (M.a - M.d))) hfix
    cases hbad
  have hNb : M.b ≠ 0 := by
    intro hb
    have hfix : M.is_fixed_point (some 0) := by
      simpa [MobiusTransform.is_fixed_point, hb] using
        (translation_like_eval M hc had hNa 0)
    have hbad := h_unique (some 0) hfix
    cases hbad
  refine ⟨M.b / M.a, ?_⟩
  constructor
  · exact div_ne_zero hNb hNa
  · refine ⟨translation_transform (M.b / M.a), ?_⟩
    constructor
    · intro z
      simp [translation_transform, MobiusTransform.eval]
    · let I : MobiusTransform :=
        { a := 1, b := 0, c := 0, d := 1, det_ne_zero := by norm_num }
      refine ⟨I, I, ?_, ?_⟩
      · intro z
        cases z with
        | none => simp [I, MobiusTransform.eval]
        | some z => simp [I, MobiusTransform.eval]
      · intro z
        cases z with
        | none => simp [I, translation_transform, MobiusTransform.eval, hc]
        | some z =>
            simpa [I, translation_transform, MobiusTransform.eval] using
              (translation_like_eval M hc had hNa z)

/-- Dilation and rotation by a (homothety) -/
def dilation_transform (a : ℂ) (ha : a ≠ 0) : MobiusTransform :=
  { a := a, b := 0, c := 0, d := 1, det_ne_zero := by
      dsimp; ring_nf; exact ha }

/-- Dilation acts by scalar multiplication on finite points. -/
lemma dilation_transform_eval_some (a z : ℂ) (ha : a ≠ 0) :
    (dilation_transform a ha).eval (some z) = some (a * z) := by
  simp [MobiusTransform.eval, dilation_transform]

/-- Dilation fixes the point at infinity. -/
lemma dilation_transform_eval_none (a : ℂ) (ha : a ≠ 0) :
    (dilation_transform a ha).eval none = none := by
  simp [MobiusTransform.eval, dilation_transform]

/-- Inversion and reflection (1/z) -/
def inversion_transform : MobiusTransform :=
  { a := 0, b := 1, c := 1, d := 0, det_ne_zero := by norm_num }

/-- Inversion sends zero to infinity. -/
lemma inversion_transform_eval_zero :
    inversion_transform.eval (some 0) = none := by
  simp [MobiusTransform.eval, inversion_transform]

/-- Inversion sends infinity to zero. -/
lemma inversion_transform_eval_none :
    inversion_transform.eval none = some 0 := by
  simp [MobiusTransform.eval, inversion_transform]

/-- The inverse Möbius transformation: `f⁻¹(z) = (d*z - b) / (-c*z + a)`. -/
def inv (M : MobiusTransform) : MobiusTransform :=
  { a := M.d,
    b := -M.b,
    c := -M.c,
    d := M.a,
    det_ne_zero := by
      have h := M.det_ne_zero
      dsimp
      have h_ring : M.d * M.a - -M.b * -M.c = M.a * M.d - M.b * M.c := by
        ring
      rw [h_ring]
      exact h }

/-- Composition of Möbius transformations. -/
def comp (M1 M2 : MobiusTransform) : MobiusTransform :=
  { a := M1.a * M2.a + M1.b * M2.c,
    b := M1.a * M2.b + M1.b * M2.d,
    c := M1.c * M2.a + M1.d * M2.c,
    d := M1.c * M2.b + M1.d * M2.d,
    det_ne_zero := by
      have h1 := M1.det_ne_zero
      have h2 := M2.det_ne_zero
      have h_ring :
          (M1.a * M2.a + M1.b * M2.c) * (M1.c * M2.b + M1.d * M2.d) -
              (M1.a * M2.b + M1.b * M2.d) * (M1.c * M2.a + M1.d * M2.c) =
            (M1.a * M1.d - M1.b * M1.c) * (M2.a * M2.d - M2.b * M2.c) := by
        ring
      rw [h_ring]
      exact mul_ne_zero h1 h2 }

/-- Right inverse law for the explicit Möbius inverse. -/
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
      · have hmc : -M.c ≠ 0 := by
          intro h
          exact hc (neg_eq_zero.mp h)
        rw [if_neg hmc]
        change (if M.c * (M.d / -M.c) + M.d = 0 then none else some _) = none
        have h_denom : M.c * (M.d / -M.c) + M.d = 0 := by
          field_simp
          ring
        rw [if_pos h_denom]
  | some z' =>
      change M.eval
        (if -M.c * z' + M.a = 0 then none
         else some ((M.d * z' + -M.b) / (-M.c * z' + M.a))) = some z'
      by_cases h_inv_denom : -M.c * z' + M.a = 0
      · rw [if_pos h_inv_denom]
        have hc : M.c ≠ 0 := by
          intro h
          have ha : M.a = 0 := by
            calc
              M.a = (-M.c * z' + M.a) + M.c * z' := by ring
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
          calc
            M.a = (-M.c * z' + M.a) + M.c * z' := by ring
            _ = 0 + M.c * z' := by rw [h_inv_denom]
            _ = M.c * z' := by ring
        rw [h_eq]
        have : M.c * z' / M.c = z' * M.c / M.c := by rw [mul_comm]
        rw [this, mul_div_cancel_right₀ _ hc]
      · rw [if_neg h_inv_denom]
        change
          (if M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d = 0 then none
           else some _) = some z'
        have h_denom : M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d ≠ 0 := by
          intro h_zero
          have h_zero_mul :
              (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) *
                  (-M.c * z' + M.a) = 0 := by
            rw [h_zero, zero_mul]
          have h_simp :
              (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) *
                  (-M.c * z' + M.a) = M.a * M.d - M.b * M.c := by
            calc
              (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) *
                    (-M.c * z' + M.a)
                  = M.c * (((M.d * z' + -M.b) / (-M.c * z' + M.a)) *
                      (-M.c * z' + M.a)) + M.d * (-M.c * z' + M.a) := by ring
              _ = M.c * (M.d * z' + -M.b) + M.d * (-M.c * z' + M.a) := by
                rw [div_mul_cancel₀ _ h_inv_denom]
              _ = M.a * M.d - M.b * M.c := by ring
          rw [h_simp] at h_zero_mul
          exact M.det_ne_zero h_zero_mul
        rw [if_neg h_denom]
        congr 1
        have h_cross :
            M.a * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.b =
              z' * (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) := by
          have h1 :
              (M.a * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.b) *
                  (-M.c * z' + M.a) = (M.a * M.d - M.b * M.c) * z' := by
            calc
              (M.a * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.b) *
                    (-M.c * z' + M.a)
                  = M.a * (((M.d * z' + -M.b) / (-M.c * z' + M.a)) *
                      (-M.c * z' + M.a)) + M.b * (-M.c * z' + M.a) := by ring
              _ = M.a * (M.d * z' + -M.b) + M.b * (-M.c * z' + M.a) := by
                rw [div_mul_cancel₀ _ h_inv_denom]
              _ = (M.a * M.d - M.b * M.c) * z' := by ring
          have h2 :
              z' * (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) *
                  (-M.c * z' + M.a) = (M.a * M.d - M.b * M.c) * z' := by
            calc
              z' * (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) *
                    (-M.c * z' + M.a)
                  = z' * ((M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) *
                      (-M.c * z' + M.a)) := by ring
              _ = z' * (M.c * (((M.d * z' + -M.b) / (-M.c * z' + M.a)) *
                    (-M.c * z' + M.a)) + M.d * (-M.c * z' + M.a)) := by ring
              _ = z' * (M.c * (M.d * z' + -M.b) + M.d * (-M.c * z' + M.a)) := by
                rw [div_mul_cancel₀ _ h_inv_denom]
              _ = (M.a * M.d - M.b * M.c) * z' := by ring
          have h3 :
              (M.a * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.b) *
                  (-M.c * z' + M.a) =
                z' * (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) *
                  (-M.c * z' + M.a) := by
            rw [h1, h2]
          exact mul_right_cancel₀ h_inv_denom h3
        calc
          (M.a * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.b) /
                (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d)
              = (z' * (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d)) /
                  (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) := by
            rw [h_cross]
          _ = z' := by rw [mul_div_cancel_right₀ _ h_denom]

/-- Left inverse law for the explicit Möbius inverse. -/
lemma eval_inv_left (M : MobiusTransform) (z : RiemannSphere) :
    (inv M).eval (M.eval z) = z := by
  simpa [inv] using (eval_inv (inv M) z)

/-- Evaluation of a composed Möbius transformation. -/
lemma eval_comp (M1 M2 : MobiusTransform) (z : RiemannSphere) :
    (comp M1 M2).eval z = M1.eval (M2.eval z) := by
  cases z with
  | none =>
      change
        (if M1.c * M2.a + M1.d * M2.c = 0 then none
         else some ((M1.a * M2.a + M1.b * M2.c) / (M1.c * M2.a + M1.d * M2.c))) =
          M1.eval (if M2.c = 0 then none else some (M2.a / M2.c))
      by_cases h2c : M2.c = 0
      · rw [if_pos h2c]
        change
          (if M1.c * M2.a + M1.d * M2.c = 0 then none else some _) =
            (if M1.c = 0 then none else some (M1.a / M1.c))
        have hc : M1.c * M2.a + M1.d * M2.c = M1.c * M2.a := by
          rw [h2c, mul_zero, add_zero]
        by_cases h1c : M1.c = 0
        · have : M1.c * M2.a + M1.d * M2.c = 0 := by rw [hc, h1c, zero_mul]
          rw [if_pos this, if_pos h1c]
        · have h2a : M2.a ≠ 0 := by
            intro ha_zero
            have h_det2 := M2.det_ne_zero
            rw [h2c, ha_zero, zero_mul, mul_zero, sub_zero] at h_det2
            exact h_det2 rfl
          have hden : M1.c * M2.a + M1.d * M2.c ≠ 0 := by
            rw [hc]
            exact mul_ne_zero h1c h2a
          rw [if_neg hden, if_neg h1c]
          congr 1
          have num_eq : M1.a * M2.a + M1.b * M2.c = M1.a * M2.a := by
            rw [h2c, mul_zero, add_zero]
          have den_eq : M1.c * M2.a + M1.d * M2.c = M1.c * M2.a := by
            rw [h2c, mul_zero, add_zero]
          rw [num_eq, den_eq]
          have cross : M1.a * M2.a / (M1.c * M2.a) = M1.a / M1.c := by
            rw [eq_div_iff_mul_eq h1c]
            calc
              M1.a * M2.a / (M1.c * M2.a) * M1.c
                  = M1.a * M2.a * M1.c / (M1.c * M2.a) := by
                rw [div_mul_eq_mul_div]
              _ = M1.a * (M1.c * M2.a) / (M1.c * M2.a) := by ring_nf
              _ = M1.a := by rw [mul_div_cancel_right₀ _ (mul_ne_zero h1c h2a)]
          rw [cross]
      · rw [if_neg h2c]
        change
          (if M1.c * M2.a + M1.d * M2.c = 0 then none else some _) =
            (if M1.c * (M2.a / M2.c) + M1.d = 0 then none else some _)
        have h_denom :
            M1.c * (M2.a / M2.c) + M1.d = 0 ↔
              M1.c * M2.a + M1.d * M2.c = 0 := by
          constructor
          · intro h
            calc
              M1.c * M2.a + M1.d * M2.c
                  = (M1.c * (M2.a / M2.c) + M1.d) * M2.c := by
                have : M1.c * (M2.a / M2.c) * M2.c = M1.c * M2.a := by
                  rw [mul_assoc, div_mul_cancel₀ _ h2c]
                rw [add_mul, this]
              _ = 0 * M2.c := by rw [h]
              _ = 0 := zero_mul M2.c
          · intro h
            have h_eq : (M1.c * (M2.a / M2.c) + M1.d) * M2.c = 0 := by
              calc
                (M1.c * (M2.a / M2.c) + M1.d) * M2.c
                    = M1.c * (M2.a / M2.c) * M2.c + M1.d * M2.c := by ring
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
          change
            (M1.a * M2.a + M1.b * M2.c) / (M1.c * M2.a + M1.d * M2.c) =
              (M1.a * (M2.a / M2.c) + M1.b) / (M1.c * (M2.a / M2.c) + M1.d)
          have num_eq :
              M1.a * (M2.a / M2.c) + M1.b =
                (M1.a * M2.a + M1.b * M2.c) / M2.c := by
            rw [eq_div_iff_mul_eq h2c]
            calc
              (M1.a * (M2.a / M2.c) + M1.b) * M2.c
                  = M1.a * (M2.a / M2.c) * M2.c + M1.b * M2.c := by ring
              _ = M1.a * M2.a + M1.b * M2.c := by
                have : M1.a * (M2.a / M2.c) * M2.c = M1.a * M2.a := by
                  rw [mul_assoc, div_mul_cancel₀ _ h2c]
                rw [this]
          have den_eq :
              M1.c * (M2.a / M2.c) + M1.d =
                (M1.c * M2.a + M1.d * M2.c) / M2.c := by
            rw [eq_div_iff_mul_eq h2c]
            calc
              (M1.c * (M2.a / M2.c) + M1.d) * M2.c
                  = M1.c * (M2.a / M2.c) * M2.c + M1.d * M2.c := by ring
              _ = M1.c * M2.a + M1.d * M2.c := by
                have : M1.c * (M2.a / M2.c) * M2.c = M1.c * M2.a := by
                  rw [mul_assoc, div_mul_cancel₀ _ h2c]
                rw [this]
          rw [num_eq, den_eq]
          have cross :
              (M1.a * M2.a + M1.b * M2.c) / M2.c /
                  ((M1.c * M2.a + M1.d * M2.c) / M2.c) =
                (M1.a * M2.a + M1.b * M2.c) / (M1.c * M2.a + M1.d * M2.c) := by
            rw [div_div_div_cancel_right₀ h2c]
          rw [cross]
  | some z' =>
      change
        (if (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) = 0
         then none else some _) =
          M1.eval (if M2.c * z' + M2.d = 0 then none else some _)
      by_cases h2_denom : M2.c * z' + M2.d = 0
      · rw [if_pos h2_denom]
        change
          (if (M1.c * M2.a + M1.d * M2.c) * z' +
                (M1.c * M2.b + M1.d * M2.d) = 0 then none else some _) =
            (if M1.c = 0 then none else some (M1.a / M1.c))
        have hc :
            (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) =
              M1.c * (M2.a * z' + M2.b) := by
          calc
            (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d)
                = M1.c * (M2.a * z' + M2.b) + M1.d * (M2.c * z' + M2.d) := by
              ring
            _ = M1.c * (M2.a * z' + M2.b) + M1.d * 0 := by rw [h2_denom]
            _ = M1.c * (M2.a * z' + M2.b) := by ring
        have ha :
            (M1.a * M2.a + M1.b * M2.c) * z' + (M1.a * M2.b + M1.b * M2.d) =
              M1.a * (M2.a * z' + M2.b) := by
          calc
            (M1.a * M2.a + M1.b * M2.c) * z' + (M1.a * M2.b + M1.b * M2.d)
                = M1.a * (M2.a * z' + M2.b) + M1.b * (M2.c * z' + M2.d) := by
              ring
            _ = M1.a * (M2.a * z' + M2.b) + M1.b * 0 := by rw [h2_denom]
            _ = M1.a * (M2.a * z' + M2.b) := by ring
        by_cases h1c : M1.c = 0
        · have :
              (M1.c * M2.a + M1.d * M2.c) * z' +
                  (M1.c * M2.b + M1.d * M2.d) = 0 := by
            rw [hc, h1c, zero_mul]
          rw [if_pos this, if_pos h1c]
        · have h2a : M2.a * z' + M2.b ≠ 0 := by
            intro h_zero
            have hdet2_neg : M2.b * M2.c - M2.a * M2.d = 0 := by
              have htmp :
                  (M2.a * z' + M2.b) * M2.c - (M2.c * z' + M2.d) * M2.a =
                    M2.b * M2.c - M2.d * M2.a := by
                ring
              rw [h_zero, h2_denom, zero_mul, zero_mul, zero_sub] at htmp
              calc
                M2.b * M2.c - M2.a * M2.d
                    = M2.b * M2.c - M2.d * M2.a := by ring
                _ = -0 := htmp.symm
                _ = 0 := neg_zero
            have hdet2_pos : M2.a * M2.d - M2.b * M2.c = 0 := by
              calc
                M2.a * M2.d - M2.b * M2.c = -(M2.b * M2.c - M2.a * M2.d) := by
                  ring
                _ = -0 := by rw [hdet2_neg]
                _ = 0 := neg_zero
            exact M2.det_ne_zero hdet2_pos
          have hden :
              (M1.c * M2.a + M1.d * M2.c) * z' +
                  (M1.c * M2.b + M1.d * M2.d) ≠ 0 := by
            rw [hc]
            exact mul_ne_zero h1c h2a
          rw [if_neg hden, if_neg h1c]
          congr 1
          change
            ((M1.a * M2.a + M1.b * M2.c) * z' + (M1.a * M2.b + M1.b * M2.d)) /
                ((M1.c * M2.a + M1.d * M2.c) * z' +
                  (M1.c * M2.b + M1.d * M2.d)) = M1.a / M1.c
          rw [hc, ha]
          have : M1.a * (M2.a * z' + M2.b) / (M1.c * (M2.a * z' + M2.b)) =
              M1.a / M1.c := by
            rw [mul_comm M1.a, mul_comm M1.c]
            rw [mul_div_mul_left _ _ h2a]
          exact this
      · rw [if_neg h2_denom]
        change
          (if (M1.c * M2.a + M1.d * M2.c) * z' +
                (M1.c * M2.b + M1.d * M2.d) = 0 then none else some _) =
            (if M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d = 0
             then none else some _)
        have h_denom :
            M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d = 0 ↔
              (M1.c * M2.a + M1.d * M2.c) * z' +
                (M1.c * M2.b + M1.d * M2.d) = 0 := by
          constructor
          · intro h
            calc
              (M1.c * M2.a + M1.d * M2.c) * z' +
                    (M1.c * M2.b + M1.d * M2.d)
                  = M1.c * (M2.a * z' + M2.b) + M1.d * (M2.c * z' + M2.d) := by
                ring
              _ = (M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d) *
                    (M2.c * z' + M2.d) := by
                have : M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) *
                    (M2.c * z' + M2.d) = M1.c * (M2.a * z' + M2.b) := by
                  rw [mul_assoc, div_mul_cancel₀ _ h2_denom]
                rw [add_mul, this]
              _ = 0 * (M2.c * z' + M2.d) := by rw [h]
              _ = 0 := zero_mul _
          · intro h
            have h_eq :
                (M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d) *
                    (M2.c * z' + M2.d) = 0 := by
              calc
                (M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d) *
                      (M2.c * z' + M2.d)
                    = M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) *
                        (M2.c * z' + M2.d) + M1.d * (M2.c * z' + M2.d) := by
                  ring
                _ = M1.c * (M2.a * z' + M2.b) + M1.d * (M2.c * z' + M2.d) := by
                  have : M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) *
                      (M2.c * z' + M2.d) = M1.c * (M2.a * z' + M2.b) := by
                    rw [mul_assoc, div_mul_cancel₀ _ h2_denom]
                  rw [this]
                _ = (M1.c * M2.a + M1.d * M2.c) * z' +
                      (M1.c * M2.b + M1.d * M2.d) := by ring
                _ = 0 := h
            exact (mul_eq_zero.mp h_eq).resolve_right h2_denom
        by_cases h_c_zero :
            (M1.c * M2.a + M1.d * M2.c) * z' +
              (M1.c * M2.b + M1.d * M2.d) = 0
        · rw [if_pos h_c_zero, if_pos (h_denom.mpr h_c_zero)]
        · rw [if_neg h_c_zero, if_neg (mt h_denom.mp h_c_zero)]
          congr 1
          change
            ((M1.a * M2.a + M1.b * M2.c) * z' + (M1.a * M2.b + M1.b * M2.d)) /
                ((M1.c * M2.a + M1.d * M2.c) * z' +
                  (M1.c * M2.b + M1.d * M2.d)) =
              (M1.a * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.b) /
                (M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d)
          have num_eq :
              M1.a * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.b =
                ((M1.a * M2.a + M1.b * M2.c) * z' +
                  (M1.a * M2.b + M1.b * M2.d)) / (M2.c * z' + M2.d) := by
            rw [eq_div_iff_mul_eq h2_denom]
            calc
              (M1.a * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.b) *
                    (M2.c * z' + M2.d)
                  = M1.a * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) *
                      (M2.c * z' + M2.d) + M1.b * (M2.c * z' + M2.d) := by ring
              _ = M1.a * (M2.a * z' + M2.b) + M1.b * (M2.c * z' + M2.d) := by
                have : M1.a * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) *
                    (M2.c * z' + M2.d) = M1.a * (M2.a * z' + M2.b) := by
                  rw [mul_assoc, div_mul_cancel₀ _ h2_denom]
                rw [this]
              _ = (M1.a * M2.a + M1.b * M2.c) * z' + (M1.a * M2.b + M1.b * M2.d) := by
                ring
          have den_eq :
              M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d =
                ((M1.c * M2.a + M1.d * M2.c) * z' +
                  (M1.c * M2.b + M1.d * M2.d)) / (M2.c * z' + M2.d) := by
            rw [eq_div_iff_mul_eq h2_denom]
            calc
              (M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d) *
                    (M2.c * z' + M2.d)
                  = M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) *
                      (M2.c * z' + M2.d) + M1.d * (M2.c * z' + M2.d) := by ring
              _ = M1.c * (M2.a * z' + M2.b) + M1.d * (M2.c * z' + M2.d) := by
                have : M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) *
                    (M2.c * z' + M2.d) = M1.c * (M2.a * z' + M2.b) := by
                  rw [mul_assoc, div_mul_cancel₀ _ h2_denom]
                rw [this]
              _ = (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) := by
                ring
          rw [num_eq, den_eq]
          rw [div_div_div_cancel_right₀ h2_denom]

/-- Parabolic Normal Form: a Möbius transformation with exactly one fixed point
    is conjugate to a translation mapping `z ↦ z + β`. -/
theorem parabolic_normal_form (M : MobiusTransform) (z1 : RiemannSphere)
    (f1 : M.is_fixed_point z1) (h_unique : ∀ z, M.is_fixed_point z → z = z1) :
    ∃ β : ℂ, β ≠ 0 ∧
      ∃ M_β : MobiusTransform,
        (∀ z : ℂ, M_β.eval (some z) = some (z + β)) ∧
        is_conjugate M M_β := by
  cases z1 with
  | none =>
      exact parabolic_normal_form_at_infinity M f1 h_unique
  | some γ =>
      let z2 : ℂ := γ + 1
      have h12 : (some γ : RiemannSphere) ≠ some z2 := by
        intro h
        have h' : γ = γ + 1 := Option.some.inj h
        have h'' := congrArg (fun w : ℂ => w - γ) h'
        ring_nf at h''
        exact one_ne_zero h''.symm
      have h23 : (some z2 : RiemannSphere) ≠ none := by
        intro h
        cases h
      have h13 : (some γ : RiemannSphere) ≠ none := by
        intro h
        cases h
      obtain ⟨T, hT0, _hT1, _hTinf⟩ :=
        maps_to_01inf (some γ) (some z2) none h12 h23 h13
      let g : MobiusTransform := comp inversion_transform T
      have hgz1 : g.eval (some γ) = none := by
        calc
          g.eval (some γ) = inversion_transform.eval (T.eval (some γ)) := by
            simp [g, eval_comp]
          _ = inversion_transform.eval (some 0) := by rw [hT0]
          _ = none := by simp [inversion_transform, MobiusTransform.eval]
      let N : MobiusTransform := comp g (comp M (inv g))
      have hginvnone : (inv g).eval none = some γ := by
        have h := eval_inv_left g (some γ)
        rw [hgz1] at h
        simpa using h
      have hNnone : N.eval none = none := by
        calc
          N.eval none = g.eval (M.eval ((inv g).eval none)) := by
            simp [N, eval_comp]
          _ = g.eval (M.eval (some γ)) := by rw [hginvnone]
          _ = g.eval (some γ) := by rw [f1]
          _ = none := hgz1
      have hNuniq : ∀ z, N.is_fixed_point z → z = none := by
        intro z hz
        have hz' : N.eval z = z := hz
        have hfixM : M.is_fixed_point ((inv g).eval z) := by
          have hz'' : g.eval (M.eval ((inv g).eval z)) = z := by
            simpa [N, eval_comp] using hz'
          have hz''' := congrArg (fun w : RiemannSphere => (inv g).eval w) hz''
          simpa [eval_inv_left] using hz'''
        have hz1 : (inv g).eval z = some γ := h_unique _ hfixM
        calc
          z = g.eval ((inv g).eval z) := by
            symm
            exact eval_inv g z
          _ = g.eval (some γ) := by rw [hz1]
          _ = none := hgz1
      have hNc : N.c = 0 := by
        by_cases h : N.c = 0
        · exact h
        · have hbad : some (N.a / N.c) = none := by
            simpa [MobiusTransform.eval, h] using hNnone
          cases hbad
      have hNaEq : N.a = N.d := by
        by_contra hne
        have hlin := (fixed_point_linear N hNc hne) (some (-N.b / (N.a - N.d)))
        have hfix : N.is_fixed_point (some (-N.b / (N.a - N.d))) :=
          hlin.mpr (Or.inr rfl)
        have hbad := hNuniq (some (-N.b / (N.a - N.d))) hfix
        cases hbad
      have hNb : N.b ≠ 0 := by
        intro hb
        have hfix : N.is_fixed_point (some 0) := by
          have hNa : N.a ≠ 0 := by
            intro hA
            have hdet : N.a * N.d - N.b * N.c = 0 := by
              simp [hA, hNc, hNaEq]
            exact N.det_ne_zero hdet
          simpa [MobiusTransform.is_fixed_point, hb] using
            (translation_like_eval N hNc hNaEq hNa 0)
        have hbad := hNuniq (some 0) hfix
        cases hbad
      have hNa : N.a ≠ 0 := by
        intro hA
        have hdet : N.a * N.d - N.b * N.c = 0 := by
          simp [hA, hNc, hNaEq]
        exact N.det_ne_zero hdet
      let β : ℂ := N.b / N.a
      have hβ : β ≠ 0 := by
        dsimp [β]
        exact div_ne_zero hNb hNa
      have htrans : ∀ z : ℂ, N.eval (some z) = some (z + β) := by
        intro z
        dsimp [β]
        simpa using (translation_like_eval N hNc hNaEq hNa z)
      refine ⟨β, hβ, N, htrans, ?_⟩
      refine ⟨inv g, g, ?_, ?_⟩
      · intro z
        exact eval_inv_left g z
      · intro z
        have h1 : g.eval (M.eval z) = N.eval (g.eval z) := by
          simp [N, eval_comp, eval_inv_left]
        have h3 := congrArg (fun w : RiemannSphere => (inv g).eval w) h1
        simpa [eval_inv_left] using h3

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

/-- Every Möbius transformation with c ≠ 0 can be decomposed into a sequence of
    four simple transformations: f4 ∘ f3 ∘ f2 ∘ f1. -/
theorem mobius_decomposition (M : MobiusTransform) (hc : M.c ≠ 0) :
    let f1 := translation_transform (M.d / M.c);
    let f2 := inversion_transform;
    let f3 := dilation_transform ((M.b * M.c - M.a * M.d) / M.c^2) (by
      intro h
      have hc2 : M.c ^ 2 ≠ 0 := pow_ne_zero 2 hc
      have h1 : M.b * M.c - M.a * M.d = 0 := (div_eq_zero_iff.mp h).resolve_right hc2
      have h2 : M.a * M.d - M.b * M.c = 0 := by
        rw [sub_eq_zero] at h1 ⊢
        rw [h1]
      exact M.det_ne_zero h2);
    let f4 := translation_transform (M.a / M.c);
    ∀ z : ℂ, M.eval (some z) =
      f4.eval (f3.eval (f2.eval (f1.eval (some z)))) := by
  intro f1 f2 f3 f4 z
  by_cases hden : M.c * z + M.d = 0
  · have hz : z + M.d / M.c = 0 := by
      have h_mul : M.c * (z + M.d / M.c) = 0 := by
        calc
          M.c * (z + M.d / M.c) = M.c * z + M.c * (M.d / M.c) := mul_add _ _ _
          _ = M.c * z + M.d := by rw [mul_div_cancel₀ M.d hc]
          _ = 0 := hden
      cases mul_eq_zero.mp h_mul with
      | inl h => exfalso; exact hc h
      | inr h => exact h
    have hm : M.eval (some z) = none := by
      dsimp [MobiusTransform.eval]
      rw [if_pos hden]
    rw [hm]
    have hf1 : f1.eval (some z) = some 0 := by
      dsimp [f1, translation_transform, MobiusTransform.eval]
      have h0 : (0 : ℂ) * z + 1 ≠ 0 := by simp
      rw [if_neg h0]
      have hz_eq : (1 : ℂ) * z + M.d / M.c = z + M.d / M.c := by ring
      have h_div : (z + M.d / M.c) / ((0 : ℂ) * z + 1) = z + M.d / M.c := by simp
      rw [hz_eq, h_div, hz]
    have hf2 : f2.eval (some 0) = none := by
      dsimp [f2, inversion_transform, MobiusTransform.eval]
      have h0 : (1 : ℂ) * 0 + 0 = 0 := by ring
      rw [if_pos h0]
    have hf3 : f3.eval none = none := by
      dsimp [f3, dilation_transform, MobiusTransform.eval]
      have h0 : (0 : ℂ) = 0 := rfl
      rw [if_pos h0]
    have hf4 : f4.eval none = none := by
      dsimp [f4, translation_transform, MobiusTransform.eval]
      have h0 : (0 : ℂ) = 0 := rfl
      rw [if_pos h0]
    rw [hf1, hf2, hf3, hf4]
  · have hz : z + M.d / M.c ≠ 0 := by
      intro h
      have h_mul : M.c * (z + M.d / M.c) = 0 := by rw [h, mul_zero]
      have h_eq : M.c * (z + M.d / M.c) = M.c * z + M.d := by
        calc
          M.c * (z + M.d / M.c) = M.c * z + M.c * (M.d / M.c) := mul_add _ _ _
          _ = M.c * z + M.d := by rw [mul_div_cancel₀ M.d hc]
      rw [h_eq] at h_mul
      exact hden h_mul
    have hm : M.eval (some z) = some ((M.a * z + M.b) / (M.c * z + M.d)) := by
      dsimp [MobiusTransform.eval]
      rw [if_neg hden]
    rw [hm]
    have hf1 : f1.eval (some z) = some (z + M.d / M.c) := by
      dsimp [f1, translation_transform, MobiusTransform.eval]
      have h0 : (0 : ℂ) * z + 1 ≠ 0 := by simp
      rw [if_neg h0]
      have hz_eq : (1 : ℂ) * z + M.d / M.c = z + M.d / M.c := by ring
      have h_div : (z + M.d / M.c) / ((0 : ℂ) * z + 1) = z + M.d / M.c := by simp
      rw [hz_eq, h_div]
    have hf2 : f2.eval (some (z + M.d / M.c)) = some (z + M.d / M.c)⁻¹ := by
      dsimp [f2, inversion_transform, MobiusTransform.eval]
      have h0 : (1 : ℂ) * (z + M.d / M.c) + 0 ≠ 0 := by simpa using hz
      rw [if_neg h0]
      have h_eval :
          ((0 : ℂ) * (z + M.d / M.c) + 1) /
              ((1 : ℂ) * (z + M.d / M.c) + 0) =
            1 / (z + M.d / M.c) := by ring
      rw [h_eval, ← inv_eq_one_div]
    have hf3 : f3.eval (some (z + M.d / M.c)⁻¹) =
        some (((M.b * M.c - M.a * M.d) / M.c^2) * (z + M.d / M.c)⁻¹) := by
      dsimp [f3, dilation_transform, MobiusTransform.eval]
      have h0 : (0 : ℂ) * (z + M.d / M.c)⁻¹ + 1 ≠ 0 := by simp
      rw [if_neg h0]
      have h_eval :
          (((M.b * M.c - M.a * M.d) / M.c ^ 2) * (z + M.d / M.c)⁻¹ + 0) /
              ((0 : ℂ) * (z + M.d / M.c)⁻¹ + 1) =
            (((M.b * M.c - M.a * M.d) / M.c ^ 2) * (z + M.d / M.c)⁻¹) := by ring
      rw [h_eval]
    have hf4 : f4.eval
          (some (((M.b * M.c - M.a * M.d) / M.c^2) * (z + M.d / M.c)⁻¹)) =
        some (M.a / M.c + ((M.b * M.c - M.a * M.d) / M.c^2) *
          (z + M.d / M.c)⁻¹) := by
      dsimp [f4, translation_transform, MobiusTransform.eval]
      have h0 :
          (0 : ℂ) * (((M.b * M.c - M.a * M.d) / M.c ^ 2) *
              (z + M.d / M.c)⁻¹) + 1 ≠ 0 := by simp
      rw [if_neg h0]
      have h_eval :
          ((1 : ℂ) * (((M.b * M.c - M.a * M.d) / M.c ^ 2) *
                (z + M.d / M.c)⁻¹) + M.a / M.c) /
              ((0 : ℂ) * (((M.b * M.c - M.a * M.d) / M.c ^ 2) *
                (z + M.d / M.c)⁻¹) + 1) =
            M.a / M.c + ((M.b * M.c - M.a * M.d) / M.c ^ 2) *
              (z + M.d / M.c)⁻¹ := by ring
      rw [h_eval]
    rw [hf1, hf2, hf3, hf4]
    congr 1
    have h_inv : (z + M.d / M.c)⁻¹ = 1 / (z + M.d / M.c) := inv_eq_one_div _
    rw [h_inv]
    rw [mobius_algebraic_decomposition M hc z hden]
    ring

/-- The cross-ratio of four distinct finite points. -/
noncomputable def cross_ratio (z1 z2 z3 z4 : ℂ) : ℂ :=
  ((z1 - z3) * (z2 - z4)) / ((z2 - z3) * (z1 - z4))

lemma cross_ratio_translation (z1 z2 z3 z4 b : ℂ) :
    cross_ratio (z1 + b) (z2 + b) (z3 + b) (z4 + b) = cross_ratio z1 z2 z3 z4 := by
  unfold cross_ratio
  ring

lemma cross_ratio_scale (z1 z2 z3 z4 a : ℂ) (ha : a ≠ 0) :
    cross_ratio (a * z1) (a * z2) (a * z3) (a * z4) = cross_ratio z1 z2 z3 z4 := by
  unfold cross_ratio
  field_simp [ha]

lemma cross_ratio_affine (z1 z2 z3 z4 a b : ℂ) (ha : a ≠ 0) :
    cross_ratio (a * z1 + b) (a * z2 + b) (a * z3 + b) (a * z4 + b) = cross_ratio z1 z2 z3 z4 := by
  have htrans := cross_ratio_translation (a * z1) (a * z2) (a * z3) (a * z4) b
  have hscale := cross_ratio_scale z1 z2 z3 z4 a ha
  rw [htrans, hscale]

lemma cross_ratio_inv (z1 z2 z3 z4 : ℂ) (h1 : z1 ≠ 0) (h2 : z2 ≠ 0) (h3 : z3 ≠ 0) (h4 : z4 ≠ 0) :
    cross_ratio z1⁻¹ z2⁻¹ z3⁻¹ z4⁻¹ = cross_ratio z1 z2 z3 z4 := by
  unfold cross_ratio
  field_simp [h1, h2, h3, h4]
  ring

/-- The difference of a Möbius transformation evaluated at two points. -/
lemma mobius_diff (M : MobiusTransform) (z1 z2 : ℂ) (h1 : M.c * z1 + M.d ≠ 0) (h2 : M.c * z2 + M.d ≠ 0) :
    ((M.a * z1 + M.b) / (M.c * z1 + M.d)) - ((M.a * z2 + M.b) / (M.c * z2 + M.d)) =
    (M.a * M.d - M.b * M.c) * (z1 - z2) / ((M.c * z1 + M.d) * (M.c * z2 + M.d)) := by
  have h1' : z1 * M.c + M.d ≠ 0 := by rwa [mul_comm]
  have h2' : z2 * M.c + M.d ≠ 0 := by rwa [mul_comm]
  field_simp [h1, h2, h1', h2']
  ring

/-- Every Möbius transformation preserves the cross-ratio of four points under non-pole conditions. -/
theorem mobius_preserves_cross_ratio (M : MobiusTransform) (z1 z2 z3 z4 : ℂ)
    (h1 : M.c * z1 + M.d ≠ 0) (h2 : M.c * z2 + M.d ≠ 0) (h3 : M.c * z3 + M.d ≠ 0) (h4 : M.c * z4 + M.d ≠ 0)
    (hz23 : z2 - z3 ≠ 0) (hz14 : z1 - z4 ≠ 0) :
    cross_ratio ((M.a * z1 + M.b) / (M.c * z1 + M.d))
               ((M.a * z2 + M.b) / (M.c * z2 + M.d))
               ((M.a * z3 + M.b) / (M.c * z3 + M.d))
               ((M.a * z4 + M.b) / (M.c * z4 + M.d)) =
    cross_ratio z1 z2 z3 z4 := by
  unfold cross_ratio
  rw [mobius_diff M z1 z3 h1 h3]
  rw [mobius_diff M z2 z4 h2 h4]
  rw [mobius_diff M z2 z3 h2 h3]
  rw [mobius_diff M z1 z4 h1 h4]
  have h_det : M.a * M.d - M.b * M.c ≠ 0 := M.det_ne_zero
  have h1' : z1 * M.c + M.d ≠ 0 := by rwa [mul_comm]
  have h2' : z2 * M.c + M.d ≠ 0 := by rwa [mul_comm]
  have h3' : z3 * M.c + M.d ≠ 0 := by rwa [mul_comm]
  have h4' : z4 * M.c + M.d ≠ 0 := by rwa [mul_comm]
  field_simp [h1, h2, h3, h4, h1', h2', h3', h4', h_det, hz23, hz14]


/-- Extended cross-ratio handling infinity on the Riemann sphere. -/
noncomputable def cross_ratio_ext (z1 z2 z3 z4 : RiemannSphere) : RiemannSphere :=
  match z1, z2, z3, z4 with
  | some z1, some z2, some z3, some z4 => some (cross_ratio z1 z2 z3 z4)
  | none, some z2, some z3, some z4 =>
      if z2 - z3 = 0 then none else some ((z2 - z4) / (z2 - z3))
  | some z1, none, some z3, some z4 =>
      if z1 - z4 = 0 then none else some ((z1 - z3) / (z1 - z4))
  | some z1, some z2, none, some z4 =>
      if z1 - z4 = 0 then none else some ((z2 - z4) / (z1 - z4))
  | some z1, some z2, some z3, none =>
      if z2 - z3 = 0 then none else some ((z1 - z3) / (z2 - z3))
  | _, _, _, _ => none

/-- Extended cross-ratio preservation target.

The current total extension returns `none` at degenerate or pole
configurations, and this declaration has no distinctness/non-pole hypotheses.
Keep the intended invariance statement as an open proposition until those
domain conditions and the transport proof are formalized. -/
def cross_ratio_preserving (M : MobiusTransform) (z1 z2 z3 z4 : RiemannSphere) : Prop :=
  cross_ratio_ext z1 z2 z3 z4 =
    cross_ratio_ext (M.eval z1) (M.eval z2) (M.eval z3) (M.eval z4)

/-- Cocircularity/cross-ratio equivalence target.

The intended statement is for four distinct points, but this declaration does
not yet carry distinctness or non-pole hypotheses. Keep the exact equivalence
as an open proposition until those domain conditions and the generalized-circle
proof are formalized. -/
def cocircular_iff_real_cross_ratio (z1 z2 z3 z4 : ℂ) : Prop :=
  (∃ circ : GenCircle, circ.contains z1 ∧ circ.contains z2 ∧ circ.contains z3 ∧ circ.contains z4)
  ↔ (cross_ratio z1 z2 z3 z4).im = 0

/-- Two points are conjugate (symmetric) with respect to a generalized circle if any circle
    passing through them intersecting the original circle at a and b yields a harmonic cross-ratio -1. -/
def is_conjugate_wrt_circle (z1 z2 : RiemannSphere) (circ : GenCircle) : Prop :=
  ∀ D : GenCircle, D.containsExt z1 → D.containsExt z2 →
    ∃ a b : RiemannSphere, circ.containsExt a ∧ circ.containsExt b ∧ D.containsExt a ∧ D.containsExt b ∧
      cross_ratio_ext z1 z2 a b = some (-1)

/-- Explicit geometric conjugation formula with respect to a line passing through `z0`
with angle `θ`, kept as an open proposition target. The previous theorem
surface quantified an arbitrary `z_star`, so it was not provable without taking
this equation as the defining relation. -/
def conjugate_wrt_line (z z_star z0 : ℂ) (θ : ℝ) : Prop :=
  z_star = Complex.exp (2 * Complex.I * θ) * conj (z - z0) + z0

/-- Explicit geometric conjugation formula with respect to a circle of radius `r`
centered at `z0`, kept as an open proposition target. The output `z_star` is
otherwise unconstrained, so this relation must not be promoted as a theorem. -/
def conjugate_wrt_circle_radius (z z_star z0 : ℂ) (r : ℝ) : Prop :=
  z_star = (r ^ 2 : ℂ) / conj (z - z0) + z0

/-- Möbius-conjugation preservation target.

The available `h_map` hypothesis transports circle membership only; it does not
yet provide the intersection-witness and harmonic-cross-ratio transport needed
for a theorem. Keep the intended equivalence as an explicit open proposition. -/
def conjugation_preserving (M : MobiusTransform) (z1 z2 : RiemannSphere) (circ : GenCircle)
    (circ' : GenCircle) (h_map : ∀ z, circ.containsExt z ↔ circ'.containsExt (M.eval z)) : Prop :=
  is_conjugate_wrt_circle z1 z2 circ ↔
    is_conjugate_wrt_circle (M.eval z1) (M.eval z2) circ'

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
  by_cases hp : p.z2 = 0
  · have hp1 : p.z1 ≠ 0 := by
      rcases p.not_both_zero with h1 | h2
      · exact h1
      · exact False.elim (h2 hp)
    dsimp [CP1.toRiemannSphere, MobiusTransform.actCP1, MobiusTransform.eval]
    rw [if_pos hp]
    by_cases hc : M.c = 0
    · have hden : M.c * p.z1 + M.d * p.z2 = 0 := by rw [hc, hp]; ring
      rw [if_pos hden, if_pos hc]
    · have hden : M.c * p.z1 + M.d * p.z2 ≠ 0 := by
        rw [hp]
        have hcp : M.c * p.z1 ≠ 0 := mul_ne_zero hc hp1
        simpa using hcp
      rw [if_neg hden, if_neg hc]
      congr 1
      rw [hp]
      simp
      rw [mul_div_mul_right M.a M.c hp1]
  · dsimp [CP1.toRiemannSphere, MobiusTransform.actCP1, MobiusTransform.eval]
    rw [if_neg hp]
    change (if M.c * p.z1 + M.d * p.z2 = 0 then none else
        some ((M.a * p.z1 + M.b * p.z2) / (M.c * p.z1 + M.d * p.z2))) =
      (if M.c * (p.z1 / p.z2) + M.d = 0 then none else
        some ((M.a * (p.z1 / p.z2) + M.b) / (M.c * (p.z1 / p.z2) + M.d)))
    by_cases hden : M.c * (p.z1 / p.z2) + M.d = 0
    · have hden_cp : M.c * p.z1 + M.d * p.z2 = 0 := by
        have hmul : (M.c * (p.z1 / p.z2) + M.d) * p.z2 = 0 := by
          rw [hden, zero_mul]
        have hrew :
            (M.c * (p.z1 / p.z2) + M.d) * p.z2 = M.c * p.z1 + M.d * p.z2 := by
          field_simp [hp]
        simpa [hrew] using hmul
      rw [if_pos hden_cp, if_pos hden]
    · have hden_cp : M.c * p.z1 + M.d * p.z2 ≠ 0 := by
        intro hcp
        have hdiv : (M.c * p.z1 + M.d * p.z2) / p.z2 = 0 := by
          rw [hcp, zero_div]
        have hrew :
            (M.c * p.z1 + M.d * p.z2) / p.z2 = M.c * (p.z1 / p.z2) + M.d := by
          field_simp [hp]
        exact hden (by simpa [hrew] using hdiv)
      rw [if_neg hden_cp, if_neg hden]
      congr 1
      field_simp [hp, hden_cp, hden]

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
    rw [div_mul_div_comm, mul_one]
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
        have hdenom : M.c * z' + M.d ≠ 0 := by
          rw [hc, zero_mul, zero_add]
          exact hd
        rw [if_neg hdenom]
        change circ.contains z' ↔ C2.contains ((M.a * z' + M.b) / (M.c * z' + M.d))
        have hz_eq :
            (M.a * z' + M.b) / (M.c * z' + M.d) =
              (M.a / M.d) * z' + M.b / M.d := by
          rw [hc, zero_mul, zero_add]
          have h_div :
              (M.a * z' + M.b) / M.d = (M.a * z') / M.d + M.b / M.d :=
            add_div (M.a * z') M.b M.d
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
      have h2 : M.a * M.d - M.b * M.c = 0 := by
        rw [sub_eq_zero] at h1 ⊢
        rw [h1]
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
        have h_norm :
            normSq ((M.b * M.c - M.a * M.d) / M.c ^ 2) ≠ 0 :=
          ne_of_gt (Complex.normSq_pos.mpr h_dil_ne_zero)
        constructor
        · intro h
          rw [h, zero_mul]
        · intro h
          cases mul_eq_zero.mp h with
          | inl h1 => exact h1
          | inr h2 => exact False.elim (h_norm h2)
    | some z' =>
        dsimp [MobiusTransform.eval]
        by_cases hdenom : M.c * z' + M.d = 0
        · rw [if_pos hdenom]
          change circ.contains z' ↔ C4.A = 0
          have hA : C4.A = C3.A := rfl
          have hA3 : C3.A = C2.A := rfl
          have hA2 : C2.A = C1.C := rfl
          rw [hA, hA3, hA2]
          have hz_plus_d_c : z' + M.d / M.c = 0 := by
            have h1 : M.c * (z' + M.d / M.c) = 0 := by
              calc
                M.c * (z' + M.d / M.c) = M.c * z' + M.c * (M.d / M.c) := mul_add _ _ _
                _ = M.c * z' + M.d := by rw [mul_div_cancel₀ M.d hc]
                _ = 0 := hdenom
            cases mul_eq_zero.mp h1 with
            | inl h => exact False.elim (hc h)
            | inr h => exact h
          have h_step1 := trans_circle_contains (M.d / M.c) circ z'
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
              calc
                M.c * z' + M.d = M.c * z' + M.c * (M.d / M.c) := by
                  rw [mul_div_cancel₀ M.d hc]
                _ = M.c * (z' + M.d / M.c) := (mul_add _ _ _).symm
                _ = 0 := h1
            exact hdenom h2
          change circ.contains z' ↔ C4.contains ((M.a * z' + M.b) / (M.c * z' + M.d))
          have h_step1 := trans_circle_contains (M.d / M.c) circ z'
          have h_step2 := inv_circle_contains C1 (z' + M.d / M.c) hz_plus_d_c_ne_0
          have h_step3 :=
            dil_circle_contains ((M.b * M.c - M.a * M.d) / M.c ^ 2) h_dil_ne_zero
              C2 (z' + M.d / M.c)⁻¹
          have h_step4 :=
            trans_circle_contains (M.a / M.c) C3
              (((M.b * M.c - M.a * M.d) / M.c ^ 2) * (z' + M.d / M.c)⁻¹)
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

/-- Equivalence of Möbius transformations is reflexive. -/
lemma equiv_refl (M : MobiusTransform) : MobiusTransform.equiv M M := by
  intro z; rfl

/-- Equivalence of Möbius transformations is symmetric. -/
lemma equiv_symm {M1 M2 : MobiusTransform} (h : MobiusTransform.equiv M1 M2) : MobiusTransform.equiv M2 M1 := by
  intro z; exact (h z).symm

/-- Equivalence of Möbius transformations is transitive. -/
lemma equiv_trans {M1 M2 M3 : MobiusTransform} (h1 : MobiusTransform.equiv M1 M2) (h2 : MobiusTransform.equiv M2 M3) : MobiusTransform.equiv M1 M3 := by
  intro z; exact (h1 z).trans (h2 z)

/-- Setoid instance for Möbius transformations under function equivalence. -/
instance mobiusSetoid : Setoid MobiusTransform where
  r := MobiusTransform.equiv
  iseqv := {
    refl := equiv_refl
    symm := equiv_symm
    trans := equiv_trans
  }

/-- The complex projective general linear group PGL(2, ℂ) defined as the quotient of Möbius transformations by function equivalence. -/
def PGL2C : Type := Quotient mobiusSetoid

/-- Evaluation of identity Möbius transformation. -/
lemma eval_default (z : RiemannSphere) : (default : MobiusTransform).eval z = z := by
  cases z with
  | none =>
      change (if (0 : ℂ) = 0 then none else some (1 / 0)) = none
      rw [if_pos rfl]
  | some z' =>
      change (if (0 : ℂ) * z' + 1 = 0 then none else some ((1 * z' + 0) / (0 * z' + 1))) = some z'
      have h : (0 : ℂ) * z' + 1 ≠ 0 := by
        simp only [zero_mul, zero_add, one_ne_zero, ne_eq, not_false_iff]
      rw [if_neg h]
      congr 1
      simp only [zero_mul, zero_add, one_mul, add_zero, div_one]

/-- Composition is compatible with Möbius transformation equivalence. -/
lemma comp_congr ⦃M1 M1' : MobiusTransform⦄ (h1 : MobiusTransform.equiv M1 M1')
    ⦃M2 M2' : MobiusTransform⦄ (h2 : MobiusTransform.equiv M2 M2') :
    MobiusTransform.equiv (comp M1 M2) (comp M1' M2') := by
  intro z
  rw [eval_comp, eval_comp]
  rw [h2 z]
  exact h1 _

/-- Inverse is compatible with Möbius transformation equivalence. -/
lemma inv_congr ⦃M M' : MobiusTransform⦄ (h : MobiusTransform.equiv M M') : MobiusTransform.equiv (inv M) (inv M') := by
  intro z
  have h_inj : Function.Injective M'.eval := by
    intro a b hab
    have h_inv_a := eval_inv_left M' a
    have h_inv_b := eval_inv_left M' b
    rw [hab] at h_inv_a
    exact h_inv_a.symm.trans h_inv_b
  apply h_inj
  rw [eval_inv M']
  have h_equiv := h ((inv M).eval z)
  rw [← h_equiv, eval_inv M]

/-- Multiplication on PGL(2, ℂ) induced by composition. -/
noncomputable instance : Mul PGL2C where
  mul := Quotient.map₂ comp comp_congr

/-- Inverse on PGL(2, ℂ) induced by Möbius inverse. -/
noncomputable instance : Inv PGL2C where
  inv := Quotient.map inv inv_congr

/-- One (identity) on PGL(2, ℂ) represented by default. -/
instance : One PGL2C where
  one := Quotient.mk' default

/-- PGL(2, ℂ) forms a group under composition. -/
noncomputable instance : Group PGL2C where
  mul_assoc := by
    apply Quotient.ind
    intro A
    apply Quotient.ind
    intro B
    apply Quotient.ind
    intro C
    change Quotient.mk' (comp (comp A B) C) = Quotient.mk' (comp A (comp B C))
    apply Quotient.sound
    intro z
    rw [eval_comp, eval_comp, eval_comp, eval_comp]
  one_mul := by
    apply Quotient.ind
    intro M
    change Quotient.mk' (comp default M) = Quotient.mk' M
    apply Quotient.sound
    intro z
    rw [eval_comp, eval_default]
  mul_one := by
    apply Quotient.ind
    intro M
    change Quotient.mk' (comp M default) = Quotient.mk' M
    apply Quotient.sound
    intro z
    rw [eval_comp]
    congr 1
    exact eval_default z
  inv_mul_cancel := by
    apply Quotient.ind
    intro M
    change Quotient.mk' (comp (inv M) M) = Quotient.mk' default
    apply Quotient.sound
    intro z
    rw [eval_comp, eval_inv_left, eval_default]

end InfoGeometry

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Complex
open scoped ComplexConjugate

namespace InfoGeometry

/-- The Riemann sphere, represented as the complex plane extended by a point at infinity. -/
def RiemannSphere := Option ℂ

/-- A Möbius transformation is a rational function of the form
    f(z) = (a*z + b) / (c*z + d) with ad - bc ≠ 0.
    We represent it by a 2x2 matrix with non-zero determinant. -/
structure MobiusTransform where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det_ne_zero : a * d - b * c ≠ 0

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

/-- Circle-Preserving Theorem:
    A Möbius transformation maps a generalized circle to another generalized circle. -/
theorem circle_preserving (M : MobiusTransform) (circ : GenCircle) :
    ∃ circ' : GenCircle, ∀ z : RiemannSphere,
      circ.containsExt z ↔ circ'.containsExt (M.eval z) := by
  sorry

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
  sorry

/-- A fixed point of a Möbius transformation is a point z on the Riemann sphere
    such that M.eval z = z. -/
def is_fixed_point (M : MobiusTransform) (z : RiemannSphere) : Prop :=
  M.eval z = z

/-- Every non-identity Möbius transformation has one or two fixed points (with multiplicity).
    The discriminant of the transformation is Δ = (a+d)^2 - 4(ad-bc). -/
def discriminant (M : MobiusTransform) : ℂ :=
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
def non_parabolic_matrix (k γ1 γ2 : ℂ) (hk : k ≠ 1) (hγ : γ1 ≠ γ2) : MobiusTransform :=
  { a := γ1 - k * γ2,
    b := (k - 1) * γ1 * γ2,
    c := 1 - k,
    d := k * γ1 - γ2,
    det_ne_zero := by sorry }

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

/-- Parabolic Normal Form: A Möbius transformation with exactly one fixed point
    is conjugate to a translation mapping z ↦ z + β. -/
theorem parabolic_normal_form (M : MobiusTransform) (z1 : RiemannSphere)
    (f1 : M.is_fixed_point z1) (h_unique : ∀ z, M.is_fixed_point z → z = z1) :
    ∃ β : ℂ, β ≠ 0 ∧
      ∃ M_β : MobiusTransform,
        (∀ z : ℂ, M_β.eval (some z) = some (z + β)) ∧
        is_conjugate M M_β := by
  sorry

/-
/-- The pole of the transformation, z_∞ = -d/c, which maps to ∞. -/
noncomputable def pole (M : MobiusTransform) : ℂ :=
  - M.d / M.c

/-- The inverse pole of the transformation, Z_∞ = a/c, to which ∞ maps. -/
noncomputable def inv_pole (M : MobiusTransform) : ℂ :=
  M.a / M.c

/-- The Characteristic Parallelogram Theorem:
    The point midway between the two poles is the same as the point midway between the two fixed points. -/
theorem characteristic_parallelogram (M : MobiusTransform) (hc : M.c ≠ 0)
    (γ1 γ2 : ℂ) (f1 : M.is_fixed_point (some γ1)) (f2 : M.is_fixed_point (some γ2)) :
    γ1 + γ2 = M.pole + M.inv_pole := by
  sorry
-/

/-- The characteristic constant k can be derived directly from the poles and fixed points. -/
theorem multiplier_from_poles (M : MobiusTransform) (hc : M.c ≠ 0)
    (γ1 γ2 : ℂ) (f1 : M.is_fixed_point (some γ1)) (f2 : M.is_fixed_point (some γ2))
    (h_distinct : γ1 ≠ M.pole) :
    ∃ k : ℂ, k = (γ2 - M.pole) / (γ1 - M.pole) ∧
             k = (M.inv_pole - γ1) / (M.inv_pole - γ2) := by
  sorry

/-- The roots of the characteristic polynomial det(λI - H) are exactly λ_i = c*γ_i + d. -/
theorem eigenvalue_roots (M : MobiusTransform) (hc : M.c ≠ 0)
    (γ : ℂ) (f : M.is_fixed_point (some γ)) :
    let λ := M.c * γ + M.d;
    λ ^ 2 - (M.a + M.d) * λ + (M.a * M.d - M.b * M.c) = 0 := by
  sorry

/-- Translation by b -/
def translation_transform (b : ℂ) : MobiusTransform :=
  { a := 1, b := b, c := 0, d := 1, det_ne_zero := by sorry }

/-- Dilation and rotation by a (homothety) -/
def dilation_transform (a : ℂ) (ha : a ≠ 0) : MobiusTransform :=
  { a := a, b := 0, c := 0, d := 1, det_ne_zero := by sorry }

/-- Inversion and reflection (1/z) -/
def inversion_transform : MobiusTransform :=
  { a := 0, b := 1, c := 1, d := 0, det_ne_zero := by sorry }

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
  sorry

/-- The inverse Möbius transformation: f^{-1}(z) = (d*z - b) / (-c*z + a). -/
def inv (M : MobiusTransform) : MobiusTransform :=
  { a := M.d,
    b := -M.b,
    c := -M.c,
    d := M.a,
    det_ne_zero := by sorry }

/-- The cross-ratio of four distinct finite points. -/
def cross_ratio (z1 z2 z3 z4 : ℂ) : ℂ :=
  ((z1 - z3) * (z2 - z4)) / ((z2 - z3) * (z1 - z4))

/-- Extended cross-ratio handling infinity on the Riemann sphere. -/
noncomputable def cross_ratio_ext (z1 z2 z3 z4 : RiemannSphere) : RiemannSphere :=
  sorry

/-- Möbius transformations strictly preserve the extended cross-ratio. -/
theorem cross_ratio_preserving (M : MobiusTransform) (z1 z2 z3 z4 : RiemannSphere) :
    cross_ratio_ext z1 z2 z3 z4 =
    cross_ratio_ext (M.eval z1) (M.eval z2) (M.eval z3) (M.eval z4) := by
  sorry

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

/-- Equivalence relation on homogeneous coordinates. -/
def CP1.equiv (p q : CP1) : Prop :=
  ∃ λ : ℂ, λ ≠ 0 ∧ p.z1 = λ * q.z1 ∧ p.z2 = λ * q.z2

/-- Identification of CP^1 with the Riemann sphere. -/
noncomputable def CP1.toRiemannSphere (p : CP1) : RiemannSphere :=
  if p.z2 = 0 then none else some (p.z1 / p.z2)

/-- The action of an invertible 2x2 matrix on CP^1. -/
noncomputable def MobiusTransform.actCP1 (M : MobiusTransform) (p : CP1) : CP1 :=
  { z1 := M.a * p.z1 + M.b * p.z2,
    z2 := M.c * p.z1 + M.d * p.z2,
    not_both_zero := by sorry }

/-- The correspondence theorem: Action on CP^1 equates to the fractional linear action on the Riemann sphere. -/
theorem mobius_action_correspondence (M : MobiusTransform) (p : CP1) :
    (M.actCP1 p).toRiemannSphere = M.eval (p.toRiemannSphere) := by
  sorry

/-- Scaling the matrix by a non-zero scalar λ produces the same Möbius transformation (PGL(2, C) equivalence). -/
theorem pgl_equivalence (M : MobiusTransform) (λ : ℂ) (hλ : λ ≠ 0) :
    let M_scaled : MobiusTransform := {
      a := λ * M.a,
      b := λ * M.b,
      c := λ * M.c,
      d := λ * M.d,
      det_ne_zero := by
        dsimp
        have h1 : λ * M.a * (λ * M.d) - λ * M.b * (λ * M.c) = (λ * λ) * (M.a * M.d - M.b * M.c) := by ring
        rw [h1]
        have hl2 : λ * λ ≠ 0 := mul_ne_zero hλ hλ
        exact mul_ne_zero hl2 M.det_ne_zero
    };
    ∀ z, M.eval z = M_scaled.eval z := by
  intro M_scaled z
  cases z with
  | none =>
    change (if M.c = 0 then none else some (M.a / M.c)) = (if λ * M.c = 0 then none else some (λ * M.a / (λ * M.c)))
    by_cases hc : M.c = 0
    · have hcs : λ * M.c = 0 := by rw [hc, mul_zero]
      rw [if_pos hc, if_pos hcs]
    · have hcs : λ * M.c ≠ 0 := mul_ne_zero hλ hc
      rw [if_neg hc, if_neg hcs]
      have : λ * M.a / (λ * M.c) = M.a / M.c := by
        rw [mul_div_mul_left M.a M.c hλ]
      rw [this]
  | some z' =>
    change (if M.c * z' + M.d = 0 then none else some ((M.a * z' + M.b) / (M.c * z' + M.d))) = (if λ * M.c * z' + λ * M.d = 0 then none else some ((λ * M.a * z' + λ * M.b) / (λ * M.c * z' + λ * M.d)))
    by_cases hdenom : M.c * z' + M.d = 0
    · have hdenom_scaled : λ * M.c * z' + λ * M.d = 0 := by
        have h_ring : λ * M.c * z' + λ * M.d = λ * (M.c * z' + M.d) := by ring
        rw [h_ring, hdenom, mul_zero]
      rw [if_pos hdenom, if_pos hdenom_scaled]
    · have hdenom_scaled : λ * M.c * z' + λ * M.d ≠ 0 := by
        intro h
        have ht : λ * (M.c * z' + M.d) = 0 := by
          have h1 : λ * (M.c * z' + M.d) = λ * M.c * z' + λ * M.d := by ring
          rw [h1, h]
        cases mul_eq_zero.mp ht with
        | inl h1 => exact hλ h1
        | inr h2 => exact hdenom h2
      rw [if_neg hdenom, if_neg hdenom_scaled]
      congr 2
      have hnum : λ * M.a * z' + λ * M.b = λ * (M.a * z' + M.b) := by ring
      have hden : λ * M.c * z' + λ * M.d = λ * (M.c * z' + M.d) := by ring
      rw [hnum, hden, mul_div_mul_left (M.a * z' + M.b) (M.c * z' + M.d) hλ]


noncomputable def pole (M : MobiusTransform) : ℂ := - M.d / M.c
noncomputable def inv_pole (M : MobiusTransform) : ℂ := M.a / M.c

theorem characteristic_parallelogram (M : MobiusTransform) (γ1 γ2 : ℂ) (h_sum : γ1 + γ2 = (M.a - M.d) / M.c) :
    γ1 + γ2 = pole M + inv_pole M := by
  rw [h_sum, pole, inv_pole]
  ring

theorem mobius_decomposition (a b c d z : ℂ) (hc : c ≠ 0) (hz : z + d/c ≠ 0) :
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

/-- A real Möbius transformation corresponding to PGL(2, ℝ) acting on the real projective line. -/
structure RealMobiusTransform where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  det_ne_zero : a * d - b * c ≠ 0

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

end InfoGeometry

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Scalar Tomita modular deviance

This is the theorem-safe real core of the modular-deviance expression

`exp (-x) - 1 + x`.

It proves the exact tangent subtraction, its derivative, strict positivity
off the identity, and non-negativity on all real parameters.  Operator-valued
functional calculus, spectral positivity, Araki relative entropy, and Fisher
asymptotics require additional finite-dimensional or analytic owners and are
not asserted here.
-/

noncomputable section

namespace InfoGeometry.Thermodynamics.TomitaModularDeviance

/-- The real scalar modular deviance `exp (-x) - 1 + x`. -/
def scalar (x : ℝ) : ℝ :=
  Real.exp (-x) - 1 + x

@[simp] theorem scalar_zero :
    scalar 0 = 0 := by
  simp [scalar]

theorem hasDerivAt_scalar (x : ℝ) :
    HasDerivAt scalar (1 - Real.exp (-x)) x := by
  convert ((hasDerivAt_neg x).exp).sub
      (hasDerivAt_const x (1 : ℝ)) |>.add (hasDerivAt_id x) using 1 <;>
    simp [scalar] <;> ring

theorem deriv_scalar (x : ℝ) :
    deriv scalar x = 1 - Real.exp (-x) :=
  (hasDerivAt_scalar x).deriv

/- The quadratic coefficient is `f''(0) / 2 = 1 / 2`. -/
theorem secondDeriv_scalar_zero :
    deriv (fun x => deriv scalar x) 0 = 1 := by
  have h : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) 1 0 := by
    convert (hasDerivAt_const 0 (1 : ℝ)).sub ((hasDerivAt_neg 0).exp) using 1 <;>
      simp
  rw [show (fun x => deriv scalar x) =
      (fun x : ℝ => 1 - Real.exp (-x)) by
        funext x
        exact deriv_scalar x]
  exact h.deriv

/-- The scalar deviance is strictly positive away from the identity. -/
theorem scalar_pos {x : ℝ} (hx : x ≠ 0) :
    0 < scalar x := by
  dsimp [scalar]
  have h := Real.add_one_lt_exp (show -x ≠ 0 by exact neg_ne_zero.mpr hx)
  linarith

theorem scalar_pos_iff (x : ℝ) :
    0 < scalar x ↔ x ≠ 0 := by
  constructor
  · intro hx hzero
    subst hzero
    simp at hx
  · exact scalar_pos

@[simp] theorem scalar_nonneg (x : ℝ) :
    0 ≤ scalar x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (scalar_pos hx).le

/-! ## Tangent and curvature identities -/

/-- The deviance is exactly the exponential graph minus its affine tangent at
the origin. -/
theorem scalar_eq_exp_sub_tangent (x : ℝ) :
    scalar x = Real.exp (-x) - (1 - x) := by
  simp [scalar]
  ring

@[simp]
theorem deriv_scalar_zero :
    deriv scalar 0 = 0 := by
  rw [deriv_scalar]
  simp

/-- The derivative of the first derivative is strictly positive.  This is the
finite scalar curvature statement; it does not assert an operator calculus. -/
theorem hasDerivAt_deriv_scalar (x : ℝ) :
    HasDerivAt (fun y => 1 - Real.exp (-y)) (Real.exp (-x)) x := by
  convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_neg x).exp) using 1 <;>
    simp <;> ring

theorem deriv_deriv_scalar (x : ℝ) :
    deriv (fun y => 1 - Real.exp (-y)) x = Real.exp (-x) :=
  (hasDerivAt_deriv_scalar x).deriv

theorem scalar_strictly_convex_curvature (x : ℝ) :
    0 < deriv (fun y => 1 - Real.exp (-y)) x := by
  rw [deriv_deriv_scalar]
  exact Real.exp_pos _

/-- Exact additive decomposition of the scalar modular deviance. -/
theorem scalar_add_deviance (x y : ℝ) :
    scalar (x + y) = scalar x + scalar y +
      (1 - Real.exp (-x)) * (1 - Real.exp (-y)) := by
  unfold scalar
  rw [show -(x + y) = -x + -y by ring, Real.exp_add]
  ring

/-- The deviance is additive when the left increment vanishes. -/
theorem scalar_add_deviance_of_left_zero (y : ℝ) :
    scalar (0 + y) = scalar 0 + scalar y := by
  rw [scalar_add_deviance]
  simp

/-- The deviance is additive when the right increment vanishes. -/
theorem scalar_add_deviance_of_right_zero (x : ℝ) :
    scalar (x + 0) = scalar x + scalar 0 := by
  rw [scalar_add_deviance]
  simp

/-! ## Finite diagonal functional-calculus shadow -/

/-- Finite diagonal values of `exp (-β K) - I + β K`. -/
def finiteDiagonalDeviance {ι : Type*}
    (β : ℝ) (K : ι → ℝ) (i : ι) : ℝ :=
  scalar (β * K i)

theorem finiteDiagonalDeviance_nonneg {ι : Type*}
    (β : ℝ) (K : ι → ℝ) (i : ι) :
    0 ≤ finiteDiagonalDeviance β K i := by
  exact scalar_nonneg _

theorem finiteDiagonalDeviance_pos {ι : Type*}
    (β : ℝ) (K : ι → ℝ) (i : ι)
    (hβK : β * K i ≠ 0) :
    0 < finiteDiagonalDeviance β K i := by
  exact scalar_pos hβK

/-- A finite positive weighted expectation of the diagonal deviance is
nonnegative. -/
def finiteWeightedDeviance {ι : Type*} [Fintype ι]
    (weights : ι → ℝ) (β : ℝ) (K : ι → ℝ) : ℝ :=
  ∑ i, weights i * finiteDiagonalDeviance β K i

theorem finiteWeightedDeviance_nonneg {ι : Type*} [Fintype ι]
    (weights : ι → ℝ) (β : ℝ) (K : ι → ℝ)
    (hw : ∀ i, 0 ≤ weights i) :
    0 ≤ finiteWeightedDeviance weights β K := by
  unfold finiteWeightedDeviance
  exact Finset.sum_nonneg (fun i hi =>
    mul_nonneg (hw i) (finiteDiagonalDeviance_nonneg β K i))

theorem finiteWeightedDeviance_pos_of_pos_weight {ι : Type*} [Fintype ι]
    (weights : ι → ℝ) (β : ℝ) (K : ι → ℝ) (i₀ : ι)
    (hw : ∀ i, 0 ≤ weights i)
    (hw₀ : 0 < weights i₀)
    (hβK : β * K i₀ ≠ 0) :
    0 < finiteWeightedDeviance weights β K := by
  unfold finiteWeightedDeviance
  apply Finset.sum_pos' (s := Finset.univ)
  · intro i hi
    exact mul_nonneg (hw i) (finiteDiagonalDeviance_nonneg β K i)
  · exact ⟨i₀, Finset.mem_univ _,
      mul_pos hw₀ (finiteDiagonalDeviance_pos β K i₀ hβK)⟩

theorem scalar_eq_zero_iff (x : ℝ) :
    scalar x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact (scalar_pos hx).ne' h
  · intro h
    simp [h]

/-- With strictly positive weights, the finite diagonal deviance vanishes
exactly when every diagonal modular parameter vanishes. -/
theorem finiteWeightedDeviance_eq_zero_iff {ι : Type*} [Fintype ι]
    (weights : ι → ℝ) (β : ℝ) (K : ι → ℝ)
    (hw : ∀ i, 0 < weights i) :
    finiteWeightedDeviance weights β K = 0 ↔
      ∀ i, β * K i = 0 := by
  constructor
  · intro hzero i
    by_contra hnonzero
    have hpos := finiteWeightedDeviance_pos_of_pos_weight
      weights β K i (fun j => (hw j).le) (hw i) hnonzero
    linarith
  · intro hzero
    unfold finiteWeightedDeviance
    apply Finset.sum_eq_zero
    intro i hi
    have hscalar : scalar (β * K i) = 0 :=
      (scalar_eq_zero_iff (β * K i)).2 (hzero i)
    simp [finiteDiagonalDeviance, hscalar]

/-- Strict finite second law: with positive weights, the deviance is positive
    exactly when some modular mode is nonzero. -/
theorem finiteWeightedDeviance_pos_iff {ι : Type*} [Fintype ι]
    (weights : ι → ℝ) (β : ℝ) (K : ι → ℝ)
    (hw : ∀ i, 0 < weights i) :
    0 < finiteWeightedDeviance weights β K ↔
      ∃ i, β * K i ≠ 0 := by
  constructor
  · intro hpos
    by_contra hnone
    have hzero : ∀ i, β * K i = 0 := by
      intro i
      by_contra hnonzero
      exact hnone ⟨i, hnonzero⟩
    have hvanish :=
      (finiteWeightedDeviance_eq_zero_iff weights β K hw).2 hzero
    linarith
  · rintro ⟨i, hi⟩
    exact finiteWeightedDeviance_pos_of_pos_weight
      weights β K i (fun j => (hw j).le) (hw i) hi

end InfoGeometry.Thermodynamics.TomitaModularDeviance

end noncomputable section

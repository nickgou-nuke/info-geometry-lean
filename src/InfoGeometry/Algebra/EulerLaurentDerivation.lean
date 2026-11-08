import Mathlib.Data.Finsupp.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Finite Laurent charges and the Euler derivation

This owner is the finite algebraic replacement for a local Laurent expansion.
`LaurentPoly R` is a finitely supported coefficient function on `ℤ`; no
convergence, analytic continuation, or infinite series is involved.

The exponent of a monomial is the Euler charge.  The coefficient of the
formal one-form `u⁻¹ du` is its algebraic residue.  Analytic zeta, contour,
and complex-logarithm owners are intentionally not imported here.
-/

noncomputable section

namespace InfoGeometry.Algebra.EulerLaurentDerivation

open scoped BigOperators

variable {R : Type*} [Ring R]

/-! ## Finite Laurent coefficient algebra -/

/-- Finite Laurent polynomials, represented by their integer-indexed
coefficient function. -/
abbrev LaurentPoly (R : Type*) [Zero R] := ℤ →₀ R

/-- The coefficient of the Laurent monomial `u^n` with coefficient `a`. -/
def monomial (n : ℤ) (a : R) : LaurentPoly R :=
  Finsupp.single n a

@[simp]
theorem monomial_apply (n k : ℤ) (a : R) :
    monomial n a k = if n = k then a else 0 := by
  change Finsupp.single n a k = _
  rw [Finsupp.single_apply]

/-! ## Euler derivation -/

/-- The finite Euler derivation `u d/du`, defined on coefficients by
`u^n ↦ n u^n`. -/
def euler (f : LaurentPoly R) : LaurentPoly R :=
  f.sum fun n a => monomial n ((n : R) * a)

@[simp]
theorem euler_monomial (n : ℤ) (a : R) :
    euler (monomial n a) = monomial n ((n : R) * a) := by
  classical
  change (Finsupp.single n a).sum _ = _
  rw [Finsupp.sum_single_index]
  all_goals simp [monomial]

@[simp]
theorem euler_zero :
    euler (0 : LaurentPoly R) = 0 := by
  classical
  ext n
  simp [euler]

theorem euler_add (f g : LaurentPoly R) :
    euler (f + g) = euler f + euler g := by
  classical
  unfold euler
  rw [Finsupp.sum_add_index]
  · intro n hn
    ext k
    simp [monomial]
  · intro n hn a b
    ext k
    simp [monomial, mul_add]

theorem euler_smul (c : R) (f : LaurentPoly R) :
    euler (c • f) = c • euler f := by
  classical
  unfold euler
  rw [Finsupp.sum_smul_index]
  · rw [Finsupp.smul_sum]
    congr 1
    funext n a
    ext k
    simp only [monomial_apply, Finsupp.smul_apply]
    by_cases h : n = k
    · subst k
      simp [mul_assoc, Int.cast_comm]
    · simp [h]
  · intro n
    simp [monomial]

/-- The Euler derivation as a native module endomorphism. -/
def eulerLinear : LaurentPoly R →ₗ[R] LaurentPoly R where
  toFun := euler
  map_add' := euler_add
  map_smul' := euler_smul

@[simp]
theorem eulerLinear_apply (f : LaurentPoly R) :
    eulerLinear f = euler f :=
  rfl

/-! ## Formal one-forms and residue -/

/-- Coefficients of formal one-forms `f(u) du`. -/
abbrev LaurentOneForm (R : Type*) [Zero R] := ℤ →₀ R

/-- The formal differential of a finite Laurent polynomial. -/
def differential (f : LaurentPoly R) : LaurentOneForm R :=
  f.sum fun n a => Finsupp.single (n - 1) ((n : R) * a)

/-- Algebraic residue: the coefficient of `u⁻¹ du`. -/
def residue (ω : LaurentOneForm R) : R :=
  ω (-1)

/-- The residue as a native linear functional on formal one-forms. -/
def residueLinear : LaurentOneForm R →ₗ[R] R where
  toFun := residue
  map_add' := by
    intro ω η
    rfl
  map_smul' := by
    intro c ω
    rfl

@[simp]
theorem residueLinear_apply (ω : LaurentOneForm R) :
    residueLinear ω = residue ω :=
  rfl

@[simp]
theorem residue_monomial (n : ℤ) (a : R) :
    residue (Finsupp.single n a) = if n = -1 then a else 0 := by
  change Finsupp.single n a (-1) = _
  rw [Finsupp.single_apply]

@[simp]
theorem differential_monomial (n : ℤ) (a : R) :
    differential (monomial n a) =
      Finsupp.single (n - 1) ((n : R) * a) := by
  classical
  change (Finsupp.single n a).sum _ = _
  rw [Finsupp.sum_single_index]
  all_goals simp [monomial]

@[simp]
theorem differential_zero :
    differential (0 : LaurentPoly R) = 0 := by
  classical
  ext n
  simp [differential]

theorem differential_add (f g : LaurentPoly R) :
    differential (f + g) = differential f + differential g := by
  classical
  unfold differential
  rw [Finsupp.sum_add_index]
  · intro n hn
    ext k
    simp
  · intro n hn a b
    ext k
    simp [add_mul, mul_add]

theorem differential_smul (c : R) (f : LaurentPoly R) :
    differential (c • f) = c • differential f := by
  classical
  unfold differential
  rw [Finsupp.sum_smul_index]
  · rw [Finsupp.smul_sum]
    congr 1
    funext n a
    ext k
    rw [Finsupp.single_apply, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases h : n - 1 = k
    · simp [h, mul_assoc, Int.cast_comm]
    · simp [h]
  · intro n
    simp

/-- The formal differential as a native module endomorphism. -/
def differentialLinear : LaurentPoly R →ₗ[R] LaurentOneForm R where
  toFun := differential
  map_add' := differential_add
  map_smul' := differential_smul

@[simp]
theorem differentialLinear_apply (f : LaurentPoly R) :
    differentialLinear f = differential f :=
  rfl

/-- Exact formal differentials lie in the kernel of the residue functional. -/
theorem residueLinear_comp_differentialLinear :
    (residueLinear : LaurentOneForm R →ₗ[R] R).comp
        (differentialLinear : LaurentPoly R →ₗ[R] LaurentOneForm R) =
      (0 : LaurentPoly R →ₗ[R] R) := by
  apply LinearMap.ext
  intro f
  change residueLinear (differentialLinear f) = 0
  change residue (differential f) = 0
  classical
  rw [differential, residue, Finsupp.sum_apply]
  refine Finset.sum_eq_zero (fun n hn => ?_)
  change (Finsupp.single (n - 1) ((n : R) * f n)) (-1) = 0
  rw [Finsupp.single_apply]
  by_cases h : n - 1 = -1
  · have h' : n = 0 := by omega
    simp [h, h']
  · simp [h]

theorem residue_differential_monomial (n : ℤ) (a : R) :
    residue (differential (monomial n a)) = 0 := by
  classical
  rw [differential_monomial]
  by_cases h : n = 0
  · subst n
    simp [residue]
  · have h' : n - 1 ≠ -1 := by omega
    change Finsupp.single (n - 1) ((n : R) * a) (-1) = 0
    rw [Finsupp.single_apply]
    simp [h']

/-! ## Local divisor packets -/

/-- A finite local divisor normal form.  `order` is the signed Laurent
order; `unit` is carried as a separate local-unit certificate. -/
structure LocalDivisorData (R : Type*) [Ring R] where
  order : ℤ
  unit : LaurentPoly R

/-- The signed pole/zero charge of a local packet. -/
def charge (D : LocalDivisorData R) : ℤ :=
  D.order

@[simp]
theorem charge_eq_order (D : LocalDivisorData R) :
    charge D = D.order := rfl

/-- Positive, zero, and negative order are the zero, regular, and pole
labels of the finite divisor packet. -/
def isZero (D : LocalDivisorData R) : Prop := 0 < D.order

def isRegular (D : LocalDivisorData R) : Prop := D.order = 0

def isPole (D : LocalDivisorData R) : Prop := D.order < 0

theorem charge_pos_iff_isZero (D : LocalDivisorData R) :
    0 < charge D ↔ isZero D := by
  rfl

theorem charge_eq_zero_iff_isRegular (D : LocalDivisorData R) :
    charge D = 0 ↔ isRegular D := by
  rfl

theorem charge_neg_iff_isPole (D : LocalDivisorData R) :
    charge D < 0 ↔ isPole D := by
  rfl

/-! ## The canonical residue representative -/

/-- The residue representative carrying a divisor charge. -/
def chargeForm (D : LocalDivisorData R) : LaurentOneForm R :=
  Finsupp.single (-1) (D.order : R)

theorem residue_chargeForm (D : LocalDivisorData R) :
    residue (chargeForm D) = (D.order : R) := by
  change Finsupp.single (-1) (D.order : R) (-1) = _
  rw [Finsupp.single_eq_same]

theorem chargeForm_residue_eq_zero_iff
    [CharZero R] (D : LocalDivisorData R) :
    residue (chargeForm D) = 0 ↔ D.order = 0 := by
  rw [residue_chargeForm]
  exact_mod_cast (show D.order = 0 ↔ D.order = 0 from Iff.rfl)

/-! ## Reflection of finite divisor labels -/

/-- A reflection-invariant finite divisor packet on a label type. -/
structure DivisorData (ι : Type*) where
  order : ι → ℤ
  reflect : ι → ι
  reflect_involutive : Function.Involutive reflect
  order_reflect : ∀ a, order (reflect a) = order a

theorem divisor_order_reflect
    {ι : Type*} (D : DivisorData ι) (a : ι) :
    D.order (D.reflect a) = D.order a :=
  D.order_reflect a

/-! ## Finite divisor index -/

/-- The signed index of a finite marked divisor. -/
def divisorIndex {ι : Type*} (marks : Finset ι) (order : ι → ℤ) : ℤ :=
  marks.sum order

@[simp]
theorem divisorIndex_empty {ι : Type*} (order : ι → ℤ) :
    divisorIndex (∅ : Finset ι) order = 0 := by
  simp [divisorIndex]

theorem divisorIndex_insert
    {ι : Type*} [DecidableEq ι]
    (marks : Finset ι) (order : ι → ℤ) (a : ι) (ha : a ∉ marks) :
    divisorIndex (insert a marks) order = order a + divisorIndex marks order := by
  simp [divisorIndex, ha, add_comm]

/-- The total finite divisor charge is invariant under the reflection
    readout.  This is the finite algebraic form of divisor symmetry. -/
theorem divisorIndex_reflection_invariant
    {ι : Type*} [Fintype ι] (D : DivisorData ι) :
    divisorIndex Finset.univ (fun a => D.order (D.reflect a)) =
      divisorIndex Finset.univ D.order := by
  simp [divisorIndex, D.order_reflect]

/-- The Euler derivation acts as multiplication by the exponent on monomials:
    `euler(u^n) = n u^n`. This is the finite algebraic form of the Mellin duality
    `M(x d/dx f)(s) = -s M[f](s)`. -/
theorem euler_eq_smul_monomial (n : ℤ) (a : R) :
    euler (monomial n a) = monomial n ((n : R) * a) :=
  euler_monomial n a

end InfoGeometry.Algebra.EulerLaurentDerivation

end noncomputable section

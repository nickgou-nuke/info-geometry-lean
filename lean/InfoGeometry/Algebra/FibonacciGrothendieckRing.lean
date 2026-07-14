import InfoGeometry.Algebra.Grothendieck

/-!
# InfoGeometry.Algebra.FibonacciGrothendieckRing

Native algebraic owner for the additive Grothendieck completion of the
Fibonacci fusion semiring skeleton.

The finite positive classes are pairs `(a, b) : ℕ × ℕ`, read as
`a·1 + b·τ`.  Their Grothendieck completion is handled by the existing
`Grothendieck` owner.  This file adds the concrete `ℤ²` fusion-ring model and
the tensor-by-`τ` compatibility used by the staged Fibonacci colimit lane.

This is not a braided category construction: there are no associators,
braidings, pentagon proofs, or hexagon proofs here.
-/

set_option autoImplicit false

namespace FibonacciGrothendieckRing

/-! ## Positive Fibonacci fusion classes and their K₀ completion -/

/-- Positive finite Fibonacci fusion classes `a·1 + b·τ`. -/
abbrev FibFusionMonoid : Type :=
  Nat × Nat

/-- The positive unit class `1`. -/
def fibOneRaw : FibFusionMonoid :=
  (1, 0)

/-- The positive Fibonacci generator `τ`. -/
def fibTauRaw : FibFusionMonoid :=
  (0, 1)

/-- Additive Grothendieck completion of positive Fibonacci fusion classes. -/
abbrev FibonacciK0 : Type :=
  Grothendieck FibFusionMonoid

/-- The K₀ class of the tensor unit. -/
def fibOneK0 : FibonacciK0 :=
  grothendieckMap FibFusionMonoid fibOneRaw

/-- The K₀ class of the Fibonacci generator `τ`. -/
def fibTauK0 : FibonacciK0 :=
  grothendieckMap FibFusionMonoid fibTauRaw

/-! ## Concrete `ℤ²` Fibonacci fusion-ring model -/

/--
Concrete additive model for `K₀(Fib)`: the pair `(a, b)` represents
`a·1 + b·τ`, with multiplication governed by `τ² = 1 + τ`.
-/
abbrev FibonacciRingModel : Type :=
  Int × Int

namespace FibonacciRingModel

/-- The model unit `1`. -/
def one : FibonacciRingModel :=
  (1, 0)

/-- The model generator `τ`. -/
def tau : FibonacciRingModel :=
  (0, 1)

/-- Multiplication in the Fibonacci fusion ring model, using `τ² = 1 + τ`. -/
def mul (x y : FibonacciRingModel) : FibonacciRingModel :=
  (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1 + x.2 * y.2)

@[simp]
theorem mul_fst (x y : FibonacciRingModel) :
    (mul x y).1 = x.1 * y.1 + x.2 * y.2 :=
  rfl

@[simp]
theorem mul_snd (x y : FibonacciRingModel) :
    (mul x y).2 = x.1 * y.2 + x.2 * y.1 + x.2 * y.2 :=
  rfl

@[simp]
theorem one_fst : one.1 = 1 :=
  rfl

@[simp]
theorem one_snd : one.2 = 0 :=
  rfl

@[simp]
theorem tau_fst : tau.1 = 0 :=
  rfl

@[simp]
theorem tau_snd : tau.2 = 1 :=
  rfl

/-- The Fibonacci fusion rule in the concrete model: `τ² = τ + 1`. -/
theorem tau_mul_tau : mul tau tau = tau + one := by
  ext <;> norm_num [mul, tau, one]

theorem one_mul (x : FibonacciRingModel) : mul one x = x := by
  ext <;> simp [mul, one]

theorem mul_one (x : FibonacciRingModel) : mul x one = x := by
  ext <;> simp [mul, one]

theorem mul_comm (x y : FibonacciRingModel) : mul x y = mul y x := by
  ext <;> simp [mul] <;> ring

theorem mul_assoc (x y z : FibonacciRingModel) : mul (mul x y) z = mul x (mul y z) := by
  ext <;> simp [mul] <;> ring

theorem left_distrib (x y z : FibonacciRingModel) :
    mul x (y + z) = mul x y + mul x z := by
  ext <;> simp [mul] <;> ring

theorem right_distrib (x y z : FibonacciRingModel) :
    mul (x + y) z = mul x z + mul y z := by
  ext <;> simp [mul] <;> ring

/--
Evaluation of the Fibonacci fusion-ring model into any commutative ring once an
element `t` satisfying `t² = t + 1` is chosen.
-/
def eval {R : Type*} [CommRing R] (t : R) (x : FibonacciRingModel) : R :=
  (x.1 : R) + (x.2 : R) * t

@[simp]
theorem eval_one {R : Type*} [CommRing R] (t : R) : eval t one = 1 := by
  simp [eval, one]

@[simp]
theorem eval_tau {R : Type*} [CommRing R] (t : R) : eval t tau = t := by
  simp [eval, tau]

theorem eval_add {R : Type*} [CommRing R] (t : R) (x y : FibonacciRingModel) :
    eval t (x + y) = eval t x + eval t y := by
  simp [eval]
  ring

theorem eval_neg {R : Type*} [CommRing R] (t : R) (x : FibonacciRingModel) :
    eval t (-x) = -eval t x := by
  simp [eval]
  ring

theorem eval_mul {R : Type*} [CommRing R] (t : R)
    (hτ : t ^ 2 = t + 1) (x y : FibonacciRingModel) :
    eval t (mul x y) = eval t x * eval t y := by
  simp [eval, mul]
  ring_nf
  rw [hτ]
  ring

end FibonacciRingModel

/-! ## Grothendieck universal map into the concrete model -/

/-- Positive classes embed additively into the concrete `ℤ²` model. -/
def rawToModel : FibFusionMonoid →+ FibonacciRingModel where
  toFun x := ((x.1 : Int), (x.2 : Int))
  map_zero' := by
    ext <;> simp
  map_add' x y := by
    ext <;> simp

/-- The Grothendieck universal lift from `K₀` into the concrete model. -/
def k0ToModel : FibonacciK0 →+ FibonacciRingModel :=
  grothendieckLift rawToModel

@[simp]
theorem k0ToModel_grothendieckMap (x : FibFusionMonoid) :
    k0ToModel (grothendieckMap FibFusionMonoid x) = rawToModel x :=
  grothendieckLift_comp rawToModel x

@[simp]
theorem k0ToModel_one : k0ToModel fibOneK0 = FibonacciRingModel.one := by
  simp [fibOneK0, fibOneRaw, rawToModel, FibonacciRingModel.one]

@[simp]
theorem k0ToModel_tau : k0ToModel fibTauK0 = FibonacciRingModel.tau := by
  simp [fibTauK0, fibTauRaw, rawToModel, FibonacciRingModel.tau]

/-! ## Tensor by `τ` and compatibility with the fusion-ring model -/

/-- Tensoring a positive Fibonacci class by `τ`: `1 ↦ τ`, `τ ↦ 1 + τ`. -/
def tensorTauRaw : FibFusionMonoid →+ FibFusionMonoid where
  toFun x := (x.2, x.1 + x.2)
  map_zero' := rfl
  map_add' x y := by
    ext <;> simp [add_comm, add_left_comm]

/-- The induced endomorphism on the Grothendieck completion. -/
def tensorTauK0 : FibonacciK0 →+ FibonacciK0 :=
  grothendieckFunctor tensorTauRaw

/-- On the concrete model, tensoring by `τ` is multiplication by `τ`. -/
theorem rawToModel_tensorTau (x : FibFusionMonoid) :
    rawToModel (tensorTauRaw x) =
      FibonacciRingModel.mul (rawToModel x) FibonacciRingModel.tau := by
  ext <;> simp [rawToModel, tensorTauRaw, FibonacciRingModel.mul, FibonacciRingModel.tau]

@[simp]
theorem tensorTauRaw_one : tensorTauRaw fibOneRaw = fibTauRaw :=
  rfl

theorem tensorTauRaw_tau : tensorTauRaw fibTauRaw = fibOneRaw + fibTauRaw := by
  rfl

@[simp]
theorem tensorTauK0_grothendieckMap (x : FibFusionMonoid) :
    tensorTauK0 (grothendieckMap FibFusionMonoid x) =
      grothendieckMap FibFusionMonoid (tensorTauRaw x) := by
  simpa [tensorTauK0, grothendieckFunctor] using
    grothendieckLift_comp ((grothendieckMap FibFusionMonoid).comp tensorTauRaw) x

theorem tensorTauK0_one : tensorTauK0 fibOneK0 = fibTauK0 := by
  simp [fibOneK0, fibTauK0, tensorTauRaw_one]

theorem tensorTauK0_tau : tensorTauK0 fibTauK0 = fibOneK0 + fibTauK0 := by
  rw [fibTauK0, tensorTauK0_grothendieckMap, tensorTauRaw_tau]
  simp [fibOneK0]

/--
The K₀ image of `τ ⊗ τ` evaluates to the concrete fusion product `τ²`, hence
to `τ + 1` in the Fibonacci model.
-/
theorem k0_tau_square_model :
    k0ToModel (tensorTauK0 fibTauK0) = FibonacciRingModel.tau + FibonacciRingModel.one := by
  rw [tensorTauK0_tau]
  ext <;> norm_num [FibonacciRingModel.tau, FibonacciRingModel.one]

end FibonacciGrothendieckRing

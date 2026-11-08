import InfoGeometry.Algebra.Grothendieck
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

namespace InfoGeometry.Algebra.FibonacciGrothendieckRing

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

/-! ## Bijectivity & Induced Multiplication on `FibonacciK0` -/

/-- Evaluation of `k0ToModel` on a quotient representative. -/
theorem k0ToModel_mk (x : FibFusionMonoid × FibFusionMonoid) :
    k0ToModel (Quotient.mk (grothendieckSetoid FibFusionMonoid) x) =
      rawToModel x.1 - rawToModel x.2 :=
  rfl

/-- `k0ToModel` is injective. -/
theorem k0ToModel_injective : Function.Injective k0ToModel := by
  intro a b hab
  revert hab
  refine Quotient.inductionOn₂
    (s₁ := grothendieckSetoid FibFusionMonoid)
    (s₂ := grothendieckSetoid FibFusionMonoid) a b ?_
  intro x y h
  have h1 : (x.1.1 : Int) - (x.2.1 : Int) = (y.1.1 : Int) - (y.2.1 : Int) := by
    exact congrArg Prod.fst h
  have h2 : (x.1.2 : Int) - (x.2.2 : Int) = (y.1.2 : Int) - (y.2.2 : Int) := by
    exact congrArg Prod.snd h
  apply Quotient.sound
  use (0, 0)
  apply Prod.ext
  · change x.1.1 + y.2.1 + 0 = x.2.1 + y.1.1 + 0
    omega
  · change x.1.2 + y.2.2 + 0 = x.2.2 + y.1.2 + 0
    omega

/-- `k0ToModel` is surjective. -/
theorem k0ToModel_surjective : Function.Surjective k0ToModel := by
  intro p
  rcases p with ⟨a, b⟩
  use Quotient.mk (grothendieckSetoid FibFusionMonoid)
    ((a.toNat, b.toNat), ((-a).toNat, (-b).toNat))
  rw [k0ToModel_mk]
  apply Prod.ext
  · change (a.toNat : Int) - ((-a).toNat : Int) = a
    omega
  · change (b.toNat : Int) - ((-b).toNat : Int) = b
    omega

/-- Additive isomorphism between `FibonacciK0` and `FibonacciRingModel`. -/
noncomputable def fibonacciK0AddEquiv : FibonacciK0 ≃+ FibonacciRingModel :=
  AddEquiv.ofBijective k0ToModel ⟨k0ToModel_injective, k0ToModel_surjective⟩

@[simp]
theorem fibonacciK0AddEquiv_apply (x : FibonacciK0) :
    fibonacciK0AddEquiv x = k0ToModel x :=
  rfl

@[simp]
theorem k0ToModel_fibonacciK0AddEquiv_symm (y : FibonacciRingModel) :
    k0ToModel (fibonacciK0AddEquiv.symm y) = y :=
  fibonacciK0AddEquiv.apply_symm_apply y

@[simp]
theorem fibonacciK0AddEquiv_symm_k0ToModel (x : FibonacciK0) :
    fibonacciK0AddEquiv.symm (k0ToModel x) = x :=
  fibonacciK0AddEquiv.symm_apply_apply x

/-- Multiplication on `FibonacciK0` induced via `fibonacciK0AddEquiv`. -/
noncomputable def k0Mul (x y : FibonacciK0) : FibonacciK0 :=
  fibonacciK0AddEquiv.symm (FibonacciRingModel.mul (fibonacciK0AddEquiv x) (fibonacciK0AddEquiv y))

@[simp]
theorem k0ToModel_k0Mul (x y : FibonacciK0) :
    k0ToModel (k0Mul x y) = FibonacciRingModel.mul (k0ToModel x) (k0ToModel y) := by
  dsimp [k0Mul]
  exact fibonacciK0AddEquiv.apply_symm_apply
    (FibonacciRingModel.mul (fibonacciK0AddEquiv x) (fibonacciK0AddEquiv y))

/-- The Fibonacci fusion rule directly in `FibonacciK0`: `τ * τ = τ + 1`. -/
theorem k0Mul_tau_tau : k0Mul fibTauK0 fibTauK0 = fibTauK0 + fibOneK0 := by
  apply k0ToModel_injective
  rw [k0ToModel_k0Mul, map_add, k0ToModel_tau, k0ToModel_one, FibonacciRingModel.tau_mul_tau]

theorem k0Mul_comm (x y : FibonacciK0) : k0Mul x y = k0Mul y x := by
  apply k0ToModel_injective
  rw [k0ToModel_k0Mul, k0ToModel_k0Mul, FibonacciRingModel.mul_comm]

theorem k0Mul_assoc (x y z : FibonacciK0) : k0Mul (k0Mul x y) z = k0Mul x (k0Mul y z) := by
  apply k0ToModel_injective
  rw [k0ToModel_k0Mul, k0ToModel_k0Mul, k0ToModel_k0Mul, k0ToModel_k0Mul,
    FibonacciRingModel.mul_assoc]

@[simp]
theorem one_k0Mul (x : FibonacciK0) : k0Mul fibOneK0 x = x := by
  apply k0ToModel_injective
  rw [k0ToModel_k0Mul, k0ToModel_one, FibonacciRingModel.one_mul]

@[simp]
theorem k0Mul_one (x : FibonacciK0) : k0Mul x fibOneK0 = x := by
  apply k0ToModel_injective
  rw [k0ToModel_k0Mul, k0ToModel_one, FibonacciRingModel.mul_one]

theorem k0Mul_left_distrib (x y z : FibonacciK0) :
    k0Mul x (y + z) = k0Mul x y + k0Mul x z := by
  apply k0ToModel_injective
  rw [k0ToModel_k0Mul, map_add, map_add, k0ToModel_k0Mul, k0ToModel_k0Mul,
    FibonacciRingModel.left_distrib]

theorem k0Mul_right_distrib (x y z : FibonacciK0) :
    k0Mul (x + y) z = k0Mul x z + k0Mul y z := by
  apply k0ToModel_injective
  rw [k0ToModel_k0Mul, map_add, map_add, k0ToModel_k0Mul, k0ToModel_k0Mul,
    FibonacciRingModel.right_distrib]

/-- Compatibility of `tensorTauK0` with `k0ToModel`. -/
theorem k0ToModel_tensorTauK0 (x : FibonacciK0) :
    k0ToModel (tensorTauK0 x) = FibonacciRingModel.mul (k0ToModel x) FibonacciRingModel.tau := by
  rcases grothendieck_eq_sub x with ⟨a, b, rfl⟩
  simp only [map_sub, tensorTauK0_grothendieckMap, k0ToModel_grothendieckMap, rawToModel_tensorTau]
  ext <;> simp [FibonacciRingModel.mul, FibonacciRingModel.tau]; ring

/-- Tensoring by `τ` in `FibonacciK0` coincides with multiplying by `fibTauK0`. -/
theorem tensorTauK0_eq_k0Mul_tau (x : FibonacciK0) :
    tensorTauK0 x = k0Mul x fibTauK0 := by
  apply k0ToModel_injective
  rw [k0ToModel_tensorTauK0, k0ToModel_k0Mul, k0ToModel_tau]

end InfoGeometry.Algebra.FibonacciGrothendieckRing

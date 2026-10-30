/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.Equivariance
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.Corner
import InfoGeometry.Core.IdempotentCartan

/-!
# Orientation grading, half-twist sandwiches, and the Hodge-conjugate codifferential

Everything here is an identity in an arbitrary associative `R`-algebra `A`, or
in its operator ring `Module.End R A`. Nothing is scalar, diagonal or
commutative.

1. `HalfTwist`: for a square-zero pair `u, v` with `Φ = u + v`,
   `J = u - v`, `V = u v + v u`, `Σ = u v - v u`, the two-sided sandwiches by
   `Φ` and `J` send `V ↦ V²` and `Σ ↦ -(V Σ)`. The sandwich by `Σ` sends
   `V ↦ V³` and `Σ ↦ V² Σ`. In the operator ring, the `J`-sandwich after the
   `Φ`-sandwich is the `Σ`-sandwich.
2. `OrientationGrading`: for an idempotent `p`, take the Cartan reflection
   `S = 2 p - 1` from `Core.IdempotentCartan` and the canonical corners
   `u = component10 p a`, `v = component01 p b`. The Hodge-type operator
   `⋆ = L_S` squares to `1` in `Module.End R A`. It exchanges `V ↔ Σ` and
   `Φ ↔ J`. The sandwiches satisfy `Φ S Φ = J S (-J) = -(V S)` and
   `Σ S Σ = V² S`.
3. `GradedDerivation`: let `S` be any involution and `x` any `S`-odd element
   (`S x = -(x S)`). Put `d_x = L_x - (y ↦ S y S x)` and
   `d̄_x = L_x + (y ↦ S y S x)`. Then `d̄_x = -(⋆ d_x ⋆)` and
   `d_x = -(⋆ d̄_x ⋆)` hold in `Module.End R A`. Also `d_x² = d̄_x² = ad_{x²}`
   and `d_x d̄_x + d̄_x d_x = 2 (L_{x²} + R_{x²})`.

The words orientation, half-twist and Hodge star are only reading aids. The
proved statements are the ring and operator-ring equations above. Sandwiches by
`Φ, J, Σ` are not conjugation by units. A `Φ`-sandwich multiplies by the
operator-valued mass `V`, not by a scalar. Nothing here is a manifold theorem.

**Correction to the intake.** The candidate claim
`{d_Φ, d̄_Φ}(X) = 2 V X` is false; a random `5 × 5` numerical model with a
non-orthogonal idempotent refutes it. The proved form is
`{d_Φ, d̄_Φ}(X) = 2 (V X + X V)`, i.e. `2 • jordanOp R V`. With `J² = -V`
the same formula gives `-2 • jordanOp R V` for `d_J`.
-/

namespace InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral

open InfoGeometry.OperatorAlgebra.LieJordan
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.IdempotentCartan (reflection reflection_sq)

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-! ### Half-twist sandwiches of a square-zero pair -/

section HalfTwist

variable {u v : A} (hu : u * u = 0) (hv : v * v = 0)
include hu hv

/-- `J Φ = Σ` for a square-zero pair. -/
theorem difference_mul_sum_eq_spin : (u - v) * (u + v) = u * v - v * u := by
  noncomm_ring [hu, hv]

/-- `Φ (-J) = Σ` for a square-zero pair. -/
theorem sum_mul_neg_difference_eq_spin : (u + v) * -(u - v) = u * v - v * u := by
  noncomm_ring [hu, hv]

/-- The `Φ`-sandwich of the mass is its square. -/
theorem sum_sandwich_mass :
    (u + v) * (u * v + v * u) * (u + v) = (u * v + v * u) * (u * v + v * u) := by
  have huuV := mul_mul_eq_zero_of_sq hu v
  have hvvU := mul_mul_eq_zero_of_sq hv u
  noncomm_ring [hu, hv, huuV, hvvU]

/-- The `Φ`-sandwich reverses the sign of the spin, with mass coefficient. -/
theorem sum_sandwich_spin :
    (u + v) * (u * v - v * u) * (u + v) = -((u * v + v * u) * (u * v - v * u)) := by
  have huuV := mul_mul_eq_zero_of_sq hu v
  have hvvU := mul_mul_eq_zero_of_sq hv u
  noncomm_ring [hu, hv, huuV, hvvU]

/-- The `J`-sandwich (with `-J` on the right) of the mass is its square. -/
theorem difference_sandwich_mass :
    (u - v) * (u * v + v * u) * -(u - v) = (u * v + v * u) * (u * v + v * u) := by
  have huuV := mul_mul_eq_zero_of_sq hu v
  have hvvU := mul_mul_eq_zero_of_sq hv u
  noncomm_ring [hu, hv, huuV, hvvU]

/-- The `J`-sandwich reverses the sign of the spin, with mass coefficient. -/
theorem difference_sandwich_spin :
    (u - v) * (u * v - v * u) * -(u - v) = -((u * v + v * u) * (u * v - v * u)) := by
  have huuV := mul_mul_eq_zero_of_sq hu v
  have hvvU := mul_mul_eq_zero_of_sq hv u
  noncomm_ring [hu, hv, huuV, hvvU]

/-- The `Σ`-sandwich of the mass is its cube. -/
theorem spin_sandwich_mass :
    (u * v - v * u) * (u * v + v * u) * (u * v - v * u) =
      (u * v + v * u) * (u * v + v * u) * (u * v + v * u) := by
  have huuV := mul_mul_eq_zero_of_sq hu v
  have hvvU := mul_mul_eq_zero_of_sq hv u
  noncomm_ring [hu, hv, huuV, hvvU]

/-- The `Σ`-sandwich keeps the sign of the spin, with coefficient `V²`. -/
theorem spin_sandwich_spin :
    (u * v - v * u) * (u * v - v * u) * (u * v - v * u) =
      (u * v + v * u) * (u * v + v * u) * (u * v - v * u) := by
  have huuV := mul_mul_eq_zero_of_sq hu v
  have hvvU := mul_mul_eq_zero_of_sq hv u
  noncomm_ring [hu, hv, huuV, hvvU]

/-- In `Module.End R A`, the `J`-sandwich after the `Φ`-sandwich is the
`Σ`-sandwich. -/
theorem sandwich_difference_comp_sum :
    sandwichOp R (u - v) (-(u - v)) * sandwichOp R (u + v) (u + v) =
      sandwichOp R (u * v - v * u) (u * v - v * u) := by
  ext x
  change (u - v) * ((u + v) * x * (u + v)) * -(u - v) =
    (u * v - v * u) * x * (u * v - v * u)
  calc (u - v) * ((u + v) * x * (u + v)) * -(u - v)
      = ((u - v) * (u + v)) * x * ((u + v) * -(u - v)) := by noncomm_ring
    _ = (u * v - v * u) * x * (u * v - v * u) := by
      rw [difference_mul_sum_eq_spin hu hv, sum_mul_neg_difference_eq_spin hu hv]

end HalfTwist

/-! ### The orientation grading `S = 2 p - 1` on canonical Peirce corners -/

section OrientationGrading

variable (R) in
/-- Left multiplication by the Cartan reflection `S = 2 p - 1`, viewed as an
element of the operator ring. -/
def hodgeStar (p : A) : Module.End R A := LinearMap.mulLeft R (reflection p)

@[simp] theorem hodgeStar_apply (p x : A) : hodgeStar R p x = reflection p * x := rfl

variable {p : A} (hp : p * p = p) (a b : A)
include hp

/-- `⋆ ∘ ⋆ = 1` in `Module.End R A`. -/
theorem hodgeStar_mul_self : hodgeStar R p * hodgeStar R p = 1 := by
  ext x
  change reflection p * (reflection p * x) = x
  rw [← mul_assoc, reflection_sq hp, one_mul]

theorem reflection_mul_component10 : reflection p * component10 p a = component10 p a := by
  simp only [reflection, two_nsmul, add_mul, sub_mul, one_mul, idem_mul_component10 hp]
  abel

theorem component10_mul_reflection :
    component10 p a * reflection p = -component10 p a := by
  simp only [reflection, two_nsmul, mul_add, mul_sub, mul_one, component10_mul_idem hp]
  abel

theorem reflection_mul_component01 :
    reflection p * component01 p b = -component01 p b := by
  simp only [reflection, two_nsmul, add_mul, sub_mul, one_mul, idem_mul_component01 hp]
  abel

theorem component01_mul_reflection : component01 p b * reflection p = component01 p b := by
  simp only [reflection, two_nsmul, mul_add, mul_sub, mul_one, component01_mul_idem hp]
  abel

/-- `S Φ = J`. -/
theorem reflection_mul_sum :
    reflection p * (component10 p a + component01 p b) =
      component10 p a - component01 p b := by
  rw [mul_add, reflection_mul_component10 hp, reflection_mul_component01 hp, sub_eq_add_neg]

/-- `S J = Φ`. -/
theorem reflection_mul_difference :
    reflection p * (component10 p a - component01 p b) =
      component10 p a + component01 p b := by
  rw [mul_sub, reflection_mul_component10 hp, reflection_mul_component01 hp, sub_neg_eq_add]

/-- `Φ S = -J`. -/
theorem sum_mul_reflection :
    (component10 p a + component01 p b) * reflection p =
      -(component10 p a - component01 p b) := by
  rw [add_mul, component10_mul_reflection hp, component01_mul_reflection hp]
  abel

/-- `J S = -Φ`. -/
theorem difference_mul_reflection :
    (component10 p a - component01 p b) * reflection p =
      -(component10 p a + component01 p b) := by
  rw [sub_mul, component10_mul_reflection hp, component01_mul_reflection hp]
  abel

/-- `S V = Σ`. -/
theorem reflection_mul_mass :
    reflection p * (component10 p a * component01 p b + component01 p b * component10 p a) =
      component10 p a * component01 p b - component01 p b * component10 p a := by
  rw [mul_add, ← mul_assoc, ← mul_assoc, reflection_mul_component10 hp,
    reflection_mul_component01 hp, neg_mul, ← sub_eq_add_neg]

/-- `S Σ = V`. -/
theorem reflection_mul_spin :
    reflection p * (component10 p a * component01 p b - component01 p b * component10 p a) =
      component10 p a * component01 p b + component01 p b * component10 p a := by
  rw [mul_sub, ← mul_assoc, ← mul_assoc, reflection_mul_component10 hp,
    reflection_mul_component01 hp, neg_mul, sub_neg_eq_add]

/-- `V S = Σ`. -/
theorem mass_mul_reflection :
    (component10 p a * component01 p b + component01 p b * component10 p a) * reflection p =
      component10 p a * component01 p b - component01 p b * component10 p a := by
  rw [add_mul, mul_assoc, mul_assoc, component01_mul_reflection hp,
    component10_mul_reflection hp, mul_neg, ← sub_eq_add_neg]

/-- `Σ S = V`. -/
theorem spin_mul_reflection :
    (component10 p a * component01 p b - component01 p b * component10 p a) * reflection p =
      component10 p a * component01 p b + component01 p b * component10 p a := by
  rw [sub_mul, mul_assoc, mul_assoc, component01_mul_reflection hp,
    component10_mul_reflection hp, mul_neg, sub_neg_eq_add]

/-- `⋆` exchanges the mass and the spin, and the two odd generators. -/
theorem hodgeStar_tetraktys :
    hodgeStar R p (component10 p a * component01 p b + component01 p b * component10 p a) =
      component10 p a * component01 p b - component01 p b * component10 p a ∧
    hodgeStar R p (component10 p a * component01 p b - component01 p b * component10 p a) =
      component10 p a * component01 p b + component01 p b * component10 p a ∧
    hodgeStar R p (component10 p a + component01 p b) =
      component10 p a - component01 p b ∧
    hodgeStar R p (component10 p a - component01 p b) =
      component10 p a + component01 p b :=
  ⟨reflection_mul_mass hp a b, reflection_mul_spin hp a b,
    reflection_mul_sum hp a b, reflection_mul_difference hp a b⟩

/-- The `Φ`-sandwich of the grading: `Φ S Φ = -(V S)`. -/
theorem sum_sandwich_reflection :
    (component10 p a + component01 p b) * reflection p * (component10 p a + component01 p b) =
      -((component10 p a * component01 p b + component01 p b * component10 p a) *
        reflection p) := by
  rw [sum_mul_reflection hp, mass_mul_reflection hp, neg_mul,
    difference_mul_sum_eq_spin (component10_sq_zero hp a) (component01_sq_zero hp b)]

/-- The `J`-sandwich of the grading: `J S (-J) = -(V S)`. -/
theorem difference_sandwich_reflection :
    (component10 p a - component01 p b) * reflection p * -(component10 p a - component01 p b) =
      -((component10 p a * component01 p b + component01 p b * component10 p a) *
        reflection p) := by
  rw [difference_mul_reflection hp, mass_mul_reflection hp, neg_mul,
    sum_mul_neg_difference_eq_spin (component10_sq_zero hp a) (component01_sq_zero hp b)]

/-- The `Σ`-sandwich of the grading: `Σ S Σ = V² S`. -/
theorem spin_sandwich_reflection :
    (component10 p a * component01 p b - component01 p b * component10 p a) * reflection p *
        (component10 p a * component01 p b - component01 p b * component10 p a) =
      (component10 p a * component01 p b + component01 p b * component10 p a) *
        (component10 p a * component01 p b + component01 p b * component10 p a) *
        reflection p := by
  rw [spin_mul_reflection hp, mul_assoc _ _ (reflection p), mass_mul_reflection hp]

end OrientationGrading

/-! ### Graded derivations and the Hodge-conjugate codifferential -/

section GradedDerivation

variable (R)

/-- The graded derivation `d_x y = x y - (S y S) x`. -/
def gradedDeriv (S x : A) : Module.End R A :=
  LinearMap.mulLeft R x - sandwichOp R S (S * x)

/-- The graded codifferential `d̄_x y = x y + (S y S) x`. -/
def gradedCodiff (S x : A) : Module.End R A :=
  LinearMap.mulLeft R x + sandwichOp R S (S * x)

/-- The operator Hodge Laplacian `{d_x, d̄_x}`. -/
def gradedLaplacian (S x : A) : Module.End R A :=
  gradedDeriv R S x * gradedCodiff R S x + gradedCodiff R S x * gradedDeriv R S x

@[simp] theorem gradedDeriv_apply (S x y : A) :
    gradedDeriv R S x y = x * y - S * y * (S * x) := rfl

@[simp] theorem gradedCodiff_apply (S x y : A) :
    gradedCodiff R S x y = x * y + S * y * (S * x) := rfl

variable {R} {S x : A}

private theorem S_S_mul (hS : S * S = 1) (y : A) : S * (S * y) = y := by
  rw [← mul_assoc, hS, one_mul]

private theorem S_x_mul (hx : S * x = -(x * S)) (y : A) : S * (x * y) = -(x * (S * y)) := by
  rw [← mul_assoc, hx, neg_mul, mul_assoc]

variable (hS : S * S = 1) (hx : S * x = -(x * S))
include hS hx

/-- The codifferential is minus the `L_S`-conjugate of the derivation. -/
theorem gradedCodiff_eq_neg_conj :
    gradedCodiff R S x =
      -(LinearMap.mulLeft R S * gradedDeriv R S x * LinearMap.mulLeft R S) := by
  ext y
  change x * y + S * y * (S * x) = -(S * (x * (S * y) - S * (S * y) * (S * x)))
  simp only [mul_sub, mul_assoc, S_S_mul hS, S_x_mul hx, neg_sub, sub_neg_eq_add]
  abel

/-- The derivation is minus the `L_S`-conjugate of the codifferential. -/
theorem gradedDeriv_eq_neg_conj :
    gradedDeriv R S x =
      -(LinearMap.mulLeft R S * gradedCodiff R S x * LinearMap.mulLeft R S) := by
  ext y
  change x * y - S * y * (S * x) = -(S * (x * (S * y) + S * (S * y) * (S * x)))
  simp only [mul_add, mul_assoc, S_S_mul hS, S_x_mul hx, neg_add, neg_neg]
  abel

/-- `d_x² = ad_{x²}`. -/
theorem gradedDeriv_mul_self :
    gradedDeriv R S x * gradedDeriv R S x = lieOp R (x * x) := by
  ext y
  change x * (x * y - S * y * (S * x)) - S * (x * y - S * y * (S * x)) * (S * x) =
    x * x * y - y * (x * x)
  simp only [mul_sub, sub_mul, mul_assoc, S_S_mul hS, S_x_mul hx, neg_mul, mul_neg]
  abel

/-- `d̄_x² = ad_{x²}`. -/
theorem gradedCodiff_mul_self :
    gradedCodiff R S x * gradedCodiff R S x = lieOp R (x * x) := by
  ext y
  change x * (x * y + S * y * (S * x)) + S * (x * y + S * y * (S * x)) * (S * x) =
    x * x * y - y * (x * x)
  simp only [mul_add, add_mul, mul_assoc, S_S_mul hS, S_x_mul hx, neg_mul, mul_neg]
  abel

/-- The Hodge Laplacian `{d_x, d̄_x}` is twice Jordan multiplication by `x²`. -/
theorem gradedDeriv_anticomm_codiff :
    gradedDeriv R S x * gradedCodiff R S x + gradedCodiff R S x * gradedDeriv R S x =
      (2 : ℕ) • jordanOp R (x * x) := by
  ext y
  change x * (x * y + S * y * (S * x)) - S * (x * y + S * y * (S * x)) * (S * x) +
      (x * (x * y - S * y * (S * x)) + S * (x * y - S * y * (S * x)) * (S * x)) =
    (2 : ℕ) • (x * x * y + y * (x * x))
  simp only [mul_add, mul_sub, add_mul, sub_mul, mul_assoc, S_S_mul hS, S_x_mul hx,
    neg_mul, mul_neg, two_nsmul]
  abel

/-- The Hodge Laplacian is twice the Jordan action of `x²`; its action is
`2 • (x² y + y x²)`, not left multiplication by `2x²`. -/
theorem gradedLaplacian_eq_two_jordan :
    gradedLaplacian R S x = (2 : ℕ) • jordanOp R (x * x) := by
  exact gradedDeriv_anticomm_codiff hS hx

/-- The Laplacian generated by `d_x` and `⋆ = L_S` alone:
`-(d ⋆ d ⋆ + ⋆ d ⋆ d) = 2 • jordanOp (x²)`. -/
theorem hodge_laplacian_from_star :
    -(gradedDeriv R S x * (LinearMap.mulLeft R S * gradedDeriv R S x * LinearMap.mulLeft R S))
      - (LinearMap.mulLeft R S * gradedDeriv R S x * LinearMap.mulLeft R S) *
        gradedDeriv R S x =
      (2 : ℕ) • jordanOp R (x * x) := by
  ext y
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, Module.End.mul_apply,
    LinearMap.mulLeft_apply, gradedDeriv_apply, LinearMap.smul_apply, jordanOp,
    LinearMap.add_apply, LinearMap.mulRight_apply]
  simp only [mul_sub, sub_mul, mul_assoc, S_S_mul hS, S_x_mul hx, mul_neg, neg_neg,
    two_nsmul]
  abel

end GradedDerivation

/-! ### Instantiation at the Peirce corner generators `Φ` and `J` -/

section CornerCodifferential

variable {p : A} (hp : p * p = p) (a b : A)
include hp

theorem reflection_anticomm_sum :
    reflection p * (component10 p a + component01 p b) =
      -((component10 p a + component01 p b) * reflection p) := by
  rw [reflection_mul_sum hp, sum_mul_reflection hp, neg_neg]

theorem reflection_anticomm_difference :
    reflection p * (component10 p a - component01 p b) =
      -((component10 p a - component01 p b) * reflection p) := by
  rw [reflection_mul_difference hp, difference_mul_reflection hp, neg_neg]

/-- `d̄_Φ = -(⋆ d_Φ ⋆)` for the corner generator `Φ`. -/
theorem sum_codiff_eq_neg_star_conj :
    gradedCodiff R (reflection p) (component10 p a + component01 p b) =
      -(hodgeStar R p * gradedDeriv R (reflection p) (component10 p a + component01 p b) *
        hodgeStar R p) :=
  gradedCodiff_eq_neg_conj (reflection_sq hp) (reflection_anticomm_sum hp a b)

/-- `d̄_J = -(⋆ d_J ⋆)` for the corner generator `J`. -/
theorem difference_codiff_eq_neg_star_conj :
    gradedCodiff R (reflection p) (component10 p a - component01 p b) =
      -(hodgeStar R p * gradedDeriv R (reflection p) (component10 p a - component01 p b) *
        hodgeStar R p) :=
  gradedCodiff_eq_neg_conj (reflection_sq hp) (reflection_anticomm_difference hp a b)

/-- The `Φ`-Hodge Laplacian is twice Jordan multiplication by the mass `V`. -/
theorem sum_hodge_laplacian :
    gradedDeriv R (reflection p) (component10 p a + component01 p b) *
        gradedCodiff R (reflection p) (component10 p a + component01 p b) +
      gradedCodiff R (reflection p) (component10 p a + component01 p b) *
        gradedDeriv R (reflection p) (component10 p a + component01 p b) =
      (2 : ℕ) • jordanOp R
        (component10 p a * component01 p b + component01 p b * component10 p a) := by
  have hsq : (component10 p a + component01 p b) * (component10 p a + component01 p b) =
      component10 p a * component01 p b + component01 p b * component10 p a := by
    noncomm_ring [component10_sq_zero hp a, component01_sq_zero hp b]
  rw [gradedDeriv_anticomm_codiff (reflection_sq hp) (reflection_anticomm_sum hp a b), hsq]

/-- The `J`-Hodge Laplacian is minus twice Jordan multiplication by `V`. -/
theorem difference_hodge_laplacian :
    gradedDeriv R (reflection p) (component10 p a - component01 p b) *
        gradedCodiff R (reflection p) (component10 p a - component01 p b) +
      gradedCodiff R (reflection p) (component10 p a - component01 p b) *
        gradedDeriv R (reflection p) (component10 p a - component01 p b) =
      -((2 : ℕ) • jordanOp R
        (component10 p a * component01 p b + component01 p b * component10 p a)) := by
  have hsq : (component10 p a - component01 p b) * (component10 p a - component01 p b) =
      -(component10 p a * component01 p b + component01 p b * component10 p a) := by
    noncomm_ring [component10_sq_zero hp a, component01_sq_zero hp b]
  rw [gradedDeriv_anticomm_codiff (reflection_sq hp) (reflection_anticomm_difference hp a b),
    hsq]
  ext y
  change (2 : ℕ) • (-(component10 p a * component01 p b + component01 p b * component10 p a) * y +
      y * -(component10 p a * component01 p b + component01 p b * component10 p a)) =
    -((2 : ℕ) • ((component10 p a * component01 p b + component01 p b * component10 p a) * y +
      y * (component10 p a * component01 p b + component01 p b * component10 p a)))
  noncomm_ring

end CornerCodifferential

end InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Core.IdempotentCartan

/-!
# Lie--Jordan endomorphisms without a commutativity hypothesis

The carrier is the full associative algebra `A`, in particular a full matrix
algebra, and the operators belong to the native endomorphism ring `Module.End`.
These are algebraic operators, not affine connections on a statistical manifold.
No metric, torsion, or differential-geometric curvature is asserted by naming.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordan

open InfoGeometry.Core.IdempotentCartan
open InfoGeometry.Core.PeirceDecomposition

variable (R : Type*) [CommRing R] {A : Type*} [Ring A] [Algebra R A]

/-- The inner derivation, bundled as a native linear endomorphism. -/
def lieOp (H : A) : Module.End R A :=
  LinearMap.mulLeft R H - LinearMap.mulRight R H

/-- Unnormalized Jordan multiplication on the full associative algebra. -/
def jordanOp (S : A) : Module.End R A :=
  LinearMap.mulLeft R S + LinearMap.mulRight R S

/-- The plus member of an algebraic Lie--Jordan pair. -/
def plus (H S : A) : Module.End R A := lieOp R H + jordanOp R S

/-- The minus member of an algebraic Lie--Jordan pair. -/
def minus (H S : A) : Module.End R A := lieOp R H - jordanOp R S

@[simp] theorem lieOp_apply (H X : A) : lieOp R H X = H * X - X * H := rfl

@[simp] theorem jordanOp_apply (S X : A) : jordanOp R S X = S * X + X * S := rfl

@[simp] theorem plus_apply (H S X : A) :
    plus R H S X = (H * X - X * H) + (S * X + X * S) := rfl

@[simp] theorem minus_apply (H S X : A) :
    minus R H S X = (H * X - X * H) - (S * X + X * S) := rfl

/-- The midpoint isolates the Lie part, without dividing by two. -/
theorem plus_add_minus (H S : A) :
    plus R H S + minus R H S = lieOp R H + lieOp R H := by
  unfold plus minus
  abel

/-- The difference isolates the Jordan part, in every characteristic. -/
theorem plus_sub_minus (H S : A) :
    plus R H S - minus R H S = jordanOp R S + jordanOp R S := by
  unfold plus minus
  abel

/-- Left multiplication is recovered with its full noncommutative order. -/
theorem plus_self (H : A) :
    plus R H H = LinearMap.mulLeft R H + LinearMap.mulLeft R H := by
  ext X
  change (H * X - X * H) + (H * X + X * H) = H * X + H * X
  abel

/-- The other homogeneous operator is negative right multiplication. -/
theorem minus_self (H : A) :
    minus R H H = -(LinearMap.mulRight R H + LinearMap.mulRight R H) := by
  ext X
  change (H * X - X * H) - (H * X + X * H) = -(X * H + X * H)
  abel

/-- The inner derivation of an idempotent has the Peirce kernel/range split
as a native endomorphism: it kills the even part, while its square fixes the
odd part. Together with `even_add_odd`, this is the algebraic Drazin split of
`ad_p` without choosing coordinates or dividing by two. -/
theorem idempotent_adjoint_peirce_split {p x : A} (hp : p * p = p) :
    evenPart p x + oddPart p x = x ∧
    lieOp R p (evenPart p x) = 0 ∧
    lieOp R p (lieOp R p (oddPart p x)) = oddPart p x := by
  have hpEven : p * evenPart p x = evenPart p x * p := by
    simp only [evenPart, component11, component00, complementIdempotent]
    noncomm_ring [hp, InfoGeometry.Core.PeirceDecomposition.idempotent_mul_nested p hp]
  refine ⟨even_add_odd p x, ?_, ?_⟩
  · change p * evenPart p x - evenPart p x * p = 0
    exact sub_eq_zero.mpr hpEven
  · change p * (p * oddPart p x - oddPart p x * p) -
      (p * oddPart p x - oddPart p x * p) * p = oddPart p x
    calc
      _ = oddPart p (oddPart p x) :=
        (odd_eq_double_commutator hp (oddPart p x)).symm
      _ = oddPart p x := (projection_laws hp x).2.2.2

/-- The two directed Peirce transition operators are square-zero root vectors
for the idempotent's inner derivation: the `10` corner has weight `+1` and the
`01` corner has weight `-1`. -/
theorem idempotent_peirce_root_operator_actions {p x : A}
    (hp : p * p = p) :
    component10 p x * component10 p x = 0 ∧
    component01 p x * component01 p x = 0 ∧
    lieOp R p (component10 p x) = component10 p x ∧
    lieOp R p (component01 p x) = -component01 p x := by
  have hSquares := InfoGeometry.Core.IdempotentCartan.corners_square_zero hp x
  have hForward : lieOp R p (component10 p x) = component10 p x := by
    change p * component10 p x - component10 p x * p = component10 p x
    simp only [component10, complementIdempotent]
    noncomm_ring [hp,
      InfoGeometry.Core.PeirceDecomposition.idempotent_mul_nested p hp]
  have hBackward : lieOp R p (component01 p x) = -component01 p x := by
    change p * component01 p x - component01 p x * p = -component01 p x
    simp only [component01, complementIdempotent]
    noncomm_ring [hp,
      InfoGeometry.Core.PeirceDecomposition.idempotent_mul_nested p hp]
  exact ⟨hSquares.1, hSquares.2, hForward, hBackward⟩

/-- The plus/minus Lie--Jordan pair is dual under every cyclic additive
functional applied to the product pairing. The functional is only a readout;
the states and actions remain elements and endomorphisms of `A`. -/
theorem plus_minus_cyclic_pairing_compatibility
    (τ : A →+ R) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (H S X Y : A) :
    τ (plus R H S X * Y) + τ (X * minus R H S Y) = 0 := by
  have hH : τ ((H * X) * Y) = τ ((X * Y) * H) := by
    calc
      τ ((H * X) * Y) = τ (H * (X * Y)) := by rw [mul_assoc]
      _ = τ ((X * Y) * H) := hτ H (X * Y)
  have hS : τ ((S * X) * Y) = τ ((X * Y) * S) := by
    calc
      τ ((S * X) * Y) = τ (S * (X * Y)) := by rw [mul_assoc]
      _ = τ ((X * Y) * S) := hτ S (X * Y)
  rw [plus_apply, minus_apply]
  simp only [sub_mul, add_mul, mul_add, mul_sub, map_add, map_sub]
  rw [hH, hS]
  simp only [mul_assoc]
  abel

/-- Commutators of inner derivations are inner derivations. -/
theorem lie_lie (H K : A) :
    lieOp R H * lieOp R K - lieOp R K * lieOp R H =
      lieOp R (H * K - K * H) := by
  ext X
  change H * (K * X - X * K) - (K * X - X * K) * H -
      (K * (H * X - X * H) - (H * X - X * H) * K) =
    (H * K - K * H) * X - X * (H * K - K * H)
  noncomm_ring

/-- The mixed commutator is Jordan multiplication by the generator defect. -/
theorem lie_jordan (H S : A) :
    lieOp R H * jordanOp R S - jordanOp R S * lieOp R H =
      jordanOp R (H * S - S * H) := by
  ext X
  change H * (S * X + X * S) - (S * X + X * S) * H -
      (S * (H * X - X * H) + (H * X - X * H) * S) =
    (H * S - S * H) * X + X * (H * S - S * H)
  noncomm_ring

/-- Two Jordan superoperators generate a Lie superoperator. -/
theorem jordan_jordan (S T : A) :
    jordanOp R S * jordanOp R T - jordanOp R T * jordanOp R S =
      lieOp R (S * T - T * S) := by
  ext X
  change S * (T * X + X * T) + (T * X + X * T) * S -
      (T * (S * X + X * S) + (S * X + X * S) * T) =
    (S * T - T * S) * X - X * (S * T - T * S)
  noncomm_ring

/-- Ordered composition retains the positive mixed term. -/
theorem minus_mul_plus (H S : A) :
    minus R H S * plus R H S =
      lieOp R H * lieOp R H - jordanOp R S * jordanOp R S +
        jordanOp R (H * S - S * H) := by
  calc
    minus R H S * plus R H S =
        lieOp R H * lieOp R H - jordanOp R S * jordanOp R S +
          (lieOp R H * jordanOp R S - jordanOp R S * lieOp R H) := by
      unfold minus plus
      simp only [sub_mul, mul_add, add_mul, mul_sub]
      abel
    _ = _ := by rw [lie_jordan]

/-- Reversing composition reverses the mixed term. -/
theorem plus_mul_minus (H S : A) :
    plus R H S * minus R H S =
      lieOp R H * lieOp R H - jordanOp R S * jordanOp R S -
        jordanOp R (H * S - S * H) := by
  calc
    plus R H S * minus R H S =
        lieOp R H * lieOp R H - jordanOp R S * jordanOp R S -
          (lieOp R H * jordanOp R S - jordanOp R S * lieOp R H) := by
      unfold plus minus
      simp only [sub_mul, mul_add, add_mul, mul_sub]
      abel
    _ = _ := by rw [lie_jordan]

/-- An exact defect formula, not a commuting-generator specialization. -/
theorem pair_commutator (H S : A) :
    minus R H S * plus R H S - plus R H S * minus R H S =
      jordanOp R (H * S - S * H) + jordanOp R (H * S - S * H) := by
  rw [minus_mul_plus, plus_mul_minus]
  abel

/-- Algebraic curvature of two plus operators, including every cross-term. -/
theorem plus_curvature (H S K T : A) :
    plus R H S * plus R K T - plus R K T * plus R H S =
      lieOp R ((H * K - K * H) + (S * T - T * S)) +
        jordanOp R ((H * T - T * H) + (S * K - K * S)) := by
  ext X
  change
    (H * ((K * X - X * K) + (T * X + X * T)) -
      ((K * X - X * K) + (T * X + X * T)) * H) +
    (S * ((K * X - X * K) + (T * X + X * T)) +
      ((K * X - X * K) + (T * X + X * T)) * S) -
    ((K * ((H * X - X * H) + (S * X + X * S)) -
      ((H * X - X * H) + (S * X + X * S)) * K) +
    (T * ((H * X - X * H) + (S * X + X * S)) +
      ((H * X - X * H) + (S * X + X * S)) * T)) =
    (((H * K - K * H) + (S * T - T * S)) * X -
      X * ((H * K - K * H) + (S * T - T * S))) +
    (((H * T - T * H) + (S * K - K * S)) * X +
      X * ((H * T - T * H) + (S * K - K * S)))
  noncomm_ring

/-- The pair is natural under actual algebra homomorphisms. -/
theorem map_plus {B : Type*} [Ring B] [Algebra R B]
    (f : A →ₐ[R] B) (H S X : A) :
    f (plus R H S X) = plus R (f H) (f S) (f X) := by
  simp only [plus_apply, map_add, map_sub, map_mul]

theorem map_minus {B : Type*} [Ring B] [Algebra R B]
    (f : A →ₐ[R] B) (H S X : A) :
    f (minus R H S X) = minus R (f H) (f S) (f X) := by
  simp only [minus_apply, map_add, map_sub, map_mul]

/-- The actual linear-map intertwining square for the plus operator. -/
theorem intertwine_plus {B : Type*} [Ring B] [Algebra R B]
    (f : A →ₐ[R] B) (H S : A) :
    f.toLinearMap.comp (plus R H S) =
      (plus R (f H) (f S)).comp f.toLinearMap := by
  ext X
  exact map_plus R f H S X

end InfoGeometry.OperatorAlgebra.LieJordan

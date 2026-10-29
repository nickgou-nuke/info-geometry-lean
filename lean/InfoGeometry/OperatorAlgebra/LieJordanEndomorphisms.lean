/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Tactic.NoncommRing

/-!
# Lie--Jordan endomorphisms without a commutativity hypothesis

The carrier is the full associative algebra `A`, in particular a full matrix
algebra, and the operators belong to the native endomorphism ring `Module.End`.
These are algebraic operators, not affine connections on a statistical manifold.
No metric, torsion, or differential-geometric curvature is asserted by naming.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordan

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

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DualSeedPeirce

/-!
# Reflection contracts on the existing square-zero Peirce carrier

The source's reflection identities are algebraic. A Clifford signature,
a Pin bundle, and a geometric involution are not consequences of the seed
contract. In particular a spatial Clifford generator squaring to minus one
must not be identified with the symmetric Majorana generator.
-/

namespace InfoGeometry.Core.PeirceReflectionContracts

open InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Core.DiracSuperalgebra
open InfoGeometry.Singular.MoorePenrose

variable {A : Type*} [Ring A] {d b : A}

/-- Multiplication order and signature are retained explicitly. -/
theorem grading_products (h : IsDualSeedPair d b) :
    phasePolarization d b * transitionVelocity d b = wheelGenerator d b ∧
    transitionVelocity d b * phasePolarization d b = -wheelGenerator d b ∧
    wheelGenerator d b * phasePolarization d b = -transitionVelocity d b := by
  change (polePlus d b - poleMinus d b) * (d + b) = d - b ∧
    (d + b) * (polePlus d b - poleMinus d b) = -(d - b) ∧
    (d - b) * (polePlus d b - poleMinus d b) = -(d + b)
  simp only [sub_mul, mul_sub, add_mul, mul_add,
    h.pd, h.pb, h.qd, h.qb, h.dp, h.bp, h.dq, h.bq]
  constructor <;> try constructor <;> abel

/-- Conjugation on the active corner exchanges its two idempotents. -/
theorem reflection_exchange (h : IsDualSeedPair d b) :
    transitionVelocity d b * polePlus d b * transitionVelocity d b = poleMinus d b ∧
    transitionVelocity d b * poleMinus d b * transitionVelocity d b = polePlus d b ∧
    transitionVelocity d b * phasePolarization d b * transitionVelocity d b =
      -phasePolarization d b := by
  have hp : transitionVelocity d b * polePlus d b * transitionVelocity d b =
      poleMinus d b := by
    change (d + b) * polePlus d b * (d + b) = b * d
    simp only [add_mul, h.dp, h.bp, zero_add, mul_add, h.b_sq, add_zero]
  have hq : transitionVelocity d b * poleMinus d b * transitionVelocity d b =
      polePlus d b := by
    change (d + b) * poleMinus d b * (d + b) = d * b
    simp only [add_mul, h.dq, h.bq, add_zero, mul_add, h.d_sq, zero_add]
  refine ⟨hp, hq, ?_⟩
  change _ * (polePlus d b - poleMinus d b) * _ = -(polePlus d b - poleMinus d b)
  rw [mul_sub, sub_mul, hp, hq]
  abel

/-- The even and odd combinations have opposite reflection parity. -/
theorem reflection_generator_parities (h : IsDualSeedPair d b) :
    transitionVelocity d b * transitionVelocity d b * transitionVelocity d b =
      transitionVelocity d b ∧
    transitionVelocity d b * wheelGenerator d b * transitionVelocity d b =
      -wheelGenerator d b := by
  constructor
  · rw [h.clifford_squares.2.1]
    change (polePlus d b + poleMinus d b) * (d + b) = d + b
    simp only [add_mul, mul_add, h.pd, h.pb, h.qd, h.qb, add_zero, zero_add]
  · calc
      _ = (-(phasePolarization d b)) * transitionVelocity d b := by
        have hqj : transitionVelocity d b * wheelGenerator d b =
            -phasePolarization d b := by
          change (d + b) * (d - b) = -(d * b - b * d)
          rw [add_mul, mul_sub, mul_sub, h.d_sq, h.b_sq]
          abel
        rw [hqj]
      _ = -wheelGenerator d b := by rw [neg_mul, (grading_products h).1]

/-- The paper's minus-square spatial convention produces a plus-square reflection. -/
theorem spatial_convention (h : IsDualSeedPair d b) :
    (wheelGenerator d b * phasePolarization d b) *
      (wheelGenerator d b * phasePolarization d b) = carrierSupport d b := by
  rw [(grading_products h).2.2, neg_mul_neg, h.clifford_squares.2.1]

/-- Both star statements require the adjoint-partner hypothesis. -/
theorem reflection_star [StarRing A] (hdual : b = star d) :
    star (transitionVelocity d b) = transitionVelocity d b ∧
    star (wheelGenerator d b) = -wheelGenerator d b :=
  majorana_star_symmetry hdual

/-- Hermiticity only gives a plus square after a separate normalization law. -/
theorem selfAdjoint_square_of_normalized [StarRing A] {r e : A}
    (hs : star r = r) (hn : r * star r = e) : r * r = e := by
  simpa only [hs] using hn

/-- A scalar phase squaring to minus one changes the supported reflection square. -/
theorem phase_twisted_square {R : Type*} [CommRing R] [Algebra R A]
    (h : IsDualSeedPair d b) (z : R) (hz : z * z = -1) :
    (z • transitionVelocity d b) * (z • transitionVelocity d b) =
      -carrierSupport d b := by
  rw [smul_mul_smul, hz, h.clifford_squares.2.1, neg_one_smul]

section Module

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- Pure left-sector vectors are sent into the opposite sector. -/
theorem pure_left_reflection_projection (h : IsDualSeedPair d b) {v : M}
    (hv : polePlus d b • v = v) :
    polePlus d b • (transitionVelocity d b • v) = 0 := by
  have hc : polePlus d b * transitionVelocity d b * polePlus d b = 0 := by
    change polePlus d b * (d + b) * polePlus d b = 0
    simp only [mul_add, add_mul, h.pd, h.pb, h.dp, zero_mul, add_zero]
  calc
    _ = (polePlus d b * transitionVelocity d b * polePlus d b) • v := by
      simp only [mul_smul, hv]
    _ = 0 := by rw [hc, zero_smul]

/-- Neither reflection eigenvalue permits a nonzero pure left-sector vector. -/
theorem pure_left_eigenvector_zero (h : IsDualSeedPair d b) {v : M}
    (hv : polePlus d b • v = v)
    (he : transitionVelocity d b • v = v ∨ transitionVelocity d b • v = -v) :
    v = 0 := by
  have hz := pure_left_reflection_projection h hv
  rcases he with he | he
  · simpa only [he, hv] using hz
  · simpa only [he, smul_neg, hv, neg_eq_zero] using hz

/-- Spatial equivariance is not pointwise reflection invariance.
A globally pure section satisfying an exchanging boundary condition vanishes.
No topology or quotient space is assumed or constructed. -/
theorem pure_equivariant_field_zero (h : IsDualSeedPair d b)
    {X : Type*} (g : X → X) (ψ : X → M)
    (he : ∀ x, ψ (g x) = transitionVelocity d b • ψ x)
    (hp : ∀ x, polePlus d b • ψ x = ψ x) : ψ = 0 := by
  funext x
  have hz : transitionVelocity d b • ψ x = 0 := by
    calc
      _ = ψ (g x) := (he x).symm
      _ = polePlus d b • ψ (g x) := (hp (g x)).symm
      _ = 0 := by rw [he x]; exact pure_left_reflection_projection h (hp x)
  have hq : poleMinus d b • ψ x = 0 := by
    calc
      _ = poleMinus d b • (polePlus d b • ψ x) := by rw [hp x]
      _ = 0 := by rw [← mul_smul, h.qp, zero_smul]
  calc
    ψ x = carrierSupport d b • ψ x := by
      change ψ x = (polePlus d b + poleMinus d b) • ψ x
      rw [add_smul, hp x, hq, add_zero]
    _ = transitionVelocity d b • (transitionVelocity d b • ψ x) := by
      rw [← mul_smul, h.clifford_squares.2.1]
    _ = 0 := by rw [hz, smul_zero]

end Module

end InfoGeometry.Core.PeirceReflectionContracts

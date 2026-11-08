/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Core.IdempotentCartan
import InfoGeometry.Core.PeirceStarCharges
import InfoGeometry.OperatorAlgebra.PeirceQuantumGeometricTensor

/-!
# Finite orbit commutator Gramian in a noncommutative star algebra

This owner formalizes the algebraic positivity and Peirce block support of a
finite family of projection commutators. It supplies an operator-level
ingredient for orbit-curvature models. It does not assert a continuum
Yang--Mills theory or a spectral mass gap.
-/

namespace InfoGeometry.OperatorAlgebra.YangMillsOrbitGramian

open scoped BigOperators

variable {A ι : Type*} [Ring A]

/-- The orbit-direction commutator of a projection and a potential. -/
def orbitCommutator (p a : A) : A := p * a - a * p

/-- The single-direction orbit mass operator, written as an ordered Gramian.
For self-adjoint `p` and `a`, this is also `- [p,a]^2`. -/
def orbitMassMode [StarRing A] (p a : A) : A :=
  star (orbitCommutator p a) * orbitCommutator p a

/-- Forward Peirce corner of an operator relative to an idempotent. -/
def orbitPeirce10 (p a : A) : A := p * a * (1 - p)

/-- For a self-adjoint idempotent and self-adjoint potential, the orbit
commutator is skew-adjoint, so the mass operator is its negative square. -/
theorem orbitMassMode_eq_neg_commutator_sq [StarRing A] {p a : A}
    (hps : star p = p) (has : star a = a) :
    orbitMassMode p a = -(orbitCommutator p a * orbitCommutator p a) := by
  have hc : star (orbitCommutator p a) = -orbitCommutator p a := by
    calc
      star (orbitCommutator p a) = star a * star p - star p * star a := by
        simp [orbitCommutator, star_sub, star_mul]
      _ = a * p - p * a := by rw [has, hps]
      _ = -orbitCommutator p a := by
        unfold orbitCommutator
        abel
  unfold orbitMassMode
  rw [hc, neg_mul]

/-- For a self-adjoint idempotent and self-adjoint potential, the orbit mass
operator is the square of the generic Peirce odd component. This identifies
the positive Gramian with the operator-valued odd-square geometry. -/
theorem orbitMassMode_eq_odd_square [StarRing A] {p a : A}
    (hp : IsIdempotentElem p) (hps : IsSelfAdjoint p) (has : IsSelfAdjoint a) :
    orbitMassMode p a = (InfoGeometry.Core.PeirceGrading.odd p a) ^ 2 := by
  have hcomm := InfoGeometry.Core.PeirceStarCharges.commutator_square hp a
  have hbridge : orbitCommutator p a = ⁅p, a⁆ := by rfl
  calc
    orbitMassMode p a = -(orbitCommutator p a * orbitCommutator p a) :=
      orbitMassMode_eq_neg_commutator_sq hps.star_eq has.star_eq
    _ = -(⁅p, a⁆ ^ 2) := by rw [hbridge, pow_two]
    _ = (InfoGeometry.Core.PeirceGrading.odd p a) ^ 2 := by
      rw [hcomm, neg_neg]

/-- The single-direction orbit mass operator commutes with its projection.
This is a noncommutative Peirce support identity, with no commutativity
assumption on the potential. -/
theorem orbitMassMode_commutes_projection [StarRing A] {p a : A}
    (hp : p * p = p) (hps : star p = p) (has : star a = a) :
    p * orbitMassMode p a = orbitMassMode p a * p := by
  rw [orbitMassMode_eq_neg_commutator_sq hps has]
  have hEven :=
    InfoGeometry.OperatorAlgebra.PeirceQuantumGeometricTensor.tangent_product_commutes
      (p := p) hp a a
  simpa [InfoGeometry.OperatorAlgebra.PeirceQuantumGeometricTensor.peirceTangent,
    orbitCommutator, mul_neg, neg_mul] using congrArg Neg.neg hEven

/-- The physical Peirce corner of the orbit mass operator is the Gramian of
the forward transition block. -/
theorem orbitMassMode_core_eq_peirce_gram [StarRing A] {p a : A}
    (hp : p * p = p) (hps : star p = p) (has : star a = a) :
    p * orbitMassMode p a * p =
      orbitPeirce10 p a * star (orbitPeirce10 p a) := by
  let q : A := 1 - p
  let u : A := orbitPeirce10 p a
  let v : A := q * a * p
  have hpq : p * q = 0 := by dsimp [q]; noncomm_ring [hp]
  have hqp : q * p = 0 := by dsimp [q]; noncomm_ring [hp]
  have hpu : p * u = u := by
    dsimp [u, orbitPeirce10]
    calc
      p * (p * a * (1 - p)) = (p * p) * a * (1 - p) := by noncomm_ring
      _ = p * a * (1 - p) := by rw [hp]
  have hpv : p * v = 0 := by
    dsimp [v]
    calc
      p * (q * a * p) = (p * q) * a * p := by noncomm_ring
      _ = 0 := by rw [hpq]; simp
  have hup : u * p = 0 := by
    dsimp [u, orbitPeirce10]
    calc
      p * a * (1 - p) * p = p * a * ((1 - p) * p) := by noncomm_ring
      _ = 0 := by rw [show (1 - p) * p = 0 by noncomm_ring [hp]]; simp
  have hvp : v * p = v := by
    dsimp [v]
    calc
      (q * a * p) * p = q * a * (p * p) := by noncomm_ring
      _ = q * a * p := by rw [hp]
  have hu2 : u * u = 0 := by
    dsimp [u, orbitPeirce10]
    calc
      (p * a * (1 - p)) * (p * a * (1 - p)) =
          p * a * ((1 - p) * p) * a * (1 - p) := by noncomm_ring
      _ = 0 := by rw [show (1 - p) * p = 0 by noncomm_ring [hp]]; simp
  have hv2 : v * v = 0 := by
    dsimp [v]
    calc
      (q * a * p) * (q * a * p) = q * a * (p * q) * a * p := by noncomm_ring
      _ = 0 := by rw [hpq]; simp
  have hcomm : orbitCommutator p a = u - v := by
    dsimp [u, v, q, orbitPeirce10, orbitCommutator]
    noncomm_ring
  have hstar : star u = v := by
    dsimp [u, orbitPeirce10, v, q]
    calc
      star (p * a * (1 - p)) = (1 - p) * (a * p) := by
        simp [star_sub, star_mul, hps, has]
      _ = (1 - p) * a * p := by rw [mul_assoc]
  rw [orbitMassMode_eq_neg_commutator_sq hps has]
  rw [hcomm, hstar]
  rw [show orbitPeirce10 p a = u from rfl]
  change p * -((u - v) * (u - v)) * p = u * v
  noncomm_ring [hu2, hv2, hpu, hpv, hup, hvp]
  calc
    p * (u * v) = (p * u) * v := by rw [← mul_assoc]
    _ = u * v := by rw [hpu]

/-- Cyclic functionals assign equal mass to the two complementary Peirce
corners of a self-adjoint orbit mode. This generalizes the finite matrix trace
identity without imposing commutativity on the operator algebra. -/
theorem cyclicFunctional_orbit_mass_corner_equipartition [StarRing A]
    {S : Type*} [AddCommGroup S] (τ : A →+ S)
    (hτ : ∀ x y : A, τ (x * y) = τ (y * x))
    {p a : A} (hp : p * p = p) (hps : star p = p) (has : star a = a) :
    τ (p * orbitMassMode p a * p) =
      τ ((1 - p) * orbitMassMode p a * (1 - p)) := by
  let q : A := 1 - p
  have hq : q * q = q := by dsimp [q]; noncomm_ring [hp]
  have hqs : star q = q := by dsimp [q]; simp [star_sub, hps]
  have hcomm : orbitCommutator q a = -orbitCommutator p a := by
    dsimp [q]
    unfold orbitCommutator
    noncomm_ring
  have hmode : orbitMassMode q a = orbitMassMode p a := by
    unfold orbitMassMode
    rw [hcomm]
    simp
  have hcorner := orbitMassMode_core_eq_peirce_gram hq hqs has
  have hstar : star (orbitPeirce10 p a) = q * a * p := by
    calc
      star (orbitPeirce10 p a) = q * (a * p) := by
        dsimp [q]
        simp [orbitPeirce10, star_sub, star_mul, hps, has]
      _ = q * a * p := by rw [mul_assoc]
  have hstarq : star (orbitPeirce10 q a) = orbitPeirce10 p a := by
    dsimp [orbitPeirce10, q]
    simp [star_sub, star_mul, hps, has, sub_sub_cancel]
    rw [← mul_assoc]
  have hother :
      (1 - p) * orbitMassMode p a * (1 - p) =
        star (orbitPeirce10 p a) * orbitPeirce10 p a := by
    have hq_eq : q = 1 - p := rfl
    calc
      (1 - p) * orbitMassMode p a * (1 - p) =
          q * orbitMassMode q a * q := by rw [← hmode, hq_eq]
      _ = orbitPeirce10 q a * star (orbitPeirce10 q a) := hcorner
      _ = star (orbitPeirce10 p a) * orbitPeirce10 p a := by
        rw [hstarq, hstar]
        simp [orbitPeirce10, q, sub_sub_cancel]
  calc
    τ (p * orbitMassMode p a * p) =
        τ (orbitPeirce10 p a * star (orbitPeirce10 p a)) := by
          rw [orbitMassMode_core_eq_peirce_gram hp hps has]
    _ = τ (star (orbitPeirce10 p a) * orbitPeirce10 p a) :=
      hτ _ _
    _ = τ ((1 - p) * orbitMassMode p a * (1 - p)) := by rw [← hother]

/-- The cyclic Bianchi identity for commutator curvature, valid for arbitrary
operators in an associative ring. It is an algebraic identity and carries no
analytic or gauge-field existence assumptions. -/
theorem commutator_bianchi (x y z : A) :
    orbitCommutator x (orbitCommutator y z) +
      orbitCommutator y (orbitCommutator z x) +
      orbitCommutator z (orbitCommutator x y) = 0 := by
  simp only [orbitCommutator]
  noncomm_ring

/-- The finite orbit Gramian is the sum of `c† c` for the ordered commutators
`c = [p, aᵢ]`. -/
def orbitGramian [Fintype ι] [StarRing A] (p : A) (potential : ι → A) : A :=
  ∑ i, star (orbitCommutator p (potential i)) * orbitCommutator p (potential i)

/-- A nonzero orbit commutator certifies that the potential does not commute
with the projection. -/
theorem orbitCommutator_ne_zero_implies_not_commute {p a : A}
    (h : orbitCommutator p a ≠ 0) : ¬ Commute p a := by
  intro hcomm
  apply h
  exact sub_eq_zero.mpr hcomm.eq

/-- Covariant commutator integration by parts for any additive cyclic
functional. The identity preserves the operator order and requires no matrix
trace, inner product, or commutativity of the operators. -/
theorem cyclicFunctional_commutator_integration_by_parts
    {S : Type*} [AddCommGroup S] (τ : A →+ S)
    (hτ : ∀ x y : A, τ (x * y) = τ (y * x))
    (d f x : A) :
    τ (f * orbitCommutator d x) =
      -τ (orbitCommutator d f * x) := by
  have hcycle : τ (f * (x * d)) = τ (d * (f * x)) := by
    calc
      τ (f * (x * d)) = τ ((f * x) * d) := by rw [mul_assoc]
      _ = τ (d * (f * x)) := hτ _ _
  unfold orbitCommutator
  rw [mul_sub, map_sub]
  rw [hcycle, sub_mul, map_sub]
  rw [← mul_assoc f d x, ← mul_assoc d f x]
  abel

section Ordered

variable [StarRing A] [PartialOrder A] [StarOrderedRing A]

/-- A single orbit mass mode is nonnegative in any star-ordered associative
algebra, directly as an operator Gramian. -/
theorem orbitMassMode_nonneg (p a : A) : 0 ≤ orbitMassMode p a := by
  exact star_mul_self_nonneg _

/-- A finite orbit Gramian is nonnegative in any star-ordered associative
algebra. -/
theorem orbitGramian_nonneg [Fintype ι] (p : A) (potential : ι → A) :
    0 ≤ orbitGramian p potential := by
  unfold orbitGramian
  exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg _

end Ordered

section PeirceSupport

variable [StarRing A]

/-- Each orbit Gramian term is even for a self-adjoint idempotent, so the
finite sum commutes with that projection. No commutativity of the algebra or
of the potentials is assumed. -/
theorem orbitGramian_commutes_projection [Fintype ι] {p : A}
    (hp : p * p = p) (hstar : star p = p) (potential : ι → A) :
    Commute p (orbitGramian p potential) := by
  change p * orbitGramian p potential = orbitGramian p potential * p
  unfold orbitGramian
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [orbitCommutator, star_sub, star_mul, hstar]
  noncomm_ring [hp, InfoGeometry.Core.PeirceDecomposition.idempotent_mul_nested p hp]

end PeirceSupport

end InfoGeometry.OperatorAlgebra.YangMillsOrbitGramian

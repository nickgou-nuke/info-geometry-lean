/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.AmariParaKahlerConnectionSumDiffPoset

/-!
# Peirce Spine Granular Extensions

## BUCKET 1 — Kernel-verified identities
Square-zero pair formulas and the Peirce corner trace pairing are proved below.

## BUCKET 2 — Conditional consequences
The nonzero contact-square consequence requires the displayed nonzero contact premise.

## BUCKET 3 — Open interpretation
No analytic bundle, continuum limit, or physical interpretation is constructed here.

This file contains the deltas that are not supplied by the existing Peirce-Spine owners:
identities for an arbitrary pair of square-zero elements, and a conditional nonvanishing
consequence for the three-horizon contact wave. The Maurer–Cartan/bracket-table, parabolic
Poly24, and Amari/Bruhat results remain in their canonical owner module
`ParabolicMaurerCartanAndBruhatTransportPoset`; they are not duplicated here as theorem bundles.

The square-zero identities assert algebraic formulas only. They do not assert that the
metric or area element is nonzero. The separate contact theorem makes its nonzero premise
explicit.

## i. Overview

The finite-stage carrier is an arbitrary associative ring `B`; all constructions use its
noncommutative multiplication.

## ii. Key results

The module proves square-zero pair identities, a conditional nonzero contact-square implication,
and a cyclic trace corner-pairing identity under the stated trace and Peirce hypotheses.

## iii. Table of contents

1. Square-zero pair metric and area identities.
2. Contact-corner nonvanishing implication.
3. Cyclic trace corner pairing.

## iv. References

The contact-square identity reuses `three_horizon_weyl_parakahler_bridge` from
`AmariParaKahlerConnectionSumDiffPoset`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceSpineGranularExtensions

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.AmariParaKahlerConnectionSumDiffPoset

universe u
variable {B : Type u} [Ring B]

/-- Symmetric and skew combinations of two square-zero operators. -/
def PhiNil (Ep Em : B) : B := Ep + Em
/-- Skew difference of two square-zero operators. -/
def JNil (Ep Em : B) : B := Ep - Em
/-- Jordan sum, used as the metric operator for the square-zero pair. -/
def VNil (Ep Em : B) : B := anticomm Ep Em
/-- Lie commutator, used as the area operator for the square-zero pair. -/
def SigmaNil (Ep Em : B) : B := comm Ep Em

/-- For two square-zero elements, the symmetric and skew combinations square to
opposite values. Their common metric commutes with both generators, and the area
operator has the same square as the metric. These are universal noncommutative
identities and make no nonvanishing claim. -/
lemma square_zero_pair_metric_and_area_identities (Ep Em : B)
    (hEp : Ep * Ep = 0) (hEm : Em * Em = 0) :
    PhiNil Ep Em * PhiNil Ep Em = VNil Ep Em ∧
    JNil Ep Em * JNil Ep Em = -(VNil Ep Em) ∧
    comm Ep (VNil Ep Em) = 0 ∧ comm Em (VNil Ep Em) = 0 ∧
    SigmaNil Ep Em * SigmaNil Ep Em = VNil Ep Em * VNil Ep Em := by
  have hEp' : ∀ W : B, Ep * (Ep * W) = 0 := fun W => by
    rw [← mul_assoc, hEp, zero_mul]
  have hEm' : ∀ W : B, Em * (Em * W) = 0 := fun W => by
    rw [← mul_assoc, hEm, zero_mul]
  constructor
  · change (Ep + Em) * (Ep + Em) = Ep * Em + Em * Ep
    simp only [mul_add, add_mul, hEp, hEm]
    abel
  constructor
  · change (Ep - Em) * (Ep - Em) = -(Ep * Em + Em * Ep)
    simp only [sub_mul, mul_sub, hEp, hEm, neg_add_rev]
    abel
  constructor
  · change comm Ep (Ep * Em + Em * Ep) = 0
    unfold comm
    simp only [mul_add, add_mul, mul_assoc, hEp, hEp']
    simp
  constructor
  · change comm Em (Ep * Em + Em * Ep) = 0
    unfold comm
    simp only [mul_add, add_mul, mul_assoc, hEm, hEm']
    simp
  · change (Ep * Em - Em * Ep) * (Ep * Em - Em * Ep) =
      (Ep * Em + Em * Ep) * (Ep * Em + Em * Ep)
    simp [mul_add, add_mul, sub_mul, mul_sub, mul_assoc, hEp', hEm']

/-- A genuine nonzero three-horizon contact corner forces the corresponding Weyl
wave to have nonzero square. Nonvanishing is an explicit premise; it is not
deduced from square-zero hypotheses. -/
lemma nonzero_contact_corner_obstructs_weyl_square_zero
    (P1 P2 X Y : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0)
    (hcontact : P1 * X * (1 - P1 - P2) * Y * P2 ≠ 0) :
    (P1 * X * (1 - P1 - P2) + (1 - P1 - P2) * Y * P2) *
      (P1 * X * (1 - P1 - P2) + (1 - P1 - P2) * Y * P2) ≠ 0 := by
  have howner := three_horizon_weyl_parakahler_bridge P1 P2 X Y h1 h2 h12 h21
  have hsquare :
      (P1 * X * (1 - P1 - P2) + (1 - P1 - P2) * Y * P2) *
        (P1 * X * (1 - P1 - P2) + (1 - P1 - P2) * Y * P2) =
        P1 * X * (1 - P1 - P2) * Y * P2 := howner.2.2.2.2.1
  rw [hsquare]
  exact hcontact

/-- The cyclic trace pairing of a source-to-waist corner with a waist observable
vanishes. The algebraic reason is the reverse corner product `W₀ * F = 0`, followed
by cyclicity of the trace. This is a Peirce support identity; no positivity,
adjointness, or Hodge decomposition is assumed. -/
lemma three_horizon_cyclic_trace_corner_pairing_zero
    {M : Type u} [AddCommGroup M] (τ : CyclicTrace B M)
    (P1 P2 A Z : B)
    (h1 : P1 * P1 = P1) (h21 : P2 * P1 = 0) :
    let P0 := 1 - P1 - P2
    let F := P1 * A * P0
    let W0 := P0 * Z * P0
    τ.tr (F * W0) = 0 ∧ τ.tr (W0 * F) = 0 := by
  intro P0 F W0
  have hP0P1 : P0 * P1 = 0 := by
    dsimp only [P0]
    noncomm_ring [h1, h21]
  have hreverse : W0 * F = 0 := by
    dsimp only [W0, F]
    calc
      (P0 * Z * P0) * (P1 * A * P0) =
          (P0 * Z * (P0 * P1)) * A * P0 := by noncomm_ring
      _ = 0 := by rw [hP0P1]; simp
  have hzero : τ.tr (0 : B) = 0 := map_zero τ.tr
  constructor
  · calc
      τ.tr (F * W0) = τ.tr (W0 * F) := τ.cyclic F W0
      _ = τ.tr 0 := by rw [hreverse]
      _ = 0 := hzero
  · rw [hreverse, hzero]

end InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceSpineGranularExtensions

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TemperleyLiebJonesBridge

/-!
# Local Kauffman braid pair satisfies the Artin relation

This file proves a finite algebraic implication in an arbitrary associative
unital `ℂ`-algebra. The generators need not commute. The result is conditional
on the Temperley–Lieb relations and the stated scalar parameter identity; it
proves the local two-generator Artin relation. It does not establish
invertibility or distant-generator relations for a full braid-group
representation, and it does not identify a framing-anomaly term with a braid
operator.
-/

noncomputable section

namespace InfoGeometry.Canonical.TemperleyLiebKauffmanYangBaxter

open TemperleyLiebJonesBridge

variable {δ : ℂ} {R : Type*} [Ring R] [Algebra ℂ R]
variable (sys : TemperleyLiebSystem δ R) (a b : ℂ)

/-- The two local Kauffman braid operators associated to a TL pair. -/
def braid1 : R := a • (1 : R) + b • sys.e1

def braid2 : R := a • (1 : R) + b • sys.e2

/-- The exact defect of the braid relation before imposing the scalar
Kauffman parameter identity. The proof uses only the TL loop and contraction
relations, preserving the noncommutative order of `e1` and `e2`. -/
theorem braid_defect_eq_scalar_mul_generator_difference :
    braid1 sys a b * braid2 sys a b * braid1 sys a b -
        braid2 sys a b * braid1 sys a b * braid2 sys a b =
      (a ^ 2 * b + a * b ^ 2 * δ + b ^ 3) • (sys.e1 - sys.e2) := by
  dsimp [braid1, braid2]
  noncomm_ring [sys.self_loop_1, sys.self_loop_2,
    sys.contraction_121, sys.contraction_212,
    smul_add, add_smul, smul_smul]
  module

/-- A vanishing Kauffman coefficient implies the Artin/Yang–Baxter relation. -/
theorem yang_baxter_of_kauffman_coefficient
    (h : a ^ 2 * b + a * b ^ 2 * δ + b ^ 3 = 0) :
    braid1 sys a b * braid2 sys a b * braid1 sys a b =
      braid2 sys a b * braid1 sys a b * braid2 sys a b := by
  have hd := braid_defect_eq_scalar_mul_generator_difference sys a b
  rw [h, zero_smul, sub_eq_zero] at hd
  exact hd

/-- Kauffman specialization: reciprocal parameters and
`δ = -(a²+b²)` make the generic defect coefficient zero. -/
theorem yang_baxter_of_reciprocal_kauffman_parameters
    (hab : a * b = 1) (hδ : δ = -(a ^ 2 + b ^ 2)) :
    braid1 sys a b * braid2 sys a b * braid1 sys a b =
      braid2 sys a b * braid1 sys a b * braid2 sys a b := by
  apply yang_baxter_of_kauffman_coefficient sys a b
  rw [hδ]
  have hA : a ^ 3 * b ^ 2 = a := by
    calc
      a ^ 3 * b ^ 2 = a * (a * b) ^ 2 := by ring
      _ = a := by rw [hab]; ring
  have hB : a * b ^ 4 = b ^ 3 := by
    calc
      a * b ^ 4 = (a * b) * b ^ 3 := by ring
      _ = b ^ 3 := by rw [hab]; ring
  calc
    a ^ 2 * b + a * b ^ 2 * (-(a ^ 2 + b ^ 2)) + b ^ 3 =
        a ^ 2 * b - a * b ^ 2 * (a ^ 2 + b ^ 2) + b ^ 3 := by ring
    _ = a ^ 2 * b - (a ^ 3 * b ^ 2 + a * b ^ 4) + b ^ 3 := by ring
    _ = 0 := by
      rw [hA, hB]
      calc
        a ^ 2 * b - (a + b ^ 3) + b ^ 3 = a ^ 2 * b - a := by ring
        _ = a * (a * b - 1) := by ring
        _ = 0 := by rw [hab]; ring

end InfoGeometry.Canonical.TemperleyLiebKauffmanYangBaxter

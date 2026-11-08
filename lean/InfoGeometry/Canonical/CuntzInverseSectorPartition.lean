/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MoorePenroseDrazinChiralDefect
import InfoGeometry.Singular.MoorePenroseSectors
import InfoGeometry.Core.JordanAssociator

/-!
# Cuntz chiral inverse sectors, with the vacuum retained

This uses the actual Cuntz two-isometry operator carrier. Completeness is not
assumed: the boundary square is the excitation projection and its complement
is the Toeplitz vacuum. Chiral parity and the MP/Drazin commutator anomaly are
distinct operators. Triple products below are the existing chiral arrows.
-/

namespace InfoGeometry.Canonical.MoorePenroseDrazinChiralDefect

open FibonacciToeplitzCuntzRepresentationBridge
open InfoGeometry.Singular.MetricAlgebraicProjectionDefect
open InfoGeometry.Singular.Drazin

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A] [StarRing A]

/-- Source and target supports of the actual Cuntz chiral arrows are disjoint. -/
theorem chiral_supports_orthogonal (ck : CuntzTwoIsometry K A) :
    ePlus ck * eMinus ck = 0 ∧ eMinus ck * ePlus ck = 0 := by
  constructor
  · change (ck.S1 * star ck.S1) * (ck.S2 * star ck.S2) = 0
    calc
      _ = ck.S1 * (star ck.S1 * ck.S2) * star ck.S2 := by simp only [mul_assoc]
      _ = 0 := by rw [ck.S1_star_S2, mul_zero, zero_mul]
  · change (ck.S2 * star ck.S2) * (ck.S1 * star ck.S1) = 0
    calc
      _ = ck.S2 * (star ck.S2 * ck.S1) * star ck.S1 := by simp only [mul_assoc]
      _ = 0 := by rw [ck.S2_star_S1, mul_zero, zero_mul]

/-- Without completeness the boundary square is excitation, not the identity. -/
theorem chiral_boundary_square (ck : CuntzTwoIsometry K A) :
    (chiralParity ck)^2 = ePlus ck + eMinus ck := by
  have hs := InfoGeometry.Singular.ProjectionSectors.mp_supports (qPlus_moorePenrose ck)
  rw [qPlus_mul_qMinus, qMinus_mul_qPlus] at hs
  obtain ⟨hpm, hmp⟩ := chiral_supports_orthogonal ck
  unfold chiralParity
  noncomm_ring [hs.1.isIdempotentElem.eq, hs.2.isIdempotentElem.eq, hpm, hmp]

/-- The null sector is exactly the unfilled vacuum complement. -/
theorem chiral_null_sector (ck : CuntzTwoIsometry K A) :
    (1 - ePlus ck) * (1 - eMinus ck) = 1 - (ePlus ck + eMinus ck) := by
  noncomm_ring [(chiral_supports_orthogonal ck).1]

/-- The inverse-projector anomaly vanishes here even when chiral parity survives. -/
theorem chiral_pair_drazin_anomaly_zero (ck : CuntzTwoIsometry K A) :
    ChiralAnomaly (qPlus ck) (qMinus ck) 0 2
      (qPlus_moorePenrose ck) (qPlus_drazin_zero ck) = 0 := by
  simp [ChiralAnomaly, Drazin_Projector]

/-- In the complete nontrivial model, parity is nonzero despite the preceding zero anomaly. -/
theorem complete_chiralParity_ne_zero [Nontrivial A] (ck : CuntzTwoIsometry K A)
    (hc : ePlus ck + eMinus ck = 1) : chiralParity ck ≠ 0 := by
  intro hz
  have h := chiralParity_sq_one ck hc
  rw [hz, zero_mul] at h
  exact zero_ne_one h

/-- The anomaly derivation of the chiral triple contracts by the Penrose equation. -/
theorem chiral_triple_commutator (ck : CuntzTwoIsometry K A) (s : A) :
    commutatorDefect s (qPlus ck) =
      commutatorDefect s (qPlus ck) * qMinus ck * qPlus ck +
      qPlus ck * commutatorDefect s (qMinus ck) * qPlus ck +
      qPlus ck * qMinus ck * commutatorDefect s (qPlus ck) := by
  have h := InfoGeometry.Singular.ProjectionSectors.commutator_triple_product
    s (qPlus ck) (qMinus ck) (qPlus ck)
  rw [(qPlus_moorePenrose ck).aba_eq_a] at h
  exact h

end InfoGeometry.Canonical.MoorePenroseDrazinChiralDefect

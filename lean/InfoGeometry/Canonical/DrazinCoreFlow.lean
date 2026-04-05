import InfoGeometry.Canonical.InverseKernelAlgebra
import InfoGeometry.Meta.Architecture
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.NoncommRing

/-!
# InfoGeometry.Canonical.DrazinCoreFlow

Exact algebra of the Drazin core projector and its complementary nilpotent
sector.

This file stays at the operator-calculus level already justified by the repo:

- the Drazin projector and its complement commute with the base operator,
- the base operator splits as core part plus complementary nilpotent part,
- the two pieces multiply to zero in both orders,
- sufficiently high powers kill the complementary projector and the nilpotent
  part.
-/

open InfoGeometry.Canonical.Drazin

namespace InfoGeometry.Canonical.Drazin.IsDrazinInverse

section Generic

variable {R : Type*} [Ring R] {a b : R} {k : ℕ}

/-- The Drazin projector commutes with the base operator on the left/right. -/
theorem projection_mul_eq_mul_projection
    (h : IsDrazinInverse a b k) :
    projection a b * a = a * projection a b := by
  unfold projection
  calc
    (a * b) * a = a * (b * a) := by simp [mul_assoc]
    _ = a * (a * b) := by rw [h.comm.symm]

/-- The Drazin projector commutes with the base operator. -/
theorem commute_projection
    (h : IsDrazinInverse a b k) :
    Commute a (projection a b) := by
  unfold Commute
  simpa using (projection_mul_eq_mul_projection (h := h)).symm

/-- The complementary Drazin projector commutes with the base operator. -/
theorem commute_complementaryProjection
    (h : IsDrazinInverse a b k) :
    Commute a (complementaryProjection a b) := by
  unfold Commute complementaryProjection projection
  have hproj : a * (a * b) = (a * b) * a := by
    simpa [projection] using (projection_mul_eq_mul_projection (h := h)).symm
  calc
    a * (1 - a * b) = a - a * (a * b) := by rw [mul_sub, mul_one]
    _ = a - (a * b) * a := by rw [hproj]
    _ = (1 - a * b) * a := by rw [sub_mul, one_mul]

/-- The core piece is the base operator followed by the Drazin projector. -/
theorem core_eq_mul_projection
    (a b : R) :
    core a b = a * projection a b := by
  simp [core, projection, mul_assoc]

/-- The core piece is also the Drazin projector followed by the base operator. -/
theorem core_eq_projection_mul
    (h : IsDrazinInverse a b k) :
    core a b = projection a b * a := by
  rw [core_eq_mul_projection]
  symm
  exact projection_mul_eq_mul_projection (h := h)

/-- The nilpotent complementary piece is the base operator times the complementary projector. -/
theorem nilpotent_eq_mul_complementaryProjection
    (a b : R) :
    nilpotent a b = a * complementaryProjection a b := by
  unfold nilpotent core complementaryProjection projection
  noncomm_ring

/-- The nilpotent complementary piece is also the complementary projector times the base operator. -/
theorem nilpotent_eq_complementaryProjection_mul
    (h : IsDrazinInverse a b k) :
    nilpotent a b = complementaryProjection a b * a := by
  rw [nilpotent_eq_mul_complementaryProjection]
  exact (commute_complementaryProjection (h := h)).eq

/-- The base operator kills the complementary projector after sufficiently high powers. -/
theorem pow_mul_complementaryProjection_eq_zero_of_le
    (h : IsDrazinInverse a b k) {m : ℕ} (hm : k ≤ m) :
    a ^ m * complementaryProjection a b = 0 := by
  unfold complementaryProjection projection
  have hpow : a ^ m * (a * b) = a ^ (m + 1) * b := by
    calc
      a ^ m * (a * b) = (a ^ m * a) * b := by simp [mul_assoc]
      _ = a ^ (m + 1) * b := by rw [pow_succ]
  calc
    a ^ m * (1 - a * b) = a ^ m - a ^ m * (a * b) := by
      rw [mul_sub, mul_one]
    _ = a ^ m - a ^ (m + 1) * b := by rw [hpow]
    _ = a ^ m - a ^ m := by
      rw [power_le (h := h) hm]
    _ = 0 := sub_self (a ^ m)

/-- Positive powers of the complementary projector stabilize to itself. -/
theorem complementaryProjection_pow_succ
    (h : IsDrazinInverse a b k) (m : ℕ) :
    complementaryProjection a b ^ (m + 1) = complementaryProjection a b := by
  induction m with
  | zero =>
      simp
  | succ m hm =>
      calc
        complementaryProjection a b ^ (m + 1 + 1)
            = complementaryProjection a b ^ (m + 1) * complementaryProjection a b := by
                rw [pow_succ]
        _ = complementaryProjection a b * complementaryProjection a b := by
              rw [hm]
        _ = complementaryProjection a b := complementaryProjection_is_idempotent (h := h)

/-- Positive powers of the nilpotent piece reduce to a power of the base operator times the complement. -/
theorem nilpotent_pow_succ_eq_pow_mul_complementaryProjection
    (h : IsDrazinInverse a b k) (m : ℕ) :
    nilpotent a b ^ (m + 1) = a ^ (m + 1) * complementaryProjection a b := by
  rw [nilpotent_eq_mul_complementaryProjection]
  have hcomm : Commute a (complementaryProjection a b) :=
    commute_complementaryProjection (h := h)
  calc
    (a * complementaryProjection a b) ^ (m + 1)
        = a ^ (m + 1) * complementaryProjection a b ^ (m + 1) := by
            simpa using hcomm.mul_pow (m + 1)
    _ = a ^ (m + 1) * complementaryProjection a b := by
          rw [complementaryProjection_pow_succ (h := h) m]

/-- The complementary nilpotent piece becomes zero after sufficiently high powers. -/
theorem nilpotent_pow_succ_eq_zero_of_le
    (h : IsDrazinInverse a b k) {m : ℕ} (hm : k ≤ m + 1) :
    nilpotent a b ^ (m + 1) = 0 := by
  rw [nilpotent_pow_succ_eq_pow_mul_complementaryProjection (h := h) m]
  exact pow_mul_complementaryProjection_eq_zero_of_le (h := h) hm

end Generic
end InfoGeometry.Canonical.Drazin.IsDrazinInverse

section Certified

open InfoGeometry.Canonical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace InfoGeometry.Canonical.CertifiedInverseKernel

variable (CIK : CertifiedInverseKernel E)

/-- The Drazin-stable core projector. -/
@[rep_depth operator]
abbrev drazinCoreProj : E →L[ℝ] E :=
  CIK.spectralProjector

/-- The complementary nilpotent projector. -/
@[rep_depth operator]
abbrev nilpotentProj : E →L[ℝ] E :=
  CIK.spectralComplementaryProjector

/-- The operator restricted to the Drazin-stable core. -/
@[rep_depth operator]
def corePart : E →L[ℝ] E :=
  CIK.A * CIK.drazinCoreProj

/-- The operator restricted to the complementary nilpotent sector. -/
@[rep_depth operator]
def nilpotentPart : E →L[ℝ] E :=
  CIK.A * CIK.nilpotentProj

@[rep_depth operator, simp] theorem A_mul_drazinCoreProj_eq_drazinCoreProj_mul_A :
    CIK.A * CIK.drazinCoreProj = CIK.drazinCoreProj * CIK.A := by
  change CIK.A * IsDrazinInverse.projection CIK.A CIK.A_D =
      IsDrazinInverse.projection CIK.A CIK.A_D * CIK.A
  simpa using (IsDrazinInverse.projection_mul_eq_mul_projection (h := CIK.hDrazin)).symm

@[rep_depth operator, simp] theorem A_mul_nilpotentProj_eq_nilpotentProj_mul_A :
    CIK.A * CIK.nilpotentProj = CIK.nilpotentProj * CIK.A := by
  change CIK.A * IsDrazinInverse.complementaryProjection CIK.A CIK.A_D =
      IsDrazinInverse.complementaryProjection CIK.A CIK.A_D * CIK.A
  simpa using (IsDrazinInverse.commute_complementaryProjection (h := CIK.hDrazin)).eq

@[rep_depth operator, simp] theorem corePart_eq_drazinCoreProj_mul_A :
    CIK.corePart = CIK.drazinCoreProj * CIK.A := by
  unfold CertifiedInverseKernel.corePart
  rw [CIK.A_mul_drazinCoreProj_eq_drazinCoreProj_mul_A]

@[rep_depth operator, simp] theorem nilpotentPart_eq_nilpotentProj_mul_A :
    CIK.nilpotentPart = CIK.nilpotentProj * CIK.A := by
  unfold CertifiedInverseKernel.nilpotentPart
  rw [CIK.A_mul_nilpotentProj_eq_nilpotentProj_mul_A]

@[rep_depth operator] theorem A_eq_corePart_add_nilpotentPart :
    CIK.A = CIK.corePart + CIK.nilpotentPart := by
  unfold CertifiedInverseKernel.corePart CertifiedInverseKernel.nilpotentPart
  calc
    CIK.A = CIK.A * (CIK.drazinCoreProj + CIK.nilpotentProj) := by
      rw [CIK.spectralProjector_add_spectralComplementaryProjector]
      simp
    _ = CIK.A * CIK.drazinCoreProj + CIK.A * CIK.nilpotentProj := by
      rw [mul_add]
    _ = CIK.corePart + CIK.nilpotentPart := by rfl

@[rep_depth operator] theorem corePart_mul_nilpotentPart_eq_zero :
    CIK.corePart * CIK.nilpotentPart = 0 := by
  rw [CIK.corePart_eq_drazinCoreProj_mul_A, CIK.nilpotentPart_eq_nilpotentProj_mul_A]
  have hQA : CIK.A * CIK.nilpotentProj = CIK.nilpotentProj * CIK.A :=
    CIK.A_mul_nilpotentProj_eq_nilpotentProj_mul_A
  have hMid : CIK.A * (CIK.nilpotentProj * CIK.A) = CIK.nilpotentProj * (CIK.A * CIK.A) := by
    calc
      CIK.A * (CIK.nilpotentProj * CIK.A) = (CIK.A * CIK.nilpotentProj) * CIK.A := by
        rw [← mul_assoc]
      _ = (CIK.nilpotentProj * CIK.A) * CIK.A := by
        rw [hQA]
      _ = CIK.nilpotentProj * (CIK.A * CIK.A) := by
        rw [mul_assoc]
  calc
    (CIK.drazinCoreProj * CIK.A) * (CIK.nilpotentProj * CIK.A)
        = CIK.drazinCoreProj * (CIK.A * (CIK.nilpotentProj * CIK.A)) := by
            simp [mul_assoc]
    _ = CIK.drazinCoreProj * (CIK.nilpotentProj * (CIK.A * CIK.A)) := by
          rw [hMid]
    _ = (CIK.drazinCoreProj * CIK.nilpotentProj) * (CIK.A * CIK.A) := by
          simp [mul_assoc]
    _ = 0 := by
          rw [CIK.spectralProjector_mul_spectralComplementaryProjector]
          simp

@[rep_depth operator] theorem nilpotentPart_mul_corePart_eq_zero :
    CIK.nilpotentPart * CIK.corePart = 0 := by
  rw [CIK.nilpotentPart_eq_nilpotentProj_mul_A, CIK.corePart_eq_drazinCoreProj_mul_A]
  have hPA : CIK.A * CIK.drazinCoreProj = CIK.drazinCoreProj * CIK.A :=
    CIK.A_mul_drazinCoreProj_eq_drazinCoreProj_mul_A
  have hMid : CIK.A * (CIK.drazinCoreProj * CIK.A) = CIK.drazinCoreProj * (CIK.A * CIK.A) := by
    calc
      CIK.A * (CIK.drazinCoreProj * CIK.A) = (CIK.A * CIK.drazinCoreProj) * CIK.A := by
        rw [← mul_assoc]
      _ = (CIK.drazinCoreProj * CIK.A) * CIK.A := by
        rw [hPA]
      _ = CIK.drazinCoreProj * (CIK.A * CIK.A) := by
        rw [mul_assoc]
  calc
    (CIK.nilpotentProj * CIK.A) * (CIK.drazinCoreProj * CIK.A)
        = CIK.nilpotentProj * (CIK.A * (CIK.drazinCoreProj * CIK.A)) := by
            simp [mul_assoc]
    _ = CIK.nilpotentProj * (CIK.drazinCoreProj * (CIK.A * CIK.A)) := by
          rw [hMid]
    _ = (CIK.nilpotentProj * CIK.drazinCoreProj) * (CIK.A * CIK.A) := by
          simp [mul_assoc]
    _ = 0 := by
          rw [CIK.spectralComplementaryProjector_mul_spectralProjector]
          simp

@[rep_depth operator] theorem corePart_commute_nilpotentPart :
    Commute CIK.corePart CIK.nilpotentPart := by
  change CIK.corePart * CIK.nilpotentPart = CIK.nilpotentPart * CIK.corePart
  rw [CIK.corePart_mul_nilpotentPart_eq_zero, CIK.nilpotentPart_mul_corePart_eq_zero]

@[rep_depth operator] theorem A_pow_mul_nilpotentProj_eq_zero_of_index_le
    {m : ℕ} (hm : CIK.drazinIndex ≤ m) :
    CIK.A ^ m * CIK.nilpotentProj = 0 := by
  change CIK.A ^ m * IsDrazinInverse.complementaryProjection CIK.A CIK.A_D = 0
  simpa using
    IsDrazinInverse.pow_mul_complementaryProjection_eq_zero_of_le
      (h := CIK.hDrazin) hm

@[rep_depth operator] theorem nilpotentPart_pow_succ_eq_zero_of_index_le
    {m : ℕ} (hm : CIK.drazinIndex ≤ m + 1) :
    CIK.nilpotentPart ^ (m + 1) = 0 := by
  rw [CIK.nilpotentPart_eq_nilpotentProj_mul_A]
  have hnil :
      (IsDrazinInverse.nilpotent CIK.A CIK.A_D) ^ (m + 1) = 0 :=
    IsDrazinInverse.nilpotent_pow_succ_eq_zero_of_le
      (a := CIK.A) (b := CIK.A_D) (k := CIK.drazinIndex) (m := m) (h := CIK.hDrazin) hm
  rw [IsDrazinInverse.nilpotent_eq_complementaryProjection_mul (h := CIK.hDrazin)] at hnil
  simpa [CertifiedInverseKernel.nilpotentProj, CertifiedInverseKernel.spectralComplementaryProjector] using hnil

end InfoGeometry.Canonical.CertifiedInverseKernel

end Certified

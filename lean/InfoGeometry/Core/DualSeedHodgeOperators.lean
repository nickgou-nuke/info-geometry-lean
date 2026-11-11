/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DualSeedCentralizer
import InfoGeometry.Core.LieJordanGenerators
import Mathlib.Tactic.FieldSimp

/-!
# Algebraic Green operator for the adjoint anticommutator

The existing negative symmetric generator is the positive-sign adjoint
anticommutator. Three bilateral sectors have eigenvalues one, two, and four.
Their explicit inverse gives a Green operator and the balanced average of the
two directional centralizer projections. No star, norm, or finite dimension is
used; the only division premise is that two is nonzero in the coefficient field.
-/

namespace InfoGeometry.Core.DualSeedPeirce

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Core.PeirceBilateralAction InfoGeometry.Core.PeirceRotor
open InfoGeometry.Core.LieJordanGenerators
open InfoGeometry.Core.DiracSuperalgebra InfoGeometry.Singular.MoorePenrose

section Ring

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem neg_symmetricGenerator_apply (d b x : A) :
    (-symmetricGenerator (R := R) d b) x =
      carrierSupport d b * x + x * carrierSupport d b -
        2 • (d * x * b + b * x * d) := by
  rw [LinearMap.neg_apply, symmetricGenerator_sandwich_apply, neg_sub]
  rfl

private theorem neg_symmetricGenerator_bilateral (d b u v x : A) :
    (-symmetricGenerator (R := R) d b) (u * x * v) =
      (carrierSupport d b * u) * x * v + u * x * (v * carrierSupport d b) -
        2 • ((d * u) * x * (v * b) + (b * u) * x * (v * d)) := by
  rw [neg_symmetricGenerator_apply]
  simp only [two_nsmul]
  noncomm_ring

private theorem bilateral_neg_symmetricGenerator (d b u v x : A) :
    u * (-symmetricGenerator (R := R) d b) x * v =
      (u * carrierSupport d b) * x * v + u * x * (carrierSupport d b * v) -
        2 • ((u * d) * x * (b * v) + (u * b) * x * (d * v)) := by
  rw [neg_symmetricGenerator_apply]
  simp only [two_nsmul]
  noncomm_ring

private theorem zeroModeSupport_symm (d b : A) :
    zeroModeSupport b d = zeroModeSupport d b := by
  change 1 - b * d - d * b = 1 - d * b - b * d
  abel

namespace IsDualSeedPair

variable {d b : A}

private theorem hodge_support_table (h : IsDualSeedPair d b) :
    carrierSupport d b * carrierSupport d b = carrierSupport d b ∧
    carrierSupport d b * d = d ∧ d * carrierSupport d b = d ∧
    carrierSupport d b * b = b ∧ b * carrierSupport d b = b ∧
    carrierSupport d b * polePlus d b = polePlus d b ∧
    polePlus d b * carrierSupport d b = polePlus d b ∧
    carrierSupport d b * poleMinus d b = poleMinus d b ∧
    poleMinus d b * carrierSupport d b = poleMinus d b := by
  change (polePlus d b + poleMinus d b) * (polePlus d b + poleMinus d b) = _ ∧
    (polePlus d b + poleMinus d b) * d = d ∧
    d * (polePlus d b + poleMinus d b) = d ∧
    (polePlus d b + poleMinus d b) * b = b ∧
    b * (polePlus d b + poleMinus d b) = b ∧
    (polePlus d b + poleMinus d b) * polePlus d b = polePlus d b ∧
    polePlus d b * (polePlus d b + poleMinus d b) = polePlus d b ∧
    (polePlus d b + poleMinus d b) * poleMinus d b = poleMinus d b ∧
    poleMinus d b * (polePlus d b + poleMinus d b) = poleMinus d b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [add_mul, mul_add, h.pp, h.qq, h.pq, h.qp,
      h.pd, h.dp, h.qd, h.dq, h.pb, h.bp, h.qb, h.bq, zero_add, add_zero]
  rfl

private theorem hodge_residual_table (h : IsDualSeedPair d b) :
    zeroModeSupport d b * d = 0 ∧ d * zeroModeSupport d b = 0 ∧
    zeroModeSupport d b * b = 0 ∧ b * zeroModeSupport d b = 0 ∧
    zeroModeSupport d b * carrierSupport d b = 0 ∧
    carrierSupport d b * zeroModeSupport d b = 0 := by
  have hd : zeroModeSupport d b * d = 0 ∧ d * zeroModeSupport d b = 0 := by
    simpa only [peirceBlock, zero_smul, one_smul, zero_add, add_zero] using
      (harmonic_block (R := ℤ) h 0 1 0 0)
  have hb : zeroModeSupport d b * b = 0 ∧ b * zeroModeSupport d b = 0 := by
    simpa only [peirceBlock, zero_smul, one_smul, zero_add, add_zero] using
      (harmonic_block (R := ℤ) h 0 0 1 0)
  have he : zeroModeSupport d b * carrierSupport d b = 0 ∧
      carrierSupport d b * zeroModeSupport d b = 0 := by
    simpa only [carrierSupport, activeSupport, peirceBlock, zero_smul,
      one_smul, zero_add, add_zero] using
      (harmonic_block (R := ℤ) h 1 0 0 1)
  exact ⟨hd.1, hd.2, hb.1, hb.2, he.1, he.2⟩

/-- Mixed active/residual blocks have eigenvalue one. -/
theorem neg_symmetricGenerator_mixed (h : IsDualSeedPair d b) (x : A) :
    (-symmetricGenerator (R := R) d b)
        (carrierSupport d b * x * zeroModeSupport d b +
          zeroModeSupport d b * x * carrierSupport d b) =
      carrierSupport d b * x * zeroModeSupport d b +
        zeroModeSupport d b * x * carrierSupport d b := by
  rcases h.hodge_support_table with ⟨hee, hed, hde, heb, hbe, _, _, _, _⟩
  rcases h.hodge_residual_table with ⟨hrd, hdr, hrb, hbr, hre, her⟩
  simp only [map_add, neg_symmetricGenerator_bilateral, hee, hed, hde, heb, hbe,
    hrd, hdr, hrb, hbr, hre, her, mul_zero, zero_mul, smul_zero,
    add_zero, zero_add, sub_zero]

/-- The active off-diagonal sector has eigenvalue two. -/
theorem neg_symmetricGenerator_offDiagonal (h : IsDualSeedPair d b) (x : A) :
    (-symmetricGenerator (R := R) d b)
        (polePlus d b * x * poleMinus d b + poleMinus d b * x * polePlus d b) =
      2 • (polePlus d b * x * poleMinus d b + poleMinus d b * x * polePlus d b) := by
  rcases h.hodge_support_table with ⟨_, _, _, _, _, hep, hpe, heq, hqe⟩
  simp only [map_add, neg_symmetricGenerator_bilateral, hep, hpe, heq, hqe,
    h.dp, h.dq, h.bp, h.bq, h.pd, h.qd, h.pb, h.qb,
    mul_zero, zero_mul, smul_zero, add_zero, sub_zero, two_nsmul]
  abel

/-- The difference between diagonal and exchanged diagonal sectors has eigenvalue four. -/
theorem neg_symmetricGenerator_diagonalDifference (h : IsDualSeedPair d b) (x : A) :
    (-symmetricGenerator (R := R) d b)
        (polePlus d b * x * polePlus d b + poleMinus d b * x * poleMinus d b -
          d * x * b - b * x * d) =
      4 • (polePlus d b * x * polePlus d b + poleMinus d b * x * poleMinus d b -
        d * x * b - b * x * d) := by
  rcases h.hodge_support_table with ⟨_, hed, hde, heb, hbe, hep, hpe, heq, hqe⟩
  have hdb : d * b = polePlus d b := rfl
  have hbd : b * d = poleMinus d b := rfl
  simp only [map_add, map_sub, neg_symmetricGenerator_bilateral,
    hed, hde, heb, hbe, hep, hpe, heq, hqe,
    h.dp, h.dq, h.bp, h.bq, h.pd, h.qd, h.pb, h.qb,
    h.d_sq, h.b_sq, hdb, hbd, mul_zero, zero_mul, add_zero, zero_add,
    two_nsmul, show (4 : ℕ) = 2 + 2 by decide, add_nsmul]
  abel

/-- The mixed-sector readout commutes with the adjoint anticommutator. -/
theorem mixed_neg_symmetricGenerator (h : IsDualSeedPair d b) (x : A) :
    carrierSupport d b * (-symmetricGenerator (R := R) d b) x * zeroModeSupport d b +
        zeroModeSupport d b * (-symmetricGenerator (R := R) d b) x * carrierSupport d b =
      carrierSupport d b * x * zeroModeSupport d b +
        zeroModeSupport d b * x * carrierSupport d b := by
  rcases h.hodge_support_table with ⟨hee, hed, hde, heb, hbe, _, _, _, _⟩
  rcases h.hodge_residual_table with ⟨hrd, hdr, hrb, hbr, hre, her⟩
  simp only [bilateral_neg_symmetricGenerator, hee, hed, hde, heb, hbe,
    hrd, hdr, hrb, hbr, hre, her, mul_zero, zero_mul, smul_zero,
    add_zero, zero_add, sub_zero]

/-- The off-diagonal readout commutes with the adjoint anticommutator. -/
theorem offDiagonal_neg_symmetricGenerator (h : IsDualSeedPair d b) (x : A) :
    polePlus d b * (-symmetricGenerator (R := R) d b) x * poleMinus d b +
        poleMinus d b * (-symmetricGenerator (R := R) d b) x * polePlus d b =
      2 • (polePlus d b * x * poleMinus d b + poleMinus d b * x * polePlus d b) := by
  rcases h.hodge_support_table with ⟨_, _, _, _, _, hep, hpe, heq, hqe⟩
  simp only [bilateral_neg_symmetricGenerator, hep, hpe, heq, hqe,
    h.dp, h.dq, h.bp, h.bq, h.pd, h.qd, h.pb, h.qb,
    mul_zero, zero_mul, smul_zero, add_zero, sub_zero, two_nsmul]
  abel

/-- The diagonal-difference readout commutes with the adjoint anticommutator. -/
theorem diagonalDifference_neg_symmetricGenerator (h : IsDualSeedPair d b) (x : A) :
    polePlus d b * (-symmetricGenerator (R := R) d b) x * polePlus d b +
        poleMinus d b * (-symmetricGenerator (R := R) d b) x * poleMinus d b -
        d * (-symmetricGenerator (R := R) d b) x * b -
        b * (-symmetricGenerator (R := R) d b) x * d =
      4 • (polePlus d b * x * polePlus d b + poleMinus d b * x * poleMinus d b -
        d * x * b - b * x * d) := by
  rcases h.hodge_support_table with ⟨_, hed, hde, heb, hbe, hep, hpe, heq, hqe⟩
  have hdb : d * b = polePlus d b := rfl
  have hbd : b * d = poleMinus d b := rfl
  simp only [bilateral_neg_symmetricGenerator,
    hed, hde, heb, hbe, hep, hpe, heq, hqe,
    h.dp, h.dq, h.bp, h.bq, h.pd, h.qd, h.pb, h.qb,
    h.d_sq, h.b_sq, hdb, hbd, mul_zero, zero_mul, add_zero, zero_add,
    two_nsmul, show (4 : ℕ) = 2 + 2 by decide, add_nsmul]
  abel

end IsDualSeedPair
end Ring

section Field

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- The average of the existing two directional common-commutant retractions. -/
def balancedCentralizerProjection (K : Type*) [Field K] [Algebra K A] (d b : A) :
    Module.End K A :=
  (1 / 2 : K) • (centralizerProjection K d b + centralizerProjection K b d)

/-- Invert the three nonzero Peirce weights and annihilate the harmonic sector. -/
def dualSeedGreen (K : Type*) [Field K] [Algebra K A] (d b : A) : Module.End K A :=
  bilateral (carrierSupport d b) (zeroModeSupport d b) +
    bilateral (zeroModeSupport d b) (carrierSupport d b) +
    (1 / 2 : K) • (bilateral (polePlus d b) (poleMinus d b) +
      bilateral (poleMinus d b) (polePlus d b)) +
    (1 / 8 : K) • (bilateral (polePlus d b) (polePlus d b) +
      bilateral (poleMinus d b) (poleMinus d b) - bilateral d b - bilateral b d)

@[simp] theorem dualSeedGreen_apply (d b x : A) :
    dualSeedGreen K d b x =
      carrierSupport d b * x * zeroModeSupport d b +
        zeroModeSupport d b * x * carrierSupport d b +
        (1 / 2 : K) • (polePlus d b * x * poleMinus d b +
          poleMinus d b * x * polePlus d b) +
        (1 / 8 : K) • (polePlus d b * x * polePlus d b +
          poleMinus d b * x * poleMinus d b - d * x * b - b * x * d) := rfl

private theorem hodge_smul_cancel {c : K} (hc : c ≠ 0) {x y : A}
    (h : c • x = c • y) : x = y := by
  have hi := congrArg (fun a : A => c⁻¹ • a) h
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hi

/-- The balanced map retains the residual corner and averages the two active diagonals. -/
theorem balancedCentralizerProjection_apply (h2 : (2 : K) ≠ 0) (d b x : A) :
    balancedCentralizerProjection K d b x =
      (1 / 2 : K) • (polePlus d b * x * polePlus d b +
        poleMinus d b * x * poleMinus d b + d * x * b + b * x * d) +
        zeroModeSupport d b * x * zeroModeSupport d b := by
  have htwohalf : (2 : K) * (1 / 2) = 1 := by field_simp
  change (1 / 2 : K) • ((polePlus d b * x * polePlus d b + b * x * d +
    zeroModeSupport d b * x * zeroModeSupport d b) +
    (poleMinus d b * x * poleMinus d b + d * x * b +
      zeroModeSupport b d * x * zeroModeSupport b d)) = _
  rw [zeroModeSupport_symm d b]
  apply hodge_smul_cancel h2
  simp only [smul_add, smul_smul, htwohalf, one_smul]
  simp only [two_smul K]
  abel

private theorem hodge_reconstruction (h2 : (2 : K) ≠ 0) (d b x : A) :
    carrierSupport d b * x * zeroModeSupport d b +
        zeroModeSupport d b * x * carrierSupport d b +
        (polePlus d b * x * poleMinus d b + poleMinus d b * x * polePlus d b) +
        (1 / 2 : K) • (polePlus d b * x * polePlus d b +
          poleMinus d b * x * poleMinus d b - d * x * b - b * x * d) =
      x - balancedCentralizerProjection K d b x := by
  have htwohalf : (2 : K) * (1 / 2) = 1 := by field_simp
  rw [balancedCentralizerProjection_apply h2]
  apply hodge_smul_cancel h2
  simp only [smul_add, smul_sub, smul_smul, htwohalf, one_smul]
  simp only [two_smul K]
  unfold carrierSupport activeSupport zeroModeSupport harmonicSupport
    polePlus poleMinus exactSupport coexactSupport
  noncomm_ring

namespace IsDualSeedPair

variable {d b : A}

private theorem green_scalar_weights (h2 : (2 : K) ≠ 0) :
    (1 / 2 : K) * 2 = 1 ∧ (1 / 8 : K) * 4 = 1 / 2 := by
  have h8 : (8 : K) ≠ 0 := by
    have he : (8 : K) = 2 * 2 * 2 := by ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero h2 h2) h2
  constructor <;> field_simp
  ring

/-- The adjoint anticommutator followed by its Green map is the nonharmonic projection. -/
theorem neg_symmetricGenerator_mul_dualSeedGreen (h : IsDualSeedPair d b)
    (h2 : (2 : K) ≠ 0) :
    (-symmetricGenerator (R := K) d b) * dualSeedGreen K d b =
      1 - balancedCentralizerProjection K d b := by
  rcases green_scalar_weights h2 with ⟨hhalf, heighth⟩
  ext x
  change (-symmetricGenerator (R := K) d b) (dualSeedGreen K d b x) =
    x - balancedCentralizerProjection K d b x
  rw [dualSeedGreen_apply]
  simp only [map_add, map_smul, h.neg_symmetricGenerator_mixed,
    h.neg_symmetricGenerator_offDiagonal, h.neg_symmetricGenerator_diagonalDifference]
  simp only [← Nat.cast_smul_eq_nsmul K, Nat.cast_ofNat, smul_smul,
    hhalf, heighth, one_smul]
  exact hodge_reconstruction h2 d b x

/-- The Green map also inverts on the other side of the nonharmonic projection. -/
theorem dualSeedGreen_mul_neg_symmetricGenerator (h : IsDualSeedPair d b)
    (h2 : (2 : K) ≠ 0) :
    dualSeedGreen K d b * (-symmetricGenerator (R := K) d b) =
      1 - balancedCentralizerProjection K d b := by
  rcases green_scalar_weights h2 with ⟨hhalf, heighth⟩
  ext x
  change dualSeedGreen K d b ((-symmetricGenerator (R := K) d b) x) =
    x - balancedCentralizerProjection K d b x
  rw [dualSeedGreen_apply, h.mixed_neg_symmetricGenerator,
    h.offDiagonal_neg_symmetricGenerator, h.diagonalDifference_neg_symmetricGenerator]
  simp only [← Nat.cast_smul_eq_nsmul K, Nat.cast_ofNat, smul_smul,
    hhalf, heighth, one_smul]
  exact hodge_reconstruction h2 d b x

/-- The explicit Green map is zero on every common-commutant element. -/
theorem dualSeedGreen_eq_zero_of_commute (h : IsDualSeedPair d b) {x : A}
    (hxd : Commute x d) (hxb : Commute x b) : dualSeedGreen K d b x = 0 := by
  have hp : Commute x (polePlus d b) := hxd.mul_right hxb
  have hq : Commute x (poleMinus d b) := hxb.mul_right hxd
  have he : Commute x (carrierSupport d b) := hp.add_right hq
  have hr : Commute x (zeroModeSupport d b) :=
    ((Commute.one_right x).sub_right hp).sub_right hq
  rcases h.hodge_residual_table with ⟨_, _, _, _, hre, her⟩
  have herx : carrierSupport d b * x * zeroModeSupport d b = 0 := by
    rw [← he.eq, mul_assoc, her, mul_zero]
  have hrex : zeroModeSupport d b * x * carrierSupport d b = 0 := by
    rw [← hr.eq, mul_assoc, hre, mul_zero]
  have hpqx : polePlus d b * x * poleMinus d b = 0 := by
    rw [← hp.eq, mul_assoc, h.pq, mul_zero]
  have hqpx : poleMinus d b * x * polePlus d b = 0 := by
    rw [← hq.eq, mul_assoc, h.qp, mul_zero]
  have hppx : polePlus d b * x * polePlus d b = x * polePlus d b := by
    rw [← hp.eq, mul_assoc, h.pp]
  have hqqx : poleMinus d b * x * poleMinus d b = x * poleMinus d b := by
    rw [← hq.eq, mul_assoc, h.qq]
  have hdbx : d * x * b = x * polePlus d b := by
    rw [← hxd.eq, mul_assoc]
    rfl
  have hbdx : b * x * d = x * poleMinus d b := by
    rw [← hxb.eq, mul_assoc]
    rfl
  rw [dualSeedGreen_apply, herx, hrex, hpqx, hqpx, hppx, hqqx, hdbx, hbdx]
  simp only [add_zero, zero_add, smul_zero]
  have hz : x * polePlus d b + x * poleMinus d b -
      x * polePlus d b - x * poleMinus d b = 0 := by abel
  rw [hz, smul_zero]

end IsDualSeedPair
end Field

end InfoGeometry.Core.DualSeedPeirce

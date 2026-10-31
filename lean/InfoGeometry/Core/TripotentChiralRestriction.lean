/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.Algebra.TripotentInvariantCarrierBridge

/-!
# Chiral intertwining and restriction for a tripotent

An endomorphism `Γ` anticommuting with `T` commutes with `1 - T²`
and interchanges the positive and negative polynomial projectors of `T`.
These polynomial identities do not require tripotence or involutivity.

When `T³ = T` and `Γ² = 1`, the existing native `zeroModeRestriction`
therefore defines an involution, and hence a linear equivalence, on `ker T`.
This is an anticommuting chiral action. It is not an identification with
the Peirce parity action that preserves the charge grades of its projector.
-/

noncomputable section

namespace InfoGeometry.Physics.Algebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Anticommutation with an endomorphism implies commutation with its square. -/
theorem anticommute_commutes_square
    (T Γ : Module.End ℝ V) (hanti : Γ * T = -(T * Γ)) :
    Γ * (T * T) = (T * T) * Γ := by
  calc
    Γ * (T * T) = (Γ * T) * T := by rw [mul_assoc]
    _ = (-(T * Γ)) * T := by rw [hanti]
    _ = -(T * (Γ * T)) := by noncomm_ring
    _ = -(T * (-(T * Γ))) := by rw [hanti]
    _ = (T * T) * Γ := by noncomm_ring

/-- The chiral action preserves the polynomial zero-mode projector. -/
theorem anticommute_endProjZero
    (T Γ : Module.End ℝ V) (hanti : Γ * T = -(T * Γ)) :
    Γ * endProjZero T = endProjZero T * Γ := by
  change Γ * (1 - T * T) = (1 - T * T) * Γ
  rw [mul_sub, sub_mul, mul_one, one_mul,
    anticommute_commutes_square T Γ hanti]

/-- Positive and negative polynomial projectors are intertwined by chirality. -/
theorem anticommute_endProjPos
    (T Γ : Module.End ℝ V) (hanti : Γ * T = -(T * Γ)) :
    Γ * endProjPos T = endProjNeg T * Γ := by
  change Γ * ((1 / 2 : ℝ) • (T * T + T)) =
    ((1 / 2 : ℝ) • (T * T - T)) * Γ
  rw [mul_smul_comm, smul_mul_assoc, mul_add, sub_mul,
    anticommute_commutes_square T Γ hanti, hanti]
  simp only [sub_eq_add_neg]

/-- Negative and positive polynomial projectors are intertwined by chirality. -/
theorem anticommute_endProjNeg
    (T Γ : Module.End ℝ V) (hanti : Γ * T = -(T * Γ)) :
    Γ * endProjNeg T = endProjPos T * Γ := by
  change Γ * ((1 / 2 : ℝ) • (T * T - T)) =
    ((1 / 2 : ℝ) • (T * T + T)) * Γ
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, add_mul,
    anticommute_commutes_square T Γ hanti, hanti, sub_neg_eq_add]

/-- The native zero-mode restriction of an anticommuting involution squares
to the identity on the whole kernel, retaining all its multiplicities. -/
theorem zeroModeRestriction_sq_of_anticommute
    (T Γ : Module.End ℝ V) (hT : T ^ 3 = T)
    (hanti : Γ * T = -(T * Γ)) (hΓ : Γ * Γ = 1) :
    zeroModeRestriction T Γ hT (anticommute_endProjZero T Γ hanti) *
      zeroModeRestriction T Γ hT (anticommute_endProjZero T Γ hanti) = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change Γ (Γ x.1) = x.1
  have hx := congrArg (fun A : Module.End ℝ V => A x.1) hΓ
  simpa only [Module.End.mul_apply, Module.End.one_apply] using hx

/-- The chiral symmetry on the horizon is an actual linear equivalence
whose underlying map is the canonical zero-mode restriction. -/
def zeroModeChiralEquiv
    (T Γ : Module.End ℝ V) (hT : T ^ 3 = T)
    (hanti : Γ * T = -(T * Γ)) (hΓ : Γ * Γ = 1) :
    zeroModeCarrier T ≃ₗ[ℝ] zeroModeCarrier T := by
  let R := zeroModeRestriction T Γ hT (anticommute_endProjZero T Γ hanti)
  have hR : R * R = 1 :=
    zeroModeRestriction_sq_of_anticommute T Γ hT hanti hΓ
  refine
    { toLinearMap := R
      invFun := R
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    change (R * R) x = x
    exact congrArg (fun A : Module.End ℝ (zeroModeCarrier T) => A x) hR
  · intro x
    change (R * R) x = x
    exact congrArg (fun A : Module.End ℝ (zeroModeCarrier T) => A x) hR

@[simp] theorem zeroModeChiralEquiv_apply
    (T Γ : Module.End ℝ V) (hT : T ^ 3 = T)
    (hanti : Γ * T = -(T * Γ)) (hΓ : Γ * Γ = 1)
    (x : zeroModeCarrier T) :
    (zeroModeChiralEquiv T Γ hT hanti hΓ x).1 = Γ x.1 := rfl

end InfoGeometry.Physics.Algebra

end noncomputable section

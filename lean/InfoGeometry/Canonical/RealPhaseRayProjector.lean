/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealComplexRotor
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Trace

/-!
# Real phase-plane projectors and overlap quadratures

An internal real endomorphism `J` with `J² = -id` supplies the phase direction.
For a symmetric bilinear form with respect to which `J` is skew, a normalized
vector `u` and `J u` form an orthonormal pair. Their two dyads give the projector
onto the real phase plane. Its finite real trace pairing is twice the sum of
the squares of the two real overlap quadratures.

The bilinear form need not be positive on the whole carrier. Normalization
selects a positive phase plane. The statements concern actual real linear
endomorphisms; no complex scalar field or commutative operator restriction is
introduced. No determinant-line topology or anomaly theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealPhaseRayProjector

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The sum of the dyads of a vector and its internal phase direction. -/
def rayProjector (B : LinearMap.BilinForm ℝ V) (J : Module.End ℝ V)
    (u : V) : Module.End ℝ V :=
  (B u).smulRight u + (B (J u)).smulRight (J u)

/-- Both real overlap quadratures, retaining the internal phase information. -/
def overlapPair (B : LinearMap.BilinForm ℝ V) (J : Module.End ℝ V)
    (u v : V) : ℝ × ℝ :=
  (B u v, B (J u) v)

@[simp] theorem rayProjector_apply (B : LinearMap.BilinForm ℝ V)
    (J : Module.End ℝ V) (u x : V) :
    rayProjector B J u x = B u x • u + B (J u) x • J u := rfl

variable (B : LinearMap.BilinForm ℝ V) (J : Module.End ℝ V)

theorem pairing_phase_phase (hJ : IsRealComplexStructure J)
    (hskew : ∀ x y, B (J x) y = -B x (J y)) (x y : V) :
    B (J x) (J y) = B x y := by
  rw [hskew x (J y), realComplexStructure_apply_sq J hJ y]
  simp

theorem pairing_phase_self (hB : B.IsSymm)
    (hskew : ∀ x y, B (J x) y = -B x (J y)) (u : V) :
    B (J u) u = 0 := by
  have hs := hskew u u
  rw [hB.eq u (J u)] at hs
  exact add_self_eq_zero.mp
    ((congrArg (fun a : ℝ => a + B (J u) u) hs).trans (neg_add_cancel _))

theorem pairing_self_phase (hB : B.IsSymm)
    (hskew : ∀ x y, B (J x) y = -B x (J y)) (u : V) :
    B u (J u) = 0 := by
  rw [hB.eq u (J u), pairing_phase_self B J hB hskew u]

theorem rayProjector_self (hB : B.IsSymm)
    (hskew : ∀ x y, B (J x) y = -B x (J y))
    (u : V) (hu : B u u = 1) :
    rayProjector B J u u = u := by
  simp [rayProjector_apply, hu, pairing_phase_self B J hB hskew u]

theorem rayProjector_phase (hB : B.IsSymm) (hJ : IsRealComplexStructure J)
    (hskew : ∀ x y, B (J x) y = -B x (J y))
    (u : V) (hu : B u u = 1) :
    rayProjector B J u (J u) = J u := by
  simp [rayProjector_apply, pairing_self_phase B J hB hskew u,
    pairing_phase_phase B J hJ hskew u u, hu]

/-- The phase-plane operator is an actual idempotent in the full endomorphism algebra. -/
theorem rayProjector_idempotent (hB : B.IsSymm) (hJ : IsRealComplexStructure J)
    (hskew : ∀ x y, B (J x) y = -B x (J y))
    (u : V) (hu : B u u = 1) :
    IsIdempotentElem (rayProjector B J u) := by
  apply LinearMap.ext
  intro x
  change rayProjector B J u (rayProjector B J u x) = rayProjector B J u x
  rw [rayProjector_apply B J u x, map_add, map_smul, map_smul,
    rayProjector_self B J hB hskew u hu,
    rayProjector_phase B J hB hJ hskew u hu]
  rfl

/-- Self-adjointness uses the specified bilinear form, which may be indefinite. -/
theorem rayProjector_adjoint (hB : B.IsSymm) (u : V) :
    LinearMap.IsAdjointPair B B (rayProjector B J u) (rayProjector B J u) := by
  intro x y
  simp only [rayProjector_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hB.eq x u, hB.eq x (J u)]
  exact congrArg₂ (fun a b : ℝ => a + b) (mul_comm _ _) (mul_comm _ _)

theorem rayProjector_commute_phase (hJ : IsRealComplexStructure J)
    (hskew : ∀ x y, B (J x) y = -B x (J y)) (u : V) :
    Commute (rayProjector B J u) J := by
  apply LinearMap.ext
  intro x
  change rayProjector B J u (J x) = J (rayProjector B J u x)
  have hcross : B u (J x) = -B (J u) x := by
    linarith [hskew u x]
  simp only [rayProjector_apply, map_add, map_smul,
    realComplexStructure_apply_sq J hJ, pairing_phase_phase B J hJ hskew, hcross]
  module

/-- The image is exactly the real span of the two phase directions. -/
theorem rayProjector_range (hB : B.IsSymm) (hJ : IsRealComplexStructure J)
    (hskew : ∀ x y, B (J x) y = -B x (J y))
    (u : V) (hu : B u u = 1) :
    LinearMap.range (rayProjector B J u) = Submodule.span ℝ ({u, J u} : Set V) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact Submodule.mem_span_pair.mpr ⟨B u y, B (J u) y, rfl⟩
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with h | h
    · subst x
      exact ⟨u, rayProjector_self B J hB hskew u hu⟩
    · have hx : x = J u := Set.mem_singleton_iff.mp h
      subst x
      exact ⟨J u, rayProjector_phase B J hB hJ hskew u hu⟩

/-- A projected vector vanishes precisely when both real overlap quadratures vanish. -/
theorem rayProjector_apply_eq_zero_iff (hB : B.IsSymm) (hJ : IsRealComplexStructure J)
    (hskew : ∀ x y, B (J x) y = -B x (J y))
    (u : V) (hu : B u u = 1) (x : V) :
    rayProjector B J u x = 0 ↔ B u x = 0 ∧ B (J u) x = 0 := by
  constructor
  · intro hx
    have hfirst := congrArg (B u) hx
    have hsecond := congrArg (B (J u)) hx
    simp only [rayProjector_apply, map_add, map_smul, smul_eq_mul, map_zero,
      pairing_self_phase B J hB hskew u,
      pairing_phase_self B J hB hskew u,
      pairing_phase_phase B J hJ hskew u u, hu,
      mul_one, mul_zero, zero_add, add_zero] at hfirst hsecond
    exact ⟨hfirst, hsecond⟩
  · rintro ⟨hfirst, hsecond⟩
    simp [rayProjector_apply, hfirst, hsecond]

/-- On the selected phase plane the bilinear quadratic is a sum of two squares. -/
theorem rayProjector_quadratic (hB : B.IsSymm) (hJ : IsRealComplexStructure J)
    (hskew : ∀ x y, B (J x) y = -B x (J y))
    (u : V) (hu : B u u = 1) (x : V) :
    B (rayProjector B J u x) (rayProjector B J u x) =
      (B u x) ^ 2 + (B (J u) x) ^ 2 := by
  simp only [rayProjector_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul,
    pairing_self_phase B J hB hskew u,
    pairing_phase_self B J hB hskew u,
    pairing_phase_phase B J hJ hskew u u, hu]
  simp [pow_two]

/-- Changing the two real phase coordinates rescales the phase-plane projector
by their squared radius. This does not require normalization or symmetry of `B`. -/
theorem rayProjector_scalar_action (hJ : IsRealComplexStructure J)
    (a b : ℝ) (u : V) :
    rayProjector B J (realComplexScalarAction J a b u) =
      (a ^ 2 + b ^ 2) • rayProjector B J u := by
  ext x
  simp only [rayProjector_apply, realComplexScalarAction, map_add, map_smul,
    realComplexStructure_apply_sq J hJ, map_neg, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.neg_apply, smul_eq_mul]
  module

theorem rayProjector_unit_phase (hJ : IsRealComplexStructure J)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (u : V) :
    rayProjector B J (realComplexScalarAction J a b u) = rayProjector B J u := by
  rw [rayProjector_scalar_action B J hJ, hab, one_smul]

/-- The repository's existing real rotor action leaves the phase projector fixed. -/
theorem rayProjector_rotor (hJ : IsRealComplexStructure J) (θ : ℝ) (u : V) :
    rayProjector B J (realRotorAction J θ u) = rayProjector B J u := by
  apply rayProjector_unit_phase B J hJ (Real.cos θ) (Real.sin θ)
  exact (add_comm ((Real.cos θ) ^ 2) ((Real.sin θ) ^ 2)).trans
    (Real.sin_sq_add_cos_sq θ)

theorem rayProjector_phase_eq (hJ : IsRealComplexStructure J) (u : V) :
    rayProjector B J (J u) = rayProjector B J u := by
  have h := rayProjector_unit_phase B J hJ 0 1 (by norm_num) u
  simpa [realComplexScalarAction] using h

/-- The left overlap coordinates rotate as a real two-component amplitude. -/
theorem overlapPair_scalar_action_left (hJ : IsRealComplexStructure J)
    (a b : ℝ) (u v : V) :
    overlapPair B J (realComplexScalarAction J a b u) v =
      (a * B u v + b * B (J u) v, a * B (J u) v - b * B u v) := by
  apply Prod.ext <;>
    simp [overlapPair, realComplexScalarAction,
      realComplexStructure_apply_sq J hJ, sub_eq_add_neg]

/-- The right overlap coordinates rotate with the opposite relative phase. -/
theorem overlapPair_scalar_action_right (hJ : IsRealComplexStructure J)
    (hskew : ∀ x y, B (J x) y = -B x (J y))
    (a b : ℝ) (u v : V) :
    overlapPair B J u (realComplexScalarAction J a b v) =
      (a * B u v - b * B (J u) v, a * B (J u) v + b * B u v) := by
  have hcross : B u (J v) = -B (J u) v := by
    linarith [hskew u v]
  apply Prod.ext <;>
    simp [overlapPair, realComplexScalarAction,
      pairing_phase_phase B J hJ hskew, hcross, sub_eq_add_neg]

theorem overlapPair_self (hB : B.IsSymm)
    (hskew : ∀ x y, B (J x) y = -B x (J y))
    (u : V) (hu : B u u = 1) :
    overlapPair B J u u = (1, 0) := by
  simp [overlapPair, hu, pairing_phase_self B J hB hskew u]

theorem overlapPair_phase (hB : B.IsSymm) (hJ : IsRealComplexStructure J)
    (hskew : ∀ x y, B (J x) y = -B x (J y))
    (u : V) (hu : B u u = 1) :
    overlapPair B J u (J u) = (0, 1) := by
  simp [overlapPair, hu, pairing_self_phase B J hB hskew u,
    pairing_phase_phase B J hJ hskew u u]

/-- Identical phase-plane projectors can have different overlap quadratures. -/
theorem phase_forgetting_witness (hB : B.IsSymm) (hJ : IsRealComplexStructure J)
    (hskew : ∀ x y, B (J x) y = -B x (J y))
    (u : V) (hu : B u u = 1) :
    rayProjector B J (J u) = rayProjector B J u ∧
      overlapPair B J u u = (1, 0) ∧
      overlapPair B J u (J u) = (0, 1) ∧ J u ≠ u := by
  refine ⟨rayProjector_phase_eq B J hJ u,
    overlapPair_self B J hB hskew u hu,
    overlapPair_phase B J hB hJ hskew u hu, ?_⟩
  intro h
  have hz := pairing_self_phase B J hB hskew u
  rw [h, hu] at hz
  norm_num at hz

/-- An intermediate nonzero real overlap, with zero second quadrature, forces
the two phase-plane projectors to fail to commute. -/
theorem rayProjectors_noncommute (hB : B.IsSymm)
    (hskew : ∀ x y, B (J x) y = -B x (J y))
    (u v : V) (hu : B u u = 1) (hv : B v v = 1)
    (hphase : B (J u) v = 0) (hoverlap : B u v ≠ 0)
    (hproper : (B u v) ^ 2 ≠ 1) :
    ¬ Commute (rayProjector B J u) (rayProjector B J v) := by
  have hcross : B (J v) u = 0 := by
    rw [hskew v u, hB.eq v (J u), hphase, neg_zero]
  have hvu : rayProjector B J v u = B u v • v := by
    simp [rayProjector_apply, hB.eq v u, hcross]
  have huv : rayProjector B J u v = B u v • u := by
    simp [rayProjector_apply, hphase]
  intro hcomm
  have h := congrArg (fun T : Module.End ℝ V => B v (T u)) hcomm.eq
  change B v (rayProjector B J u (rayProjector B J v u)) =
    B v (rayProjector B J v (rayProjector B J u u)) at h
  rw [hvu, map_smul, huv, rayProjector_self B J hB hskew u hu, hvu] at h
  simp only [map_smul, smul_eq_mul, hB.eq v u, hv, mul_one] at h
  have hprod : B u v * ((B u v) ^ 2 - 1) = 0 := by nlinarith [h]
  exact hproper (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hoverlap))

section Trace

variable [FiniteDimensional ℝ V]

theorem trace_rayProjector (hJ : IsRealComplexStructure J)
    (hskew : ∀ x y, B (J x) y = -B x (J y)) (u : V) :
    LinearMap.trace ℝ V (rayProjector B J u) = 2 * B u u := by
  simp only [rayProjector, map_add, LinearMap.trace_smulRight,
    pairing_phase_phase B J hJ hskew u u]
  ring

/-- A normalized real phase-plane projector has real trace two. -/
theorem trace_rayProjector_eq_two (hJ : IsRealComplexStructure J)
    (hskew : ∀ x y, B (J x) y = -B x (J y))
    (u : V) (hu : B u u = 1) :
    LinearMap.trace ℝ V (rayProjector B J u) = 2 := by
  rw [trace_rayProjector B J hJ hskew u, hu, mul_one]

/-- The finite real trace of a projector product retains the squared magnitude
of the two overlap quadratures and loses their relative phase. The factor two
records that a phase ray is a two-dimensional real plane. -/
theorem trace_rayProjector_mul (hB : B.IsSymm) (hJ : IsRealComplexStructure J)
    (hskew : ∀ x y, B (J x) y = -B x (J y)) (u v : V) :
    LinearMap.trace ℝ V (rayProjector B J u * rayProjector B J v) =
      2 * ((B u v) ^ 2 + (B (J u) v) ^ 2) := by
  have hmul : rayProjector B J u * rayProjector B J v =
      (B v).smulRight (rayProjector B J u v) +
        (B (J v)).smulRight (rayProjector B J u (J v)) := by
    ext x
    change rayProjector B J u (B v x • v + B (J v) x • J v) = _
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smulRight_apply]
  have hcross : B u (J v) = -B (J u) v := by
    linarith [hskew u v]
  rw [hmul, map_add, LinearMap.trace_smulRight, LinearMap.trace_smulRight]
  simp only [rayProjector_apply, map_add, map_smul, smul_eq_mul]
  rw [hB.eq v u, hB.eq v (J u), hB.eq (J v) u, hB.eq (J v) (J u),
    hcross, pairing_phase_phase B J hJ hskew u v]
  ring

theorem trace_rayProjector_mul_nonneg (hB : B.IsSymm) (hJ : IsRealComplexStructure J)
    (hskew : ∀ x y, B (J x) y = -B x (J y)) (u v : V) :
    0 ≤ LinearMap.trace ℝ V (rayProjector B J u * rayProjector B J v) := by
  rw [trace_rayProjector_mul B J hB hJ hskew u v]
  positivity

end Trace

end InfoGeometry.Canonical.RealPhaseRayProjector

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KleinBottleSewing

/-! # Exact chiral readout of the existing sewing defect

Extends the sewn-state vanishing theorem to arbitrary densities. Uses the
existing Klein sewing operators and state carrier. This is a trace identity,
not a derivation of particle production or baryogenesis.
-/
namespace InfoGeometry.Canonical.KleinSewingDefect

section General
variable {A G : Type*} [Ring A] [AddCommGroup G]

/-- A grading-odd involution reverses the cyclic chiral trace. -/
theorem trace_sewing_reversal (τ : A →+ G)
    (hτ : ∀ a b, τ (a*b)=τ (b*a)) (q γ ρ : A)
    (hq : q*q=1) (hanti : q*γ= -(γ*q)) :
    τ (γ*(q*ρ*q))= -τ (γ*ρ) := by
  have hg : q*γ*q= -γ := by
    rw [hanti,neg_mul,mul_assoc,hq,mul_one]
  calc
    _ = τ ((γ*q*ρ)*q) := by simp only [mul_assoc]
    _ = τ (q*(γ*q*ρ)) := hτ _ _
    _ = τ ((q*γ*q)*ρ) := by simp only [mul_assoc]
    _ = -τ (γ*ρ) := by rw [hg,neg_mul,map_neg]

/-- Exact defect law, retaining possible additive two-torsion in the target. -/
theorem trace_sewing_defect (τ : A →+ G)
    (hτ : ∀ a b, τ (a*b)=τ (b*a)) (q γ ρ : A)
    (hq : q*q=1) (hanti : q*γ= -(γ*q)) :
    τ (γ*(q*ρ*q-ρ))= -(2 • τ (γ*ρ)) := by
  rw [mul_sub,map_sub,trace_sewing_reversal τ hτ q γ ρ hq hanti,two_nsmul]
  abel
end General

/-- The existing concrete sewing defect measures exactly minus twice the
existing chiral index, whether or not the state is sewn. -/
theorem boundary_defect_trace (s : BoundaryState) :
    Matrix.trace (tilt*(switch*s.rho*switch-s.rho))= -(2 • chiralIndex s) := by
  exact trace_sewing_defect (Matrix.traceAddMonoidHom (Fin 2) ℂ)
    (fun a b => Matrix.trace_mul_comm a b) switch tilt s.rho
    (by simpa only [pow_two] using switch_sq) switch_tilt_anticomm

/-- Exact equivalence for the scalar readout, not equivalence to sewing itself. -/
theorem boundary_defect_trace_zero_iff (s : BoundaryState) :
    Matrix.trace (tilt*(switch*s.rho*switch-s.rho))=0 ↔ chiralIndex s=0 := by
  rw [boundary_defect_trace,neg_eq_zero,two_nsmul]
  constructor
  · intro h
    have hz : (2 : ℂ)*chiralIndex s=0 := by simpa only [two_mul] using h
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · intro h; simp [h]

/-- Nonvacuity: the existing normalized pure boundary state has nonzero defect. -/
theorem concrete_boundary_defect :
    Matrix.trace (tilt*(switch*concreteBoundaryState.rho*switch-concreteBoundaryState.rho))=
      (-2 : ℂ) := by
  rw [boundary_defect_trace]
  norm_num [chiralIndex,tilt,concreteBoundaryState,Matrix.trace,
    Matrix.mul_apply,Fin.sum_univ_two]

end InfoGeometry.Canonical.KleinSewingDefect

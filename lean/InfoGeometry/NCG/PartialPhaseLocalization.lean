/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.NCG.ChiralMatrixTrace
import InfoGeometry.QuantumContext.DrazinSpectralKernel
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Partial-phase defects and finite chiral trace localization. A tripotent
phase is not assumed invertible. The actual kernel is identified only in the
index-one case; no analytic index theorem is asserted. -/

namespace InfoGeometry.NCG.PartialPhaseLocalization

open Matrix NonCommutativeFredholmIndex
open InfoGeometry.QuantumContext.Drazin
open InfoGeometry.NCG.ChiralMatrixTrace

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- The precise obstruction to commuting a phase with its commutator square. -/
theorem phase_commutator_square_defect (F E : Matrix n n R) :
    commutator F (commutator F E * commutator F E) =
      commutator (commutator (F * F) E) (commutator F E) := by
  simp only [commutator]
  noncomm_ring

/-- For a partial phase the support, not necessarily the unit, controls the defect. -/
theorem phase_commutes_commutator_square {F E : Matrix n n R}
    (h : Commute (F * F) E) :
    Commute F (commutator F E * commutator F E) := by
  apply sub_eq_zero.mp
  change commutator F (commutator F E * commutator F E) = 0
  rw [phase_commutator_square_defect]
  simp only [commutator, h.eq, sub_self, zero_mul, mul_zero]

/-- Orthogonal idempotents give the square of a signed partial phase. -/
theorem signed_projection_square {P Q : Matrix n n R}
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    (P - Q) * (P - Q) = P + Q := by
  noncomm_ring [hP.eq, hQ.eq, hPQ, hQP]

/-- The signed partial phase is tripotent without requiring full support. -/
theorem signed_projection_tripotent {P Q : Matrix n n R}
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    (P - Q) * (P - Q) * (P - Q) = P - Q := by
  rw [signed_projection_square hP hQ hPQ hQP]
  noncomm_ring [hP.eq, hQ.eq, hPQ, hQP]

/-- Every tripotent is its own Drazin inverse with index bound one. -/
theorem tripotent_isDrazinInverse {F : Matrix n n R} (hF : F * F * F = F) :
    IsDrazinInverse F F 1 := by
  refine ⟨hF, rfl, ?_⟩
  simpa only [Nat.reduceAdd, pow_two, pow_one] using hF

/-- A self-adjoint tripotent has a native star projection as its support. -/
theorem tripotent_support_isStarProjection [StarRing R] {F : Matrix n n R}
    (hF : F * F * F = F) (hstar : IsSelfAdjoint F) : IsStarProjection (F * F) := by
  refine ⟨?_, ?_⟩
  · change (F * F) * (F * F) = F * F
    rw [← mul_assoc, hF]
  · change star (F * F) = F * F
    rw [star_mul, hstar.star_eq]

/-- The partial-isometry equation follows from self-adjointness and tripotency. -/
theorem tripotent_partial_isometry [StarRing R] {F : Matrix n n R}
    (hF : F * F * F = F) (hstar : IsSelfAdjoint F) : F * star F * F = F := by
  rw [hstar.star_eq, hF]

/-- The index-one complementary projector has exactly the original operator's kernel. -/
theorem group_inverse_kernel_range {D B : Matrix n n R}
    (h : IsDrazinInverse D B 1) :
    LinearMap.range (Matrix.toLin' (kernelProj D B)) = LinearMap.ker (Matrix.toLin' D) := by
  apply le_antisymm
  · rintro v ⟨x, rfl⟩
    change Matrix.toLin' D (Matrix.toLin' (kernelProj D B) x) = 0
    rw [← Matrix.toLin'_mul_apply, group_inverse_nilpotent_zero h]
    simp
  · intro v hv
    have hv' : Matrix.toLin' D v = 0 := hv
    refine ⟨v, ?_⟩
    change Matrix.toLin' (1 - D * B) v = v
    rw [h.comm]
    simp only [map_sub, LinearMap.sub_apply, Matrix.toLin'_one, LinearMap.id_apply,
      Matrix.toLin'_mul_apply, hv', map_zero, sub_zero]

/-- Zero modes of a partial phase are the range of its complementary support. -/
theorem tripotent_kernel_range {F : Matrix n n R} (hF : F * F * F = F) :
    LinearMap.range (Matrix.toLin' (1 - F * F)) = LinearMap.ker (Matrix.toLin' F) :=
  group_inverse_kernel_range (tripotent_isDrazinInverse hF)

/-- Chiral cancellation removes the regular Drazin sector from the weighted trace. -/
theorem trace_spectralProj_zero [IsAddTorsionFree R] {γ D B : Matrix n n R} {k : ℕ}
    (hγ : anticommutator γ D = 0) (hD : IsDrazinInverse D B k) :
    trace (γ * spectralProj D B) = 0 :=
  trace_mul_eq_zero hγ hD.comm

/-- The remaining trace is exactly carried by the complementary Drazin projector. -/
theorem trace_kernelProj_eq [IsAddTorsionFree R] {γ D B : Matrix n n R} {k : ℕ}
    (hγ : anticommutator γ D = 0) (hD : IsDrazinInverse D B k) :
    trace (γ * kernelProj D B) = trace γ := by
  rw [kernelProj, mul_sub, mul_one, trace_sub, trace_spectralProj_zero hγ hD, sub_zero]

/-- In a self-inverse partial phase, localization is to its actual zero-mode projector. -/
theorem trace_tripotent_kernel_eq [IsAddTorsionFree R] {γ F : Matrix n n R}
    (hγ : anticommutator γ F = 0) (hF : F * F * F = F) :
    trace (γ * (1 - F * F)) = trace γ :=
  trace_kernelProj_eq hγ (tripotent_isDrazinInverse hF)

end InfoGeometry.NCG.PartialPhaseLocalization

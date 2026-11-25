/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.SkewGraphNeutralPairing

/-!
# Sign reversal on the primal coordinate of neutral graph submodules

The mirror is the negative of the existing native para-involution.
It exchanges the graphs of any linear map `P : E* → E` and `-P`.

Its fixed vectors in a graph are exactly the graph intersection, equivalently
the vectors `(0, ξ)` with `ξ ∈ ker P`. None of these statements needs
evaluation-skewness of `P`.

These are real linear-algebra statements. No physical CPT transformation,
Poisson integrability, or identification of covectors with entropy functions
is asserted.
-/

noncomputable section

namespace InfoGeometry.Geometry.DiracGraphMirror

open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Geometry.SkewGraphNeutralPairing
open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Sign reversal on the primal coordinate of the actual dual phase space. -/
def diracMirror : Module.End ℝ (PhaseSpaceCarrier E) :=
  -neutralParaInvolution

@[simp] theorem diracMirror_apply (z : PhaseSpaceCarrier E) :
    diracMirror z = (-z.1, z.2) := by
  simp [diracMirror, neutralParaInvolution_apply]

@[simp] theorem diracMirror_involutive (z : PhaseSpaceCarrier E) :
    diracMirror (diracMirror z) = z := by
  apply Prod.ext <;> simp only [diracMirror_apply, neg_neg]

theorem diracMirror_sq :
    diracMirror (E := E) * diracMirror = 1 := by
  apply LinearMap.ext
  intro z
  exact diracMirror_involutive z

/-- The mirror reverses the sign of the neutral bilinear form. -/
theorem diracMirror_anti_isometry (z w : PhaseSpaceCarrier E) :
    canonicalNeutralBilin (diracMirror z) (diracMirror w) =
      -canonicalNeutralBilin z w := by
  simp only [diracMirror_apply, canonicalNeutralBilin_apply, map_neg]
  abel

/-- Membership is exchanged between opposite graph submodules.
No skewness assumption is required. -/
@[simp] theorem diracMirror_mem_neg_dualGraph_iff
    (P : Module.Dual ℝ E →ₗ[ℝ] E) (z : PhaseSpaceCarrier E) :
    diracMirror z ∈ dualGraph (-P) ↔ z ∈ dualGraph P := by
  simp only [mem_dualGraph, diracMirror_apply, LinearMap.neg_apply, neg_inj]

theorem mem_dualGraph_iff_diracMirror_mem_neg
    (P : Module.Dual ℝ E →ₗ[ℝ] E) (z : PhaseSpaceCarrier E) :
    z ∈ dualGraph P ↔ diracMirror z ∈ dualGraph (-P) :=
  (diracMirror_mem_neg_dualGraph_iff P z).symm

/-- The mirror transports the actual graph submodule onto the opposite graph. -/
theorem diracMirror_map_dualGraph
    (P : Module.Dual ℝ E →ₗ[ℝ] E) :
    (dualGraph P).map diracMirror = dualGraph (-P) := by
  ext z
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (diracMirror_mem_neg_dualGraph_iff P w).mpr hw
  · intro hz
    refine ⟨diracMirror z, ?_, diracMirror_involutive z⟩
    simpa only [neg_neg] using
      (diracMirror_mem_neg_dualGraph_iff (-P) z).mpr hz

/-- Over the real numbers, a mirror-fixed vector has zero primal coordinate. -/
theorem diracMirror_fixed_iff (z : PhaseSpaceCarrier E) :
    diracMirror z = z ↔ z.1 = 0 := by
  constructor
  · intro hz
    have hneg : -z.1 = z.1 := by
      simpa only [diracMirror_apply] using congrArg Prod.fst hz
    have htwo : (2 : ℝ) • z.1 = 0 := by
      calc
        (2 : ℝ) • z.1 = z.1 + z.1 := by module
        _ = -z.1 + z.1 :=
          congrArg (fun x : E => x + z.1) hneg.symm
        _ = 0 := neg_add_cancel _
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  · intro hz
    rw [diracMirror_apply]
    exact Prod.ext (by simp only [hz, neg_zero]) rfl

/-- The fixed locus inside a graph is the zero primal coordinate over its
kernel. This holds for every linear map `P`, without skewness. -/
theorem mem_dualGraph_and_fixed_iff
    (P : Module.Dual ℝ E →ₗ[ℝ] E) (z : PhaseSpaceCarrier E) :
    (z ∈ dualGraph P ∧ diracMirror z = z) ↔
      z.1 = 0 ∧ P z.2 = 0 := by
  rw [mem_dualGraph, diracMirror_fixed_iff]
  constructor
  · rintro ⟨hgraph, hzero⟩
    exact ⟨hzero, hgraph.symm.trans hzero⟩
  · rintro ⟨hzero, hker⟩
    exact ⟨hzero.trans hker.symm, hzero⟩

/-- The graph-fixed locus is exactly the intersection of opposite graphs. -/
theorem mem_dualGraph_and_fixed_iff_mem_inf
    (P : Module.Dual ℝ E →ₗ[ℝ] E) (z : PhaseSpaceCarrier E) :
    (z ∈ dualGraph P ∧ diracMirror z = z) ↔
      z ∈ dualGraph P ⊓ dualGraph (-P) :=
  (mem_dualGraph_and_fixed_iff P z).trans
    (mem_dualGraph_inf_neg P z).symm

/-- Explicit native kernel-image formulation of the same fixed locus. -/
theorem mem_dualGraph_and_fixed_iff_mem_kernelImage
    (P : Module.Dual ℝ E →ₗ[ℝ] E) (z : PhaseSpaceCarrier E) :
    (z ∈ dualGraph P ∧ diracMirror z = z) ↔
      z ∈ (LinearMap.ker P).map
        (LinearMap.inr ℝ E (Module.Dual ℝ E)) := by
  rw [← dualGraph_inf_neg_eq P]
  exact mem_dualGraph_and_fixed_iff_mem_inf P z

/-- Mirroring both endpoints of every scalar contraction gives one sign per edge. -/
theorem diracMirror_pairing_prod {ι : Type*} (s : Finset ι)
    (z w : ι → PhaseSpaceCarrier E) :
    (∏ i ∈ s, canonicalNeutralBilin (diracMirror (z i)) (diracMirror (w i))) =
      (-1 : ℝ) ^ s.card * ∏ i ∈ s, canonicalNeutralBilin (z i) (w i) := by
  simpa only [diracMirror_anti_isometry] using
    (Finset.prod_neg (s := s) (fun i => canonicalNeutralBilin (z i) (w i)))

end InfoGeometry.Geometry.DiracGraphMirror

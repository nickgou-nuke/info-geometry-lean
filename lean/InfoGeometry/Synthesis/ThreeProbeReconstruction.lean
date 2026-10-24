/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.SedenionSocleDirectSumSeparationBridge

/-! Exact invisible matrices and reconstruction for the owner's three probes.
These statements concern the full real matrix space, not a restricted Lie family. -/

namespace InfoGeometry.Synthesis.SedenionSocleDirectSumSeparationBridge

abbrev ProbeMatrix := Matrix (Fin 3) (Fin 3) ℝ

def invisibleRows (c : Fin 3 → ℝ) : ProbeMatrix :=
  fun i j => c i * (![-1, 1, -1] : Fin 3 → ℝ) j

theorem invisibleRows_injective : Function.Injective invisibleRows := by
  intro c d h
  funext i
  have hi := congrArg (fun X : ProbeMatrix => X i 1) h
  simpa [invisibleRows] using hi

theorem two_probe_kernel_iff (X : ProbeMatrix) :
    (X.mulVec probeP1 = 0 ∧ X.mulVec probeP2 = 0) ↔
      X = invisibleRows (fun i => X i 1) := by
  constructor
  · rintro ⟨h1, h2⟩
    ext i j
    have hi1 := congrFun h1 i
    have hi2 := congrFun h2 i
    simp [probeP1, probeP2, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hi1 hi2
    fin_cases j <;> simp [invisibleRows] <;> linarith
  · intro h
    rw [h]
    constructor <;> funext i <;>
      simp [invisibleRows, probeP1, probeP2, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem two_probe_kernel_unique (X : ProbeMatrix) :
    (X.mulVec probeP1 = 0 ∧ X.mulVec probeP2 = 0) ↔
      ∃! c, X = invisibleRows c := by
  constructor
  · intro h
    refine ⟨fun i => X i 1, (two_probe_kernel_iff X).mp h, ?_⟩
    intro c hc
    exact invisibleRows_injective (hc.symm.trans ((two_probe_kernel_iff X).mp h))
  · rintro ⟨c, rfl, _⟩
    apply (two_probe_kernel_iff _).mpr
    simp [invisibleRows]

theorem two_probe_fiber_iff (X Y : ProbeMatrix) :
    (X.mulVec probeP1 = Y.mulVec probeP1 ∧ X.mulVec probeP2 = Y.mulVec probeP2) ↔
      ∃! c, X - Y = invisibleRows c := by
  rw [← two_probe_kernel_unique]
  simp only [Matrix.sub_mulVec, sub_eq_zero]

noncomputable def reconstructProbes (u v w : Fin 3 → ℝ) : ProbeMatrix :=
  fun i => ![(v i + w i - u i) / 2,
             (u i + v i - w i) / 2,
             (u i + w i - v i) / 2]

theorem reconstructProbes_readback (X : ProbeMatrix) :
    reconstructProbes (X.mulVec probeP1) (X.mulVec probeP2) (X.mulVec probeP3) = X := by
  ext i j
  fin_cases j <;>
    simp [reconstructProbes, probeP1, probeP2, probeP3,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem three_probes_injective : Function.Injective
    (fun X : ProbeMatrix => (X.mulVec probeP1, X.mulVec probeP2, X.mulVec probeP3)) := by
  intro X Y h
  have h1 := congrArg (fun p => p.1) h
  have h2 := congrArg (fun p => p.2.1) h
  have h3 := congrArg (fun p => p.2.2) h
  dsimp only at h1 h2 h3
  rw [← reconstructProbes_readback X, h1, h2, h3, reconstructProbes_readback]

end InfoGeometry.Synthesis.SedenionSocleDirectSumSeparationBridge

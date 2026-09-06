import InfoGeometry.Topology.MobiusGeometry
import InfoGeometry.Topology.MobiusRecoveredHelpers
import InfoGeometry.Topology.MobiusNormalizationRecovered

namespace InfoGeometry

open Classical

/-- Strict 3-transitivity of the Möbius action, rebuilt from the concrete `0,1,∞` packet. -/
theorem strictly_three_transitive
    (z1 z2 z3 : RiemannSphere) (h12 : z1 ≠ z2) (h23 : z2 ≠ z3) (h13 : z1 ≠ z3)
    (w1 w2 w3 : RiemannSphere) (g12 : w1 ≠ w2) (g23 : w2 ≠ w3) (g13 : w1 ≠ w3) :
    ∃ M : MobiusTransform,
      M.eval z1 = w1 ∧ M.eval z2 = w2 ∧ M.eval z3 = w3 ∧
      ∀ M' : MobiusTransform, M'.eval z1 = w1 ∧ M'.eval z2 = w2 ∧ M'.eval z3 = w3 →
        M.equiv M' := by
  obtain ⟨M1, h1z1, h1z2, h1z3⟩ := maps_to_01inf_recovered z1 z2 z3 h12 h23 h13
  obtain ⟨M2, h2w1, h2w2, h2w3⟩ := maps_to_01inf_recovered w1 w2 w3 g12 g23 g13
  let M := InfoGeometry.Topology.MobiusRecoveredHelpers.comp
      (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2) M1
  have hmz1 : M.eval z1 = w1 := by
    have hcomp : M.eval z1 = (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2).eval (M1.eval z1) := by
      simpa [M, InfoGeometry.Topology.MobiusRecoveredHelpers.comp] using
        (InfoGeometry.Topology.MobiusRecoveredHelpers.eval_comp
          (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2) M1 z1)
    rw [h1z1] at hcomp
    rw [hcomp]
    exact by
      have h_inv : (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2).eval (M2.eval w1) = w1 :=
        InfoGeometry.Topology.MobiusRecoveredHelpers.eval_inv_left M2 w1
      rw [h2w1] at h_inv
      exact h_inv
  have hmz2 : M.eval z2 = w2 := by
    have hcomp : M.eval z2 = (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2).eval (M1.eval z2) := by
      simpa [M, InfoGeometry.Topology.MobiusRecoveredHelpers.comp] using
        (InfoGeometry.Topology.MobiusRecoveredHelpers.eval_comp
          (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2) M1 z2)
    rw [h1z2] at hcomp
    rw [hcomp]
    exact by
      have h_inv : (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2).eval (M2.eval w2) = w2 :=
        InfoGeometry.Topology.MobiusRecoveredHelpers.eval_inv_left M2 w2
      rw [h2w2] at h_inv
      exact h_inv
  have hmz3 : M.eval z3 = w3 := by
    have hcomp : M.eval z3 = (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2).eval (M1.eval z3) := by
      simpa [M, InfoGeometry.Topology.MobiusRecoveredHelpers.comp] using
        (InfoGeometry.Topology.MobiusRecoveredHelpers.eval_comp
          (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2) M1 z3)
    rw [h1z3] at hcomp
    rw [hcomp]
    exact by
      have h_inv : (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2).eval (M2.eval w3) = w3 :=
        InfoGeometry.Topology.MobiusRecoveredHelpers.eval_inv_left M2 w3
      rw [h2w3] at h_inv
      exact h_inv
  refine ⟨M, hmz1, hmz2, hmz3, ?_⟩
  intro M' hM'
  intro z
  let M_test := InfoGeometry.Topology.MobiusRecoveredHelpers.comp M2
      (InfoGeometry.Topology.MobiusRecoveredHelpers.comp M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1))
  have ht0 : M_test.eval (some 0) = some 0 := by
    have hcomp1 : M_test.eval (some 0) = M2.eval ((InfoGeometry.Topology.MobiusRecoveredHelpers.comp M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1)).eval (some 0)) := by
      simpa [M_test, InfoGeometry.Topology.MobiusRecoveredHelpers.comp] using
        (InfoGeometry.Topology.MobiusRecoveredHelpers.eval_comp
          M2 (InfoGeometry.Topology.MobiusRecoveredHelpers.comp M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1)) (some 0))
    rw [hcomp1]
    have hcomp2 : (InfoGeometry.Topology.MobiusRecoveredHelpers.comp M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1)).eval (some 0) =
        M'.eval ((InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1).eval (some 0)) := by
      simpa [InfoGeometry.Topology.MobiusRecoveredHelpers.comp] using
        (InfoGeometry.Topology.MobiusRecoveredHelpers.eval_comp M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1) (some 0))
    rw [hcomp2]
    have h_inv : (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1).eval (M1.eval z1) = z1 :=
      InfoGeometry.Topology.MobiusRecoveredHelpers.eval_inv_left M1 z1
    rw [h1z1] at h_inv
    rw [h_inv]
    rw [hM'.1]
    exact h2w1
  have ht1 : M_test.eval (some 1) = some 1 := by
    have hcomp1 : M_test.eval (some 1) = M2.eval ((InfoGeometry.Topology.MobiusRecoveredHelpers.comp M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1)).eval (some 1)) := by
      simpa [M_test, InfoGeometry.Topology.MobiusRecoveredHelpers.comp] using
        (InfoGeometry.Topology.MobiusRecoveredHelpers.eval_comp
          M2 (InfoGeometry.Topology.MobiusRecoveredHelpers.comp M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1)) (some 1))
    rw [hcomp1]
    have hcomp2 : (InfoGeometry.Topology.MobiusRecoveredHelpers.comp M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1)).eval (some 1) =
        M'.eval ((InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1).eval (some 1)) := by
      simpa [InfoGeometry.Topology.MobiusRecoveredHelpers.comp] using
        (InfoGeometry.Topology.MobiusRecoveredHelpers.eval_comp M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1) (some 1))
    rw [hcomp2]
    have h_inv : (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1).eval (M1.eval z2) = z2 :=
      InfoGeometry.Topology.MobiusRecoveredHelpers.eval_inv_left M1 z2
    rw [h1z2] at h_inv
    rw [h_inv]
    rw [hM'.2.1]
    exact h2w2
  have htinf : M_test.eval none = none := by
    have hcomp1 : M_test.eval none = M2.eval ((InfoGeometry.Topology.MobiusRecoveredHelpers.comp M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1)).eval none) := by
      simpa [M_test, InfoGeometry.Topology.MobiusRecoveredHelpers.comp] using
        (InfoGeometry.Topology.MobiusRecoveredHelpers.eval_comp
          M2 (InfoGeometry.Topology.MobiusRecoveredHelpers.comp M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1)) none)
    rw [hcomp1]
    have hcomp2 : (InfoGeometry.Topology.MobiusRecoveredHelpers.comp M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1)).eval none =
        M'.eval ((InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1).eval none) := by
      simpa [InfoGeometry.Topology.MobiusRecoveredHelpers.comp] using
        (InfoGeometry.Topology.MobiusRecoveredHelpers.eval_comp M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1) none)
    rw [hcomp2]
    have h_inv : (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1).eval (M1.eval z3) = z3 :=
      InfoGeometry.Topology.MobiusRecoveredHelpers.eval_inv_left M1 z3
    rw [h1z3] at h_inv
    rw [h_inv]
    rw [hM'.2.2]
    exact h2w3
  have h_id := mobius_unique_01inf M_test ht0 ht1 htinf
  have h_M_eq_M' : ∀ y, M.eval y = M'.eval y := by
    intro y
    have h_z_eq : M_test.eval (M1.eval y) = M1.eval y := h_id (M1.eval y)
    have h_z_expand : M_test.eval (M1.eval y) = M2.eval (M'.eval y) := by
      have hstep1 : M_test.eval (M1.eval y) = M2.eval ((InfoGeometry.Topology.MobiusRecoveredHelpers.comp M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1)).eval (M1.eval y)) := by
        simpa [M_test, InfoGeometry.Topology.MobiusRecoveredHelpers.comp] using
          (InfoGeometry.Topology.MobiusRecoveredHelpers.eval_comp
            M2 (InfoGeometry.Topology.MobiusRecoveredHelpers.comp M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1)) (M1.eval y))
      have hstep2 : M2.eval ((InfoGeometry.Topology.MobiusRecoveredHelpers.comp M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1)).eval (M1.eval y)) =
          M2.eval (M'.eval ((InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1).eval (M1.eval y))) := by
        simpa [InfoGeometry.Topology.MobiusRecoveredHelpers.comp] using
          congrArg M2.eval (InfoGeometry.Topology.MobiusRecoveredHelpers.eval_comp
            M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1) (M1.eval y))
      have hstep3 : M2.eval (M'.eval ((InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1).eval (M1.eval y))) = M2.eval (M'.eval y) := by
        simpa using congrArg (fun t => M2.eval (M'.eval t))
          (InfoGeometry.Topology.MobiusRecoveredHelpers.eval_inv_left M1 y)
      calc M_test.eval (M1.eval y) = M2.eval ((InfoGeometry.Topology.MobiusRecoveredHelpers.comp M' (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1)).eval (M1.eval y)) := hstep1
        _ = M2.eval (M'.eval ((InfoGeometry.Topology.MobiusRecoveredHelpers.inv M1).eval (M1.eval y))) := hstep2
        _ = M2.eval (M'.eval y) := hstep3
    rw [h_z_expand] at h_z_eq
    have hmain1 : M.eval y = (InfoGeometry.Topology.MobiusRecoveredHelpers.comp (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2) M1).eval y := rfl
    have hmain2 : (InfoGeometry.Topology.MobiusRecoveredHelpers.comp (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2) M1).eval y =
        (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2).eval (M1.eval y) := by
      simpa [M, InfoGeometry.Topology.MobiusRecoveredHelpers.comp] using
        (InfoGeometry.Topology.MobiusRecoveredHelpers.eval_comp
          (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2) M1 y)
    have hmain3 : (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2).eval (M1.eval y) =
        (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2).eval (M2.eval (M'.eval y)) := by rw [← h_z_eq]
    have hmain4 : (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2).eval (M2.eval (M'.eval y)) = M'.eval y :=
      InfoGeometry.Topology.MobiusRecoveredHelpers.eval_inv_left M2 (M'.eval y)
    calc M.eval y = (InfoGeometry.Topology.MobiusRecoveredHelpers.comp (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2) M1).eval y := hmain1
      _ = (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2).eval (M1.eval y) := hmain2
      _ = (InfoGeometry.Topology.MobiusRecoveredHelpers.inv M2).eval (M2.eval (M'.eval y)) := hmain3
      _ = M'.eval y := hmain4
  exact h_M_eq_M' z

end InfoGeometry

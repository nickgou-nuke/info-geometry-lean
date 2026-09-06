import InfoGeometry.Topology.MobiusGeometry

/-!
# MobiusNormalizationRecovered

Small recovery packet for the concrete `0,1,∞` normalization.
-/

namespace InfoGeometry

open Complex

lemma maps_to_01inf_recovered (z1 z2 z3 : RiemannSphere)
    (h12 : z1 ≠ z2) (h23 : z2 ≠ z3) (h13 : z1 ≠ z3) :
    ∃ M : MobiusTransform, M.eval z1 = some 0 ∧ M.eval z2 = some 1 ∧ M.eval z3 = none := by
  cases z1 with
  | none =>
      cases z2 with
      | none => exact (h12 rfl).elim
      | some z2 =>
          cases z3 with
          | none => exact (h13 rfl).elim
          | some z3 =>
              have hz23 : z2 ≠ z3 := by
                intro hz
                exact h23 (by simpa [hz])
              let M : MobiusTransform :=
                { a := 0,
                  b := z2 - z3,
                  c := 1,
                  d := -z3,
                  det_ne_zero := by
                    have hdet : (0 : ℂ) * (-z3) - (z2 - z3) * (1 : ℂ) = -(z2 - z3) := by ring
                    rw [hdet]
                    exact neg_ne_zero.mpr (sub_ne_zero.mpr hz23) }
              refine ⟨M, ?_, ?_, ?_⟩
              · simp [M, MobiusTransform.eval]
              · have hden : z2 - z3 ≠ 0 := sub_ne_zero.mpr hz23
                have hsub : z2 + -z3 = z2 - z3 := by ring
                simp [M, MobiusTransform.eval, hden, hsub]
              · have hden0 : z3 + -z3 = 0 := by ring
                simp [M, MobiusTransform.eval, hden0]
  | some z1 =>
      cases z2 with
      | none =>
          cases z3 with
          | none => exact (h23 rfl).elim
          | some z3 =>
              have hz13 : z1 ≠ z3 := by
                intro hz
                exact h13 (by simpa [hz])
              let M : MobiusTransform :=
                { a := 1,
                  b := -z1,
                  c := 1,
                  d := -z3,
                  det_ne_zero := by
                    have hdet : (1 : ℂ) * (-z3) - (-z1) * (1 : ℂ) = z1 - z3 := by ring
                    rw [hdet]
                    exact sub_ne_zero.mpr hz13 }
              refine ⟨M, ?_, ?_, ?_⟩
              · have hden : z1 - z3 ≠ 0 := sub_ne_zero.mpr hz13
                have hsub : z1 + -z3 = z1 - z3 := by ring
                simp [M, MobiusTransform.eval, hden, hsub]
              · simp [M, MobiusTransform.eval]
              · have hden0 : z3 + -z3 = 0 := by ring
                simp [M, MobiusTransform.eval, hden0]
      | some z2 =>
          cases z3 with
          | none =>
              have hz12 : z1 ≠ z2 := by
                intro hz
                exact h12 (by simpa [hz])
              let M : MobiusTransform :=
                { a := 1,
                  b := -z1,
                  c := 0,
                  d := z2 - z1,
                  det_ne_zero := by
                    have hdet : (1 : ℂ) * (z2 - z1) - (-z1) * (0 : ℂ) = z2 - z1 := by ring
                    rw [hdet]
                    exact sub_ne_zero.mpr hz12.symm }
              refine ⟨M, ?_, ?_, ?_⟩
              · have hden : z2 - z1 ≠ 0 := sub_ne_zero.mpr hz12.symm
                simp [M, MobiusTransform.eval, hden]
              · have hden : z2 - z1 ≠ 0 := sub_ne_zero.mpr hz12.symm
                have hsub : z2 + -z1 = z2 - z1 := by ring
                simp [M, MobiusTransform.eval, hden, hsub]
              · simp [M, MobiusTransform.eval]
          | some z3 =>
              have hz12 : z1 ≠ z2 := by
                intro hz
                exact h12 (by simpa [hz])
              have hz23 : z2 ≠ z3 := by
                intro hz
                exact h23 (by simpa [hz])
              have hz13 : z1 ≠ z3 := by
                intro hz
                exact h13 (by simpa [hz])
              let M : MobiusTransform :=
                { a := z2 - z3,
                  b := -(z2 - z3) * z1,
                  c := z2 - z1,
                  d := -(z2 - z1) * z3,
                  det_ne_zero := by
                    have hdet :
                        (z2 - z3) * (-(z2 - z1) * z3) - (-(z2 - z3) * z1) * (z2 - z1) =
                          (z2 - z3) * (z2 - z1) * (z1 - z3) := by
                      ring
                    rw [hdet]
                    exact mul_ne_zero
                      (mul_ne_zero (sub_ne_zero.mpr hz23) (sub_ne_zero.mpr hz12.symm))
                      (sub_ne_zero.mpr hz13) }
              refine ⟨M, ?_, ?_, ?_⟩
              · have hden1 : (z2 - z1) * z1 + (z1 - z2) * z3 ≠ 0 := by
                  have hneq : (z2 - z1) * (z1 - z3) ≠ 0 := by
                    exact mul_ne_zero (sub_ne_zero.mpr hz12.symm) (sub_ne_zero.mpr hz13)
                  have hiden : (z2 - z1) * z1 + (z1 - z2) * z3 = (z2 - z1) * (z1 - z3) := by
                    ring
                  rw [hiden]
                  exact hneq
                have hnum : (z2 - z3) * z1 + (z3 - z2) * z1 = 0 := by ring
                simp [M, MobiusTransform.eval, hden1, hnum]
              · have hden2 : (z2 - z1) * z2 + (z1 - z2) * z3 ≠ 0 := by
                  have hneq : (z2 - z1) * (z2 - z3) ≠ 0 := by
                    exact mul_ne_zero (sub_ne_zero.mpr hz12.symm) (sub_ne_zero.mpr hz23)
                  have hiden : (z2 - z1) * z2 + (z1 - z2) * z3 = (z2 - z1) * (z2 - z3) := by
                    ring
                  rw [hiden]
                  exact hneq
                have hq : ((z2 - z3) * z2 + (z3 - z2) * z1) / ((z2 - z1) * z2 + (z1 - z2) * z3) = 1 := by
                  have hnumden :
                      (z2 - z3) * z2 + (z3 - z2) * z1 = (z2 - z1) * z2 + (z1 - z2) * z3 := by
                    ring
                  rw [hnumden]
                  exact div_self hden2
                simp [M, MobiusTransform.eval, hden2, hq]
              · have hden0 : (z2 - z1) * z3 + (z1 - z2) * z3 = 0 := by ring
                simp [M, MobiusTransform.eval, hden0]

end InfoGeometry

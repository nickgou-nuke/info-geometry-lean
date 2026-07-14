import InfoGeometry.Topology.MobiusGeometry

/-!
# MobiusInverseEval

Basic inverse-evaluation readback for Möbius transformations.
-/

namespace InfoGeometry

open Complex

/-- Explicit inverse Möbius transform. -/
def mobiusInv (M : MobiusTransform) : MobiusTransform :=
  { a := M.d,
    b := -M.b,
    c := -M.c,
    d := M.a,
    det_ne_zero := by
      have h : M.d * M.a - -M.b * -M.c = M.a * M.d - M.b * M.c := by ring
      rw [h]
      exact M.det_ne_zero }

lemma mobius_inverse_eval (M : MobiusTransform) (z : RiemannSphere) :
    M.eval ((mobiusInv M).eval z) = z := by
  cases z with
  | none =>
      by_cases hc : M.c = 0
      · simp [MobiusTransform.eval, mobiusInv, hc]
      · have hden : M.c * (M.d / -M.c) + M.d = 0 := by
          field_simp [hc]
          ring
        simp [MobiusTransform.eval, mobiusInv, hc, hden]
  | some z =>
      by_cases hN : -M.c * z + M.a = 0
      · have hc : M.c ≠ 0 := by
          intro hc
          have ha : M.a = 0 := by simpa [hc] using hN
          have hdet : M.a * M.d - M.b * M.c = 0 := by
            simpa [ha, hc] using (show M.a * M.d - M.b * M.c = 0 by ring)
          exact M.det_ne_zero hdet
        have hmul : M.a = z * M.c := by
          have h' : M.a - M.c * z = 0 := by
            calc
              M.a - M.c * z = -M.c * z + M.a := by ring
              _ = 0 := hN
          have h'' : M.a = M.c * z := sub_eq_zero.mp h'
          simpa [mul_comm] using h''
        have hinv0 : (mobiusInv M).eval (some z) = none := by
          dsimp [mobiusInv, MobiusTransform.eval]
          rw [hN]
          simp
        have hM : M.eval none = some z := by
          dsimp [MobiusTransform.eval]
          rw [if_neg hc]
          have hq : M.a / M.c = z := by
            have h'' : M.a = z * M.c := hmul
            exact (div_eq_iff hc).2 h''
          simp [hq, sub_eq_add_neg]
        simpa [hinv0, hM]
      · have hN' : -M.c * z + M.a ≠ 0 := hN
        set N : ℂ := -M.c * z + M.a
        set w : ℂ := (M.d * z - M.b) / N
        have hw : (mobiusInv M).eval (some z) = some w := by
          dsimp [mobiusInv, MobiusTransform.eval, N, w]
          rw [if_neg hN']
          simp [sub_eq_add_neg]
        have hwN : w * N = M.d * z - M.b := by
          subst w
          field_simp [hN']
        have hprod : (M.c * w + M.d) * N = M.a * M.d - M.b * M.c := by
          calc
            (M.c * w + M.d) * N = M.c * (w * N) + M.d * N := by ring
            _ = M.c * (M.d * z - M.b) + M.d * N := by rw [hwN]
            _ = M.a * M.d - M.b * M.c := by
              subst N
              ring
        have hden : M.c * w + M.d ≠ 0 := by
          intro hzero
          have hdet : M.a * M.d - M.b * M.c = 0 := by
            have h := hprod
            rw [hzero, zero_mul] at h
            exact h.symm
          exact M.det_ne_zero hdet
        have hq : (M.a * w + M.b) / (M.c * w + M.d) = z := by
          subst N w
          field_simp [hN']
          ring_nf
        simp [MobiusTransform.eval, hw, hden, hq]

end InfoGeometry

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveNilpotentFlows

/-! Double-shear square law on the existing reflexive square-zero carrier.
The support term is `-d*B`, not `-B*d`. -/

namespace InfoGeometry.Canonical.ReflexiveNilpotentFlows

variable {A : Type*} [Ring A]

def doubleShear (d B : A) : A := (1 + d) * (1 - B)

theorem doubleShear_square {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hr : d * B * d = d) (hs : B * d * B = B) :
    doubleShear d B * doubleShear d B = complement d B - d * B + d - B := by
  have hc := (complement_annihilates hd hB hr hs).2.2.1
  calc
    _ = weyl d B * (1 - B) := by
      rw [← weyl_factorization hd hr]
      simp only [doubleShear, mul_assoc]
    _ = _ := by unfold weyl; noncomm_ring [hc, hB]

theorem doubleShear_wrong_square_iff {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hr : d * B * d = d) (hs : B * d * B = B) :
    doubleShear d B * doubleShear d B = complement d B + d - B - B * d ↔
      d * B = B * d := by
  rw [doubleShear_square hd hB hr hs]
  constructor <;> intro h <;> linear_combination (norm := noncomm_ring) -h

end InfoGeometry.Canonical.ReflexiveNilpotentFlows

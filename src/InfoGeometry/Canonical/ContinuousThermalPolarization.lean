/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.BogoliubovProjectorTransport

noncomputable section
namespace InfoGeometry.Canonical.BogoliubovProjectorTransport

open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

 theorem modular_j_conjugates_weighted_polarization (q : ℝ) :
    ((modular_j (E := E)).comp
        ((((1 + q) / 2 : ℝ) • spectralPlusProj (E := E)) +
          (((1 - q) / 2 : ℝ) • spectralMinusProj (E := E)))).comp
        (modular_j (E := E)) =
      (((1 - q) / 2 : ℝ) • spectralPlusProj (E := E)) +
        (((1 + q) / 2 : ℝ) • spectralMinusProj (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hp := congrArg (fun F : EndH => F u)
    (spectralPlusProj_comp_modular_j (E := E))
  have hm := congrArg (fun F : EndH => F u)
    (spectralMinusProj_comp_modular_j (E := E))
  have hj := congrArg (fun F : EndH => F u)
    (modular_j_involution (E := E))
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    smul_apply] at hp hm hj ⊢
  rw [map_add, map_smul, map_smul]
  rw [hp, hm]
  have hjp : modular_j (E := E) (modular_j (E := E)
      (spectralPlusProj (E := E) u)) = spectralPlusProj (E := E) u := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun F : EndH => F (spectralPlusProj (E := E) u))
        (modular_j_involution (E := E))
  have hjm : modular_j (E := E) (modular_j (E := E)
      (spectralMinusProj (E := E) u)) = spectralMinusProj (E := E) u := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun F : EndH => F (spectralMinusProj (E := E) u))
        (modular_j_involution (E := E))
  rw [hjm, hjp]
  module

end InfoGeometry.Canonical.BogoliubovProjectorTransport

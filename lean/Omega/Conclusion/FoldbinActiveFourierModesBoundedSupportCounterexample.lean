/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Omega.Conclusion.FoldbinActiveFourierModesDiverge

namespace Omega.Conclusion

/-- A one-mode family on growing finite carriers. Its coefficient-square sum
is exactly the normalized excess in `hCol`, but its active support always has
cardinality one. Thus the source lower bound alone does not imply divergence
unless the normalized excess is assumed to grow. -/
def oneModeCoefficient (n : ℕ) (k : Fin (n + 2)) : ℝ :=
  if k.val = 1 then 1 else 0

noncomputable def oneModeCollisionValue (n : ℕ) : ℝ := 2 / (n + 2 : ℝ)

theorem one_mode_support_stays_bounded_on_growing_carriers (n : ℕ) :
    (Fintype.card {k : Fin (n + 2) // k ≠ 0 ∧ oneModeCoefficient n k ≠ 0} : ℝ) = 1 ∧
      (Fintype.card (Fin (n + 2)) : ℝ) *
          (oneModeCollisionValue n -
            1 / (Fintype.card (Fin (n + 2)) : ℝ)) =
        ∑ k : {k : Fin (n + 2) // k ≠ 0}, (oneModeCoefficient n k) ^ 2 ∧
      (∀ k, 0 ≤ oneModeCoefficient n k ∧ oneModeCoefficient n k ≤ 1) := by
  classical
  let k₁ : Fin (n + 2) := ⟨1, by omega⟩
  have hk₁ : k₁ ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [k₁] at hv
  let z : {k : Fin (n + 2) // k ≠ 0} := ⟨k₁, hk₁⟩
  have hsum :
      ∑ k : {k : Fin (n + 2) // k ≠ 0}, (oneModeCoefficient n k.1) ^ 2 = 1 := by
    calc
      ∑ k : {k : Fin (n + 2) // k ≠ 0}, (oneModeCoefficient n k.1) ^ 2 =
          ∑ k : {k : Fin (n + 2) // k ≠ 0}, if k = z then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro k hk
            by_cases h : k = z
            · simp [oneModeCoefficient, z, k₁, h]
            · have hval : k.1.val ≠ 1 := by
                intro hv
                apply h
                apply Subtype.ext
                apply Fin.ext
                simpa [z, k₁] using hv
              simp [oneModeCoefficient, h, hval]
      _ = 1 := by simp [z]
  have hcard : Fintype.card {k : Fin (n + 2) // k ≠ 0 ∧ oneModeCoefficient n k ≠ 0} = 1 := by
    let e : {k : Fin (n + 2) // k ≠ 0 ∧ oneModeCoefficient n k ≠ 0} ≃ PUnit.{1} :=
      { toFun := fun _ => PUnit.unit
        invFun := fun _ => ⟨k₁, ⟨hk₁, by simp [oneModeCoefficient, k₁]⟩⟩
        left_inv := by
          intro k
          apply Subtype.ext
          apply Fin.ext
          have hv : k.1.val = 1 := by
            by_contra hne
            have hz : oneModeCoefficient n k.1 = 0 := by
              simp [oneModeCoefficient, hne]
            exact k.2.2 hz
          simpa [k₁] using hv.symm
        right_inv := by intro u; cases u; rfl }
    simpa using Fintype.card_congr e
  have hdim : (Fintype.card (Fin (n + 2)) : ℝ) = (n + 2 : ℝ) := by simp
  have hden : (n + 2 : ℝ) ≠ 0 := by positivity
  have hcollision :
      (Fintype.card (Fin (n + 2)) : ℝ) *
          (oneModeCollisionValue n -
            1 / (Fintype.card (Fin (n + 2)) : ℝ)) = 1 := by
    rw [hdim]
    simp only [oneModeCollisionValue]
    field_simp
    <;> ring
  refine ⟨by exact_mod_cast hcard, hcollision.trans hsum.symm, ?_⟩
  intro k
  by_cases h : k.val = 1 <;> simp [oneModeCoefficient, h]

end Omega.Conclusion

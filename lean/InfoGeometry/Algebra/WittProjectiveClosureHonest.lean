import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Virasoro.WittAlgebra
import InfoGeometry.External.Virasoro.VirasoroCocycle

/-!
# Honest Witt / projective closure packet

This file records only finite theorem-honest facts already supported by the
repo's imported Witt/Virasoro infrastructure.

It does NOT prove any physical vanishing of a global central charge, any
`O(5,5)` cancellation theorem, or any Krein-realization theorem for Virasoro.

It DOES prove:
- the anomaly polynomial `m^3 - m` vanishes on `{-1,0,1}`;
- therefore the Virasoro cocycle vanishes on the projective generators;
- the Witt bracket on `ℓ_{-1}, ℓ_0, ℓ_1` is the usual centerless bracket;
- if the Witt bracket coefficient is nonzero on two projective generators, then
  the output index stays inside `{-1,0,1}`.
-/

namespace InfoGeometry.Algebra.WittProjectiveClosureHonest

open VirasoroProject
open VirasoroProject.WittAlgebra

/-- The projective generator set `{−1, 0, 1}`. -/
def ProjectiveClosure : Set ℤ := {n | n = -1 ∨ n = 0 ∨ n = 1}

@[simp] theorem mem_projectiveClosure (n : ℤ) :
    n ∈ ProjectiveClosure ↔ n = -1 ∨ n = 0 ∨ n = 1 := Iff.rfl

/-- The scalar anomaly factor appearing in the Virasoro cocycle. -/
def anomalyFactor (m : ℤ) : ℤ := m ^ 3 - m

@[simp] theorem anomalyFactor_neg_one : anomalyFactor (-1) = 0 := by
  norm_num [anomalyFactor]

@[simp] theorem anomalyFactor_zero : anomalyFactor 0 = 0 := by
  norm_num [anomalyFactor]

@[simp] theorem anomalyFactor_one : anomalyFactor 1 = 0 := by
  norm_num [anomalyFactor]

/-- On the Möbius/projective indices `{-1,0,1}`, the anomaly factor vanishes. -/
theorem anomalyFactor_eq_zero_of_mem_projective {m : ℤ} (hm : m ∈ ProjectiveClosure) :
    anomalyFactor m = 0 := by
  rcases hm with rfl | rfl | rfl <;> simp [anomalyFactor]

section Field

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]

/-- The Virasoro cocycle vanishes on every projective generator `ℓ_m`, `m ∈ {-1,0,1}`. -/
theorem virasoroCocycle_lgen_left_projective_zero (m n : ℤ) (hm : m ∈ ProjectiveClosure) :
    virasoroCocycle 𝕜 (lgen 𝕜 m) (lgen 𝕜 n) = 0 := by
  rw [virasoroCocycle_apply_lgen_lgen]
  rcases hm with rfl | rfl | rfl
  · by_cases h : -1 + n = 0
    · have hn : n = 1 := by linarith
      simp [hn]
      norm_num
    · simp [h]
  · simp
  · by_cases h : 1 + n = 0
    · have hn : n = -1 := by linarith
      simp [hn]
    · simp [h]

/-- Symmetrically, the Virasoro cocycle vanishes when the right index is projective. -/
theorem virasoroCocycle_lgen_right_projective_zero (m n : ℤ) (hn : n ∈ ProjectiveClosure) :
    virasoroCocycle 𝕜 (lgen 𝕜 m) (lgen 𝕜 n) = 0 := by
  rw [virasoroCocycle_apply_lgen_lgen]
  rcases hn with rfl | rfl | rfl
  · by_cases h : m + -1 = 0
    · have hm : m = 1 := by linarith
      simp [hm]
    · simp [h]
  · by_cases hm : m = 0
    · simp [hm]
    · simp [hm]
  · by_cases h : m + 1 = 0
    · have hm : m = -1 := by linarith
      simp [hm]
      norm_num
    · simp [h]

end Field

section CommRing

variable (𝕜 : Type*) [CommRing 𝕜] [CharZero 𝕜] [IsDomain 𝕜]
  [Module.IsTorsionFree 𝕜 (WittAlgebra 𝕜)]

/-- On the projective generators, the bracket is the centerless Witt bracket.
This is just the imported Witt-algebra basis relation, recorded on the
projective surface. -/
theorem projective_bracket_eq_witt (m n : ℤ) (_hm : m ∈ ProjectiveClosure) (_hn : n ∈ ProjectiveClosure) :
    ⁅lgen 𝕜 m, lgen 𝕜 n⁆ = (m - n : 𝕜) • lgen 𝕜 (m + n) := by
  exact bracket_lgen_lgen (𝕜 := 𝕜) m n

end CommRing

section ClosureOnly

variable (𝕜 : Type*) [CommRing 𝕜]

/-- If two projective generators have nonzero Witt bracket coefficient, then the
output index still lies in the projective set. This is the finite `sl₂` closure
fact for `{-1,0,1}`. -/
theorem projective_sum_mem_of_bracket_coeff_ne_zero
    {m n : ℤ} (hm : m ∈ ProjectiveClosure) (hn : n ∈ ProjectiveClosure)
    (hcoeff : (m - n : 𝕜) ≠ 0) :
    m + n ∈ ProjectiveClosure := by
  rcases hm with rfl | rfl | rfl <;>
    rcases hn with rfl | rfl | rfl <;>
    simp at hcoeff ⊢

end ClosureOnly

end InfoGeometry.Algebra.WittProjectiveClosureHonest

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.HodgeCohomology.KreinHodgeObstruction

/-!
# Bounded contraction of the exact Krein-null complex

Contract: retain `nullDirac` on the owner's `DoubledSpace ℝ`, with its
indefinite adjoint unchanged. Construct a continuous linear homotopy `h`
with `h² = 0` and `dh + hd = 1`. Every closed state then has the unique
primitive annihilated by `h`. This strengthens the existing categorical
exactness and zero-homology theorems with an explicit bounded splitting;
it does not identify Krein harmonic vectors with homology representatives.
-/

noncomputable section

namespace InfoGeometry.HodgeCohomology.KreinNullContraction

open InfoGeometry.Krein KreinHodgeObstruction

/-- The normalized complementary null direction. This is a homotopy, not the
Krein adjoint, which the owner proves equals `nullDirac` itself. -/
def nullHomotopy : Plane →L[ℝ] Plane :=
  (1 / 4 : ℝ) • (fst_L - snd_L : Plane →L[ℝ] ℝ).smulRight (to_doubled 1 1)

theorem nullHomotopy_apply (x : Plane) :
    nullHomotopy x = to_doubled
      ((WithLp.fst x - WithLp.snd x) / 4)
      ((WithLp.fst x - WithLp.snd x) / 4) := by
  apply DoubledSpace.ext <;> simp [nullHomotopy, fst_L, snd_L] <;> ring

theorem nullHomotopy_square : nullHomotopy * nullHomotopy = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change nullHomotopy (nullHomotopy x) = 0
  simp only [nullHomotopy_apply, fst_to_doubled, snd_to_doubled, sub_self, zero_div]
  rfl

/-- An explicit contraction, stronger than merely asserting exactness. -/
theorem null_contracting_identity :
    nullDirac * nullHomotopy + nullHomotopy * nullDirac = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change nullDirac (nullHomotopy x) + nullHomotopy (nullDirac x) = x
  apply DoubledSpace.ext <;>
    simp [nullDirac_apply, nullHomotopy_apply] <;> ring

/-- Every state decomposes into the differential and homotopy ranges. -/
theorem null_state_decomposition (x : Plane) :
    nullDirac (nullHomotopy x) + nullHomotopy (nullDirac x) = x :=
  congrArg (fun T : Plane →L[ℝ] Plane => T x) null_contracting_identity

/-- A closed state has its explicitly normalized primitive. -/
theorem null_closed_primitive (x : Plane) (hx : nullDirac x = 0) :
    nullDirac (nullHomotopy x) = x := by
  simpa only [hx, map_zero, add_zero] using null_state_decomposition x

/-- A state closed for both complementary differentials must vanish. This is
about `h`, not the indefinite adjoint from the obstruction. -/
theorem null_joint_kernel (x : Plane) (hd : nullDirac x = 0)
    (hh : nullHomotopy x = 0) : x = 0 := by
  have h := null_state_decomposition x
  simpa only [hd, hh, map_zero, add_zero] using h.symm

/-- Constructive exactness with a unique primitive in the homotopy kernel. -/
theorem null_closed_unique_primitive (x : Plane) (hx : nullDirac x = 0) :
    ∃! y : Plane, nullDirac y = x ∧ nullHomotopy y = 0 := by
  refine ⟨nullHomotopy x, ⟨null_closed_primitive x hx, ?_⟩, ?_⟩
  · exact congrArg (fun T : Plane →L[ℝ] Plane => T x) nullHomotopy_square
  · intro y hy
    have h := null_state_decomposition y
    simpa only [hy.1, hy.2, map_zero, zero_add] using h.symm

end InfoGeometry.HodgeCohomology.KreinNullContraction

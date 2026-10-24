/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Streaming.TwoBoundaryDyadCompression

/-! Exact multiplication defect and the multiplicative domain on the right
of the existing regular two-boundary functional. -/
noncomputable section
namespace InfoGeometry.Streaming.TwoBoundaryDyadCompression
open FiniteTwoBoundaryWeakFunctional
variable {ι : Type*} [Fintype ι]

theorem weakValue_mul_of_pre_eigenvector (p : RegularBoundaryPair ι)
    (A B : Operator ι) (hB : B p.pre = weakValue p B • p.pre) :
    weakValue p (A * B) = weakValue p A * weakValue p B := by
  change pairing p.post (A (B p.pre)) / overlap p = weakValue p A * weakValue p B
  rw [hB, map_smul, pairing_smul_right]
  change weakValue p B * pairing p.post (A p.pre) / overlap p =
    (pairing p.post (A p.pre) / overlap p) * weakValue p B
  ring

theorem weakValue_dyad_middle (p : RegularBoundaryPair ι) (A B : Operator ι) :
    weakValue p (A * boundaryDyad p * B) = weakValue p A * weakValue p B := by
  unfold weakValue numerator
  simp only [Module.End.mul_apply, boundaryDyad_apply, map_smul, pairing_smul_right]
  ring

/-- The complementary dyad measures the entire failure of multiplicativity. -/
theorem weakValue_mul_defect (p : RegularBoundaryPair ι) (A B : Operator ι) :
    weakValue p (A * B) - weakValue p A * weakValue p B =
      weakValue p (A * (1 - boundaryDyad p) * B) := by
  rw [mul_sub, mul_one, sub_mul, weakValue_sub, weakValue_dyad_middle]

/-- Rank-one maps with range in the preselected line detect every covector. -/
theorem weakValue_rankOne_pre_mul (p : RegularBoundaryPair ι)
    (f : Module.Dual ℂ (State ι)) (B : Operator ι) :
    weakValue p (f.smulRight p.pre * B) = f (B p.pre) := by
  simp only [weakValue, numerator, Module.End.mul_apply, LinearMap.smulRight_apply,
    pairing_smul_right]
  exact mul_div_cancel_right₀ _ p.overlap_ne

theorem weakValue_rankOne_pre (p : RegularBoundaryPair ι)
    (f : Module.Dual ℂ (State ι)) :
    weakValue p (f.smulRight p.pre) = f p.pre := by
  simpa using weakValue_rankOne_pre_mul p f 1

/-- This is an exact criterion, not an extra multiplicativity hypothesis. -/
theorem weakValue_mul_all_left_iff (p : RegularBoundaryPair ι) (B : Operator ι) :
    (∀ A : Operator ι, weakValue p (A * B) = weakValue p A * weakValue p B) ↔
      B p.pre = weakValue p B • p.pre := by
  constructor
  · intro h
    funext i
    have hi := h ((LinearMap.proj i : Module.Dual ℂ (State ι)).smulRight p.pre)
    rw [weakValue_rankOne_pre_mul, weakValue_rankOne_pre] at hi
    simpa [mul_comm] using hi
  · intro h A
    exact weakValue_mul_of_pre_eigenvector p A B h

end InfoGeometry.Streaming.TwoBoundaryDyadCompression

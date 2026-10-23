/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerLastBitClosure

/-! Pivot elimination on the native flag stabilizer, without cardinality assumptions. -/

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagResidualPivots

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open G2TwoPCRecovery G2NativeFlagStabilizerTransport
open G2NativeFlagStabilizerClosureReadback G2NativeFlagLineCoordinateConstraints
open G2ImaginaryOctImBridge
open G2TwoPCRecoveryStep4 G2TwoPCRecoveryStep5

theorem peel34_basis8_two_y1_false {f : SplitOctF2Aut}
    (hf : f ∈ nativeFlagStabilizer) :
    ((peel34 f).1 (basis8 2)).y1 = false := by
  rw [nativeFlagStabilizer_peel34_basis8_two_y1_coordinate_control hf,
    nativeFlagStabilizer_basis8_two_x0 hf]
  cases h : (f.1 (basis8 2)).y1 <;> rfl

theorem fullPeel_basis8_two_y1_false {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 2)).y1 = false := by
  have hr := peel2_mem_nativeFlagStabilizer
    (peel1_mem_nativeFlagStabilizer (peel0_mem_nativeFlagStabilizer hg))
  have hs := peel34_mem_nativeFlagStabilizer hr
  have h2 := peel34_basis8_two_y1_false hr
  have h4 := nativeFlagStabilizer_basis8_four hs
  rw [fullPeel_basis8_two_y1_readback]
  split
  · rw [automorphism_map_add, h4]
    change (((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).y1 ^^ false) = false
    rw [h2]
    rfl
  · exact h2

theorem peel34_basis8_three_x2_false {f : SplitOctF2Aut}
    (h4 : f.1 (basis8 4) = basis8 4)
    (h5 : f.1 (basis8 5) = basis8 5) :
    ((peel34 f).1 (basis8 3)).x2 = false := by
  cases he4 : (f.1 (basis8 2)).y1 <;>
    cases ht : (f.1 (basis8 3)).x2
  · simp [peel34, he4, ht]
  · simp only [peel34, he4, ht]
    change (f.1 (add (basis8 3) (basis8 4))).x2 = false
    rw [f.2.2.1, h4]
    change ((f.1 (basis8 3)).x2 ^^ true) = false
    rw [ht]
    rfl
  · simp only [peel34, he4, ht]
    change (f.1 (add (basis8 3) (basis8 5))).x2 = false
    rw [f.2.2.1, h5]
    change ((f.1 (basis8 3)).x2 ^^ false) = false
    rw [ht]
    rfl
  · simp only [peel34, he4, ht]
    change (f.1 (add (basis8 3) (add (basis8 4) (basis8 5)))).x2 = false
    rw [f.2.2.1, f.2.2.1, h4, h5]
    change ((f.1 (basis8 3)).x2 ^^ (true ^^ false)) = false
    rw [ht]
    rfl

theorem peel5_basis8_three_eq (f : SplitOctF2Aut) :
    (peel5 f).1 (basis8 3) = f.1 (basis8 3) := by
  dsimp [peel5]
  split
  · change f.1 (basis8 3) = f.1 (basis8 3)
    rfl
  · rfl

theorem fullPeel_basis8_three_x2_false {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 3)).x2 = false := by
  have hr := peel2_mem_nativeFlagStabilizer
    (peel1_mem_nativeFlagStabilizer (peel0_mem_nativeFlagStabilizer hg))
  have h4 := nativeFlagStabilizer_basis8_four hr
  have h5 : (peel2 (peel1 (peel0 g))).1 (basis8 5) = basis8 5 := by
    rw [peel2_peel1_peel0_basis8_5_eq_peel0]
    exact preceding_peel0_basis8_five_readback hg
  change ((peel5 (peel34 (peel2 (peel1 (peel0 g))))).1 (basis8 3)).x2 = false
  rw [peel5_basis8_three_eq]
  exact peel34_basis8_three_x2_false h4 h5

end InfoGeometry.Algebra.Zorn.G2NativeFlagResidualPivots

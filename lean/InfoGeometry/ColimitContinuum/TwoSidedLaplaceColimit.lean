/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TwoSidedCayleyDicksonLaplaceKernel
import InfoGeometry.Core.DualSeedPeirce

/-!
# Gap 4: Tensor Tower Colimit of Two-Sided Laplace Kernels
-/

namespace InfoGeometry.ColimitContinuum.TwoSidedLaplaceColimit

open InfoGeometry.Canonical.TwoSidedCayleyDicksonLaplaceKernel
open InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Core.DualSeedPeirce.IsDualSeedPair

variable {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]

/-- Bonding maps commute with the two-sided hyperbolic Laplace kernel
    when they preserve the algebra structure. -/
theorem laplace_colimit_bonding_commutes
    {ι_n : A → B} (hι : ∀ (x y : A), ι_n (x * y) = ι_n x * ι_n y)
    (hι_add : ∀ (x y : A), ι_n (x + y) = ι_n x + ι_n y)
    (hι_smul : ∀ (r : ℝ) (x : A), ι_n (r • x) = r • ι_n x)
    {dA BA : A} {dB BB : B}
    (_ : IsDualSeedPair dA BA) (_ : IsDualSeedPair dB BB)
    (h_compat_d : ι_n dA = dB) (h_compat_B : ι_n BA = BB)
    {lamL muL lamR muR : ℝ} {X : A} :
    ι_n (twoSidedHyperbolicLaplace lamL muL lamR muR dA BA X) =
      twoSidedHyperbolicLaplace lamL muL lamR muR dB BB (ι_n X) := by
  have hp : ι_n (polePlus dA BA) = polePlus dB BB := by
    show ι_n (dA * BA) = dB * BB
    rw [hι dA BA, h_compat_d, h_compat_B]
  have hq : ι_n (poleMinus dA BA) = poleMinus dB BB := by
    show ι_n (BA * dA) = BB * dB
    rw [hι BA dA, h_compat_B, h_compat_d]
  have h₁ : ι_n ((lamL • polePlus dA BA + muL • poleMinus dA BA) * X * (lamR • polePlus dA BA + muR • poleMinus dA BA)) =
      (lamL • polePlus dB BB + muL • poleMinus dB BB) * ι_n X * (lamR • polePlus dB BB + muR • poleMinus dB BB) := by
    calc
      ι_n ((lamL • polePlus dA BA + muL • poleMinus dA BA) * X * (lamR • polePlus dA BA + muR • poleMinus dA BA))
        = ι_n ((lamL • polePlus dA BA + muL • poleMinus dA BA) * X) * ι_n (lamR • polePlus dA BA + muR • poleMinus dA BA) := by
          rw [hι]
        _ = (ι_n (lamL • polePlus dA BA + muL • poleMinus dA BA) * ι_n X) * ι_n (lamR • polePlus dA BA + muR • poleMinus dA BA) := by
          rw [hι]
        _ = (ι_n (lamL • polePlus dA BA) + ι_n (muL • poleMinus dA BA)) * ι_n X * (ι_n (lamR • polePlus dA BA) + ι_n (muR • poleMinus dA BA)) := by
          rw [hι_add, hι_add]
        _ = (lamL • ι_n (polePlus dA BA) + muL • ι_n (poleMinus dA BA)) * ι_n X * (lamR • ι_n (polePlus dA BA) + muR • ι_n (poleMinus dA BA)) := by
          rw [hι_smul, hι_smul, hι_smul, hι_smul]
        _ = (lamL • polePlus dB BB + muL • poleMinus dB BB) * ι_n X * (lamR • polePlus dB BB + muR • poleMinus dB BB) := by
          simp [hp, hq]
  calc
    ι_n (twoSidedHyperbolicLaplace lamL muL lamR muR dA BA X)
      = ι_n ((lamL • polePlus dA BA + muL • poleMinus dA BA) * X * (lamR • polePlus dA BA + muR • poleMinus dA BA)) := by
        simp [twoSidedHyperbolicLaplace, hyperbolicKernel]
      _ = (lamL • polePlus dB BB + muL • poleMinus dB BB) * ι_n X * (lamR • polePlus dB BB + muR • poleMinus dB BB) := by
        rw [h₁]
      _ = twoSidedHyperbolicLaplace lamL muL lamR muR dB BB (ι_n X) := by
        simp [twoSidedHyperbolicLaplace, hyperbolicKernel]

end InfoGeometry.ColimitContinuum.TwoSidedLaplaceColimit

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

open InfoGeometry.Canonical
open InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Core.DualSeedPeirce.IsDualSeedPair

variable {A_n A_{n+1} : Type*} [Ring A_n] [Ring A_{n+1}] [Algebra ℝ A_n] [Algebra ℝ A_{n+1}]

/-- Bonding maps commute with the two-sided hyperbolic Laplace kernel
    when they preserve the algebra structure. -/
theorem laplace_colimit_bonding_commutes
    {ι_n : A_n → A_{n+1}} (hι : ∀ (x y : A_n), ι_n (x * y) = ι_n x * ι_n y)
    (hι_add : ∀ (x y : A_n), ι_n (x + y) = ι_n x + ι_n y)
    (hι_smul : ∀ (r : ℝ) (x : A_n), ι_n (r • x) = r • ι_n x)
    {d_n B_n : A_n} {d_{n+1} B_{n+1} : A_{n+1}}
    (h_n : IsDualSeedPair d_n B_n) (h_{n+1} : IsDualSeedPair d_{n+1} B_{n+1})
    (h_compat_d : ι_n d_n = d_{n+1}) (h_compat_B : ι_n B_n = B_{n+1})
    {λ_L μ_L λ_R μ_R : ℝ} {X : A_n} :
    ι_n (twoSidedHyperbolicLaplace λ_L μ_L λ_R μ_R d_n B_n X) =
      twoSidedHyperbolicLaplace λ_L μ_L λ_R μ_R d_{n+1} B_{n+1} (ι_n X) := by
  simp [twoSidedHyperbolicLaplace, hyperbolicKernel]
  -- polePlus d B = d * B (exactSupport)
  have hp : ι_n (polePlus d_n B_n) = polePlus d_{n+1} B_{n+1} := by
    show ι_n (d_n * B_n) = d_{n+1} * B_{n+1}
    rw [hι d_n B_n, h_compat_d, h_compat_B]
  have hq : ι_n (poleMinus d_n B_n) = poleMinus d_{n+1} B_{n+1} := by
    show ι_n (B_n * d_n) = B_{n+1} * d_{n+1}
    rw [hι B_n d_n, h_compat_B, h_compat_d]
  rw [hι_add (λ_L • polePlus d_n B_n) (μ_L • poleMinus d_n B_n)]
  rw [hι_smul λ_L (polePlus d_n B_n), hι_smul μ_L (poleMinus d_n B_n)]
  rw [hp, hq]
  -- Now handle the right side and the middle X
  have h_mul : ι_n (hyperbolicKernel λ_L μ_L d_n B_n * X * hyperbolicKernel λ_R μ_R d_n B_n) =
      (λ_L • polePlus d_{n+1} B_{n+1} + μ_L • poleMinus d_{n+1} B_{n+1}) *
      ι_n X *
      (λ_R • polePlus d_{n+1} B_{n+1} + μ_R • poleMinus d_{n+1} B_{n+1}) := by
    rw [hι (hyperbolicKernel λ_L μ_L d_n B_n * X) (hyperbolicKernel λ_R μ_R d_n B_n)]
    rw [hι (hyperbolicKernel λ_L μ_L d_n B_n) X]
    rw [hι_add (λ_L • polePlus d_n B_n) (μ_L • poleMinus d_n B_n)]
    rw [hι_smul λ_L (polePlus d_n B_n), hι_smul μ_L (poleMinus d_n B_n)]
    rw [hp, hq]
    rw [hι_add (λ_R • polePlus d_n B_n) (μ_R • poleMinus d_n B_n)]
    rw [hι_smul λ_R (polePlus d_n B_n), hι_smul μ_R (poleMinus d_n B_n)]
    rw [hp, hq]
    rfl
  exact h_mul

end InfoGeometry.ColimitContinuum.TwoSidedLaplaceColimit

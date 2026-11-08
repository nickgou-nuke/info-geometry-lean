/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Core.DualSeedPeirce
import InfoGeometry.Canonical.IntegralSplitOctonionAlternativity
import InfoGeometry.Canonical.MoufangIdentities

/-! # Two-Sided Cayley–Dickson Laplace Kernel over a Dual Seed Pair

This module implements Stream 9 of the Ludkovsky (`arXiv:math/0612755`) stream:
a two-sided Laplace–Mellin kernel `D(λ_L, μ_L) * X * D(λ_R, μ_R)` acting on a
noncommutative, non-associative Cayley–Dickson carrier via the existing
`IsDualSeedPair` carrier (`Core/DualSeedPeirce.lean`). It proves the exact
four-sector Peirce eigen-scaling law, the symmetric vs. antisymmetric Laplace
selectivity theorem, and the Moufang two-sided convolution law.

No new seed predicate, pole, or Moufang identity is defined: all are reused
from their existing owners. -/
namespace InfoGeometry.Canonical.TwoSidedCayleyDicksonLaplaceKernel

open InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Canonical

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]

/-! ## 1. Kernels over the Existing Dual Seed Carrier -/

/-- Active hyperbolic Laplace kernel `D(λ, μ) = λ • P_+ + μ • P_-`. -/
def hyperbolicKernel (lam mu : R) (d B : A) : A :=
  lam • polePlus d B + mu • poleMinus d B

/-- Active elliptic Fourier–Laplace phase kernel `R(c, s) = c • Δ + s • J`. -/
def ellipticKernel (c s : R) (d B : A) : A :=
  c • carrierSupport d B + s • wheelGenerator d B

/-- Two-sided hyperbolic Laplace transform `D(λ_L, μ_L) * X * D(λ_R, μ_R)`. -/
def twoSidedHyperbolicLaplace (lamL muL lamR muR : R) (d B X : A) : A :=
  hyperbolicKernel lamL muL d B * X * hyperbolicKernel lamR muR d B

/-!
## 2. Node 0: Two-Sided 4-Sector Peirce Eigen-Scaling
-/

lemma hyperbolicKernel_mul_d {d B : A} (h : IsDualSeedPair d B) (lam mu : R) :
    hyperbolicKernel lam mu d B * d = lam • d := by
  unfold hyperbolicKernel
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, IsDualSeedPair.pd h, IsDualSeedPair.qd h, smul_zero, add_zero]

lemma d_mul_hyperbolicKernel {d B : A} (h : IsDualSeedPair d B) (lam mu : R) :
    d * hyperbolicKernel lam mu d B = mu • d := by
  unfold hyperbolicKernel
  rw [mul_add, mul_smul_comm, mul_smul_comm, IsDualSeedPair.dp h, IsDualSeedPair.dq h, smul_zero, zero_add]

lemma hyperbolicKernel_mul_B {d B : A} (h : IsDualSeedPair d B) (lam mu : R) :
    hyperbolicKernel lam mu d B * B = mu • B := by
  unfold hyperbolicKernel
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, IsDualSeedPair.pb h, IsDualSeedPair.qb h, smul_zero, zero_add]

lemma B_mul_hyperbolicKernel {d B : A} (h : IsDualSeedPair d B) (lam mu : R) :
    B * hyperbolicKernel lam mu d B = lam • B := by
  unfold hyperbolicKernel
  rw [mul_add, mul_smul_comm, mul_smul_comm, IsDualSeedPair.bp h, IsDualSeedPair.bq h, smul_zero, add_zero]

abbrev hyperbolicKernel_mul_b {d B : A} (h : IsDualSeedPair d B) (lam mu : R) :=
  hyperbolicKernel_mul_B h lam mu

abbrev b_mul_hyperbolicKernel {d B : A} (h : IsDualSeedPair d B) (lam mu : R) :=
  B_mul_hyperbolicKernel h lam mu

lemma hyperbolicKernel_mul_polePlus {d B : A} (h : IsDualSeedPair d B) (lam mu : R) :
    hyperbolicKernel lam mu d B * polePlus d B = lam • polePlus d B := by
  unfold hyperbolicKernel
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, IsDualSeedPair.pp h, IsDualSeedPair.qp h, smul_zero, add_zero]

lemma polePlus_mul_hyperbolicKernel {d B : A} (h : IsDualSeedPair d B) (lam mu : R) :
    polePlus d B * hyperbolicKernel lam mu d B = lam • polePlus d B := by
  unfold hyperbolicKernel
  rw [mul_add, mul_smul_comm, mul_smul_comm, IsDualSeedPair.pp h, IsDualSeedPair.pq h, smul_zero, add_zero]

lemma hyperbolicKernel_mul_poleMinus {d B : A} (h : IsDualSeedPair d B) (lam mu : R) :
    hyperbolicKernel lam mu d B * poleMinus d B = mu • poleMinus d B := by
  unfold hyperbolicKernel
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, IsDualSeedPair.pq h, IsDualSeedPair.qq h, smul_zero, zero_add]

lemma poleMinus_mul_hyperbolicKernel {d B : A} (h : IsDualSeedPair d B) (lam mu : R) :
    poleMinus d B * hyperbolicKernel lam mu d B = mu • poleMinus d B := by
  unfold hyperbolicKernel
  rw [mul_add, mul_smul_comm, mul_smul_comm, IsDualSeedPair.qp h, IsDualSeedPair.qq h, smul_zero, zero_add]

/-!
## 3. Node 1: Symmetric vs. Antisymmetric Two-Sided Laplace Selectivity
-/

/-- **Two-Sided 4-Sector Laplace Scaling Theorem**:
    `D(λ_L, μ_L) * X * D(λ_R, μ_R)` scales `(P_+, P_-, d, B)` by
    `(λ_L * λ_R, μ_L * μ_R, λ_L * μ_R, μ_L * λ_R)`. -/
theorem twoSidedHyperbolicLaplace_sector_scaling {d B : A}
    (h : IsDualSeedPair d B) (lamL muL lamR muR : R) :
    twoSidedHyperbolicLaplace lamL muL lamR muR d B (polePlus d B) =
      (lamL * lamR) • polePlus d B ∧
    twoSidedHyperbolicLaplace lamL muL lamR muR d B (poleMinus d B) =
      (muL * muR) • poleMinus d B ∧
    twoSidedHyperbolicLaplace lamL muL lamR muR d B d =
      (lamL * muR) • d ∧
    twoSidedHyperbolicLaplace lamL muL lamR muR d B B =
      (muL * lamR) • B := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold twoSidedHyperbolicLaplace
    rw [hyperbolicKernel_mul_polePlus h, smul_mul_assoc,
        polePlus_mul_hyperbolicKernel h, ← smul_smul]
  · unfold twoSidedHyperbolicLaplace
    rw [hyperbolicKernel_mul_poleMinus h, smul_mul_assoc,
        poleMinus_mul_hyperbolicKernel h, ← smul_smul]
  · unfold twoSidedHyperbolicLaplace
    rw [hyperbolicKernel_mul_d h, smul_mul_assoc,
        d_mul_hyperbolicKernel h, ← smul_smul]
  · unfold twoSidedHyperbolicLaplace
    rw [hyperbolicKernel_mul_B h, smul_mul_assoc,
        B_mul_hyperbolicKernel h, ← smul_smul]

/-!
## 4. Node 2: Symmetric vs. Antisymmetric Selectivity (`λ * μ = 1`)
-/

theorem symmetric_vs_antisymmetric_laplace_selectivity {d B : A}
    (h : IsDualSeedPair d B) {lam mu : R} (h_lm : lam * mu = 1) :
    (twoSidedHyperbolicLaplace lam mu lam mu d B d = d ∧
     twoSidedHyperbolicLaplace lam mu lam mu d B B = B ∧
     twoSidedHyperbolicLaplace lam mu lam mu d B (polePlus d B) =
       (lam * lam) • polePlus d B ∧
     twoSidedHyperbolicLaplace lam mu lam mu d B (poleMinus d B) =
       (mu * mu) • poleMinus d B) ∧
    (twoSidedHyperbolicLaplace lam mu mu lam d B (polePlus d B) =
      polePlus d B ∧
     twoSidedHyperbolicLaplace lam mu mu lam d B (poleMinus d B) =
      poleMinus d B ∧
     twoSidedHyperbolicLaplace lam mu mu lam d B d = (lam * lam) • d ∧
     twoSidedHyperbolicLaplace lam mu mu lam d B B = (mu * mu) • B) := by
  have h_ml : mu * lam = 1 := by rw [mul_comm, h_lm]
  rcases twoSidedHyperbolicLaplace_sector_scaling h lam mu lam mu with ⟨s1, s2, s3, s4⟩
  rcases twoSidedHyperbolicLaplace_sector_scaling h lam mu mu lam with ⟨a1, a2, a3, a4⟩
  rw [h_lm, one_smul] at s3 a1
  rw [h_ml, one_smul] at s4 a2
  exact ⟨⟨s3, s4, s1, s2⟩, ⟨a1, a2, a3, a4⟩⟩

/-!
## 5. Node 3: Octonionic Moufang Two-Sided Laplace Convolution Law
-/

/-- **Moufang Two-Sided Laplace Convolution**:
    Reuses `splitOctonion_flexible` and `splitOctonion_moufang_middle` from
    `InfoGeometry.Canonical.IntegralSplitOctonionAlternativity` and
    `InfoGeometry.Canonical.MoufangIdentities` over the standard integral
    split-octonion carrier `StandardIntegralSplitOctonion`. -/
theorem moufang_two_sided_laplace_convolution
    (K X Y : StandardIntegralSplitOctonion) :
    splitOctonionMul (splitOctonionMul K X) K =
      splitOctonionMul K (splitOctonionMul X K) ∧
    splitOctonionMul (splitOctonionMul K X) (splitOctonionMul Y K) =
      splitOctonionMul K
        (splitOctonionMul (splitOctonionMul X Y) K) :=
  ⟨splitOctonion_flexible K X, splitOctonion_moufang_middle K X Y⟩

end InfoGeometry.Canonical.TwoSidedCayleyDicksonLaplaceKernel

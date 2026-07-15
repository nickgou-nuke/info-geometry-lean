import InfoGeometry.Algebra.N2ModeCentralExtension

/-!
# Supergraded N=2 cocycle

The ordinary `LieTwoCocycle` layer is skew-symmetric, so it correctly models
ordinary Lie central extensions.  The N=2 odd-odd channel is different:
two odd generators close through a symmetric anticommutator.

This file defines the supergraded cocycle directly on the same finite-support
mode base used by `N2ModeCentralExtension`.  It does not pretend to be a
`LieTwoCocycle`; it is the symmetric odd-odd cocycle feeding the N=2
super-anticommutator lane.
-/

namespace SupergradedCocycle

open Module
open N2ModeCentralExtension
open VirasoroProject

universe u

variable {ι : Type u} [DecidableEq ι]
variable (𝕜 : Type u) [Field 𝕜]

/--
The supergraded N=2 central cocycle on mode labels.

Unlike the ordinary Lie cocycle, the `Qᵢ,Rⱼ` and `Rⱼ,Qᵢ` odd-odd channels have
the same sign, because they belong to an anticommutator.
-/
def superLabelCocycle : N2ModeLabel ι → N2ModeLabel ι → 𝕜
  | N2ModeLabel.q i, N2ModeLabel.r j => if i = j then 1 else 0
  | N2ModeLabel.r i, N2ModeLabel.q j => if i = j then 1 else 0
  | _, _ => 0

@[simp]
theorem superLabelCocycle_q_r (i j : ι) :
    superLabelCocycle 𝕜 (N2ModeLabel.q i) (N2ModeLabel.r j) =
      if i = j then 1 else 0 :=
  rfl

@[simp]
theorem superLabelCocycle_r_q (i j : ι) :
    superLabelCocycle 𝕜 (N2ModeLabel.r i) (N2ModeLabel.q j) =
      if i = j then 1 else 0 :=
  rfl

@[simp]
theorem superLabelCocycle_self (a : N2ModeLabel ι) :
    superLabelCocycle 𝕜 a a = 0 := by
  cases a <;> simp [superLabelCocycle]

/-- The odd `Q/R` super-cocycle is symmetric on generators. -/
theorem superLabelCocycle_q_r_symm (i j : ι) :
    superLabelCocycle 𝕜 (N2ModeLabel.q i) (N2ModeLabel.r j) =
      superLabelCocycle 𝕜 (N2ModeLabel.r j) (N2ModeLabel.q i) := by
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- Bilinear extension of the supergraded N=2 cocycle to finite-support modes. -/
noncomputable def superBilin :
    N2ModeBase ι 𝕜 →ₗ[𝕜] N2ModeBase ι 𝕜 →ₗ[𝕜] 𝕜 :=
  (AbelianLieAlgebraOn.jgen (ι := N2ModeLabel ι) 𝕜).constr 𝕜 <| fun a =>
    (AbelianLieAlgebraOn.jgen (ι := N2ModeLabel ι) 𝕜).constr 𝕜 <| fun b =>
      superLabelCocycle 𝕜 a b

@[simp]
theorem superBilin_apply_jgen_jgen (a b : N2ModeLabel ι) :
    superBilin 𝕜
        (AbelianLieAlgebraOn.jgen (ι := N2ModeLabel ι) 𝕜 a)
        (AbelianLieAlgebraOn.jgen (ι := N2ModeLabel ι) 𝕜 b) =
      superLabelCocycle 𝕜 a b := by
  simp [superBilin]

@[simp]
theorem superBilin_qgen_rgen (i j : ι) :
    superBilin 𝕜 (N2ModeBase.qgen 𝕜 i) (N2ModeBase.rgen 𝕜 j) =
      if i = j then 1 else 0 := by
  simp [N2ModeBase.qgen, N2ModeBase.rgen]

@[simp]
theorem superBilin_rgen_qgen (i j : ι) :
    superBilin 𝕜 (N2ModeBase.rgen 𝕜 i) (N2ModeBase.qgen 𝕜 j) =
      if i = j then 1 else 0 := by
  simp [N2ModeBase.rgen, N2ModeBase.qgen]

/-- The supergraded odd-odd cocycle is symmetric on lifted `Q/R` base modes. -/
theorem superBilin_qgen_rgen_symm (i j : ι) :
    superBilin 𝕜 (N2ModeBase.qgen 𝕜 i) (N2ModeBase.rgen 𝕜 j) =
      superBilin 𝕜 (N2ModeBase.rgen 𝕜 j) (N2ModeBase.qgen 𝕜 i) := by
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/--
The supergraded cocycle supplies the central coefficient for the N=2 odd-odd
anticommutator channel.
-/
theorem superBilin_qgen_rgen_centralCoefficient (i j : ι) :
    superBilin 𝕜 (N2ModeBase.qgen 𝕜 i) (N2ModeBase.rgen 𝕜 j) =
      if i = j then (1 : 𝕜) else 0 := by
  simp

end SupergradedCocycle

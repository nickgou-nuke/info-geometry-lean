import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.SelfDualNormalForm1pmu

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The `u = 1` specialization `B(1)` of the self-dual family. -/
def self_dual_u1_two_channel_zeta_B1 (B0 : SelfDualBlockMatrix) : SelfDualBlockMatrix :=
  selfDualFamily 1 B0

/-- Scalar determinant of `I - z B(1)` in the concrete `2 × 2` block presentation. -/
def self_dual_u1_two_channel_zeta_delta (z : ℂ) (B0 : SelfDualBlockMatrix) : ℂ :=
  let B1 := self_dual_u1_two_channel_zeta_B1 B0
  (1 - z * B1.X) * (1 - z * B1.W) - z ^ 2 * B1.Y * B1.Z

/-- The `V₊` channel factor on the unit slice. -/
def self_dual_u1_two_channel_zeta_plus_factor (z : ℂ) (B0 : SelfDualBlockMatrix) : ℂ :=
  1 - 2 * z * B0.X

/-- The `V₋` channel factor on the unit slice. -/
def self_dual_u1_two_channel_zeta_minus_factor (z : ℂ) (B0 : SelfDualBlockMatrix) : ℂ :=
  1 - 2 * z * B0.W

/-- Full zeta factor at `u = 1`. -/
def self_dual_u1_two_channel_zeta_zeta (z : ℂ) (B0 : SelfDualBlockMatrix) : ℂ :=
  (self_dual_u1_two_channel_zeta_delta z B0)⁻¹

/-- The `V₊` channel zeta factor. -/
def self_dual_u1_two_channel_zeta_plus_zeta (z : ℂ) (B0 : SelfDualBlockMatrix) : ℂ :=
  (self_dual_u1_two_channel_zeta_plus_factor z B0)⁻¹

/-- The `V₋` channel zeta factor. -/
def self_dual_u1_two_channel_zeta_minus_zeta (z : ℂ) (B0 : SelfDualBlockMatrix) : ℂ :=
  (self_dual_u1_two_channel_zeta_minus_factor z B0)⁻¹

/-- Concrete `u = 1` two-channel `Δ/ζ` factorization. -/
def SelfDualU1TwoChannelZetaStatement (z : ℂ) (B0 : SelfDualBlockMatrix) : Prop :=
  self_dual_u1_two_channel_zeta_delta z B0 =
      self_dual_u1_two_channel_zeta_plus_factor z B0 *
        self_dual_u1_two_channel_zeta_minus_factor z B0 ∧
    self_dual_u1_two_channel_zeta_zeta z B0 =
      self_dual_u1_two_channel_zeta_plus_zeta z B0 *
        self_dual_u1_two_channel_zeta_minus_zeta z B0

/-- Paper label: `cor:self-dual-u1-two-channel-zeta`. -/
theorem paper_self_dual_u1_two_channel_zeta (z : ℂ) (B0 : SelfDualBlockMatrix) :
    SelfDualU1TwoChannelZetaStatement z B0 := by
  have hnormal :=
    paper_self_dual_normal_form_1pmu (u := 1) B0.X B0.Y B0.Z B0.W
  rcases hnormal with ⟨_, hfamily, _, _⟩
  have hfamily' : selfDualFamily 1 B0 = selfDualNormalForm 1 B0 := by
    simpa using hfamily
  have hone : ((1 : ℂ) + 1) = 2 := by
    norm_num
  have hB1 :
      self_dual_u1_two_channel_zeta_B1 B0 =
        { X := 2 * B0.X, Y := 0, Z := 0, W := 2 * B0.W } := by
    calc
      self_dual_u1_two_channel_zeta_B1 B0 = selfDualNormalForm 1 B0 := by
        simpa [self_dual_u1_two_channel_zeta_B1] using hfamily'
      _ = { X := 2 * B0.X, Y := 0, Z := 0, W := 2 * B0.W } := by
        exact SelfDualBlockMatrix.ext _ _
          (by simp [selfDualNormalForm, hone])
          (by simp [selfDualNormalForm])
          (by simp [selfDualNormalForm])
          (by simp [selfDualNormalForm, hone])
  have hdelta :
      self_dual_u1_two_channel_zeta_delta z B0 =
        self_dual_u1_two_channel_zeta_plus_factor z B0 *
          self_dual_u1_two_channel_zeta_minus_factor z B0 := by
    rw [self_dual_u1_two_channel_zeta_delta, hB1]
    simp [self_dual_u1_two_channel_zeta_plus_factor,
      self_dual_u1_two_channel_zeta_minus_factor]
    ring
  refine ⟨hdelta, ?_⟩
  rw [self_dual_u1_two_channel_zeta_zeta, hdelta]
  simp [self_dual_u1_two_channel_zeta_plus_zeta,
    self_dual_u1_two_channel_zeta_minus_zeta,
    mul_comm]

end

end Omega.SyncKernelWeighted

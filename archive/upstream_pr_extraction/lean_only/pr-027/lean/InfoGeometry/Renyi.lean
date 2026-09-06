import InfoGeometry.KL

/-!
# Rényi Divergence Interface

Standard Rényi divergence is packaged from `KL.Phi` as

`D_τ(P||Q) = log (Phi (τ - 1)) / (τ - 1)`.

The shifted form `log (Phi s) / s` is also exposed directly.
-/

namespace InfoGeometry

/-- Support-faithfulness condition inherited from the `KL.Phi` layer. -/
def RenyiSupportFaithful
    {α : Type} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α) : Prop :=
  KL.PhiSupportFaithful N_func Q


/-- Shifted-order Rényi expression `log (Phi s) / s` (order `τ = s + 1`). Requires support-faithful Q. -/
noncomputable def RenyiDShifted
    {α : Type} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (s : ℝ)
    (hQ : KL.PhiSupportFaithful N_func Q) : ℝ :=
  KL.renyiBridge N_func Q s hQ


/-- Standard Rényi divergence of order `τ`, expressed via the shifted kernel parameter `τ - 1`. Requires support-faithful Q. -/
noncomputable def RenyiD
    {α : Type} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
    (hQ : KL.PhiSupportFaithful N_func Q) : ℝ :=
  RenyiDShifted N_func Q (τ - 1) hQ


@[simp] lemma RenyiDShifted_eq_log_Phi_div
  {α : Type} [Fintype α]
  (N_func : EmpiricalCounts α)
  (Q : ProbabilityDist α)
  (s : ℝ)
  (hQ : KL.PhiSupportFaithful N_func Q) :
  RenyiDShifted N_func Q s hQ = Real.log (KL.Phi N_func Q s) / s := rfl


lemma RenyiD_eq_log_Phi_shift_div
  {α : Type} [Fintype α]
  (N_func : EmpiricalCounts α)
  (Q : ProbabilityDist α)
  (τ : ℝ)
  (hQ : KL.PhiSupportFaithful N_func Q) :
  RenyiD N_func Q τ hQ = Real.log (KL.Phi N_func Q (τ - 1)) / (τ - 1) := rfl


/-- Equivalent multiplicative form for `τ ≠ 1`. -/
lemma RenyiD_mul_order_sub_one
    {α : Type} [Fintype α]
    (N_func : EmpiricalCounts α)
    (Q : ProbabilityDist α)
    (τ : ℝ)
    (hτ : τ ≠ 1)
    (hQ : KL.PhiSupportFaithful N_func Q) :
    (τ - 1) * RenyiD N_func Q τ hQ = Real.log (KL.Phi N_func Q (τ - 1)) := by
  have hs : τ - 1 ≠ 0 := sub_ne_zero.mpr hτ
  simpa [RenyiD, RenyiDShifted] using
    (KL.renyiBridge_mul N_func Q (τ - 1) hs hQ)

end InfoGeometry

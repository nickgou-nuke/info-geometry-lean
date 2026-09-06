import Mathlib

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.LieFlowMatching

/--
Abstract Lie-flow-matching interface for a group-orbit generative process.

The model uses only explicit field identities on `exp`/`log`; no concrete Lie
group machinery is assumed.
-/

structure LieFlowChart (G : Type*) [Group G] (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  exp : V → G
  log : G → V
  hExpLog : ∀ g : G, exp (log g) = g
  hLogExp : ∀ v : V, log (exp v) = v
  hExpZero : exp (0 : V) = 1

section

variable {G X V : Type*}
variable [Group G]
variable [MulAction G X]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Flow generator extracted from an orbit transformation `g`. -/
def algebraSpeed (L : LieFlowChart G V) (g : G) : V :=
  L.log g⁻¹

/-- Trajectory point at interpolation time `t ∈ [0,1]`: `x_t = exp(tA) • (g • x1)`. -/
def geodesicPoint (L : LieFlowChart G V) (x1 : X) (g : G) (t : ℝ) : X :=
  (L.exp (t • algebraSpeed L g)) • (g • x1)

/-- Step 5-7 endpoint identity: at `t = 0`, we are at transformed noise `g • x1`. -/
theorem geodesicPoint_zero (L : LieFlowChart G V) (x1 : X) (g : G) :
    geodesicPoint L x1 g 0 = g • x1 := by
  simp [geodesicPoint, algebraSpeed, L.hExpZero]

/-- Step 7 endpoint identity: at `t = 1`, we recover the data point `x1`. -/
theorem geodesicPoint_one (L : LieFlowChart G V) (x1 : X) (g : G) :
    geodesicPoint L x1 g 1 = x1 := by
  calc
    geodesicPoint L x1 g 1 = (L.exp (1 • algebraSpeed L g)) • (g • x1) := by
      simp [geodesicPoint]
    _ = (L.exp (L.log (g⁻¹))) • (g • x1) := by simp [algebraSpeed]
    _ = g⁻¹ • (g • x1) := by simpa using congrArg (fun h => h • (g • x1)) (L.hExpLog (g⁻¹))
    _ = x1 := by
      exact inv_smul_smul g x1

/-- Step-8 pointwise (MSE-like) trajectory loss in algebra coordinates. -/
def flowLoss (v : X → ℝ → V) (x : X) (t : ℝ) (A : V) : ℝ :=
  ‖v x t - A‖ ^ 2

/-- Step-8 trajectory loss along the interpolating curve. -/
def trajectoryLoss (L : LieFlowChart G V) (v : X → ℝ → V)
    (x1 : X) (g : G) (t : ℝ) : ℝ :=
  let A : V := algebraSpeed L g
  flowLoss v (geodesicPoint L x1 g t) t A

/-- If velocity model is perfect, trajectory loss vanishes. -/
theorem trajectoryLoss_eq_zero_if_perfect (L : LieFlowChart G V) (v : X → ℝ → V)
    (x1 : X) (g : G) (t : ℝ)
    (h : ∀ x t, v x t = algebraSpeed L g) :
    trajectoryLoss L v x1 g t = 0 := by
  simp [trajectoryLoss, flowLoss, h]

/-- Finite batch over times; used by empirical stochastic estimator. -/
def batchLoss (L : LieFlowChart G V) (v : X → ℝ → V)
    (x1 : X) (g : G) (ts : Finset ℝ) : ℝ :=
  Finset.sum ts (fun t => trajectoryLoss L v x1 g t)

/-- If all batch points are matched exactly, batch loss is zero. -/
theorem batchLoss_eq_zero_if_perfect (L : LieFlowChart G V) (v : X → ℝ → V)
    (x1 : X) (g : G) (ts : Finset ℝ)
    (h : ∀ x t, v x t = algebraSpeed L g) :
    batchLoss L v x1 g ts = 0 := by
  unfold batchLoss
  refine Finset.sum_eq_zero ?_
  intro t ht
  simpa using (trajectoryLoss_eq_zero_if_perfect L v x1 g t h)

/-- Discrete-symmetry correction: power-time schedule `τ = t^γ`, `γ>1`. -/
def powerTime (γ : ℝ) (t : ℝ) : ℝ := t ^ γ

/-- Step-8 with corrected schedule `v(x, t^γ)` instead of `v(x,t)`. -/
def scheduledTrajectoryLoss (L : LieFlowChart G V) (v : X → ℝ → V)
    (x1 : X) (g : G) (γ : ℝ) (t : ℝ) : ℝ :=
  let A : V := algebraSpeed L g
  flowLoss (fun x τ => v x (powerTime γ τ)) (geodesicPoint L x1 g t) t A

/-- If velocity model is perfect even under power schedule, loss stays zero. -/
theorem scheduledTrajectoryLoss_eq_zero_if_perfect (L : LieFlowChart G V) (v : X → ℝ → V)
    (x1 : X) (g : G) (γ : ℝ) (t : ℝ)
    (h : ∀ x t, v x t = algebraSpeed L g) :
    scheduledTrajectoryLoss L v x1 g γ t = 0 := by
  simp [scheduledTrajectoryLoss, flowLoss, h]

/-- Practical model-side prior for late-time focus stabilization. -/
theorem powerScheduleCompression
    (t : ℝ) (γ : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hγ : 1 < γ) :
    powerTime γ t ≤ t := by
  by_cases ht : t = 0
  · subst ht
    have hγpos : 0 < γ := lt_trans zero_lt_one hγ
    rw [powerTime, Real.zero_rpow hγpos.ne']
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hγ1 : (1 : ℝ) ≤ γ := le_of_lt hγ
    have hle : t ^ γ ≤ t ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge htpos ht1 hγ1
    simpa [powerTime] using hle

end

end InfoGeometry.Canonical.LieFlowMatching

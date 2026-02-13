import InfoGeometry.KL
import Mathlib

open scoped BigOperators

noncomputable def logRNDensity
		{α : Type*} [Fintype α]
		(N_func : EmpiricalCounts α)
		(Q : ProbabilityDist α)
		(x : α) : ℝ :=
	Real.log (densityRatio N_func Q x)

noncomputable def relativeSurprisal
		{α : Type*} [Fintype α]
		(N_func : EmpiricalCounts α)
		(Q : ProbabilityDist α)
		(x : α) : ℝ :=
	-logRNDensity N_func Q x

/-- Z(τ) = ∑ Q(x) * exp(-τ * ℓ(x)). -/
noncomputable def partitionFunction
		{α : Type*} [Fintype α]
		(N_func : EmpiricalCounts α)
		(Q : ProbabilityDist α)
		(τ : ℝ) : ℝ :=
	∑ x, Q.prob x * Real.exp (-τ * relativeSurprisal N_func Q x)

/-- Φ(τ) = log Z(τ). -/
noncomputable def Phi
		{α : Type*} [Fintype α]
		(N_func : EmpiricalCounts α)
		(Q : ProbabilityDist α)
		(τ : ℝ) : ℝ :=
	Real.log (partitionFunction N_func Q τ)

/-- Rényi section: D_τ = Φ(τ)/(τ-1). -/
noncomputable def RenyiD
		{α : Type*} [Fintype α]
		(N_func : EmpiricalCounts α)
		(Q : ProbabilityDist α)
		(τ : ℝ) : ℝ :=
	Phi N_func Q τ / (τ - 1)

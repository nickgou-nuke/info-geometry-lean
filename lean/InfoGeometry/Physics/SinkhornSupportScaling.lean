/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.SinkhornSupportIteration
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Closed log-potential image on a sparse finite support

Four-cycles do not generate all cycle constraints of an arbitrary bipartite
support. Instead use the closed finite-dimensional image of the actual
row-plus-column potential map on the active edge set. This constructs positive
scaling factors for every support-faithful limit of positive diagonal scalings.
-/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace InfoGeometry.Physics.AmariSinkhornAlternatingProjections
variable {I J : Type*} [Fintype I] [Fintype J]

abbrev ActiveEdge (K : TransportPlan I J) := {ij : I × J // 0 < K ij.1 ij.2}
local instance activeEdgeFintype (K : TransportPlan I J) : Fintype (ActiveEdge K) :=
  Fintype.ofFinite _

/-- The actual finite-dimensional linear image of row and column log potentials. -/
def supportedLogPotential (K : TransportPlan I J) :
    ((I → ℝ) × (J → ℝ)) →ₗ[ℝ] (ActiveEdge K → ℝ) where
  toFun ab e := ab.1 e.1.1 + ab.2 e.1.2
  map_add' ab cd := by
    funext e
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' a ab := by
    funext e
    simp [smul_eq_mul, mul_add]

/-- No choice of a cycle basis is required for closedness of the finite image. -/
theorem isClosed_supportedLogPotential_range (K : TransportPlan I J) :
    IsClosed (Set.range (supportedLogPotential K)) := by
  exact (LinearMap.range (supportedLogPotential K)).closed_of_finiteDimensional

/-- A positive diagonal scaling has its active log ratio in the potential image. -/
theorem logRatio_mem_supportedLogPotential_range
    (K : TransportPlan I J) (u : I → ℝ) (v : J → ℝ)
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) :
    (fun e : ActiveEdge K => Real.log
      (u e.1.1 * K e.1.1 e.1.2 * v e.1.2 / K e.1.1 e.1.2)) ∈
      Set.range (supportedLogPotential K) := by
  refine ⟨(fun i => Real.log (u i), fun j => Real.log (v j)), ?_⟩
  funext e
  change Real.log (u e.1.1) + Real.log (v e.1.2) = _
  have hquot : u e.1.1 * K e.1.1 e.1.2 * v e.1.2 / K e.1.1 e.1.2 =
      u e.1.1 * v e.1.2 := by
    field_simp [e.2.ne'] <;> ring
  rw [hquot, Real.log_mul (hu _).ne' (hv _).ne']

/-- Positive factors for a support-faithful limit are constructed from the closed
potential image, including supports with cycles longer than four. -/
theorem scaling_of_supported_limit (K Q : TransportPlan I J)
    (hK : ∀ i j, 0 ≤ K i j) (hQ : ∀ i j, 0 ≤ Q i j)
    (hQK : ∀ i j, Q i j = 0 ↔ K i j = 0)
    (M : ℕ → TransportPlan I J)
    (hM : ∀ n, ∃ u : I → ℝ, ∃ v : J → ℝ,
      (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧ M n = fun i j => u i * K i j * v j)
    (ht : Tendsto M atTop (𝓝 Q)) :
    ∃ u : I → ℝ, ∃ v : J → ℝ,
      (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧ Q = fun i j => u i * K i j * v j := by
  let F : TransportPlan I J → (ActiveEdge K → ℝ) :=
    fun A e => Real.log (A e.1.1 e.1.2 / K e.1.1 e.1.2)
  have hQpos (e : ActiveEdge K) : 0 < Q e.1.1 e.1.2 := by
    apply lt_of_le_of_ne (hQ _ _)
    intro hz
    exact e.2.ne' ((hQK _ _).1 hz.symm)
  have hcont : ContinuousAt F Q := by
    apply continuousAt_pi.2
    intro e
    have hcoord : ContinuousAt (fun A : TransportPlan I J => A e.1.1 e.1.2) Q :=
      ((continuous_apply e.1.2).comp (continuous_apply e.1.1)).continuousAt
    exact (hcoord.div_const _).log (div_pos (hQpos e) e.2).ne'
  have hmem : ∀ n, F (M n) ∈ Set.range (supportedLogPotential K) := by
    intro n
    obtain ⟨u, v, hu, hv, he⟩ := hM n
    rw [he]
    exact logRatio_mem_supportedLogPotential_range K u v hu hv
  have hFQ := (isClosed_supportedLogPotential_range K).mem_of_tendsto
    (hcont.tendsto.comp ht) (Eventually.of_forall hmem)
  obtain ⟨ab, hab⟩ := hFQ
  refine ⟨fun i => Real.exp (ab.1 i), fun j => Real.exp (ab.2 j),
    fun _ => Real.exp_pos _, fun _ => Real.exp_pos _, ?_⟩
  funext i j
  by_cases hz : K i j = 0
  · simp [hz, (hQK i j).2 hz]
  · have hp : 0 < K i j := lt_of_le_of_ne (hK i j) (Ne.symm hz)
    let e : ActiveEdge K := ⟨(i, j), hp⟩
    have he : ab.1 i + ab.2 j = Real.log (Q i j / K i j) := congrFun hab e
    have he' := congrArg Real.exp he
    rw [Real.exp_add, Real.exp_log (div_pos (hQpos e) hp)] at he'
    have heq := (eq_div_iff hz).1 he'
    calc
      Q i j = (Real.exp (ab.1 i) * Real.exp (ab.2 j)) * K i j := heq.symm
      _ = Real.exp (ab.1 i) * K i j * Real.exp (ab.2 j) := by ring

/-- A balanced diagonal scaling is unique on its fixed support. -/
theorem diagonal_scaling_unique_supported (K : TransportPlan I J)
    (u u' : I → ℝ) (v v' : J → ℝ)
    (hK : ∀ i j, 0 ≤ K i j)
    (hu : ∀ i, 0 < u i) (hu' : ∀ i, 0 < u' i)
    (hv : ∀ j, 0 < v j) (hv' : ∀ j, 0 < v' j)
    (hr : ∀ i, rowMass (fun i j => u i * K i j * v j) i =
      rowMass (fun i j => u' i * K i j * v' j) i)
    (hc : ∀ j, colMass (fun i j => u i * K i j * v j) j =
      colMass (fun i j => u' i * K i j * v' j) j) :
    (fun i j => u i * K i j * v j) = (fun i j => u' i * K i j * v' j) := by
  let P : TransportPlan I J := fun i j => u i * K i j * v j
  let Q : TransportPlan I J := fun i j => u' i * K i j * v' j
  have hP : ∀ i j, 0 ≤ P i j := fun i j => mul_nonneg (mul_nonneg (hu i).le (hK i j)) (hv j).le
  have hQ : ∀ i j, 0 ≤ Q i j := fun i j => mul_nonneg (mul_nonneg (hu' i).le (hK i j)) (hv' j).le
  have hsP : ∀ i j, P i j = 0 ↔ K i j = 0 := by
    intro i j
    simp [P, (hu i).ne', (hv j).ne']
  have hsQ : ∀ i j, Q i j = 0 ↔ K i j = 0 := by
    intro i j
    simp [Q, (hu' i).ne', (hv' j).ne']
  have h₁ := matrixKL_pythagorean_scaling_supported P K u' v' hK hu' hv'
    (fun i j h => (hsP i j).2 h) hr hc
  have h₂ := matrixKL_pythagorean_scaling_supported Q K u v hK hu hv
    (fun i j h => (hsQ i j).2 h) (fun i => (hr i).symm) (fun j => (hc j).symm)
  have hPQ := matrixKL_nonneg_supported P Q hP hQ
    (fun i j h => (hsP i j).2 ((hsQ i j).1 h))
  have hQP := matrixKL_nonneg_supported Q P hQ hP
    (fun i j h => (hsQ i j).2 ((hsP i j).1 h))
  apply (matrixKL_eq_zero_iff_supported P Q hP hQ
    (fun i j h => (hsP i j).2 ((hsQ i j).1 h))).1
  change matrixKL P K = matrixKL P Q + matrixKL Q K at h₁
  change matrixKL Q K = matrixKL Q P + matrixKL P K at h₂
  linarith

end InfoGeometry.Physics.AmariSinkhornAlternatingProjections

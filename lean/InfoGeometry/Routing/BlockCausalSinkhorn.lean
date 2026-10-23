/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InfoGeometry.Routing.CausalPrefixPooling

/-!
# Finite log-Sinkhorn and normalized prefix-local readout

Operational log-coordinate recurrence for the supplied code. Existing
`Canonical.SinkhornFoundation` owns positive-matrix normalization; this file
models the finite log recurrence and its exact reconstruction, not its
convergence or an inverse-existence theorem. A channel processor is a pure
function of current data; no Poisson correctness is inferred from locality.

Unlike the supplied raw-gain Lean decoder, `responsibility` includes the
channel row normalization used in the runtime. `ChunkData` is a native
product of finite coordinate spaces, giving actual normed-space instances.
-/
noncomputable section
namespace InfoGeometry.Routing.BlockCausalSinkhorn
open scoped BigOperators
open InfoGeometry.Routing.CausalPrefixPooling

variable {K : Type*} [Fintype K]

def logSumExp (a : K → ℝ) : ℝ := Real.log (∑ k, Real.exp (a k))

/-- Finite alternating log-domain updates. -/
def potentials (S : Matrix K K ℝ) : ℕ → (K → ℝ) × (K → ℝ)
  | 0 => (0, 0)
  | n+1 =>
      let old := potentials S n
      let u := fun i => -logSumExp (fun j => S i j + old.2 j)
      let v := fun j => -logSumExp (fun i => S i j + u i)
      (u, v)

def core (S : Matrix K K ℝ) (T : ℕ) : Matrix K K ℝ :=
  fun i j => Real.exp (S i j + (potentials S T).1 i + (potentials S T).2 j)

def gauge (S : Matrix K K ℝ) (T : ℕ) : ℝ :=
  (∑ k, ((potentials S T).1 k - (potentials S T).2 k)) /
    (2 * (Fintype.card K : ℝ))

def logShapeGain (S : Matrix K K ℝ) (T : ℕ) (i : K) : ℝ :=
  -(potentials S T).1 i + gauge S T

def logDetectorGain (S : Matrix K K ℝ) (T : ℕ) (j : K) : ℝ :=
  -(potentials S T).2 j - gauge S T

theorem core_pos (S : Matrix K K ℝ) (T : ℕ) (i j : K) : 0 < core S T i j :=
  Real.exp_pos _

theorem reconstruct (S : Matrix K K ℝ) (T : ℕ) (i j : K) :
    Real.exp (logShapeGain S T i) * core S T i j *
      Real.exp (logDetectorGain S T j) = Real.exp (S i j) := by
  unfold logShapeGain logDetectorGain core
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem normalized_exp_sum [Nonempty K] (a : K → ℝ) :
    ∑ k, Real.exp (a k - logSumExp a) = 1 := by
  have hp : 0 < ∑ k, Real.exp (a k) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) Finset.univ_nonempty
  simp_rw [Real.exp_sub]
  rw [← Finset.sum_div]
  unfold logSumExp
  rw [Real.exp_log hp, div_self hp.ne']

/-- The final column update normalizes columns. Finite T does not establish
simultaneous row normalization. -/
theorem core_column_sum [Nonempty K] (S : Matrix K K ℝ) (T : ℕ) (j : K) :
    ∑ i, core S (T+1) i j = 1 := by
  let u : K → ℝ := fun i => -logSumExp (fun l => S i l + (potentials S T).2 l)
  change (∑ i, Real.exp (S i j + u i + -logSumExp (fun r => S r j + u r))) = 1
  simpa only [sub_eq_add_neg] using normalized_exp_sum (fun i => S i j + u i)

/-- Row-normalized gain-calibrated detector responsibilities. -/
def responsibility {L : Type*} (S : Matrix K K ℝ) (T : ℕ)
    (logV : Matrix L K ℝ) : Matrix L K ℝ :=
  fun j k => Real.exp (logV j k + logDetectorGain S T k -
    logSumExp (fun l => logV j l + logDetectorGain S T l))

theorem responsibility_pos {L : Type*} (S : Matrix K K ℝ) (T : ℕ)
    (logV : Matrix L K ℝ) (j : L) (k : K) : 0 < responsibility S T logV j k :=
  Real.exp_pos _

theorem responsibility_sum [Nonempty K] {L : Type*}
    (S : Matrix K K ℝ) (T : ℕ) (logV : Matrix L K ℝ) (j : L) :
    ∑ k, responsibility S T logV j k = 1 :=
  normalized_exp_sum (fun k => logV j k + logDetectorGain S T k)

/-- Mass logs; four feature tables (key, shape value, query, detector value);
then token log-responsibilities. Local extraction is a separate map. -/
abbrev ChunkData (L K D : Type*) :=
  (K → ℝ) × (Fin 4 → Matrix K D ℝ) × Matrix L K ℝ

section Pipeline
variable {C L D : Type*} [Fintype C] [LinearOrder C]
variable [Fintype L] [Fintype D]

def pooledFeature (x : C → ChunkData L K D) (t : C) (a : Fin 4) : Matrix K D ℝ :=
  fun k d => pool (prefixSet t) (fun s => (x s).1 k) (fun s => (x s).2.1 a k d)

def logScore (x : C → ChunkData L K D) (t : C)
    (tau : ℝ) (prior : Matrix K K ℝ) : Matrix K K ℝ :=
  fun k l => (∑ d, pooledFeature x t 0 k d * (x t).2.1 2 l d) / tau + prior k l

/-- The nonlinear processor receives only current core and prefix signals. -/
def output (psi : Matrix K K ℝ → Matrix K D ℝ → Matrix K D ℝ → Matrix K D ℝ)
    (T : ℕ) (tau : ℝ) (prior : Matrix K K ℝ)
    (x : C → ChunkData L K D) (t : C) : Matrix L D ℝ :=
  responsibility (logScore x t tau prior) T (x t).2.2 *
    psi (core (logScore x t tau prior) T) (pooledFeature x t 1) ((x t).2.1 3)

theorem pooledFeature_local (x y : C → ChunkData L K D) (t : C)
    (h : Set.EqOn x y (Set.Iic t)) (a : Fin 4) :
    pooledFeature x t a = pooledFeature y t a := by
  ext k d
  apply prefix_pool_congr
  · intro s hs
    rw [h hs]
  · intro s hs
    rw [h hs]

theorem logScore_local (x y : C → ChunkData L K D) (t : C)
    (h : Set.EqOn x y (Set.Iic t)) (tau : ℝ) (prior : Matrix K K ℝ) :
    logScore x t tau prior = logScore y t tau prior := by
  have hx : x t = y t := h (le_refl t)
  simp only [logScore, pooledFeature_local x y t h 0, hx]

/-- Exact equality under arbitrary future-chunk changes. Neither matrix
invertibility nor Sinkhorn convergence is needed for this dependency claim. -/
theorem output_local
    (psi : Matrix K K ℝ → Matrix K D ℝ → Matrix K D ℝ → Matrix K D ℝ)
    (T : ℕ) (tau : ℝ) (prior : Matrix K K ℝ)
    (x y : C → ChunkData L K D) (t : C) (h : Set.EqOn x y (Set.Iic t)) :
    output psi T tau prior x t = output psi T tau prior y t := by
  have hx : x t = y t := h (le_refl t)
  simp only [output, logScore_local x y t h tau prior,
    pooledFeature_local x y t h 1, hx]

theorem output_update_future
    (psi : Matrix K K ℝ → Matrix K D ℝ → Matrix K D ℝ → Matrix K D ℝ)
    (T : ℕ) (tau : ℝ) (prior : Matrix K K ℝ)
    (x : C → ChunkData L K D) {t s : C} (h : t < s) (v : ChunkData L K D) :
    output psi T tau prior (Function.update x s v) t = output psi T tau prior x t :=
  output_local psi T tau prior _ _ t (update_future_eqOn x h v)

/-- Actual pipeline specialization, on the native normed coordinate product. -/
theorem output_future_derivative
    (psi : Matrix K K ℝ → Matrix K D ℝ → Matrix K D ℝ → Matrix K D ℝ)
    (T : ℕ) (tau : ℝ) (prior : Matrix K K ℝ)
    (x : C → ChunkData L K D) {t s : C} (h : t < s)
    (ell : (Matrix L D ℝ) →L[ℝ] ℝ) :
    HasFDerivAt (fun v => output psi T tau prior (Function.update x s v) t)
      (0 : ChunkData L K D →L[ℝ] Matrix L D ℝ) (x s) ∧
    HasFDerivAt (fun v => ell (output psi T tau prior (Function.update x s v) t))
      (0 : ChunkData L K D →L[ℝ] ℝ) (x s) ∧
    ell.comp (0 : ChunkData L K D →L[ℝ] Matrix L D ℝ) = 0 :=
  future_derivative_and_pullback t (fun z => output psi T tau prior z t)
    (fun a b hab => output_local psi T tau prior a b t hab) x h ell

end Pipeline
end InfoGeometry.Routing.BlockCausalSinkhorn

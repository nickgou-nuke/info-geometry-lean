/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation

/-!
# Continuation-coordinate transport for finite Markov trajectories

This scratch owner fixes the carrier/index semantics needed by the first-step
induction: after a history through time one, continuation successors are the
coordinates at times two through `n + 1`. The output path is a `Fin.cons` of
the first successor and this continuation tail.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectoryContinuationTransport

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
open InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance
local instance (n : ℕ) : MeasurableSpace (Fin n → ι) := ⊤
local instance (n : ℕ) : MeasurableSingletonClass (Fin n → ι) := inferInstance

/-- Extract successor states at times `1, …, n`. -/
def trajectorySuccessors (n : ℕ) :
    (Π _ : Finset.Iic n, ι) → Fin n → ι :=
  fun x k => x ⟨k.val + 1, Finset.mem_Iic.mpr (Nat.succ_le_of_lt k.isLt)⟩

/-- Extract the states at times `2, …, n + 1` from a continuation history
indexed by `Iic (n + 1)`. -/
def continuationTail (n : ℕ) :
    (Π _ : Finset.Iic (n + 1), ι) → Fin n → ι :=
  fun x k => x ⟨k.val + 2, Finset.mem_Iic.mpr (by
    have hk : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
    omega)⟩

/-- Coordinate decomposition: all successor states through time `n + 1` are
the first state at time one followed by the continuation tail from time two. -/
theorem trajectorySuccessors_eq_cons_continuationTail (n : ℕ)
    (x : Π _ : Finset.Iic (n + 1), ι) :
    trajectorySuccessors (n + 1) x =
      Fin.cons (x ⟨1, Finset.mem_Iic.mpr (by omega)⟩) (continuationTail n x) := by
  funext k
  refine Fin.cases ?_ ?_ k
  · rfl
  · intro k
    rfl

/-- The continuation tail map is measurable for finite product measurable
structures. -/
theorem continuationTail_measurable (n : ℕ) :
    Measurable (continuationTail (ι := ι) n) := by
  fun_prop

/-- A continuation of length one depends only on the state at time one and
has exactly that state's row-PMF transition law. This is the first base case
for transporting a general continuation through successor-path coordinates. -/
theorem oneStepContinuation_tail_law
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (h : Π _ : Finset.Iic 1, ι) :
    ((finiteTrajectoryKernel P hP 1 2 h).map
      (continuationTail (ι := ι) 1)) =
      (successorPathPMF P hP 1
        (h ⟨1, Finset.mem_Iic.mpr (by omega)⟩)).toMeasure := by
  let endpoint : (Π _ : Finset.Iic 1, ι) → ι :=
    fun x => x ⟨1, Finset.mem_Iic.mpr (by omega)⟩
  let endpointFinal : (Π _ : Finset.Iic 2, ι) → ι :=
    fun x => x ⟨2, Finset.mem_Iic.mpr (by omega)⟩
  let pathEmbed : ι → Fin 1 → ι := fun j _ => j
  have hcoords : continuationTail (ι := ι) 1 = pathEmbed ∘ endpointFinal := by
    funext x k
    fin_cases k
    rfl
  have hendpoint := congrArg (fun κ : Kernel (Π _ : Finset.Iic 1, ι) ι => κ h)
    (finiteTrajectoryKernel_succ_endpoint P hP 1)
  have hpmf : successorPathPMF P hP 1 (endpoint h) =
      (rowPMF P hP (endpoint h)).map pathEmbed := by
    simp only [successorPathPMF, PMF.pure_map]
    convert PMF.bind_pure_comp (p := rowPMF P hP (endpoint h))
      (f := pathEmbed) using 1
    congr 1
    funext j
    apply congrArg PMF.pure
    funext k
    fin_cases k
    rfl
  rw [hcoords, ← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [Kernel.map_apply _ (by fun_prop) h] at hendpoint
  rw [hendpoint, hpmf]
  have hhistory : historyTransitionKernel P hP 1 h =
      (rowPMF P hP (endpoint h)).toMeasure := by
    simp only [historyTransitionKernel, Kernel.comp_apply, Kernel.deterministic_apply]
    rw [Measure.dirac_bind (by fun_prop) (endpoint h)]
    rfl
  rw [hhistory]
  exact PMF.toMeasure_map (rowPMF P hP (endpoint h)) (f := pathEmbed) (by fun_prop)

end InfoGeometry.QuantumContext.FiniteMarkovTrajectoryContinuationTransport
end

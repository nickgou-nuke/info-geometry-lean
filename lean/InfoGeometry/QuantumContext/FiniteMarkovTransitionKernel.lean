/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.IonescuTulcea.Maps
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite Markov transition kernels from stochastic matrices

This owner turns a finite row-stochastic real matrix into a probability mass
function in each row and then into a Mathlib Markov kernel. It records the
singleton transition probabilities. This is a finite-step foundation only;
it does not assert an infinite trajectory measure or hitting-time formula.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance

/-- The finite probability mass function selected by row `i` of a
row-stochastic matrix. -/
def rowPMF (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι) : PMF ι :=
  PMF.ofFintype (fun j => ENNReal.ofReal (P i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun j _ => Matrix.nonneg_of_mem_rowStochastic hP)]
    rw [Matrix.sum_row_of_mem_rowStochastic hP i]
    norm_num)

/-- The transition kernel whose row at `i` is the PMF determined by `P i`. -/
def transitionKernel (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) : Kernel ι ι := by
  exact Kernel.ofFunOfCountable (fun i => (rowPMF P hP i).toMeasure)

instance transitionKernel_isMarkovKernel (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) :
    IsMarkovKernel (transitionKernel P hP) := by
  refine ⟨?_⟩
  intro i
  change IsProbabilityMeasure ((rowPMF P hP i).toMeasure)
  infer_instance

/-- A one-step transition assigns exactly the corresponding matrix entry to
the singleton destination event. -/
@[simp]
theorem transitionKernel_singleton (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (i j : ι) :
    transitionKernel P hP i {j} = ENNReal.ofReal (P i j) := by
  rw [transitionKernel]
  simp [Kernel.ofFunOfCountable, rowPMF]

/-- The expectation of a real observable after one transition is the
corresponding row of matrix-vector multiplication. This is the finite
probability-to-algebra bridge used by the first-hit Bellman recurrence. -/
theorem transitionKernel_integral_eq_mulVec (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι) (x : ι → ℝ) :
    ∫ j, x j ∂transitionKernel P hP i = (P.mulVec x) i := by
  change ∫ j, x j ∂(rowPMF P hP i).toMeasure = (P.mulVec x) i
  rw [PMF.integral_eq_sum]
  simp [Matrix.mulVec, dotProduct, rowPMF, ENNReal.toReal_ofReal,
    Matrix.nonneg_of_mem_rowStochastic hP]

/-- At time `n`, the transition law depends on a history only through its
state at time `n`. -/
noncomputable def historyTransitionKernel (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ) :
    Kernel (Π _ : Finset.Iic n, ι) ι :=
  transitionKernel P hP ∘ₖ
    Kernel.deterministic
      (fun x : Π _k : Finset.Iic n, ι => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
      (by fun_prop)

/-- The transition law of a history depends only on its endpoint. This is the
time-homogeneity fact needed when a finite path suffix is reindexed as a new
trajectory. -/
theorem historyTransitionKernel_apply_eq_of_endpoint_eq
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ)
    (x y : Π _ : Finset.Iic n, ι)
    (hxy : x ⟨n, Finset.mem_Iic.mpr le_rfl⟩ =
      y ⟨n, Finset.mem_Iic.mpr le_rfl⟩) :
    historyTransitionKernel P hP n x = historyTransitionKernel P hP n y := by
  simp only [historyTransitionKernel, Kernel.comp_apply, Kernel.deterministic_apply]
  rw [hxy]

/-- Pushing a history transition through Mathlib's `piSingleton` equivalence
preserves the one-step probability of the selected successor. This is the
transition-fiber factor used when extending a finite trajectory by one step. -/
theorem historyTransitionKernel_piSingleton_singleton
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (n : ℕ) (h : Π _ : Finset.Iic n, ι) (y : ι) :
    ((historyTransitionKernel P hP n).map
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n)) h
      ({MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n y} :
        Set (Π _ : Finset.Ioc n (n + 1), ι)) =
      ENNReal.ofReal (P (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) y) := by
  have hf : Measurable
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n) :=
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n).measurable
  have hs : MeasurableSet
      ({MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n y} :
        Set (Π _ : Finset.Ioc n (n + 1), ι)) := MeasurableSet.singleton _
  rw [Kernel.map_apply' _ hf h hs]
  simp only [historyTransitionKernel, Kernel.comp_apply, Kernel.deterministic_apply]
  rw [Measure.dirac_bind (by fun_prop)
    (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)]
  have hpre :
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n) ⁻¹'
        {MeasurableEquiv.piSingleton (X := fun _ : ℕ => ι) n y} = {y} := by
    ext z
    simp
  rw [hpre]
  exact transitionKernel_singleton P hP _ _

instance historyTransitionKernel_isMarkovKernel (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ) :
    IsMarkovKernel (historyTransitionKernel P hP n) := by
  change IsMarkovKernel
    (transitionKernel P hP ∘ₖ
      Kernel.deterministic
        (fun x : Π _k : Finset.Iic n, ι => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
        (by fun_prop))
  infer_instance

/-- The finite-horizon trajectory kernel assembled from the one-step matrix
transitions. Its source and target are histories indexed by `Iic a` and
`Iic b`; the initial history is supplied separately when applying the kernel. -/
noncomputable def finiteTrajectoryKernel (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (a b : ℕ) :
    Kernel (Π _ : Finset.Iic a, ι) (Π _ : Finset.Iic b, ι) :=
  Kernel.partialTraj (X := fun _ => ι) (historyTransitionKernel P hP) a b

set_option linter.style.haveILetI false in
instance finiteTrajectoryKernel_isMarkovKernel (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (a b : ℕ) :
    IsMarkovKernel (finiteTrajectoryKernel P hP a b) := by
  haveI : ∀ n, IsMarkovKernel (historyTransitionKernel P hP n) :=
    fun n => historyTransitionKernel_isMarkovKernel P hP n
  change IsMarkovKernel
    (Kernel.partialTraj (X := fun _ => ι) (historyTransitionKernel P hP) a b)
  infer_instance

/-- Finite trajectory laws are horizon-consistent: extending from `a` to `b`
and then `b` to `c` gives the same kernel as extending directly to `c`. -/
theorem finiteTrajectoryKernel_comp (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    finiteTrajectoryKernel P hP b c ∘ₖ finiteTrajectoryKernel P hP a b =
      finiteTrajectoryKernel P hP a c := by
  exact Kernel.partialTraj_comp_partialTraj hab hbc

/-- The endpoint marginal of a one-step trajectory extension is the transition
law selected by the old endpoint. This is the one-step marginal identity used
when decomposing finite path expectations. -/
theorem finiteTrajectoryKernel_succ_endpoint (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (n : ℕ) :
    (finiteTrajectoryKernel P hP n (n + 1)).map
      (fun x : Π _ : Finset.Iic (n + 1), ι =>
        x ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) = historyTransitionKernel P hP n := by
  exact Kernel.map_partialTraj_succ_self
    (X := fun _ => ι) (κ := historyTransitionKernel P hP) n

set_option linter.style.haveILetI false in
/-- For a fixed initial state, the production one-step trajectory law, pushed
to its sole successor coordinate, is exactly the row PMF used by the
transition-kernel construction. This is the one-transition base case for a
future identification of the full finite path law. -/
theorem finiteTrajectoryKernel_initial_oneStep_successor_law
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι) :
    (finiteTrajectoryKernel P hP 0 1 (fun _ => i)).map
        (fun x : Π _ : Finset.Iic 1, ι =>
          fun _ : Fin 1 => x ⟨1, Finset.mem_Iic.mpr le_rfl⟩) =
      ((rowPMF P hP i).map (fun j => fun _ : Fin 1 => j)).toMeasure := by
  letI : MeasurableSpace (Fin 1 → ι) := ⊤
  letI : MeasurableSingletonClass (Fin 1 → ι) := inferInstance
  let endpoint : (Π _ : Finset.Iic 1, ι) → ι :=
    fun x => x ⟨1, Finset.mem_Iic.mpr le_rfl⟩
  let pathEmbed : ι → Fin 1 → ι := fun j _ => j
  let initialHistory : Π _ : Finset.Iic 0, ι := fun _ => i
  have hendpoint := congrArg (fun κ => κ (initialHistory))
    (finiteTrajectoryKernel_succ_endpoint P hP 0)
  rw [Kernel.map_apply _ (by fun_prop) _] at hendpoint
  have hcoord :
      (fun x : Π _ : Finset.Iic 1, ι => fun _ : Fin 1 =>
        x ⟨1, Finset.mem_Iic.mpr le_rfl⟩) = pathEmbed ∘ endpoint := by
    funext x
    funext k
    rfl
  rw [hcoord, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have hendpoint' :
      Measure.map endpoint
          (finiteTrajectoryKernel P hP 0 1 initialHistory) =
        historyTransitionKernel P hP 0 initialHistory := by
    change Measure.map endpoint
        (finiteTrajectoryKernel P hP 0 1 initialHistory) = _ at hendpoint
    exact hendpoint
  rw [hendpoint']
  simp only [historyTransitionKernel, Kernel.comp_apply,
    Kernel.deterministic_apply, transitionKernel]
  rw [Measure.dirac_bind (by fun_prop) i]
  exact PMF.toMeasure_map (rowPMF P hP i) (f := pathEmbed) (by fun_prop)

end InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
end

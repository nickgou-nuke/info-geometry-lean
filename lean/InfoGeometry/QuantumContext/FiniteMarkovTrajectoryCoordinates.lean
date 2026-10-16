/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

/-!
# Coordinates and support of finite Markov trajectories

This owner provides the exact successor-coordinate map, the history
reconstruction fiber with fixed initial state, and the almost-everywhere
initial-state law supplied by `partialTraj`.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovTrajectoryCoordinates

open MeasureTheory ProbabilityTheory
open InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance
local instance (n : ℕ) : MeasurableSpace (Fin n → ι) := ⊤
local instance (n : ℕ) : MeasurableSingletonClass (Fin n → ι) := inferInstance

/-- Read successor states from a trajectory history, omitting time zero. -/
def trajectorySuccessors (n : ℕ) (x : Π _ : Finset.Iic n, ι) : Fin n → ι :=
  fun k => x ⟨k.val + 1,
    Finset.mem_Iic.mpr (Nat.succ_le_of_lt k.isLt)⟩

/-- The initial state of a finite trajectory history. -/
def trajectoryInitial (n : ℕ) (x : Π _ : Finset.Iic n, ι) : ι :=
  x ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩

/-- Reconstruct a history from its fixed initial state and successor path. -/
def historyOfSuccessors (n : ℕ) (i : ι) (p : Fin n → ι) :
    Π _ : Finset.Iic n, ι := fun t =>
  if ht : t.1 = 0 then i else p ⟨t.1 - 1, by
    have ht' := Finset.mem_Iic.mp t.2
    have hp : t.1 - 1 < n := by omega
    exact hp⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Successor extraction recovers the path used to reconstruct a history. -/
theorem trajectorySuccessors_historyOfSuccessors (n : ℕ) (i : ι)
    (p : Fin n → ι) :
    trajectorySuccessors n (historyOfSuccessors n i p) = p := by
  funext k
  simp only [trajectorySuccessors, historyOfSuccessors]
  have hk : k.val + 1 ≠ 0 := by omega
  simp only [dite_eq_right hk]
  congr 1

omit [Fintype ι] [DecidableEq ι] in
/-- With the time-zero coordinate fixed, successor coordinates determine a
history uniquely. -/
theorem history_ext_of_successors {n : ℕ} (i : ι)
    (x y : Π _ : Finset.Iic n, ι)
    (hx : trajectoryInitial n x = i)
    (hy : trajectoryInitial n y = i)
    (hxy : trajectorySuccessors n x = trajectorySuccessors n y) : x = y := by
  funext t
  by_cases ht : t.1 = 0
  · have ht0 : t = ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩ := Subtype.ext ht
    rw [ht0]
    change trajectoryInitial n x = trajectoryInitial n y
    rw [hx, hy]
  · have htpos : 0 < t.1 := Nat.pos_of_ne_zero ht
    have htle : t.1 ≤ n := Finset.mem_Iic.mp t.2
    let k : Fin n := ⟨t.1 - 1, by omega⟩
    have hcoord : t = ⟨k.val + 1, Finset.mem_Iic.mpr (by omega)⟩ := by
      apply Subtype.ext
      change t.1 = k.val + 1
      simp [k]
      omega
    rw [hcoord]
    exact congrFun hxy k

omit [Fintype ι] [DecidableEq ι] in
/-- The fiber of successor extraction on histories with initial state `i` is
the singleton containing the reconstructed history. -/
theorem successorFiber_eq_singleton {n : ℕ} (i : ι) (p : Fin n → ι) :
    {x : Π _ : Finset.Iic n, ι | trajectoryInitial n x = i ∧
      trajectorySuccessors n x = p} = {historyOfSuccessors n i p} := by
  ext x
  constructor
  · rintro ⟨h0, hpath⟩
    have hEq := history_ext_of_successors i x
      (historyOfSuccessors n i p) h0 (by simp [trajectoryInitial, historyOfSuccessors])
      (hpath.trans (trajectorySuccessors_historyOfSuccessors n i p).symm)
    simp [hEq]
  · intro hx
    have hx' : x = historyOfSuccessors n i p := by simpa using hx
    subst x
    exact ⟨by simp [trajectoryInitial, historyOfSuccessors],
      trajectorySuccessors_historyOfSuccessors n i p⟩

/-- The production trajectory kernel retains its complete input prefix under
the restriction map. -/
theorem partialTraj_output_prefix_is_dirac
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (a b : ℕ) (hab : a ≤ b) (h : Π _ : Finset.Iic a, ι) :
    Measure.map (Preorder.frestrictLe₂ (π := fun _ : ℕ => ι) hab)
      (Kernel.partialTraj (X := fun _ : ℕ => ι)
        (historyTransitionKernel P hP) a b h) = Measure.dirac h := by
  rw [Kernel.partialTraj_map_frestrictLe₂_apply
    (X := fun _ : ℕ => ι) (κ := historyTransitionKernel P hP) h
    (a := a) (b := a) (c := b) hab]
  simp only [Kernel.partialTraj_self, Kernel.id_apply]

/-- The time-zero coordinate is equal to the prescribed initial state almost
everywhere under the finite trajectory measure. -/
theorem finiteTrajectoryKernel_initial_ae
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (n : ℕ) (i : ι) :
    ∀ᵐ x ∂ finiteTrajectoryKernel P hP 0 n (fun _ => i),
      trajectoryInitial n x = i := by
  let μ := finiteTrajectoryKernel P hP 0 n (fun _ => i)
  let r : (Π _ : Finset.Iic n, ι) → (Π _ : Finset.Iic 0, ι) :=
    Preorder.frestrictLe₂ (π := fun _ : ℕ => ι) (Nat.zero_le n)
  let z : (Π _ : Finset.Iic 0, ι) → ι :=
    fun y => y ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩
  have hprefix : Measure.map r μ = Measure.dirac (fun _ : Finset.Iic 0 => i) := by
    exact partialTraj_output_prefix_is_dirac P hP 0 n (Nat.zero_le n) (fun _ => i)
  have hz : Measure.map z (Measure.map r μ) = Measure.dirac i := by
    rw [hprefix]
    simp [z]
  have hz' : Measure.map (z ∘ r) μ = Measure.dirac i := by
    rw [← Measure.map_map (by fun_prop) (by fun_prop)]
    exact hz
  have hset : {y : ι | y = i} ∈ ae (Measure.dirac i) := by simp
  have hae : (z ∘ r) ⁻¹' {i} ∈ ae μ :=
    (mem_ae_map_iff (by fun_prop) (MeasurableSet.singleton i)).mp
      (by simp [hz'])
  have hmap : z ∘ r = trajectoryInitial n := by
    funext x
    rfl
  change ∀ᵐ x ∂μ, x ∈ (z ∘ r) ⁻¹' {i} at hae
  simpa [hmap] using hae

end InfoGeometry.QuantumContext.FiniteMarkovTrajectoryCoordinates
end

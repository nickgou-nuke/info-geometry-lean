import Mathlib.Tactic
import Omega.EA.SyncKernelResetWords

namespace Omega.EA

open scoped BigOperators

/-- Uniform-input transition kernel on the 10-state synchronization automaton. -/
def sync10UniformKernel (q q' : Sync10State) : ℚ :=
  ((Finset.univ.filter fun d : Fin 3 => sync10Step q d = q').card : ℚ) / 3

/-- The explicit stationary law of the uniform-input `Sync10` chain in appendix order
`000,001,002,010,100,101,0-12,1-12,01-1,11-1`. -/
def sync10UniformStationaryVector : Sync10State → ℚ
  | .q000 => 7 / 48
  | .q001 => 1 / 6
  | .q002 => 1 / 8
  | .q010 => 1 / 8
  | .q100 => 1 / 6
  | .q101 => 7 / 48
  | .q0m12 => 1 / 24
  | .q1m12 => 1 / 48
  | .q01m1 => 1 / 48
  | .q11m1 => 1 / 24

/-- Left action of a probability vector on the uniform `Sync10` kernel. -/
def sync10UniformLeftAction (v : Sync10State → ℚ) (q' : Sync10State) : ℚ :=
  ∑ q, v q * sync10UniformKernel q q'

/-- The explicit vector is normalized and stationary for the uniform-input `Sync10` chain. -/
def sync10UniformNormalizedStationaryVector : Prop :=
  (∑ q, sync10UniformStationaryVector q = 1) ∧
    ∀ q, sync10UniformLeftAction sync10UniformStationaryVector q = sync10UniformStationaryVector q

theorem sync10State_univ :
    (Finset.univ : Finset Sync10State) =
      {Sync10State.q000, Sync10State.q001, Sync10State.q002, Sync10State.q010,
       Sync10State.q100, Sync10State.q101, Sync10State.q0m12, Sync10State.q1m12,
       Sync10State.q01m1, Sync10State.q11m1} := by
  ext q
  cases q <;> simp

private theorem fin3_univ : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
  ext i
  fin_cases i <;> simp

private theorem sync10_stationary_mass_total :
    (∑ q : Sync10State, sync10UniformStationaryVector q) = 1 := by
  simp [sync10State_univ, sync10UniformStationaryVector]
  norm_num

private theorem sync10_count_to_q000 (q : Sync10State) :
    (Finset.univ.filter fun d : Fin 3 => sync10Step q d = Sync10State.q000).card =
      if q = Sync10State.q000 ∨ q = Sync10State.q100 ∨ q = Sync10State.q002 then 1 else 0 := by
  fin_cases q <;> simp [fin3_univ, sync10Step, Finset.filter_insert,
    Finset.filter_singleton]

private theorem sync10_count_to_q001 (q : Sync10State) :
    (Finset.univ.filter fun d : Fin 3 => sync10Step q d = Sync10State.q001).card =
      if q = Sync10State.q000 ∨ q = Sync10State.q100 ∨ q = Sync10State.q002 ∨
          q = Sync10State.q01m1 ∨ q = Sync10State.q11m1 then 1 else 0 := by
  fin_cases q <;> simp [fin3_univ, sync10Step, Finset.filter_insert,
    Finset.filter_singleton]

private theorem sync10_count_to_q002 (q : Sync10State) :
    (Finset.univ.filter fun d : Fin 3 => sync10Step q d = Sync10State.q002).card =
      if q = Sync10State.q000 ∨ q = Sync10State.q100 ∨
          q = Sync10State.q01m1 ∨ q = Sync10State.q11m1 then 1 else 0 := by
  fin_cases q <;> simp [fin3_univ, sync10Step, Finset.filter_insert,
    Finset.filter_singleton]

private theorem sync10_count_to_q010 (q : Sync10State) :
    (Finset.univ.filter fun d : Fin 3 => sync10Step q d = Sync10State.q010).card =
      if q = Sync10State.q001 ∨ q = Sync10State.q101 ∨
          q = Sync10State.q0m12 ∨ q = Sync10State.q1m12 then 1 else 0 := by
  fin_cases q <;> simp [fin3_univ, sync10Step, Finset.filter_insert,
    Finset.filter_singleton]

private theorem sync10_count_to_q100 (q : Sync10State) :
    (Finset.univ.filter fun d : Fin 3 => sync10Step q d = Sync10State.q100).card =
      if q = Sync10State.q001 ∨ q = Sync10State.q010 ∨ q = Sync10State.q101 ∨
          q = Sync10State.q0m12 ∨ q = Sync10State.q1m12 then 1 else 0 := by
  fin_cases q <;> simp [fin3_univ, sync10Step, Finset.filter_insert,
    Finset.filter_singleton]

private theorem sync10_count_to_q101 (q : Sync10State) :
    (Finset.univ.filter fun d : Fin 3 => sync10Step q d = Sync10State.q101).card =
      if q = Sync10State.q001 ∨ q = Sync10State.q010 ∨ q = Sync10State.q101 then 1 else 0 := by
  fin_cases q <;> simp [fin3_univ, sync10Step, Finset.filter_insert,
    Finset.filter_singleton]

private theorem sync10_count_to_q0m12 (q : Sync10State) :
    (Finset.univ.filter fun d : Fin 3 => sync10Step q d = Sync10State.q0m12).card =
      if q = Sync10State.q010 then 1 else 0 := by
  fin_cases q <;> simp [fin3_univ, sync10Step, Finset.filter_insert,
    Finset.filter_singleton]

private theorem sync10_count_to_q1m12 (q : Sync10State) :
    (Finset.univ.filter fun d : Fin 3 => sync10Step q d = Sync10State.q1m12).card =
      if q = Sync10State.q01m1 ∨ q = Sync10State.q11m1 then 1 else 0 := by
  fin_cases q <;> simp [fin3_univ, sync10Step, Finset.filter_insert,
    Finset.filter_singleton]

private theorem sync10_count_to_q01m1 (q : Sync10State) :
    (Finset.univ.filter fun d : Fin 3 => sync10Step q d = Sync10State.q01m1).card =
      if q = Sync10State.q0m12 ∨ q = Sync10State.q1m12 then 1 else 0 := by
  fin_cases q <;> simp [fin3_univ, sync10Step, Finset.filter_insert,
    Finset.filter_singleton]

private theorem sync10_count_to_q11m1 (q : Sync10State) :
    (Finset.univ.filter fun d : Fin 3 => sync10Step q d = Sync10State.q11m1).card =
      if q = Sync10State.q002 then 1 else 0 := by
  fin_cases q <;> simp [fin3_univ, sync10Step, Finset.filter_insert,
    Finset.filter_singleton]

private theorem sync10_stationary_q000 :
    sync10UniformLeftAction sync10UniformStationaryVector Sync10State.q000 =
      sync10UniformStationaryVector Sync10State.q000 := by
  unfold sync10UniformLeftAction sync10UniformKernel
  rw [sync10State_univ]
  simp [sync10UniformStationaryVector, sync10_count_to_q000]
  norm_num

private theorem sync10_stationary_q001 :
    sync10UniformLeftAction sync10UniformStationaryVector Sync10State.q001 =
      sync10UniformStationaryVector Sync10State.q001 := by
  unfold sync10UniformLeftAction sync10UniformKernel
  rw [sync10State_univ]
  simp [sync10UniformStationaryVector, sync10_count_to_q001]
  norm_num

private theorem sync10_stationary_q002 :
    sync10UniformLeftAction sync10UniformStationaryVector Sync10State.q002 =
      sync10UniformStationaryVector Sync10State.q002 := by
  unfold sync10UniformLeftAction sync10UniformKernel
  rw [sync10State_univ]
  simp [sync10UniformStationaryVector, sync10_count_to_q002]
  norm_num

private theorem sync10_stationary_q010 :
    sync10UniformLeftAction sync10UniformStationaryVector Sync10State.q010 =
      sync10UniformStationaryVector Sync10State.q010 := by
  unfold sync10UniformLeftAction sync10UniformKernel
  rw [sync10State_univ]
  simp [sync10UniformStationaryVector, sync10_count_to_q010]
  norm_num

private theorem sync10_stationary_q100 :
    sync10UniformLeftAction sync10UniformStationaryVector Sync10State.q100 =
      sync10UniformStationaryVector Sync10State.q100 := by
  unfold sync10UniformLeftAction sync10UniformKernel
  rw [sync10State_univ]
  simp [sync10UniformStationaryVector, sync10_count_to_q100]
  norm_num

private theorem sync10_stationary_q101 :
    sync10UniformLeftAction sync10UniformStationaryVector Sync10State.q101 =
      sync10UniformStationaryVector Sync10State.q101 := by
  unfold sync10UniformLeftAction sync10UniformKernel
  rw [sync10State_univ]
  simp [sync10UniformStationaryVector, sync10_count_to_q101]
  norm_num

private theorem sync10_stationary_q0m12 :
    sync10UniformLeftAction sync10UniformStationaryVector Sync10State.q0m12 =
      sync10UniformStationaryVector Sync10State.q0m12 := by
  unfold sync10UniformLeftAction sync10UniformKernel
  rw [sync10State_univ]
  simp [sync10UniformStationaryVector, sync10_count_to_q0m12]
  norm_num

private theorem sync10_stationary_q1m12 :
    sync10UniformLeftAction sync10UniformStationaryVector Sync10State.q1m12 =
      sync10UniformStationaryVector Sync10State.q1m12 := by
  unfold sync10UniformLeftAction sync10UniformKernel
  rw [sync10State_univ]
  simp [sync10UniformStationaryVector, sync10_count_to_q1m12]
  norm_num

private theorem sync10_stationary_q01m1 :
    sync10UniformLeftAction sync10UniformStationaryVector Sync10State.q01m1 =
      sync10UniformStationaryVector Sync10State.q01m1 := by
  unfold sync10UniformLeftAction sync10UniformKernel
  rw [sync10State_univ]
  simp [sync10UniformStationaryVector, sync10_count_to_q01m1]
  norm_num

private theorem sync10_stationary_q11m1 :
    sync10UniformLeftAction sync10UniformStationaryVector Sync10State.q11m1 =
      sync10UniformStationaryVector Sync10State.q11m1 := by
  unfold sync10UniformLeftAction sync10UniformKernel
  rw [sync10State_univ]
  simp [sync10UniformStationaryVector, sync10_count_to_q11m1]
  norm_num

/-- Uniform-input stationary law for the 10-state synchronization kernel.
    prop:sync10-uniform-stationary -/
theorem paper_sync10_uniform_stationary : sync10UniformNormalizedStationaryVector := by
  constructor
  · exact sync10_stationary_mass_total
  · intro q
    cases q with
    | q000 => exact sync10_stationary_q000
    | q001 => exact sync10_stationary_q001
    | q002 => exact sync10_stationary_q002
    | q010 => exact sync10_stationary_q010
    | q100 => exact sync10_stationary_q100
    | q101 => exact sync10_stationary_q101
    | q0m12 => exact sync10_stationary_q0m12
    | q1m12 => exact sync10_stationary_q1m12
    | q01m1 => exact sync10_stationary_q01m1
    | q11m1 => exact sync10_stationary_q11m1

end Omega.EA

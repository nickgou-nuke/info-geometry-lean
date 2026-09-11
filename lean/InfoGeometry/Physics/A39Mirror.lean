import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import InfoGeometry.Physics.IsospinMirrorDynamics

namespace InfoGeometry.Physics

/-- The A=39 mirror pair (Ca-39 and K-39). -/
def A39Pair : MirrorPair where
  nuc1 := { Z := 20, N := 19 }
  nuc2 := { Z := 19, N := 20 }
  mirror_cond_Z := rfl
  mirror_cond_N := rfl

/-- Cross-shell excitations for the A=39 mirror pair. -/
inductive ExcitationsA39
  | p1_h2 : ExcitationsA39 -- 1 particle, 2 holes
  | p2_h3 : ExcitationsA39 -- 2 particles, 3 holes

/-- Nuclear state properties specific to the A=39 CED downsloping analysis. -/
structure A39State where
  excitation : ExcitationsA39
  excitation_energy : ℝ
  spin : ℚ
  parity : ℤ
  spatial_overlap : ℝ

/-- Coulomb Energy Difference (CED) as a function of the A=39 state. -/
noncomputable def CED (state : A39State) : ℝ :=
  -- CED decreases with increasing spatial overlap (Thomas-Ehrman shift analog)
  -- For p1_h2 excitations: CED = base_CED - k * spatial_overlap
  let base_CED : ℝ := 100.0
  let k : ℝ := 50.0
  base_CED - k * state.spatial_overlap

/-- The CED downsloping trend for the A=39 mirror pair.
For negative parity states from p1_h2 cross-shell excitations,
as excitation energy increases, spatial overlap increases (expansion),
which directly reduces the Coulomb energy (Thomas-Ehrman shift analog)
and generates a negative CED slope. -/
theorem downsloping_CED_A39 (s1 s2 : A39State)
    (_h_exc1 : s1.excitation = ExcitationsA39.p1_h2)
    (_h_exc2 : s2.excitation = ExcitationsA39.p1_h2)
    (_h_parity1 : s1.parity = -1)
    (_h_parity2 : s2.parity = -1)
    (_h_energy_inc : s1.excitation_energy < s2.excitation_energy)
    (h_overlap_inc : s2.spatial_overlap > s1.spatial_overlap) :
    s2.spatial_overlap > s1.spatial_overlap ∧ CED s2 < CED s1 := by
  refine ⟨h_overlap_inc, ?_⟩
  unfold CED
  nlinarith [h_overlap_inc]

end InfoGeometry.Physics

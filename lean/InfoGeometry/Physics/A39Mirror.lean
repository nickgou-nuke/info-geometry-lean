import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import InfoGeometry.Physics.IsospinMirrorDynamics

namespace InfoGeometry.Physics

/-- The A=39 mirror pair (Ca-39 and K-39). -/
def A39Pair : MirrorPair where
  nuc1 := (20, 19)
  nuc2 := (19, 20)
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

/-- The CED decreases when the overlap parameter increases. -/
theorem downsloping_CED_A39 (s1 s2 : A39State)
    (h_overlap_inc : s2.spatial_overlap > s1.spatial_overlap) :
    s2.spatial_overlap > s1.spatial_overlap ∧ CED s2 < CED s1 := by
  refine ⟨h_overlap_inc, ?_⟩
  unfold CED
  nlinarith [h_overlap_inc]

end InfoGeometry.Physics

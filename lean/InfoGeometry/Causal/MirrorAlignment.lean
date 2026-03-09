import Mathlib.Tactic
import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Krein.Grading

namespace InfoGeometry.Causal

open InfoGeometry.Clifford
open InfoGeometry.Krein

abbrev V := DoubledSpace ℝ

noncomputable abbrev q11OnDoubled (v : V) : ℝ := splitQ11 (v.fst, v.snd)

def NullCone : Set V := {v | q11OnDoubled v = 0}
def TimelikeCone : Set V := {v | 0 < q11OnDoubled v}

noncomputable def MirrorMismatch : V →L[ℝ] V :=
  clmComm (gradePlusProj (E := ℝ)) (spectralPlusProj (E := ℝ))

lemma MirrorMismatch_eq_half_complexI :
    MirrorMismatch = ((2 : ℝ)⁻¹) • complexI (E := ℝ) := by
  simpa [MirrorMismatch] using (projector_commutator_gradePlus_spectralPlus_eq_half_complexI (E := ℝ))

lemma MirrorMismatch_apply_pair (a b : ℝ) :
    MirrorMismatch (a, b) = (-(2 : ℝ)⁻¹ * b, (2 : ℝ)⁻¹ * a) := by
  have h := congrArg (fun T => T (a, b)) MirrorMismatch_eq_half_complexI
  simpa [ContinuousLinearMap.smul_apply, complexI, modularJ, spectralEpsilon, mul_assoc, mul_comm, mul_left_comm] using h

lemma MirrorMismatch_maps_NullCone {v : V} (hv : v ∈ NullCone) : MirrorMismatch v ∈ NullCone := by
  rcases v with ⟨a, b⟩
  have hv' : a * a - b * b = 0 := by
    simpa [NullCone, q11OnDoubled, splitQ11_apply] using hv
  have hMM : MirrorMismatch (a, b) = (-(2 : ℝ)⁻¹ * b, (2 : ℝ)⁻¹ * a) :=
    MirrorMismatch_apply_pair (a := a) (b := b)
  have hq :
      (-(2 : ℝ)⁻¹ * b) * (-(2 : ℝ)⁻¹ * b) - ((2 : ℝ)⁻¹ * a) * ((2 : ℝ)⁻¹ * a) = 0 := by
    nlinarith [hv']
  change q11OnDoubled (MirrorMismatch (a, b)) = 0
  rw [hMM]
  simpa [q11OnDoubled, splitQ11_apply] using hq

theorem MirrorMismatch_ne_zero_on_NullCone {v : V} (hv : v ∈ NullCone) (h0 : v ≠ 0) : MirrorMismatch v ≠ 0 := by
  rcases v with ⟨a, b⟩
  simp [NullCone, q11OnDoubled, splitQ11_apply] at hv
  have hhalf : ((2 : ℝ)⁻¹) ≠ 0 := by norm_num
  intro hMM
  have hb : b = 0 := by
    have hmfst : (MirrorMismatch (a, b)).fst = 0 := by
      simpa using congrArg DoubledSpace.fst hMM
    have hfst : (-(2 : ℝ)⁻¹ * b) = 0 := by
      simpa [MirrorMismatch_apply_pair (a := a) (b := b)] using hmfst
    have hmul : ((2 : ℝ)⁻¹) * b = 0 := by
      nlinarith [hfst]
    exact (mul_eq_zero.mp hmul).resolve_left hhalf
  have ha : a = 0 := by
    have hmsnd : (MirrorMismatch (a, b)).snd = 0 := by
      simpa using congrArg DoubledSpace.snd hMM
    have hsnd : ((2 : ℝ)⁻¹ * a) = 0 := by
      simpa [MirrorMismatch_apply_pair (a := a) (b := b)] using hmsnd
    exact (mul_eq_zero.mp hsnd).resolve_left hhalf
  apply h0
  apply (WithLp.ofLp_injective 2)
  simp [ha, hb]

end InfoGeometry.Causal

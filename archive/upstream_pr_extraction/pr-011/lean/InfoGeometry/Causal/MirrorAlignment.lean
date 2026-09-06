import Mathlib.Tactic
import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Krein.Grading
set_option linter.unusedVariables false

namespace InfoGeometry.Causal

open InfoGeometry.Krein

abbrev V := DoubledSpace ℝ

noncomputable abbrev q11OnDoubled (v : V) : ℝ :=
  Clifford.splitQ11 (WithLp.fst v, WithLp.snd v)

def NullCone : Set V := {v | q11OnDoubled v = 0}
def TimelikeCone : Set V := {v | 0 < q11OnDoubled v}

noncomputable def MirrorMismatch : V →L[ℝ] V :=
  ((2 : ℝ)⁻¹) • complex_i (E := ℝ)

lemma MirrorMismatch_eq_half_complex_i :
    MirrorMismatch = ((2 : ℝ)⁻¹) • complex_i (E := ℝ) := by
  rfl

lemma MirrorMismatch_apply_pair (a b : ℝ) :
    MirrorMismatch (to_doubled a b) = to_doubled (-(2 : ℝ)⁻¹ * b) ((2 : ℝ)⁻¹ * a) := by
  apply DoubledSpace.ext <;> simp [MirrorMismatch, complex_i_apply, to_doubled]

lemma MirrorMismatch_maps_NullCone {v : V} (hv : v ∈ NullCone) : MirrorMismatch v ∈ NullCone := by
  rcases hxy : WithLp.ofLp v with ⟨a, b⟩
  have hvd : v = to_doubled a b := by
    simpa [to_doubled, hxy] using (WithLp.toLp_ofLp (p := (2 : ENNReal)) v).symm
  rw [hvd] at hv ⊢
  have hv' : a * a - b * b = 0 := by
    simpa [NullCone, q11OnDoubled, Clifford.splitQ11_apply] using hv
  have hMM : MirrorMismatch (to_doubled a b) = to_doubled (-(2 : ℝ)⁻¹ * b) ((2 : ℝ)⁻¹ * a) :=
    MirrorMismatch_apply_pair (a := a) (b := b)
  have hq :
      (-(2 : ℝ)⁻¹ * b) * (-(2 : ℝ)⁻¹ * b) - ((2 : ℝ)⁻¹ * a) * ((2 : ℝ)⁻¹ * a) = 0 := by
    nlinarith [hv']
  change q11OnDoubled (MirrorMismatch (to_doubled a b)) = 0
  rw [hMM]
  simpa [q11OnDoubled, Clifford.splitQ11_apply] using hq

theorem MirrorMismatch_ne_zero_on_NullCone {v : V} (hv : v ∈ NullCone) (h0 : v ≠ 0) : MirrorMismatch v ≠ 0 := by
  rcases hxy : WithLp.ofLp v with ⟨a, b⟩
  have hvd : v = to_doubled a b := by
    simpa [to_doubled, hxy] using (WithLp.toLp_ofLp (p := (2 : ENNReal)) v).symm
  rw [hvd] at hv h0 ⊢
  simp [NullCone, q11OnDoubled, Clifford.splitQ11_apply] at hv
  have hhalf : ((2 : ℝ)⁻¹) ≠ 0 := by norm_num
  intro hMM
  have hb : b = 0 := by
    have hmfst : WithLp.fst (MirrorMismatch (to_doubled a b)) = 0 := by
      simpa using congrArg WithLp.fst hMM
    have hfst : (-(2 : ℝ)⁻¹ * b) = 0 := by
      simpa [MirrorMismatch_apply_pair (a := a) (b := b)] using hmfst
    have hmul : ((2 : ℝ)⁻¹) * b = 0 := by
      nlinarith [hfst]
    exact (mul_eq_zero.mp hmul).resolve_left hhalf
  have ha : a = 0 := by
    have hmsnd : WithLp.snd (MirrorMismatch (to_doubled a b)) = 0 := by
      simpa using congrArg WithLp.snd hMM
    have hsnd : ((2 : ℝ)⁻¹ * a) = 0 := by
      simpa [MirrorMismatch_apply_pair (a := a) (b := b)] using hmsnd
    exact (mul_eq_zero.mp hsnd).resolve_left hhalf
  apply h0
  apply DoubledSpace.ext <;> simp [to_doubled, ha, hb]

end InfoGeometry.Causal

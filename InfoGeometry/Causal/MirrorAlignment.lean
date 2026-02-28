import Mathlib.Tactic
import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Krein.Grading

namespace InfoGeometry.Causal

open InfoGeometry.Clifford
open InfoGeometry.Krein

/-- Lorentz plane in this minimal model. -/
abbrev V := DoubledSpace ℝ

/-- Causal boundary (lightcone): null locus of `splitQ11`. -/
def NullCone : Set V := {v | splitQ11 v = 0}

/-- Interior (timelike cone). -/
def TimelikeCone : Set V := {v | 0 < splitQ11 v}

/-- Mirror mismatch commutator `[P₊(J), P₊(ε)]`. -/
noncomputable def MirrorMismatch : V →L[ℝ] V :=
  clmComm (E := ℝ) (gradePlusProj (E := ℝ)) (spectralPlusProj (E := ℝ))

lemma MirrorMismatch_eq_half_complexI :
    MirrorMismatch = ((2 : ℝ)⁻¹) • complexI (E := ℝ) := by
  simpa [MirrorMismatch] using
    (projector_commutator_gradePlus_spectralPlus_eq_half_complexI (E := ℝ))

lemma MirrorMismatch_apply_pair (a b : ℝ) :
    MirrorMismatch (a, b) = (-(2 : ℝ)⁻¹ * b, (2 : ℝ)⁻¹ * a) := by
  have h := congrArg (fun T => T (a, b)) MirrorMismatch_eq_half_complexI
  -- ((1/2)•I)(a,b) = (1/2)•(-b,a)
  simpa [ContinuousLinearMap.smul_apply, complexI, modularJ, spectralEpsilon, mul_assoc, mul_comm,
    mul_left_comm] using h

lemma MirrorMismatch_maps_NullCone {v : V} (hv : v ∈ NullCone) :
    MirrorMismatch v ∈ NullCone := by
  rcases v with ⟨a, b⟩
  simp [NullCone] at hv ⊢
  have hv' : a * a - b * b = 0 := by
    simpa [splitQ11_apply] using hv
  have hab : a * a = b * b := by linarith
  -- compute Q(MM(a,b)) = 0
  simp [MirrorMismatch_apply_pair (a := a) (b := b), splitQ11_apply, hab]

theorem MirrorMismatch_ne_zero_on_NullCone {v : V} (hv : v ∈ NullCone) (h0 : v ≠ 0) :
    MirrorMismatch v ≠ 0 := by
  rcases v with ⟨a, b⟩
  have hhalf : ((2 : ℝ)⁻¹) ≠ 0 := by norm_num
  intro hMM
  have hpair :
      (-(2 : ℝ)⁻¹ * b, (2 : ℝ)⁻¹ * a) = (0 : V) := by
    simpa [MirrorMismatch_apply_pair (a := a) (b := b)] using hMM
  have hb : b = 0 := by
    have : (-(2 : ℝ)⁻¹ * b) = 0 := by simpa using congrArg Prod.fst hpair
    have : ((2 : ℝ)⁻¹ * b) = 0 := by simpa using (neg_eq_zero.mp this)
    exact (mul_eq_zero.mp this).resolve_left hhalf
  have ha : a = 0 := by
    have : ((2 : ℝ)⁻¹ * a) = 0 := by simpa using congrArg Prod.snd hpair
    exact (mul_eq_zero.mp this).resolve_left hhalf
  apply h0
  ext <;> simp [ha, hb]

end InfoGeometry.Causal

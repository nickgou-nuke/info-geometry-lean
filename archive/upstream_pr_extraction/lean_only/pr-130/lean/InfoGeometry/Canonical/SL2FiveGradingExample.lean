/-
# SL2FiveGradingExample.lean

Concrete 5-graded Lie algebra: **𝔰𝔩₂(ℝ)** graded by the eigenvalues
of the Cartan element `h`.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger

set_option linter.dupNamespace false

noncomputable section

open Matrix

namespace InfoGeometry.Canonical.SL2FiveGradingExample

open InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger

/-! ## 1. The Lie algebra 𝔰𝔩₂(ℝ) -/

def e : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
def f : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
def h : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

lemma comm_e_f : e * f - f * e = h := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [e, f, h]
lemma comm_h_e : h * e - e * h = (2 : ℝ) • e := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [e, f, h]
lemma comm_h_f : h * f - f * h = (-2 : ℝ) • f := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [e, f, h]

def sl₂ : LieSubalgebra ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
  { carrier := {A | A.trace = 0}
    add_mem' := by intro A B hA hB; simp at hA hB ⊢; simp [hA, hB]
    zero_mem' := by simp
    smul_mem' := fun r A hA => by simp at hA ⊢; simp [hA]
    lie_mem' := by intro A B hA hB; simp [hA, hB, Matrix.trace_mul_comm] }

lemma e_mem_sl₂ : e ∈ sl₂ := by unfold sl₂ e; simp
lemma f_mem_sl₂ : f ∈ sl₂ := by unfold sl₂ f; simp
lemma h_mem_sl₂ : h ∈ sl₂ := by unfold sl₂ h; simp

/-! ## 2. The five‑grading -/

noncomputable def fₛ : sl₂ := ⟨f, f_mem_sl₂⟩
noncomputable def hₛ : sl₂ := ⟨h, h_mem_sl₂⟩
noncomputable def eₛ : sl₂ := ⟨e, e_mem_sl₂⟩

noncomputable def G₂ : Submodule ℝ sl₂ := Submodule.span ℝ {fₛ}
noncomputable def G₁ : Submodule ℝ sl₂ := ⊥
noncomputable def G₀ : Submodule ℝ sl₂ := Submodule.span ℝ {hₛ}
noncomputable def G₁' : Submodule ℝ sl₂ := ⊥
noncomputable def G₂' : Submodule ℝ sl₂ := Submodule.span ℝ {eₛ}

lemma smul_lie' {L : Type} [LieRing L] [LieAlgebra ℝ L] (t : ℝ) (x y : L) : ⁅t • x, y⁆ = t • ⁅x, y⁆ := by
  calc
    ⁅t • x, y⁆ = -⁅y, t • x⁆ := by rw [lie_skew]
    _ = -(t • ⁅y, x⁆) := by rw [LieAlgebra.lie_smul]
    _ = t • (-⁅y, x⁆) := by rw [smul_neg]
    _ = t • ⁅x, y⁆ := by rw [lie_skew]

lemma lie_f_e : ⁅fₛ, eₛ⁆ = -hₛ := by
  ext : 1
  calc
    (⁅fₛ, eₛ⁆ : Matrix (Fin 2) (Fin 2) ℝ) = (fₛ : Matrix (Fin 2) (Fin 2) ℝ) * (eₛ : Matrix (Fin 2) (Fin 2) ℝ) -
      (eₛ : Matrix (Fin 2) (Fin 2) ℝ) * (fₛ : Matrix (Fin 2) (Fin 2) ℝ) := rfl
    _ = f * e - e * f := by simp [fₛ, eₛ]
    _ = -(e * f - f * e) := by abel
    _ = -h := by rw [comm_e_f]
    _ = (-hₛ : Matrix (Fin 2) (Fin 2) ℝ) := by simp [hₛ, h]

lemma lie_e_f : ⁅eₛ, fₛ⁆ = hₛ := by
  calc
    ⁅eₛ, fₛ⁆ = -⁅fₛ, eₛ⁆ := by simp [lie_skew]
    _ = -(-hₛ) := by rw [lie_f_e]
    _ = hₛ := by simp

lemma lie_h_e : ⁅hₛ, eₛ⁆ = (2 : ℝ) • eₛ := by
  ext : 1
  calc
    (⁅hₛ, eₛ⁆ : Matrix (Fin 2) (Fin 2) ℝ) = (hₛ : Matrix (Fin 2) (Fin 2) ℝ) * (eₛ : Matrix (Fin 2) (Fin 2) ℝ) -
      (eₛ : Matrix (Fin 2) (Fin 2) ℝ) * (hₛ : Matrix (Fin 2) (Fin 2) ℝ) := rfl
    _ = h * e - e * h := by simp [hₛ, eₛ]
    _ = (2 : ℝ) • e := comm_h_e
    _ = ((2 : ℝ) • eₛ : Matrix (Fin 2) (Fin 2) ℝ) := by simp [eₛ, e]

lemma lie_h_f : ⁅hₛ, fₛ⁆ = (-2 : ℝ) • fₛ := by
  ext : 1
  calc
    (⁅hₛ, fₛ⁆ : Matrix (Fin 2) (Fin 2) ℝ) = (hₛ : Matrix (Fin 2) (Fin 2) ℝ) * (fₛ : Matrix (Fin 2) (Fin 2) ℝ) -
      (fₛ : Matrix (Fin 2) (Fin 2) ℝ) * (hₛ : Matrix (Fin 2) (Fin 2) ℝ) := rfl
    _ = h * f - f * h := by simp [hₛ, fₛ]
    _ = (-2 : ℝ) • f := comm_h_f
    _ = ((-2 : ℝ) • fₛ : Matrix (Fin 2) (Fin 2) ℝ) := by simp [fₛ, f]

noncomputable def sl2FiveGrading : FiveGrading sl₂ :=
  { gNegTwo := G₂
    gNegOne := G₁
    gZero   := G₀
    gPosOne := G₁'
    gPosTwo := G₂'
    negOne_posOne_mem_zero := by
      intro X Y hX hY
      have hX0 : X = 0 := by simpa using hX
      subst hX0; simp [Submodule.zero_mem]
    bracket_negTwo_posTwo := by
      intro X Y hX hY
      rcases Submodule.mem_span_singleton.mp hX with ⟨a, rfl⟩
      rcases Submodule.mem_span_singleton.mp hY with ⟨b, rfl⟩
      have h_eq : ⁅a • fₛ, b • eₛ⁆ = (-(a * b)) • hₛ := by
        calc
          ⁅a • fₛ, b • eₛ⁆ = a • ⁅fₛ, b • eₛ⁆ := by rw [smul_lie']
          _ = a • (b • ⁅fₛ, eₛ⁆) := by rw [LieAlgebra.lie_smul]
          _ = (a * b) • (-hₛ) := by simp [smul_smul, lie_f_e]
          _ = (-(a * b)) • hₛ := by simp [smul_smul]
      rw [h_eq]
      refine Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span (by simp)
    posOne_posOne_mem_posTwo := by
      intro X Y hX hY
      have hX0 : X = 0 := by simpa using hX
      subst hX0; simp [Submodule.zero_mem]
    negOne_negOne_mem_negTwo := by
      intro X Y hX hY
      have hX0 : X = 0 := by simpa using hX
      subst hX0; simp [Submodule.zero_mem] }

end InfoGeometry.Canonical.SL2FiveGradingExample

/-
# SL2SpinorLadder.lean

5-graded Lie algebra: 𝔰𝔩₂(ℝ) ⋉ ℝ².

All 5 grading slots are non-trivial:
  gNegTwo = ℝ·f   gNegOne = ℝ·v   gZero = ℝ·h
  gPosOne = ℝ·u   gPosTwo = ℝ·e
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger

set_option linter.dupNamespace false

noncomputable section

namespace SL2SpinorLadder

open FiveGradedInformationLedger

abbrev Alg : Type := ℝ × ℝ × ℝ × ℝ × ℝ

namespace Alg

def basisE : Alg := (1, 0, 0, 0, 0)
def basisH : Alg := (0, 1, 0, 0, 0)
def basisF : Alg := (0, 0, 1, 0, 0)
def basisU : Alg := (0, 0, 0, 1, 0)
def basisV : Alg := (0, 0, 0, 0, 1)

/-! ## The bracket -/

def br (x y : Alg) : Alg :=
  (2*(x.2.1*y.1 - x.1*y.2.1),
   x.1*y.2.2.1 - x.2.2.1*y.1,
   -2*(x.2.1*y.2.2.1 - x.2.2.1*y.2.1),
   (x.2.1*y.2.2.2.1 - x.2.2.2.1*y.2.1) + (x.1*y.2.2.2.2 - x.2.2.2.2*y.1),
   -(x.2.1*y.2.2.2.2 - x.2.2.2.2*y.2.1) + (x.2.2.1*y.2.2.2.1 - x.2.2.2.1*y.2.2.1))

lemma br_add_left (x y z : Alg) : br (x + y) z = br x z + br y z := by
  ext <;> dsimp [br] <;> ring

lemma br_add_right (x y z : Alg) : br x (y + z) = br x y + br x z := by
  ext <;> dsimp [br] <;> ring

lemma br_smul_left (r : ℝ) (x y : Alg) : br (r • x) y = r • br x y := by
  ext <;> dsimp [br] <;> ring

lemma br_smul_right (r : ℝ) (x y : Alg) : br x (r • y) = r • br x y := by
  ext <;> dsimp [br] <;> ring

lemma br_skew (x y : Alg) : br x y = -br y x := by
  ext <;> dsimp [br] <;> ring

lemma br_jacobi (x y z : Alg) : br x (br y z) + br y (br z x) + br z (br x y) = 0 := by
  ext <;> dsimp [br] <;> ring

noncomputable instance : LieRing Alg where
  bracket := br
  add_lie := br_add_left
  lie_add := br_add_right
  lie_self := λ x => by ext <;> dsimp [br] <;> ring
  leibniz_lie := λ x y z => by
    have h := br_jacobi x y z
    have h1 : br y (br z x) = -br y (br x z) := by
      calc
        br y (br z x) = br y (-br x z) := by rw [br_skew z x]
        _ = br y ((-1 : ℝ) • br x z) := by simp
        _ = (-1 : ℝ) • br y (br x z) := by rw [br_smul_right]
        _ = -br y (br x z) := by simp
    have h2 : br z (br x y) = -br (br x y) z := by rw [br_skew z (br x y)]
    rw [h1, h2] at h
    calc
      br x (br y z) = (br x (br y z) + (-br y (br x z)) + (-br (br x y) z)) + (br y (br x z) + br (br x y) z) := by abel
      _ = 0 + (br y (br x z) + br (br x y) z) := by rw [h]
      _ = br y (br x z) + br (br x y) z := by simp
      _ = br (br x y) z + br y (br x z) := by abel

noncomputable instance : LieAlgebra ℝ Alg :=
  { lie_smul := br_smul_right }

/-! ## The 5-grading -/

noncomputable def G₂ : Submodule ℝ Alg := Submodule.span ℝ {basisF}
noncomputable def G₁ : Submodule ℝ Alg := Submodule.span ℝ {basisV}
noncomputable def G₀ : Submodule ℝ Alg := Submodule.span ℝ {basisH}
noncomputable def G₁' : Submodule ℝ Alg := Submodule.span ℝ {basisU}
noncomputable def G₂' : Submodule ℝ Alg := Submodule.span ℝ {basisE}

/--
Helper: split `X ∈ span {v}` into `X = a • v`.
-/
lemma span_singleton_eq {v : Alg} (hX : X ∈ Submodule.span ℝ {v}) : ∃ a : ℝ, X = a • v := by
  have := (Submodule.mem_span_singleton (x := X) (y := v)).mp hX
  rcases this with ⟨a, ha⟩
  exact ⟨a, ha.symm⟩

/--
`FiveGrading` — all 5 slots non-trivial.
-/
noncomputable def spinorFiveGrading : FiveGrading Alg :=
  { gNegTwo := G₂
    gNegOne := G₁
    gZero   := G₀
    gPosOne := G₁'
    gPosTwo := G₂'
    negOne_posOne_mem_zero := by
      intro X Y hX hY
      rcases span_singleton_eq hX with ⟨a, rfl⟩
      rcases span_singleton_eq hY with ⟨b, rfl⟩
      have hzero : br (a • basisV) (b • basisU) = 0 := by
        simp [br, basisV, basisU, smul_smul]
      have hzero' : ⁅a • basisV, b • basisU⁆ = 0 := hzero
      rw [hzero']; exact Submodule.zero_mem (p := G₀)
    bracket_negTwo_posTwo := by
      intro X Y hX hY
      rcases span_singleton_eq hX with ⟨a, rfl⟩
      rcases span_singleton_eq hY with ⟨b, rfl⟩
      have h_eq : br (a • basisF) (b • basisE) = (-(a * b)) • basisH := by
        calc
          br (a • basisF) (b • basisE) = (a * b) • br basisF basisE := by
            rw [br_smul_left, br_smul_right, smul_smul]
          _ = (a * b) • (-basisH) := by norm_num [br, basisF, basisE, basisH]
          _ = (-(a * b)) • basisH := by simp [smul_smul]
      have h_eq' : ⁅a • basisF, b • basisE⁆ = (-(a * b)) • basisH := h_eq
      rw [h_eq']
      exact Submodule.smul_mem _ _ (by simp [G₀, basisH])
    posOne_posOne_mem_posTwo := by
      intro X Y hX hY
      rcases span_singleton_eq hX with ⟨a, rfl⟩
      rcases span_singleton_eq hY with ⟨b, rfl⟩
      have hzero : br (a • basisU) (b • basisU) = 0 := by
        simp [br, basisU, smul_smul]
      have hzero' : ⁅a • basisU, b • basisU⁆ = 0 := hzero
      rw [hzero']; exact Submodule.zero_mem (p := G₂')
    negOne_negOne_mem_negTwo := by
      intro X Y hX hY
      rcases span_singleton_eq hX with ⟨a, rfl⟩
      rcases span_singleton_eq hY with ⟨b, rfl⟩
      have hzero : br (a • basisV) (b • basisV) = 0 := by
        simp [br, basisV, smul_smul]
      have hzero' : ⁅a • basisV, b • basisV⁆ = 0 := hzero
      rw [hzero']; exact Submodule.zero_mem (p := G₂) }

/-! ## Extra grade-bracket conditions -/

lemma zero_zero_mem_zero (X Y : Alg) (hX : X ∈ G₀) (hY : Y ∈ G₀) : ⁅X, Y⁆ ∈ G₀ := by
  rcases span_singleton_eq hX with ⟨a, rfl⟩
  rcases span_singleton_eq hY with ⟨b, rfl⟩
  have hzero : br (a • basisH) (b • basisH) = 0 := by
    simp [br, basisH, smul_smul]
  rw [show ⁅a • basisH, b • basisH⁆ = 0 from hzero]
  exact Submodule.zero_mem (p := G₀)

lemma zero_posTwo_mem_posTwo (X Y : Alg) (hX : X ∈ G₀) (hY : Y ∈ G₂') : ⁅X, Y⁆ ∈ G₂' := by
  rcases span_singleton_eq hX with ⟨a, rfl⟩
  rcases span_singleton_eq hY with ⟨b, rfl⟩
  have h_eq : br (a • basisH) (b • basisE) = (a * b * 2) • basisE := by
    calc
      br (a • basisH) (b • basisE) = (a * b) • br basisH basisE := by
        rw [br_smul_left, br_smul_right, smul_smul]
      _ = (a * b) • ((2 : ℝ) • basisE) := by norm_num [br, basisH, basisE]
      _ = (a * b * 2) • basisE := by simp [smul_smul]
  rw [show ⁅a • basisH, b • basisE⁆ = (a * b * 2) • basisE from h_eq]
  exact Submodule.smul_mem _ _ (by simp [G₂', basisE])

lemma zero_negTwo_mem_negTwo (X Y : Alg) (hX : X ∈ G₀) (hY : Y ∈ G₂) : ⁅X, Y⁆ ∈ G₂ := by
  rcases span_singleton_eq hX with ⟨a, rfl⟩
  rcases span_singleton_eq hY with ⟨b, rfl⟩
  have h_eq : br (a • basisH) (b • basisF) = (a * b * (-2 : ℝ)) • basisF := by
    calc
      br (a • basisH) (b • basisF) = (a * b) • br basisH basisF := by
        rw [br_smul_left, br_smul_right, smul_smul]
      _ = (a * b) • ((-2 : ℝ) • basisF) := by norm_num [br, basisH, basisF]
      _ = (a * b * (-2 : ℝ)) • basisF := by simp [smul_smul]
  rw [show ⁅a • basisH, b • basisF⁆ = (a * b * (-2 : ℝ)) • basisF from h_eq]
  exact Submodule.smul_mem _ _ (by simp [G₂, basisF])

lemma zero_posOne_mem_posOne (X Y : Alg) (hX : X ∈ G₀) (hY : Y ∈ G₁') : ⁅X, Y⁆ ∈ G₁' := by
  rcases span_singleton_eq hX with ⟨a, rfl⟩
  rcases span_singleton_eq hY with ⟨b, rfl⟩
  have h_eq : br (a • basisH) (b • basisU) = (a * b) • basisU := by
    calc
      br (a • basisH) (b • basisU) = (a * b) • br basisH basisU := by
        rw [br_smul_left, br_smul_right, smul_smul]
      _ = (a * b) • basisU := by norm_num [br, basisH, basisU]
  rw [show ⁅a • basisH, b • basisU⁆ = (a * b) • basisU from h_eq]
  exact Submodule.smul_mem _ _ (by simp [G₁', basisU])

lemma zero_negOne_mem_negOne (X Y : Alg) (hX : X ∈ G₀) (hY : Y ∈ G₁) : ⁅X, Y⁆ ∈ G₁ := by
  rcases span_singleton_eq hX with ⟨a, rfl⟩
  rcases span_singleton_eq hY with ⟨b, rfl⟩
  have h_eq : br (a • basisH) (b • basisV) = (-(a * b)) • basisV := by
    calc
      br (a • basisH) (b • basisV) = (a * b) • br basisH basisV := by
        rw [br_smul_left, br_smul_right, smul_smul]
      _ = (a * b) • (-basisV) := by norm_num [br, basisH, basisV]
      _ = (-(a * b)) • basisV := by simp [smul_smul]
  rw [show ⁅a • basisH, b • basisV⁆ = (-(a * b)) • basisV from h_eq]
  exact Submodule.smul_mem _ _ (by simp [G₁, basisV])

lemma posTwo_negOne_mem_posOne (X Y : Alg) (hX : X ∈ G₂') (hY : Y ∈ G₁) : ⁅X, Y⁆ ∈ G₁' := by
  rcases span_singleton_eq hX with ⟨a, rfl⟩
  rcases span_singleton_eq hY with ⟨b, rfl⟩
  have h_eq : br (a • basisE) (b • basisV) = (a * b) • basisU := by
    calc
      br (a • basisE) (b • basisV) = (a * b) • br basisE basisV := by
        rw [br_smul_left, br_smul_right, smul_smul]
      _ = (a * b) • basisU := by norm_num [br, basisE, basisV, basisU]
  rw [show ⁅a • basisE, b • basisV⁆ = (a * b) • basisU from h_eq]
  exact Submodule.smul_mem _ _ (by simp [G₁', basisU])

lemma negTwo_posOne_mem_negOne (X Y : Alg) (hX : X ∈ G₂) (hY : Y ∈ G₁') : ⁅X, Y⁆ ∈ G₁ := by
  rcases span_singleton_eq hX with ⟨a, rfl⟩
  rcases span_singleton_eq hY with ⟨b, rfl⟩
  have h_eq : br (a • basisF) (b • basisU) = (a * b) • basisV := by
    calc
      br (a • basisF) (b • basisU) = (a * b) • br basisF basisU := by
        rw [br_smul_left, br_smul_right, smul_smul]
      _ = (a * b) • basisV := by norm_num [br, basisF, basisU, basisV]
  rw [show ⁅a • basisF, b • basisU⁆ = (a * b) • basisV from h_eq]
  exact Submodule.smul_mem _ _ (by simp [G₁, basisV])

lemma posTwo_negTwo_mem_zero (X Y : Alg) (hX : X ∈ G₂') (hY : Y ∈ G₂) : ⁅X, Y⁆ ∈ G₀ := by
  rcases span_singleton_eq hX with ⟨a, rfl⟩
  rcases span_singleton_eq hY with ⟨b, rfl⟩
  have h_eq : br (a • basisE) (b • basisF) = (a * b) • basisH := by
    calc
      br (a • basisE) (b • basisF) = (a * b) • br basisE basisF := by
        rw [br_smul_left, br_smul_right, smul_smul]
      _ = (a * b) • basisH := by norm_num [br, basisE, basisF, basisH]
  rw [show ⁅a • basisE, b • basisF⁆ = (a * b) • basisH from h_eq]
  exact Submodule.smul_mem _ _ (by simp [G₀, basisH])

lemma posOne_negOne_mem_zero (X Y : Alg) (hX : X ∈ G₁') (hY : Y ∈ G₁) : ⁅X, Y⁆ ∈ G₀ := by
  rcases span_singleton_eq hX with ⟨a, rfl⟩
  rcases span_singleton_eq hY with ⟨b, rfl⟩
  have hzero : br (a • basisU) (b • basisV) = 0 := by
    simp [br, basisU, basisV, smul_smul]
  have hzero' : ⁅a • basisU, b • basisV⁆ = 0 := hzero
  rw [hzero']; exact Submodule.zero_mem (p := G₀)

lemma posTwo_posTwo_zero (X Y : Alg) (hX : X ∈ G₂') (hY : Y ∈ G₂') : ⁅X, Y⁆ = 0 := by
  rcases span_singleton_eq hX with ⟨a, rfl⟩
  rcases span_singleton_eq hY with ⟨b, rfl⟩
  have hzero : br (a • basisE) (b • basisE) = 0 := by
    simp [br, basisE, smul_smul]
  rw [show ⁅a • basisE, b • basisE⁆ = 0 from hzero]

lemma negTwo_negTwo_zero (X Y : Alg) (hX : X ∈ G₂) (hY : Y ∈ G₂) : ⁅X, Y⁆ = 0 := by
  rcases span_singleton_eq hX with ⟨a, rfl⟩
  rcases span_singleton_eq hY with ⟨b, rfl⟩
  have hzero : br (a • basisF) (b • basisF) = 0 := by
    simp [br, basisF, smul_smul]
  rw [show ⁅a • basisF, b • basisF⁆ = 0 from hzero]

end Alg

end SL2SpinorLadder

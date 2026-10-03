import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.SinaiHyperbolicErgodicConeFieldBridge
import InfoGeometry.Canonical.SinaiHyperbolicSplittingBridge

open InfoGeometry.Canonical.SinaiHyperbolicErgodicConeFieldBridge
open InfoGeometry.Canonical.SinaiHyperbolicSplittingBridge

namespace SinaiBilliards

def unstableConeForward (τ κ α : ℝ) : Set (Fin 2 → ℝ) :=
  { v | ∃ cu cs : ℝ, v = cu • eigenvecU τ κ + cs • eigenvecS τ κ ∧ 0 ≤ cu ∧ |cs| ≤ α * cu }

lemma eigenvec_decomp_unique {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ)
    {cu cs cu' cs' : ℝ}
    (h_eq : cu • eigenvecU τ κ + cs • eigenvecS τ κ = cu' • eigenvecU τ κ + cs' • eigenvecS τ κ) :
    cu = cu' ∧ cs = cs' := by
  have h_sum : (cu - cu') • eigenvecU τ κ + (cs - cs') • eigenvecS τ κ = 0 := by
    calc (cu - cu') • eigenvecU τ κ + (cs - cs') • eigenvecS τ κ
      _ = cu • eigenvecU τ κ + cs • eigenvecS τ κ - (cu' • eigenvecU τ κ + cs' • eigenvecS τ κ) := by simp [sub_smul]; abel
      _ = cu • eigenvecU τ κ + cs • eigenvecS τ κ - (cu • eigenvecU τ κ + cs • eigenvecS τ κ) := by rw [h_eq]
      _ = 0 := sub_self _
  have h_eq0 : (∑ i : Fin 2, ![cu - cu', cs - cs'] i • ![eigenvecU τ κ, eigenvecS τ κ] i) = 0 := by
    have : (cu - cu') • eigenvecU τ κ + (cs - cs') • eigenvecS τ κ = 0 := h_sum
    simp [Fin.sum_univ_two, this]
  have hg := eigenvec_linear_independent hτ hκ
  rw [Fintype.linearIndependent_iff] at hg
  have h1 := hg ![cu - cu', cs - cs'] h_eq0
  have hcu : cu - cu' = 0 := by have h2 := h1 0; simp at h2; exact h2
  have hcs : cs - cs' = 0 := by have h2 := h1 1; simp at h2; exact h2
  exact ⟨sub_eq_zero.mp hcu, sub_eq_zero.mp hcs⟩

def coneLE (τ κ α : ℝ) (p q : Fin 2 → ℝ) : Prop :=
  (q - p) ∈ unstableConeForward τ κ α

def causalDiamond (τ κ α : ℝ) (p q : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  { x | coneLE τ κ α p x ∧ coneLE τ κ α x q }

def isBoundedInBasis (τ κ : ℝ) (S : Set (Fin 2 → ℝ)) : Prop :=
  ∃ M : ℝ, ∀ v ∈ S, ∃ cu cs : ℝ, v = cu • eigenvecU τ κ + cs • eigenvecS τ κ ∧ |cu| ≤ M ∧ |cs| ≤ M

lemma exists_decomp {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) (v : Fin 2 → ℝ) :
    ∃ cu cs : ℝ, v = cu • eigenvecU τ κ + cs • eigenvecS τ κ := by
  have hg := eigenvec_linear_independent hτ hκ
  have h_top : Submodule.span ℝ (Set.range ![eigenvecU τ κ, eigenvecS τ κ]) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hdim : Module.finrank ℝ (Fin 2 → ℝ) = 2 := by simp
    rw [hdim]
    have : Module.finrank ℝ (Submodule.span ℝ (Set.range ![eigenvecU τ κ, eigenvecS τ κ])) = Fintype.card (Fin 2) :=
      finrank_span_eq_card hg
    exact this
  have h_mem : v ∈ Submodule.span ℝ (Set.range ![eigenvecU τ κ, eigenvecS τ κ]) := by
    rw [h_top]
    exact Submodule.mem_top
  have h_range : Set.range ![eigenvecU τ κ, eigenvecS τ κ] = ({eigenvecU τ κ} : Set (Fin 2 → ℝ)) ∪ {eigenvecS τ κ} := by
    ext x
    simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [h_range, Submodule.span_union] at h_mem
  rw [Submodule.mem_sup] at h_mem
  rcases h_mem with ⟨vu, hvu, vs, hvs, rfl⟩
  rw [Submodule.mem_span_singleton] at hvu hvs
  rcases hvu with ⟨cu, rfl⟩
  rcases hvs with ⟨cs, rfl⟩
  exact ⟨cu, cs, rfl⟩

theorem causalDiamond_bounded {τ κ α : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) (hα : 0 < α)
    (p q : Fin 2 → ℝ) :
    isBoundedInBasis τ κ (causalDiamond τ κ α p q) := by
  rcases exists_decomp hτ hκ p with ⟨pu, ps, hp⟩
  rcases exists_decomp hτ hκ (q - p) with ⟨du, ds, hd⟩
  use |pu| + |du| + α * |du| + |ps| + α * |du|
  intro v hv
  rcases hv with ⟨hv1, hv2⟩
  rcases hv1 with ⟨cu1, cs1, h_eq1, h_cu1, h_cs1⟩
  have hv_eq : v = (pu + cu1) • eigenvecU τ κ + (ps + cs1) • eigenvecS τ κ := by
    calc v = p + (v - p) := by abel
      _ = (pu • eigenvecU τ κ + ps • eigenvecS τ κ) + (cu1 • eigenvecU τ κ + cs1 • eigenvecS τ κ) := by
        congr 1
      _ = (pu + cu1) • eigenvecU τ κ + (ps + cs1) • eigenvecS τ κ := by simp [add_smul]; abel
  use pu + cu1, ps + cs1
  refine ⟨hv_eq, ?_, ?_⟩
  · rcases hv2 with ⟨cu2, cs2, h_eq2, h_cu2, h_cs2⟩
    have h_q_p : q - p = (cu1 + cu2) • eigenvecU τ κ + (cs1 + cs2) • eigenvecS τ κ := by
      calc q - p = (v - p) + (q - v) := by abel
        _ = (cu1 • eigenvecU τ κ + cs1 • eigenvecS τ κ) + (cu2 • eigenvecU τ κ + cs2 • eigenvecS τ κ) := by
          congr 1
        _ = (cu1 + cu2) • eigenvecU τ κ + (cs1 + cs2) • eigenvecS τ κ := by simp [add_smul]; abel
    have h_trans : du • eigenvecU τ κ + ds • eigenvecS τ κ = (cu1 + cu2) • eigenvecU τ κ + (cs1 + cs2) • eigenvecS τ κ := hd.symm.trans h_q_p
    have ⟨hdu, _⟩ := eigenvec_decomp_unique hτ hκ h_trans
    have h_cu1_le : cu1 ≤ du := by linarith
    have h_abs_cu1 : |cu1| ≤ |du| := by
      rw [abs_of_nonneg h_cu1]
      calc cu1 ≤ du := h_cu1_le
        _ ≤ |du| := le_abs_self du
    calc |pu + cu1| ≤ |pu| + |cu1| := abs_add_le pu cu1
      _ ≤ |pu| + |du| := by linarith
      _ ≤ |pu| + |du| + α * |du| + |ps| + α * |du| := by
        have : 0 ≤ α * |du| := mul_nonneg (le_of_lt hα) (abs_nonneg du)
        have : 0 ≤ |ps| := abs_nonneg ps
        linarith
  · rcases hv2 with ⟨cu2, cs2, h_eq2, h_cu2, h_cs2⟩
    have h_q_p : q - p = (cu1 + cu2) • eigenvecU τ κ + (cs1 + cs2) • eigenvecS τ κ := by
      calc q - p = (v - p) + (q - v) := by abel
        _ = (cu1 • eigenvecU τ κ + cs1 • eigenvecS τ κ) + (cu2 • eigenvecU τ κ + cs2 • eigenvecS τ κ) := by
          congr 1
        _ = (cu1 + cu2) • eigenvecU τ κ + (cs1 + cs2) • eigenvecS τ κ := by simp [add_smul]; abel
    have h_trans : du • eigenvecU τ κ + ds • eigenvecS τ κ = (cu1 + cu2) • eigenvecU τ κ + (cs1 + cs2) • eigenvecS τ κ := hd.symm.trans h_q_p
    have ⟨hdu, _⟩ := eigenvec_decomp_unique hτ hκ h_trans
    have h_cu1_le : cu1 ≤ du := by linarith
    have h_abs_cu1 : cu1 ≤ |du| := by
      calc cu1 ≤ du := h_cu1_le
        _ ≤ |du| := le_abs_self du
    have h_abs_cs1 : |cs1| ≤ α * |du| := by
      calc |cs1| ≤ α * cu1 := h_cs1
        _ ≤ α * |du| := mul_le_mul_of_nonneg_left h_abs_cu1 (le_of_lt hα)
    calc |ps + cs1| ≤ |ps| + |cs1| := abs_add_le ps cs1
      _ ≤ |ps| + α * |du| := by linarith
      _ ≤ |pu| + |du| + α * |du| + |ps| + α * |du| := by
        have : 0 ≤ |pu| := abs_nonneg pu
        have : 0 ≤ |du| := abs_nonneg du
        have : 0 ≤ α * |du| := mul_nonneg (le_of_lt hα) (abs_nonneg du)
        linarith

end SinaiBilliards

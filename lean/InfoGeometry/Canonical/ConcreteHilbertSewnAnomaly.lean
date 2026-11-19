/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ConcreteHilbertCuntzO2
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Infinite-Dimensional Hilbert-Space Sewn Boundary Anomaly Cancellation on `H_lp`

Lifts the modular swap involution `modular_j` and fundamental symmetry `spectral_epsilon`
from the fiber `DoubledSpace E := WithLp 2 (E × E)` onto the completed binary Cantor
Hilbert boundary carrier `H_lp E := lp (fun _ : BinaryCantorBoundary => DoubledSpace E) 2`,
establishes their `Cl(1,1)` anticommutation with `J_lp ∘ ε_lp = K_lp`, proves self-adjointness
of `J_lp` wrt Mathlib's `lp` inner product `lp.instInnerProductSpace`, proves non-commuting
Cuntz `O₂` branch sewing invariance, and closes infinite-dimensional boundary anomaly
cancellation (`⟪ψ, ε_lp (B ψ)⟫ = 0` and `∑' i, ⟪e i, ε_lp (B (e i))⟫ = 0`) for any
`J_lp`-sewn bounded operator `B : H_lp E →L[ℝ] H_lp E`.
-/

noncomputable section

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.ErlangenNet
open InfoGeometry.Topology
open InfoGeometry.Canonical.ConcreteHilbertCommutation
open InfoGeometry.Canonical.ConcreteHilbertCuntzO2

namespace InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## 1. Fiber Norm & Self-Adjointness Identities on `DoubledSpace E` -/

omit [CompleteSpace E] in
lemma modular_j_norm (u : DoubledSpace E) :
    ‖modular_j (E := E) u‖ = ‖u‖ := by
  have hnn : ‖modular_j (E := E) u‖₊ = ‖u‖₊ := by
    have htop : (2 : ENNReal) ≠ ⊤ := by norm_num
    rw [WithLp.prod_nnnorm_eq_add (p := (2 : ENNReal)) htop]
    rw [WithLp.prod_nnnorm_eq_add (p := (2 : ENNReal)) htop]
    simp [modular_j_apply, add_comm]
  exact congrArg (fun x : NNReal => (x : ℝ)) hnn

omit [CompleteSpace E] in
lemma spectral_epsilon_norm (u : DoubledSpace E) :
    ‖spectral_epsilon (E := E) u‖ = ‖u‖ := by
  have hnn : ‖spectral_epsilon (E := E) u‖₊ = ‖u‖₊ := by
    have htop : (2 : ENNReal) ≠ ⊤ := by norm_num
    rw [WithLp.prod_nnnorm_eq_add (p := (2 : ENNReal)) htop]
    rw [WithLp.prod_nnnorm_eq_add (p := (2 : ENNReal)) htop]
    simp [spectral_epsilon_apply]
  exact congrArg (fun x : NNReal => (x : ℝ)) hnn

omit [CompleteSpace E] in
private lemma inner_modular_j_selfAdjoint (u v : DoubledSpace E) :
    inner ℝ (modular_j (E := E) u) v = inner ℝ u (modular_j (E := E) v) := by
  simp [modular_j_apply, WithLp.prod_inner_apply, add_comm]

/-! ## 2. Completed Hilbert Swap `J_lp_clm` and Chiral Symmetry `epsilon_lp_clm` -/

/-- Pointwise modular swap action on `BinaryCantorBoundary → DoubledSpace E`. -/
def J_raw (ψ : BinaryCantorBoundary → DoubledSpace E) (x : BinaryCantorBoundary) :
    DoubledSpace E :=
  modular_j (E := E) (ψ x)

omit [CompleteSpace E] in
lemma summable_J_raw (ψ : BinaryCantorBoundary → DoubledSpace E)
    (h : Summable fun x => ‖ψ x‖ ^ (2 : ℝ)) :
    Summable fun x => ‖J_raw (E := E) ψ x‖ ^ (2 : ℝ) := by
  have h_eq : (fun x => ‖J_raw (E := E) ψ x‖ ^ (2 : ℝ)) =
      (fun x => ‖ψ x‖ ^ (2 : ℝ)) := by
    ext x
    change ‖modular_j (E := E) (ψ x)‖ ^ (2 : ℝ) = ‖ψ x‖ ^ (2 : ℝ)
    rw [modular_j_norm]
  rw [h_eq]
  exact h

/-- The modular swap operator `J_lp` on `H_lp E`. -/
def J_lp (ψ : H_lp E) : H_lp E :=
  ⟨J_raw (E := E) ψ, by
    apply memℓp_gen
    have h1 : (2 : ENNReal).toReal = 2 := rfl
    rw [h1]
    have h2 : Memℓp ψ.1 2 := ψ.prop
    have h3 := (memℓp_gen_iff zero_lt_two).mp h2
    rw [h1] at h3
    exact summable_J_raw (E := E) ψ h3⟩

lemma J_lp_norm_eq (ψ : H_lp E) :
    ‖J_lp (E := E) ψ‖ = ‖ψ‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hpoint : (fun x : BinaryCantorBoundary => ‖J_raw (E := E) ψ x‖ ^ (2 : ℝ)) =
      (fun x : BinaryCantorBoundary => ‖ψ x‖ ^ (2 : ℝ)) := by
    ext x
    change ‖modular_j (E := E) (ψ x)‖ ^ (2 : ℝ) = ‖ψ x‖ ^ (2 : ℝ)
    rw [modular_j_norm]
  have hpowJ : ‖J_lp (E := E) ψ‖ ^ (2 : ℝ) =
      ∑' x : BinaryCantorBoundary, ‖J_lp (E := E) ψ x‖ ^ (2 : ℝ) := by
    simpa only [show (2 : ENNReal).toReal = (2 : ℝ) by rfl] using
      (lp.norm_rpow_eq_tsum hp (J_lp (E := E) ψ))
  have hpowψ : ‖ψ‖ ^ (2 : ℝ) =
      ∑' x : BinaryCantorBoundary, ‖ψ x‖ ^ (2 : ℝ) := by
    simpa only [show (2 : ENNReal).toReal = (2 : ℝ) by rfl] using
      (lp.norm_rpow_eq_tsum hp ψ)
  have hpow : ‖J_lp (E := E) ψ‖ ^ (2 : ℝ) = ‖ψ‖ ^ (2 : ℝ) := by
    rw [hpowJ, hpowψ]
    have htsum := congrArg (fun f : BinaryCantorBoundary → ℝ => ∑' x, f x) hpoint
    have hcoe : (fun x : BinaryCantorBoundary => ‖J_lp (E := E) ψ x‖ ^ (2 : ℝ)) =
        (fun x : BinaryCantorBoundary => ‖J_raw (E := E) ψ x‖ ^ (2 : ℝ)) := rfl
    rw [hcoe]
    exact htsum
  exact (Real.rpow_left_inj (lp.norm_nonneg' _) (lp.norm_nonneg' _) (by norm_num)).mp hpow

lemma J_lp_add (ψ φ : H_lp E) :
    J_lp (E := E) (ψ + φ) = J_lp (E := E) ψ + J_lp (E := E) φ := by
  apply Subtype.ext
  funext x
  change modular_j (E := E) ((ψ + φ) x) =
    modular_j (E := E) (ψ x) + modular_j (E := E) (φ x)
  rw [lp.coeFn_add]
  exact (modular_j (E := E)).map_add _ _

lemma J_lp_smul (a : ℝ) (ψ : H_lp E) :
    J_lp (E := E) (a • ψ) = a • J_lp (E := E) ψ := by
  apply Subtype.ext
  funext x
  change modular_j (E := E) ((a • ψ) x) = a • modular_j (E := E) (ψ x)
  rw [lp.coeFn_smul]
  exact (modular_j (E := E)).map_smul a _

/-- Underlying ℝ-linear map for the completed modular swap on `H_lp E`. -/
def J_lp_linear : H_lp E →ₗ[ℝ] H_lp E where
  toFun := J_lp (E := E)
  map_add' := J_lp_add (E := E)
  map_smul' := J_lp_smul (E := E)

/-- Continuous linear modular swap involution `J_lp_clm` on `H_lp E`. -/
def J_lp_clm : H_lp E →L[ℝ] H_lp E :=
  (J_lp_linear (E := E)).mkContinuous 1 (by
    intro ψ
    change ‖J_lp (E := E) ψ‖ ≤ 1 * ‖ψ‖
    rw [J_lp_norm_eq]
    simp)

@[simp] private theorem J_lp_clm_apply (ψ : H_lp E) (x : BinaryCantorBoundary) :
    J_lp_clm (E := E) ψ x = modular_j (E := E) (ψ x) :=
  rfl

theorem J_lp_clm_isometry :
    Isometry (J_lp_clm (E := E)) := by
  intro ψ φ
  have hnorm := J_lp_norm_eq (E := E) (ψ - φ)
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← map_sub]
  exact congrArg ENNReal.ofReal hnorm

theorem J_lp_clm_comp_self :
    (J_lp_clm (E := E)).comp (J_lp_clm (E := E)) =
      ContinuousLinearMap.id ℝ (H_lp E) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply Subtype.ext
  funext x
  change ((modular_j (E := E)).comp (modular_j (E := E))) (ψ x) = ψ x
  rw [modular_j_involution E]
  rfl

/-- Pointwise fundamental symmetry action on `BinaryCantorBoundary → DoubledSpace E`. -/
def epsilon_raw (ψ : BinaryCantorBoundary → DoubledSpace E) (x : BinaryCantorBoundary) :
    DoubledSpace E :=
  spectral_epsilon (E := E) (ψ x)

omit [CompleteSpace E] in
lemma summable_epsilon_raw (ψ : BinaryCantorBoundary → DoubledSpace E)
    (h : Summable fun x => ‖ψ x‖ ^ (2 : ℝ)) :
    Summable fun x => ‖epsilon_raw (E := E) ψ x‖ ^ (2 : ℝ) := by
  have h_eq : (fun x => ‖epsilon_raw (E := E) ψ x‖ ^ (2 : ℝ)) =
      (fun x => ‖ψ x‖ ^ (2 : ℝ)) := by
    ext x
    change ‖spectral_epsilon (E := E) (ψ x)‖ ^ (2 : ℝ) = ‖ψ x‖ ^ (2 : ℝ)
    rw [spectral_epsilon_norm]
  rw [h_eq]
  exact h

/-- The chiral fundamental symmetry operator `epsilon_lp` on `H_lp E`. -/
def epsilon_lp (ψ : H_lp E) : H_lp E :=
  ⟨epsilon_raw (E := E) ψ, by
    apply memℓp_gen
    have h1 : (2 : ENNReal).toReal = 2 := rfl
    rw [h1]
    have h2 : Memℓp ψ.1 2 := ψ.prop
    have h3 := (memℓp_gen_iff zero_lt_two).mp h2
    rw [h1] at h3
    exact summable_epsilon_raw (E := E) ψ h3⟩

lemma epsilon_lp_norm_eq (ψ : H_lp E) :
    ‖epsilon_lp (E := E) ψ‖ = ‖ψ‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hpoint : (fun x : BinaryCantorBoundary => ‖epsilon_raw (E := E) ψ x‖ ^ (2 : ℝ)) =
      (fun x : BinaryCantorBoundary => ‖ψ x‖ ^ (2 : ℝ)) := by
    ext x
    change ‖spectral_epsilon (E := E) (ψ x)‖ ^ (2 : ℝ) = ‖ψ x‖ ^ (2 : ℝ)
    rw [spectral_epsilon_norm]
  have hpowE : ‖epsilon_lp (E := E) ψ‖ ^ (2 : ℝ) =
      ∑' x : BinaryCantorBoundary, ‖epsilon_lp (E := E) ψ x‖ ^ (2 : ℝ) := by
    simpa only [show (2 : ENNReal).toReal = (2 : ℝ) by rfl] using
      (lp.norm_rpow_eq_tsum hp (epsilon_lp (E := E) ψ))
  have hpowψ : ‖ψ‖ ^ (2 : ℝ) =
      ∑' x : BinaryCantorBoundary, ‖ψ x‖ ^ (2 : ℝ) := by
    simpa only [show (2 : ENNReal).toReal = (2 : ℝ) by rfl] using
      (lp.norm_rpow_eq_tsum hp ψ)
  have hpow : ‖epsilon_lp (E := E) ψ‖ ^ (2 : ℝ) = ‖ψ‖ ^ (2 : ℝ) := by
    rw [hpowE, hpowψ]
    have htsum := congrArg (fun f : BinaryCantorBoundary → ℝ => ∑' x, f x) hpoint
    have hcoe : (fun x : BinaryCantorBoundary => ‖epsilon_lp (E := E) ψ x‖ ^ (2 : ℝ)) =
        (fun x : BinaryCantorBoundary => ‖epsilon_raw (E := E) ψ x‖ ^ (2 : ℝ)) := rfl
    rw [hcoe]
    exact htsum
  exact (Real.rpow_left_inj (lp.norm_nonneg' _) (lp.norm_nonneg' _) (by norm_num)).mp hpow

lemma epsilon_lp_add (ψ φ : H_lp E) :
    epsilon_lp (E := E) (ψ + φ) = epsilon_lp (E := E) ψ + epsilon_lp (E := E) φ := by
  apply Subtype.ext
  funext x
  change spectral_epsilon (E := E) ((ψ + φ) x) =
    spectral_epsilon (E := E) (ψ x) + spectral_epsilon (E := E) (φ x)
  rw [lp.coeFn_add]
  exact (spectral_epsilon (E := E)).map_add _ _

lemma epsilon_lp_smul (a : ℝ) (ψ : H_lp E) :
    epsilon_lp (E := E) (a • ψ) = a • epsilon_lp (E := E) ψ := by
  apply Subtype.ext
  funext x
  change spectral_epsilon (E := E) ((a • ψ) x) = a • spectral_epsilon (E := E) (ψ x)
  rw [lp.coeFn_smul]
  exact (spectral_epsilon (E := E)).map_smul a _

/-- Underlying ℝ-linear map for the chiral fundamental symmetry on `H_lp E`. -/
def epsilon_lp_linear : H_lp E →ₗ[ℝ] H_lp E where
  toFun := epsilon_lp (E := E)
  map_add' := epsilon_lp_add (E := E)
  map_smul' := epsilon_lp_smul (E := E)

/-- Continuous linear chiral involution `epsilon_lp_clm` on `H_lp E`. -/
def epsilon_lp_clm : H_lp E →L[ℝ] H_lp E :=
  (epsilon_lp_linear (E := E)).mkContinuous 1 (by
    intro ψ
    change ‖epsilon_lp (E := E) ψ‖ ≤ 1 * ‖ψ‖
    rw [epsilon_lp_norm_eq]
    simp)

@[simp] private theorem epsilon_lp_clm_apply (ψ : H_lp E) (x : BinaryCantorBoundary) :
    epsilon_lp_clm (E := E) ψ x = spectral_epsilon (E := E) (ψ x) :=
  rfl

theorem epsilon_lp_clm_isometry :
    Isometry (epsilon_lp_clm (E := E)) := by
  intro ψ φ
  have hnorm := epsilon_lp_norm_eq (E := E) (ψ - φ)
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← map_sub]
  exact congrArg ENNReal.ofReal hnorm

theorem epsilon_lp_clm_comp_self :
    (epsilon_lp_clm (E := E)).comp (epsilon_lp_clm (E := E)) =
      ContinuousLinearMap.id ℝ (H_lp E) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply Subtype.ext
  funext x
  change ((spectral_epsilon (E := E)).comp (spectral_epsilon (E := E))) (ψ x) = ψ x
  rw [spectral_epsilon_involution E]
  rfl

/-! ## 3. Infinite-Dimensional Clifford(1,1) / Sewing Algebra & Self-Adjointness -/

theorem J_lp_clm_comp_epsilon_lp_clm :
    (J_lp_clm (E := E)).comp (epsilon_lp_clm (E := E)) = K_lp_clm (E := E) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply Subtype.ext
  funext x
  change ((modular_j (E := E)).comp (spectral_epsilon (E := E))) (ψ x) =
    clockAxis (E := E) (ψ x)
  rfl

theorem J_lp_clm_anticomm_epsilon_lp_clm :
    (J_lp_clm (E := E)).comp (epsilon_lp_clm (E := E)) =
      -((epsilon_lp_clm (E := E)).comp (J_lp_clm (E := E))) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply Subtype.ext
  funext x
  have h := congrArg (fun T : DoubledSpace E →L[ℝ] DoubledSpace E => T (ψ x))
    (modular_j_spectral_epsilon_anticommute E)
  simpa [ContinuousLinearMap.comp_apply, J_lp_clm_apply, epsilon_lp_clm_apply] using h

theorem inner_J_lp_clm_selfAdjoint (ψ φ : H_lp E) :
    inner ℝ (J_lp_clm (E := E) ψ) φ = inner ℝ ψ (J_lp_clm (E := E) φ) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  exact tsum_congr fun x => inner_modular_j_selfAdjoint (E := E) (ψ x) (φ x)

/-! ## 4. Cuntz `O₂` Sewing Invariance & Operator Non-Commutativity on `H_lp` -/

theorem S_left_lp_clm_commutes_J_lp_clm :
    (S_left_lp_clm (E := E)).comp (J_lp_clm (E := E)) =
      (J_lp_clm (E := E)).comp (S_left_lp_clm (E := E)) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply Subtype.ext
  funext x
  change S_left_lp_clm (E := E) (J_lp_clm (E := E) ψ) x =
    modular_j (E := E) (S_left_lp_clm (E := E) ψ x)
  rw [S_left_lp_clm_apply, S_left_lp_clm_apply]
  split_ifs
  · rfl
  · exact (map_zero (modular_j (E := E))).symm

theorem S_right_lp_clm_commutes_J_lp_clm :
    (S_right_lp_clm (E := E)).comp (J_lp_clm (E := E)) =
      (J_lp_clm (E := E)).comp (S_right_lp_clm (E := E)) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply Subtype.ext
  funext x
  change S_right_lp_clm (E := E) (J_lp_clm (E := E) ψ) x =
    modular_j (E := E) (S_right_lp_clm (E := E) ψ x)
  rw [S_right_lp_clm_apply, S_right_lp_clm_apply]
  split_ifs
  · rfl
  · exact (map_zero (modular_j (E := E))).symm

theorem S_left_lp_clm_commutes_epsilon_lp_clm :
    (S_left_lp_clm (E := E)).comp (epsilon_lp_clm (E := E)) =
      (epsilon_lp_clm (E := E)).comp (S_left_lp_clm (E := E)) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply Subtype.ext
  funext x
  change S_left_lp_clm (E := E) (epsilon_lp_clm (E := E) ψ) x =
    spectral_epsilon (E := E) (S_left_lp_clm (E := E) ψ x)
  rw [S_left_lp_clm_apply, S_left_lp_clm_apply]
  split_ifs
  · rfl
  · exact (map_zero (spectral_epsilon (E := E))).symm

theorem S_right_lp_clm_commutes_epsilon_lp_clm :
    (S_right_lp_clm (E := E)).comp (epsilon_lp_clm (E := E)) =
      (epsilon_lp_clm (E := E)).comp (S_right_lp_clm (E := E)) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply Subtype.ext
  funext x
  change S_right_lp_clm (E := E) (epsilon_lp_clm (E := E) ψ) x =
    spectral_epsilon (E := E) (S_right_lp_clm (E := E) ψ x)
  rw [S_right_lp_clm_apply, S_right_lp_clm_apply]
  split_ifs
  · rfl
  · exact (map_zero (spectral_epsilon (E := E))).symm

theorem S_left_lp_clm_sewn_invariant :
    (J_lp_clm (E := E)).comp ((S_left_lp_clm (E := E)).comp (J_lp_clm (E := E))) =
      S_left_lp_clm (E := E) := by
  rw [S_left_lp_clm_commutes_J_lp_clm, ← ContinuousLinearMap.comp_assoc, J_lp_clm_comp_self]
  exact ContinuousLinearMap.id_comp _

theorem S_right_lp_clm_sewn_invariant :
    (J_lp_clm (E := E)).comp ((S_right_lp_clm (E := E)).comp (J_lp_clm (E := E))) =
      S_right_lp_clm (E := E) := by
  rw [S_right_lp_clm_commutes_J_lp_clm, ← ContinuousLinearMap.comp_assoc, J_lp_clm_comp_self]
  exact ContinuousLinearMap.id_comp _

/-- Canonical Cantor boundary word consisting uniformly of `+` sectors. -/
def basePlusWord : BinaryCantorBoundary := fun _ => BinarySector.plus

section ConcreteState
open Classical

/-- Canonical non-zero `J_lp_clm`-fixed Cantor boundary state `(δ_{+++...}) ⊗ (1, 1)`. -/
def canonicalCantorSewnState : H_lp ℝ :=
  lp.single (2 : ENNReal) basePlusWord (to_doubled (1 : ℝ) (1 : ℝ))

@[simp] private lemma canonicalCantorSewnState_apply_basePlusWord :
    canonicalCantorSewnState basePlusWord = to_doubled (1 : ℝ) (1 : ℝ) := by
  simp [canonicalCantorSewnState]

theorem canonicalCantorSewnState_ne_zero :
    canonicalCantorSewnState ≠ 0 := by
  intro hzero
  have h1 : canonicalCantorSewnState basePlusWord = (0 : H_lp ℝ) basePlusWord :=
    congrArg (fun f : H_lp ℝ => f basePlusWord) hzero
  have hfst := congrArg WithLp.fst h1
  rw [canonicalCantorSewnState_apply_basePlusWord, fst_to_doubled] at hfst
  norm_num at hfst

theorem canonicalCantorSewnState_fixed :
    J_lp_clm (E := ℝ) canonicalCantorSewnState = canonicalCantorSewnState := by
  apply Subtype.ext
  funext x
  rw [J_lp_clm_apply]
  by_cases hx : x = basePlusWord
  · subst hx
    rw [canonicalCantorSewnState_apply_basePlusWord, modular_j_to_doubled]
  · have hx0 : canonicalCantorSewnState x = 0 := by
      simp [canonicalCantorSewnState, hx]
    rw [hx0]
    exact map_zero (modular_j (E := ℝ))

end ConcreteState

/-- Non-commutativity witness on the completed Hilbert Cuntz `O₂` carrier: `S_left ∘ S_right ≠ S_right ∘ S_left`. -/
theorem S_left_right_lp_clm_noncomm :
    (S_left_lp_clm (E := ℝ)).comp (S_right_lp_clm (E := ℝ)) ≠
      (S_right_lp_clm (E := ℝ)).comp (S_left_lp_clm (E := ℝ)) := by
  intro heq
  let y : BinaryCantorBoundary :=
    prefixBoundary BinarySector.plus (prefixBoundary BinarySector.minus basePlusWord)
  have hy_eval :=
    congrArg (fun T : H_lp ℝ →L[ℝ] H_lp ℝ => T canonicalCantorSewnState y) heq
  have hhead_y : headBoundary y = BinarySector.plus := rfl
  have hhead_tail_y : headBoundary (tailBoundary y) = BinarySector.minus := rfl
  have htail_tail_y : tailBoundary (tailBoundary y) = basePlusWord := rfl
  have hL : ((S_left_lp_clm (E := ℝ)).comp (S_right_lp_clm (E := ℝ))) canonicalCantorSewnState y =
      to_doubled (1 : ℝ) (1 : ℝ) := by
    rw [ContinuousLinearMap.comp_apply, S_left_lp_clm_apply]
    simp [hhead_y, S_right_lp_clm_apply, hhead_tail_y, htail_tail_y]
  have hR : ((S_right_lp_clm (E := ℝ)).comp (S_left_lp_clm (E := ℝ))) canonicalCantorSewnState y =
      0 := by
    rw [ContinuousLinearMap.comp_apply, S_right_lp_clm_apply, hhead_y]
    simp
  rw [hL, hR] at hy_eval
  have hfst := congrArg WithLp.fst hy_eval
  rw [fst_to_doubled] at hfst
  norm_num at hfst

/-! ## 5. Infinite-Dimensional Boundary Anomaly Cancellation Theorems on `H_lp E` -/

/-- For every `J_lp_clm`-sewn bounded operator `B` and every vector `v : H_lp E`, the swap-paired
chiral expectation `⟪v, ε_lp (B v)⟫ + ⟪J_lp v, ε_lp (B (J_lp v))⟫` cancels identically. -/
theorem infinite_hilbert_paired_chiral_summand_zero
    (B : H_lp E →L[ℝ] H_lp E)
    (hB : (J_lp_clm (E := E)).comp (B.comp (J_lp_clm (E := E))) = B)
    (v : H_lp E) :
    inner ℝ v (((epsilon_lp_clm (E := E)).comp B) v) +
      inner ℝ (J_lp_clm (E := E) v) (((epsilon_lp_clm (E := E)).comp B) (J_lp_clm (E := E) v)) = 0 := by
  have h_second :
      inner ℝ (J_lp_clm (E := E) v) (((epsilon_lp_clm (E := E)).comp B) (J_lp_clm (E := E) v)) =
        -inner ℝ v (((epsilon_lp_clm (E := E)).comp B) v) := by
    calc
      inner ℝ (J_lp_clm (E := E) v) (((epsilon_lp_clm (E := E)).comp B) (J_lp_clm (E := E) v))
          = inner ℝ v ((J_lp_clm (E := E))
              ((epsilon_lp_clm (E := E)) (B (J_lp_clm (E := E) v)))) := by
              rw [ContinuousLinearMap.comp_apply, inner_J_lp_clm_selfAdjoint]
      _ = inner ℝ v (-((epsilon_lp_clm (E := E))
              ((J_lp_clm (E := E)) (B (J_lp_clm (E := E) v))))) := by
              have h :=
                congrArg (fun T : H_lp E →L[ℝ] H_lp E => T (B (J_lp_clm (E := E) v)))
                  (J_lp_clm_anticomm_epsilon_lp_clm (E := E))
              rw [ContinuousLinearMap.comp_apply, neg_apply,
                ContinuousLinearMap.comp_apply] at h
              rw [h]
      _ = -inner ℝ v ((epsilon_lp_clm (E := E))
            (((J_lp_clm (E := E)).comp (B.comp (J_lp_clm (E := E)))) v)) := by
              simp only [ContinuousLinearMap.comp_apply, inner_neg_right]
      _ = -inner ℝ v (((epsilon_lp_clm (E := E)).comp B) v) := by
              rw [hB, ContinuousLinearMap.comp_apply]
  linarith

/-- For every `J_lp_clm`-sewn bounded operator `B` on `H_lp E` and every `J_lp_clm`-fixed state `ψ`,
the chiral expectation `⟪ψ, ε_lp (B ψ)⟫` vanishes identically. -/
theorem infinite_hilbert_sewn_chiral_expectation_zero
    (B : H_lp E →L[ℝ] H_lp E)
    (hB : (J_lp_clm (E := E)).comp (B.comp (J_lp_clm (E := E))) = B)
    (ψ : H_lp E)
    (hψ : J_lp_clm (E := E) ψ = ψ) :
    inner ℝ ψ (((epsilon_lp_clm (E := E)).comp B) ψ) = 0 := by
  have hpair := infinite_hilbert_paired_chiral_summand_zero B hB ψ
  rw [hψ] at hpair
  linarith

/-- For any `J_lp_clm`-sewn bounded operator `B` and any `J_lp_clm`-paired family `(e i)_{i : ι}`
with summable chiral diagonal entries, the infinite-series chiral index vanishes:
`∑' i : ι, ⟪e i, ε_lp (B (e i))⟫ = 0`. -/
theorem infinite_hilbert_tsum_chiral_index_zero
    {ι : Type*} (σ : ι ≃ ι) (e : ι → H_lp E)
    (he : ∀ i, e (σ i) = J_lp_clm (E := E) (e i))
    (B : H_lp E →L[ℝ] H_lp E)
    (hB : (J_lp_clm (E := E)).comp (B.comp (J_lp_clm (E := E))) = B)
    (hsum : Summable (fun i : ι => inner ℝ (e i) (((epsilon_lp_clm (E := E)).comp B) (e i)))) :
    (∑' i : ι, inner ℝ (e i) (((epsilon_lp_clm (E := E)).comp B) (e i))) = 0 := by
  let f : ι → ℝ := fun i => inner ℝ (e i) (((epsilon_lp_clm (E := E)).comp B) (e i))
  have hf_pair : ∀ i : ι, f i + f (σ i) = 0 := by
    intro i
    dsimp [f]
    rw [he i]
    exact infinite_hilbert_paired_chiral_summand_zero B hB (e i)
  have hsum_σ : Summable (fun i : ι => f (σ i)) := (σ.summable_iff).mpr hsum
  have htsum_σ : (∑' i : ι, f (σ i)) = ∑' i : ι, f i := σ.tsum_eq f
  have hsum_double : (∑' i : ι, f i) + (∑' i : ι, f i) = 0 := by
    calc
      (∑' i : ι, f i) + (∑' i : ι, f i)
          = (∑' i : ι, f i) + (∑' i : ι, f (σ i)) := by rw [htsum_σ]
      _ = ∑' i : ι, (f i + f (σ i)) := (hsum.tsum_add hsum_σ).symm
      _ = ∑' _ : ι, (0 : ℝ) := tsum_congr hf_pair
      _ = 0 := tsum_zero
  change (∑' i : ι, f i) = 0
  linarith

/-- Concrete non-zero sewn Cantor vacuum chiral expectation vanishing on `H_lp ℝ` for any sewn `B`. -/
theorem canonicalCantorSewnState_chiral_zero
    (B : H_lp ℝ →L[ℝ] H_lp ℝ)
    (hB : (J_lp_clm (E := ℝ)).comp (B.comp (J_lp_clm (E := ℝ))) = B) :
    inner ℝ canonicalCantorSewnState (((epsilon_lp_clm (E := ℝ)).comp B) canonicalCantorSewnState) = 0 :=
  infinite_hilbert_sewn_chiral_expectation_zero B hB canonicalCantorSewnState canonicalCantorSewnState_fixed

end InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly

import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.FundamentalSymmetryProjectors
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped InnerProductSpace BigOperators

noncomputable section

namespace InfoGeometry.Krein.BornRuleCore

open KreinSpace
open FundamentalSymmetryProjectors

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]

theorem kreinInner_fundamentalSymmetry_right
    (u v : H) :
    kreinInner u ((KreinSpace.J : H ≃ₗᵢ[ℝ] H) v) = ⟪u, v⟫_ℝ := by
  rw [kreinInner_def]
  exact (KreinSpace.J : H ≃ₗᵢ[ℝ] H).inner_map_map u v

theorem kreinInner_fundamentalSymmetry_left
    (u v : H) :
    kreinInner ((KreinSpace.J : H ≃ₗᵢ[ℝ] H) u) v = ⟪u, v⟫_ℝ := by
  rw [kreinInner_def, KreinSpace.J_invol]

def kreinAdaptedAmplitude (final initial : H) : ℝ :=
  kreinInner final ((KreinSpace.J : H ≃ₗᵢ[ℝ] H) initial)

theorem kreinAdaptedAmplitude_eq_inner
    (final initial : H) :
    kreinAdaptedAmplitude final initial = ⟪final, initial⟫_ℝ :=
  kreinInner_fundamentalSymmetry_right final initial

def kreinAdaptedProbability (final initial : H) : ℝ :=
  |kreinAdaptedAmplitude final initial| ^ 2 /
    (‖final‖ ^ 2 * ‖initial‖ ^ 2)

theorem kreinAdaptedProbability_nonnegative
    (final initial : H) :
    0 ≤ kreinAdaptedProbability final initial := by
  apply div_nonneg
  · exact sq_nonneg _
  · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem amplitude_sq_le_norm_sq_mul_norm_sq
    (final initial : H) :
    |kreinAdaptedAmplitude final initial| ^ 2 ≤
      ‖final‖ ^ 2 * ‖initial‖ ^ 2 := by
  rw [kreinAdaptedAmplitude_eq_inner]
  have h := abs_real_inner_le_norm final initial
  have hf : 0 ≤ ‖final‖ := norm_nonneg final
  have hi : 0 ≤ ‖initial‖ := norm_nonneg initial
  have ha : 0 ≤ |⟪final, initial⟫_ℝ| := abs_nonneg _
  nlinarith

theorem kreinAdaptedProbability_le_one
    (final initial : H)
    (hfinal : final ≠ 0)
    (hinitial : initial ≠ 0) :
    kreinAdaptedProbability final initial ≤ 1 := by
  rw [kreinAdaptedProbability, div_le_one]
  · exact amplitude_sq_le_norm_sq_mul_norm_sq final initial
  · positivity

theorem kreinAdaptedProbability_mem_unitInterval
    (final initial : H)
    (hfinal : final ≠ 0)
    (hinitial : initial ≠ 0) :
    kreinAdaptedProbability final initial ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨kreinAdaptedProbability_nonnegative final initial,
    kreinAdaptedProbability_le_one final initial hfinal hinitial⟩

theorem sum_kreinAdaptedProbability_orthonormalBasis
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ H)
    (initial : H)
    (hinitial : ‖initial‖ = 1) :
    ∑ i, kreinAdaptedProbability (b i) initial = 1 := by
  have hb (i : ι) : ‖b i‖ = 1 :=
    b.orthonormal.1 i
  have hparseval :=
    b.sum_inner_mul_inner initial initial
  simp_rw [kreinAdaptedProbability, kreinAdaptedAmplitude_eq_inner, hb, hinitial]
  simp only [one_pow, one_mul, div_one]
  rw [real_inner_self_eq_norm_sq, hinitial, one_pow] at hparseval
  calc
    ∑ i, |⟪b i, initial⟫_ℝ| ^ 2 =
        ∑ i, ⟪initial, b i⟫_ℝ * ⟪b i, initial⟫_ℝ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [real_inner_comm initial (b i)]
          rw [sq_abs, pow_two]
    _ = 1 := hparseval

def physicalProjector : H →ₗ[ℝ] H :=
  K_plus (1 / 2 : ℝ) (KreinSpace.jCLM (H := H)).toLinearMap

def ghostProjector : H →ₗ[ℝ] H :=
  K_minus (1 / 2 : ℝ) (KreinSpace.jCLM (H := H)).toLinearMap

theorem physicalProjector_add_ghostProjector
    (u : H) :
    physicalProjector u + ghostProjector u = u := by
  exact K_plus_add_K_minus
    (KreinSpace.jCLM (H := H)).toLinearMap
    (1 / 2 : ℝ) (by norm_num) u

theorem fundamentalSymmetry_physicalProjector
    (u : H) :
    KreinSpace.jCLM (physicalProjector u) = physicalProjector u := by
  exact J_K_plus
    (KreinSpace.jCLM (H := H)).toLinearMap
    (by
      exact LinearMap.ext fun x =>
        congrArg (fun T : H →L[ℝ] H => T x)
          (KreinSpace.jCLM_comp_self (H := H)))
    (1 / 2 : ℝ) u

theorem fundamentalSymmetry_ghostProjector
    (u : H) :
    KreinSpace.jCLM (ghostProjector u) = -ghostProjector u := by
  exact J_K_minus
    (KreinSpace.jCLM (H := H)).toLinearMap
    (by
      exact LinearMap.ext fun x =>
        congrArg (fun T : H →L[ℝ] H => T x)
          (KreinSpace.jCLM_comp_self (H := H)))
    (1 / 2 : ℝ) u

theorem physicalProjector_idempotent
    (u : H) :
    physicalProjector (physicalProjector u) = physicalProjector u := by
  exact K_plus_idempotent
    (KreinSpace.jCLM (H := H)).toLinearMap
    (by
      exact LinearMap.ext fun x =>
        congrArg (fun T : H →L[ℝ] H => T x)
          (KreinSpace.jCLM_comp_self (H := H)))
    (1 / 2 : ℝ) (by norm_num) u

theorem ghostProjector_idempotent
    (u : H) :
    ghostProjector (ghostProjector u) = ghostProjector u := by
  exact K_minus_idempotent
    (KreinSpace.jCLM (H := H)).toLinearMap
    (by
      exact LinearMap.ext fun x =>
        congrArg (fun T : H →L[ℝ] H => T x)
          (KreinSpace.jCLM_comp_self (H := H)))
    (1 / 2 : ℝ) (by norm_num) u

theorem physicalProjector_comp_ghostProjector
    (u : H) :
    physicalProjector (ghostProjector u) = 0 := by
  rw [physicalProjector, K_plus_apply]
  change (1 / 2 : ℝ) •
    (ghostProjector u + KreinSpace.jCLM (ghostProjector u)) = 0
  rw [fundamentalSymmetry_ghostProjector]
  simp

theorem ghostProjector_comp_physicalProjector
    (u : H) :
    ghostProjector (physicalProjector u) = 0 := by
  rw [ghostProjector, K_minus_apply]
  change (1 / 2 : ℝ) •
    (physicalProjector u - KreinSpace.jCLM (physicalProjector u)) = 0
  rw [fundamentalSymmetry_physicalProjector]
  simp

theorem inner_physicalProjector_ghostProjector
    (u v : H) :
    ⟪physicalProjector u, ghostProjector v⟫_ℝ = 0 := by
  have hselfAdj :=
    KreinSpace.J_selfAdj (physicalProjector u) (ghostProjector v)
  change
    ⟪KreinSpace.jCLM (physicalProjector u), ghostProjector v⟫_ℝ =
      ⟪physicalProjector u, KreinSpace.jCLM (ghostProjector v)⟫_ℝ
    at hselfAdj
  rw [fundamentalSymmetry_physicalProjector,
    fundamentalSymmetry_ghostProjector, inner_neg_right] at hselfAdj
  linarith

theorem kreinInner_physicalProjector_ghostProjector
    (u v : H) :
    kreinInner (physicalProjector u) (ghostProjector v) = 0 := by
  rw [kreinInner_def]
  change
    ⟪KreinSpace.jCLM (physicalProjector u), ghostProjector v⟫_ℝ = 0
  rw [fundamentalSymmetry_physicalProjector]
  exact inner_physicalProjector_ghostProjector u v

theorem physicalGhostDecomposition_unique
    (u physical ghost : H)
    (hu : u = physical + ghost)
    (hphysical : KreinSpace.jCLM physical = physical)
    (hghost : KreinSpace.jCLM ghost = -ghost) :
    physicalProjector u = physical ∧ ghostProjector u = ghost := by
  subst u
  constructor
  · rw [map_add, physicalProjector, K_plus_apply, K_plus_apply]
    change
      (1 / 2 : ℝ) • (physical + KreinSpace.jCLM physical) +
          (1 / 2 : ℝ) • (ghost + KreinSpace.jCLM ghost) =
        physical
    rw [hphysical, hghost]
    module
  · rw [map_add, ghostProjector, K_minus_apply, K_minus_apply]
    change
      (1 / 2 : ℝ) • (physical - KreinSpace.jCLM physical) +
          (1 / 2 : ℝ) • (ghost - KreinSpace.jCLM ghost) =
        ghost
    rw [hphysical, hghost]
    module

theorem kreinInner_physicalProjector_self
    (u : H) :
    kreinInner (physicalProjector u) (physicalProjector u) =
      ‖physicalProjector u‖ ^ 2 := by
  rw [kreinInner_def]
  change ⟪KreinSpace.jCLM (physicalProjector u), physicalProjector u⟫_ℝ =
    ‖physicalProjector u‖ ^ 2
  rw [fundamentalSymmetry_physicalProjector]
  exact real_inner_self_eq_norm_sq _

theorem kreinInner_ghostProjector_self
    (u : H) :
    kreinInner (ghostProjector u) (ghostProjector u) =
      -(‖ghostProjector u‖ ^ 2) := by
  rw [kreinInner_def]
  change ⟪KreinSpace.jCLM (ghostProjector u), ghostProjector u⟫_ℝ =
    -(‖ghostProjector u‖ ^ 2)
  rw [fundamentalSymmetry_ghostProjector, inner_neg_left,
    real_inner_self_eq_norm_sq]

theorem kreinInner_physicalProjector_nonnegative
    (u : H) :
    0 ≤ kreinInner (physicalProjector u) (physicalProjector u) := by
  rw [kreinInner_physicalProjector_self]
  positivity

theorem kreinInner_ghostProjector_nonpositive
    (u : H) :
    kreinInner (ghostProjector u) (ghostProjector u) ≤ 0 := by
  rw [kreinInner_ghostProjector_self]
  exact neg_nonpos.mpr (sq_nonneg _)

theorem abs_kreinInner_physicalProjector_self
    (u : H) :
    |kreinInner (physicalProjector u) (physicalProjector u)| =
      ‖physicalProjector u‖ ^ 2 := by
  rw [kreinInner_physicalProjector_self, abs_of_nonneg (sq_nonneg _)]

theorem abs_kreinInner_ghostProjector_self
    (u : H) :
    |kreinInner (ghostProjector u) (ghostProjector u)| =
      ‖ghostProjector u‖ ^ 2 := by
  rw [kreinInner_ghostProjector_self, abs_neg, abs_of_nonneg (sq_nonneg _)]

theorem indefinite_normalization_agrees_on_physical_sector
    (final initial : H) :
    |kreinInner (physicalProjector final) (physicalProjector final)| *
        |kreinInner (physicalProjector initial) (physicalProjector initial)| =
      ‖physicalProjector final‖ ^ 2 * ‖physicalProjector initial‖ ^ 2 := by
  rw [abs_kreinInner_physicalProjector_self,
    abs_kreinInner_physicalProjector_self]

theorem indefinite_normalization_agrees_on_ghost_sector
    (final initial : H) :
    |kreinInner (ghostProjector final) (ghostProjector final)| *
        |kreinInner (ghostProjector initial) (ghostProjector initial)| =
      ‖ghostProjector final‖ ^ 2 * ‖ghostProjector initial‖ ^ 2 := by
  rw [abs_kreinInner_ghostProjector_self,
    abs_kreinInner_ghostProjector_self]

theorem doubled_diagonal_isotropic
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : E) :
    KreinSpace.kreinInner
        (WithLp.toLp 2 (x, x))
        (WithLp.toLp 2 (x, x)) = 0 := by
  rw [InfoGeometry.Krein.krein_inner_prod_l2]
  simp

theorem doubled_diagonal_nonzero
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {x : E}
    (hx : x ≠ 0) :
    WithLp.toLp 2 (x, x) ≠ 0 := by
  intro h
  have hpair := congrArg (WithLp.ofLp (p := (2 : ENNReal))) h
  simp only [WithLp.ofLp_zero] at hpair
  exact hx (congrArg Prod.fst hpair)

theorem exists_nonzero_krein_null_vector
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : E)
    (hx : x ≠ 0) :
    ∃ u : WithLp 2 (E × E),
      u ≠ 0 ∧ KreinSpace.kreinInner u u = 0 :=
  ⟨WithLp.toLp 2 (x, x), doubled_diagonal_nonzero hx,
    doubled_diagonal_isotropic x⟩

theorem krein_isometry_preserves_indefinite_norm
    (U : H →L[ℝ] H)
    (hU : IsKreinIsometry U)
    (u : H) :
    kreinInner (U u) (U u) = kreinInner u u :=
  hU u u

theorem pseudo_unitarity_iff_krein_isometry
    (U : H →L[ℝ] H) :
    IsKreinIsometry U ↔
      (kreinAdjoint U).comp U = ContinuousLinearMap.id ℝ H :=
  isKreinIsometry_iff_star_comp_self U

theorem kreinIsometry_commutes_fundamentalSymmetry_preserves_inner
    (U : H →L[ℝ] H)
    (hU : IsKreinIsometry U)
    (hcomm :
      U.comp (KreinSpace.jCLM (H := H)) =
        (KreinSpace.jCLM (H := H)).comp U)
    (u v : H) :
    ⟪U u, U v⟫_ℝ = ⟪u, v⟫_ℝ := by
  rw [← kreinInner_fundamentalSymmetry_right]
  rw [← kreinInner_fundamentalSymmetry_right]
  have hcomm_apply :=
    congrArg (fun T : H →L[ℝ] H => T v) hcomm
  simp only [ContinuousLinearMap.comp_apply] at hcomm_apply
  change
    kreinInner (U u) (KreinSpace.jCLM (U v)) =
      kreinInner u (KreinSpace.jCLM v)
  rw [← hcomm_apply]
  exact hU u (KreinSpace.jCLM v)

theorem pseudoUnitary_commutes_fundamentalSymmetry_preserves_inner
    (U : H →L[ℝ] H)
    (hpseudo :
      (kreinAdjoint U).comp U = ContinuousLinearMap.id ℝ H)
    (hcomm :
      U.comp (KreinSpace.jCLM (H := H)) =
        (KreinSpace.jCLM (H := H)).comp U)
    (u v : H) :
    ⟪U u, U v⟫_ℝ = ⟪u, v⟫_ℝ := by
  apply kreinIsometry_commutes_fundamentalSymmetry_preserves_inner U
  · exact (pseudo_unitarity_iff_krein_isometry U).mpr hpseudo
  · exact hcomm

theorem kreinIsometry_commutes_fundamentalSymmetry_preserves_norm
    (U : H →L[ℝ] H)
    (hU : IsKreinIsometry U)
    (hcomm :
      U.comp (KreinSpace.jCLM (H := H)) =
        (KreinSpace.jCLM (H := H)).comp U)
    (u : H) :
    ‖U u‖ = ‖u‖ := by
  have hinner :=
    kreinIsometry_commutes_fundamentalSymmetry_preserves_inner
      U hU hcomm u u
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
  nlinarith [norm_nonneg (U u), norm_nonneg u]

theorem kreinIsometry_commutes_fundamentalSymmetry_preserves_amplitude
    (U : H →L[ℝ] H)
    (hU : IsKreinIsometry U)
    (hcomm :
      U.comp (KreinSpace.jCLM (H := H)) =
        (KreinSpace.jCLM (H := H)).comp U)
    (final initial : H) :
    kreinAdaptedAmplitude (U final) (U initial) =
      kreinAdaptedAmplitude final initial := by
  rw [kreinAdaptedAmplitude_eq_inner, kreinAdaptedAmplitude_eq_inner]
  exact kreinIsometry_commutes_fundamentalSymmetry_preserves_inner
    U hU hcomm final initial

theorem kreinIsometry_commutes_fundamentalSymmetry_preserves_probability
    (U : H →L[ℝ] H)
    (hU : IsKreinIsometry U)
    (hcomm :
      U.comp (KreinSpace.jCLM (H := H)) =
        (KreinSpace.jCLM (H := H)).comp U)
    (final initial : H) :
    kreinAdaptedProbability (U final) (U initial) =
      kreinAdaptedProbability final initial := by
  rw [kreinAdaptedProbability, kreinAdaptedProbability]
  rw [kreinIsometry_commutes_fundamentalSymmetry_preserves_amplitude
    U hU hcomm]
  rw [kreinIsometry_commutes_fundamentalSymmetry_preserves_norm
    U hU hcomm]
  rw [kreinIsometry_commutes_fundamentalSymmetry_preserves_norm
    U hU hcomm]

end InfoGeometry.Krein.BornRuleCore

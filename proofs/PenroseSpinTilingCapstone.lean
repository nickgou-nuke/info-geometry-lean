import proofs.PenroseSpinTilingConfig
import proofs.PenroseSpinIncidenceTessellation
import proofs.NonIsoConf3QuadricD4PointCount
import proofs.KleinErlangenGrothendieckBridge
import proofs.NonIsoConf3DupontGysinModel
import proofs.NonIsoConf3ThreePointDeRhamCooperad
import proofs.NonIsoConf3DeRhamCooperad
import proofs.NonIsoConf3LiteratureLemmaChain
import proofs.NonIsoConf3RankDecision
import proofs.OakuTakayamaDModuleDeRham

/-!
# Penrose spin tiling capstone

This is the canonical finite-spine entry point for the Penrose/incidence layer.
It composes the proved finite facts available to the Lean kernel.

The old rank-`32` product signature is retained as a legacy reduced
bookkeeping theorem.  The corrected visible `D=4` quadric candidate is anchored
through `NonIsoConf3QuadricD4Model.candidateRank`.
-/

noncomputable section

namespace PenroseSpinTilingCapstone

open PenroseSpinTilingConfig
open PenroseSpinIncidenceTessellation
open NonIsoConf3QuadricD4Model
open NonIsoConf3QuadricD4PointCount
open KleinErlangenGrothendieckBridge
open TKKJordanPairData.Legacy
open NonIsoConf3DupontGysinModel
open NonIsoConf3ThreePointDeRhamCooperad
open NonIsoConf3DeRhamCooperad
open NonIsoConf3LiteratureLemmaChain
open NonIsoConf3RankDecision
open OakuTakayamaDModuleDeRham

/-- The finite facts currently compiled by the Lean kernel for this layer. -/
structure FiniteSpineFacts where
  sixLocalGenerators : Fintype.card SpinTileGenerator = 6
  legacyReducedRank32 : Fintype.card Config3PoincareSignature = 32
  correctedD4DegreeTwoRank : candidateRank 2 = 2
  correctedD4TopSupportCutoff : candidateRank 12 = 0
  f3PointCountFingerprint : countPolynomial 3 = 1296
  kleinLine01 : OnKleinQuadric line01
  kleinLine23 : OnKleinQuadric line23
  kleinMixedLine : OnKleinQuadric mixedLine
  tkkConformalPairingGrade : gradeAdd TKKGrade.m1 TKKGrade.p1 = some TKKGrade.z0
  dupontStrataEight : Fintype.card StratumMask = 8
  dupontGysinCoversTwelve : Fintype.card GysinCover = 12
  threePointD4Colimit : three_point_non_iso_colimit_target
  productLerayRank32 : Fintype.card ProductBasis = 32
  osAlphaRank24 : Fintype.card OSFluxBasis = 24
  productOsRankGap : Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8
  incidenceSynthesis :
    Fintype.card SpinTileGenerator = 6 ∧
    (∀ e : Edge3, genDegree (edgeToAlpha e) = 1) ∧
    (∀ e : Edge3, genDegree (edgeToBeta e) = 3) ∧
    NonIsoConf3QuadricD4Model.vadd (NonIsoConf3QuadricD4Model.vsub (reduceAlphaProduct AlphaProduct.a12a23) (reduceAlphaProduct AlphaProduct.a12a13))
          (reduceAlphaProduct AlphaProduct.a23a13) = 0 ∧
    candidateRank 2 = 2 ∧
    countPolynomial 3 = 1296

/-- The finite spine assembles the compiled facts for this layer. -/
def finiteSpineFacts : FiniteSpineFacts where
  sixLocalGenerators := spinTileGenerator_card
  legacyReducedRank32 := config3_signature_total_rank
  correctedD4DegreeTwoRank := rfl
  correctedD4TopSupportCutoff := rfl
  f3PointCountFingerprint := countPolynomial_at_three
  kleinLine01 := klein_line01
  kleinLine23 := klein_line23
  kleinMixedLine := klein_mixedLine
  tkkConformalPairingGrade := tkk_conformal_pairing_grade
  dupontStrataEight := stratumMask_card
  dupontGysinCoversTwelve := gysinCover_card
  threePointD4Colimit := three_point_non_iso_D4_inductive_colimit
  productLerayRank32 := productBasis_card
  osAlphaRank24 := osFluxBasis_card
  productOsRankGap := product_vs_os_rank_gap
  incidenceSynthesis := penrose_spin_incidence_tessellation_synthesis

/-- The finite portion of the capstone. -/
theorem finite_spine_kernel_core :
    Fintype.card SpinTileGenerator = 6 ∧
    Fintype.card Config3PoincareSignature = 32 ∧
    candidateRank 2 = 2 ∧
    candidateRank 12 = 0 ∧
    countPolynomial 3 = 1296 ∧
    OnKleinQuadric line01 ∧
    OnKleinQuadric line23 ∧
    OnKleinQuadric mixedLine ∧
    gradeAdd TKKGrade.m1 TKKGrade.p1 = some TKKGrade.z0 ∧
    Fintype.card StratumMask = 8 ∧
    Fintype.card GysinCover = 12 ∧
    three_point_non_iso_colimit_target ∧
    Fintype.card ProductBasis = 32 ∧
    Fintype.card OSFluxBasis = 24 ∧
    Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 := by
  refine And.intro finiteSpineFacts.sixLocalGenerators ?_
  refine And.intro finiteSpineFacts.legacyReducedRank32 ?_
  refine And.intro finiteSpineFacts.correctedD4DegreeTwoRank ?_
  refine And.intro finiteSpineFacts.correctedD4TopSupportCutoff ?_
  refine And.intro finiteSpineFacts.f3PointCountFingerprint ?_
  refine And.intro finiteSpineFacts.kleinLine01 ?_
  refine And.intro finiteSpineFacts.kleinLine23 ?_
  refine And.intro finiteSpineFacts.kleinMixedLine ?_
  refine And.intro finiteSpineFacts.tkkConformalPairingGrade ?_
  refine And.intro finiteSpineFacts.dupontStrataEight ?_
  refine And.intro finiteSpineFacts.dupontGysinCoversTwelve ?_
  refine And.intro finiteSpineFacts.threePointD4Colimit ?_
  refine And.intro finiteSpineFacts.productLerayRank32 ?_
  refine And.intro finiteSpineFacts.osAlphaRank24 ?_
  exact finiteSpineFacts.productOsRankGap

/-- Capstone theorem: the proved finite combinatorics and arithmetic
fingerprints packaged together. -/
theorem finite_spine_unification :
    Fintype.card SpinTileGenerator = 6 ∧
    Fintype.card Config3PoincareSignature = 32 ∧
    candidateRank 2 = 2 ∧
    candidateRank 12 = 0 ∧
    countPolynomial 3 = 1296 ∧
    OnKleinQuadric line01 ∧
    OnKleinQuadric line23 ∧
    OnKleinQuadric mixedLine ∧
    gradeAdd TKKGrade.m1 TKKGrade.p1 = some TKKGrade.z0 ∧
    Fintype.card StratumMask = 8 ∧
    Fintype.card GysinCover = 12 ∧
    three_point_non_iso_colimit_target ∧
    Fintype.card ProductBasis = 32 ∧
    Fintype.card OSFluxBasis = 24 ∧
    Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 := by
  simpa using finite_spine_kernel_core

/-- 1. Incidence-card skeleton at stage 0. -/
def penroseTileIncidenceCard : Prop :=
  Fintype.card SpinTileGenerator = 6

/-- 2. Edge-degree skeleton at stage 1. -/
def penroseTileDegreeSkeleton : Prop :=
  (∀ e : Edge3, genDegree (edgeToAlpha e) = 1) ∧
    (∀ e : Edge3, genDegree (edgeToBeta e) = 3)

/-- 3. Corrected finite-rank skeleton at stage 2. -/
def penroseTileCandidateSkeleton : Prop :=
  candidateRank 2 = 2 ∧ candidateRank 12 = 0

/-- 4. Arithmetic fingerprint skeleton at stage 3. -/
def penroseTilePointCountSkeleton : Prop :=
  countPolynomial 3 = 1296

/-- 5. Residual geometric/Klein and Dupont-card skeleton at stage 4. -/
def penroseTileGeometrySkeleton : Prop :=
  Fintype.card Config3PoincareSignature = 32 ∧
    OnKleinQuadric line01 ∧
    OnKleinQuadric line23 ∧
    OnKleinQuadric mixedLine ∧
    gradeAdd TKKGrade.m1 TKKGrade.p1 = some TKKGrade.z0 ∧
    Fintype.card StratumMask = 8 ∧
    Fintype.card GysinCover = 12 ∧
    three_point_non_iso_colimit_target ∧
    Fintype.card ProductBasis = 32 ∧
    Fintype.card OSFluxBasis = 24 ∧
    Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8

/-- Inductive finite-colimit style assembly for the capstone spine. -/
inductive PenroseSpinFiniteColimit : ℕ → Prop where
  | stage0 : penroseTileIncidenceCard → PenroseSpinFiniteColimit 0
  | stage1 : PenroseSpinFiniteColimit 0 → penroseTileDegreeSkeleton → PenroseSpinFiniteColimit 1
  | stage2 : PenroseSpinFiniteColimit 1 → penroseTileCandidateSkeleton → PenroseSpinFiniteColimit 2
  | stage3 : PenroseSpinFiniteColimit 2 → penroseTilePointCountSkeleton → PenroseSpinFiniteColimit 3
  | stage4 : PenroseSpinFiniteColimit 3 → penroseTileGeometrySkeleton → PenroseSpinFiniteColimit 4

/-- Final target of the finite colimit tower. -/
def penrose_spin_tiling_colimit_target : Prop :=
  PenroseSpinFiniteColimit 4

/-- Inductive colimit theorem for the finite capstone data. -/
theorem penrose_spin_tiling_inductive_colimit :
    penrose_spin_tiling_colimit_target := by
  refine PenroseSpinFiniteColimit.stage4
    (PenroseSpinFiniteColimit.stage3
      (PenroseSpinFiniteColimit.stage2
        (PenroseSpinFiniteColimit.stage1
          (PenroseSpinFiniteColimit.stage0 finiteSpineFacts.sixLocalGenerators)
          ⟨edgeToAlpha_degree, edgeToBeta_degree⟩)
        ⟨finiteSpineFacts.correctedD4DegreeTwoRank,
          finiteSpineFacts.correctedD4TopSupportCutoff⟩)
      finiteSpineFacts.f3PointCountFingerprint)
    ⟨finiteSpineFacts.legacyReducedRank32,
      finiteSpineFacts.kleinLine01,
      finiteSpineFacts.kleinLine23,
      finiteSpineFacts.kleinMixedLine,
      finiteSpineFacts.tkkConformalPairingGrade,
      finiteSpineFacts.dupontStrataEight,
      finiteSpineFacts.dupontGysinCoversTwelve,
      finiteSpineFacts.threePointD4Colimit,
      finiteSpineFacts.productLerayRank32,
      finiteSpineFacts.osAlphaRank24,
      finiteSpineFacts.productOsRankGap⟩

/-- Recover kernel finite data from the finite-colimit target. -/
theorem finite_spine_kernel_from_colimit_target
    (hcol : penrose_spin_tiling_colimit_target) :
    Fintype.card SpinTileGenerator = 6 ∧
      Fintype.card Config3PoincareSignature = 32 ∧
      candidateRank 2 = 2 ∧
      candidateRank 12 = 0 ∧
      countPolynomial 3 = 1296 ∧
      OnKleinQuadric line01 ∧
      OnKleinQuadric line23 ∧
      OnKleinQuadric mixedLine ∧
      gradeAdd TKKGrade.m1 TKKGrade.p1 = some TKKGrade.z0 ∧
      Fintype.card StratumMask = 8 ∧
      Fintype.card GysinCover = 12 ∧
      three_point_non_iso_colimit_target ∧
      Fintype.card ProductBasis = 32 ∧
      Fintype.card OSFluxBasis = 24 ∧
      Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 := by
  change PenroseSpinFiniteColimit 4 at hcol
  cases hcol with
  | stage4 h3 hgeo =>
    cases h3 with
    | stage3 h2 hpc =>
      cases h2 with
      | stage2 h1 hcan =>
        cases h1 with
        | stage1 h0 _hdeg =>
          cases h0 with
          | stage0 hcard =>
            rcases hcan with ⟨hr2, hr12⟩
            rcases hgeo with
              ⟨h32, h01, h23, hmixed, htkk, hstr, hgcov, h3col, hprod, hos, hgap⟩
            refine And.intro ?_ ?_
            · simpa only using hcard
            refine And.intro ?_ ?_
            · simpa only using h32
            refine And.intro ?_ ?_
            · simpa only using hr2
            refine And.intro ?_ ?_
            · simpa only using hr12
            refine And.intro ?_ ?_
            · simpa only using hpc
            refine And.intro ?_ ?_
            · simpa only using h01
            refine And.intro ?_ ?_
            · simpa only using h23
            refine And.intro ?_ ?_
            · simpa only using hmixed
            refine And.intro ?_ ?_
            · simpa only using htkk
            refine And.intro ?_ ?_
            · simpa only using hstr
            refine And.intro ?_ ?_
            · simpa only using hgcov
            refine And.intro ?_ ?_
            · simpa only using h3col
            refine And.intro ?_ ?_
            · simpa only using hprod
            refine And.intro ?_ ?_
            · simpa only using hos
            · simpa only using hgap

/-- Finite unification can be factored through the finite-colimit target. -/
theorem finite_spine_unification_from_colimit_target
    (hcol : penrose_spin_tiling_colimit_target) :
    Fintype.card SpinTileGenerator = 6 ∧
      Fintype.card Config3PoincareSignature = 32 ∧
      candidateRank 2 = 2 ∧
      candidateRank 12 = 0 ∧
      countPolynomial 3 = 1296 ∧
      OnKleinQuadric line01 ∧
      OnKleinQuadric line23 ∧
      OnKleinQuadric mixedLine ∧
      gradeAdd TKKGrade.m1 TKKGrade.p1 = some TKKGrade.z0 ∧
      Fintype.card StratumMask = 8 ∧
      Fintype.card GysinCover = 12 ∧
      three_point_non_iso_colimit_target ∧
      Fintype.card ProductBasis = 32 ∧
      Fintype.card OSFluxBasis = 24 ∧
      Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 := by
  simpa using finite_spine_kernel_from_colimit_target hcol

/-
theorem finite_spine_unification_iff_inductive_colimit
    :
    (Fintype.card SpinTileGenerator = 6 ∧
      Fintype.card Config3PoincareSignature = 32 ∧
      candidateRank 2 = 2 ∧
      candidateRank 12 = 0 ∧
      countPolynomial 3 = 1296 ∧
      OnKleinQuadric line01 ∧
      OnKleinQuadric line23 ∧
      OnKleinQuadric mixedLine ∧
      gradeAdd TKKGrade.m1 TKKGrade.p1 = some TKKGrade.z0 ∧
      Fintype.card StratumMask = 8 ∧
      Fintype.card GysinCover = 12 ∧
      three_point_non_iso_colimit_target ∧
      Fintype.card ProductBasis = 32 ∧
      Fintype.card OSFluxBasis = 24 ∧
      Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8) ↔
      penrose_spin_tiling_colimit_target := by
  refine Iff.intro ?_ ?_
  · intro _hUni
    exact penrose_spin_tiling_inductive_colimit
  · intro hcol
    simpa using finite_spine_unification_from_colimit_target hcol
-/

/-
theorem finite_spine_unification_refines_inductive_colimit
    (_hUni : Fintype.card SpinTileGenerator = 6 ∧
      Fintype.card Config3PoincareSignature = 32 ∧
      candidateRank 2 = 2 ∧
      candidateRank 12 = 0 ∧
      countPolynomial 3 = 1296 ∧
      OnKleinQuadric line01 ∧
      OnKleinQuadric line23 ∧
      OnKleinQuadric mixedLine ∧
      gradeAdd TKKGrade.m1 TKKGrade.p1 = some TKKGrade.z0 ∧
      Fintype.card StratumMask = 8 ∧
      Fintype.card GysinCover = 12 ∧
      three_point_non_iso_colimit_target ∧
      Fintype.card ProductBasis = 32 ∧
      Fintype.card OSFluxBasis = 24 ∧
      Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8) :
    penrose_spin_tiling_colimit_target := by
  exact penrose_spin_tiling_inductive_colimit
-/

end PenroseSpinTilingCapstone

end noncomputable section

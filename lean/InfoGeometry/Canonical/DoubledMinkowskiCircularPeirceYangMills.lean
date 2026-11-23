/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.RealDoubledChiralKreinFrame
import InfoGeometry.Canonical.ThermofieldWittSoldering
import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
import InfoGeometry.Lie.SplitOctonionEllDoubledKreinFrameBridge
import InfoGeometry.Lie.SplitOctonionCircularWittForm
import InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge
import InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge
import InfoGeometry.OperatorAlgebra.TetraktysZornYangMillsBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
import InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge
import InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
import InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
import InfoGeometry.Canonical.BogomolnyiAlgebraicBoundBridge
import InfoGeometry.Canonical.TwoSheetedYangMillsInductiveColimit
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Typed Bridge: Doubled Minkowski–Krein Carrier, Circular Split-Octonion Chiral Frames, and Two-Sheeted Yang–Mills

## i. Overview

This module constructs explicit maps and kernel-checked compatibility results
connecting the separate repository owners on their actual Lean types.  It links
the circular split-octonion Peirce carrier `CanonicalZorn`, the Ell Krein
eigenbasis frame `ellCircularToDoubledFrame` on `KreinFrame4`, two chiral
Pauli-Weyl and bispinor representations, a two-sheeted non-Abelian gauge-Higgs
connection with a helicity-split self-dual Yang-Mills solution, and inductive
star-ring colimit transport.

*Scope boundary*: All results here are finite-dimensional, algebraic,
exterior-algebraic, or star-ring colimit identities.  The frame comparison on
`KreinFrame4` is strictly linear/bilinear data and does not identify
split-octonion multiplication with associative operator composition on
`KreinFrame4` or `M_8(ℝ)`.  No smooth 4-manifold PDE existence, analytic
lattice spacing `a → 0` limit, or continuum Wightman mass gap is claimed or
proved.

## ii. Key results

1. **Doubled Minkowski–Krein Carrier & Metric (`@[rep_depth krein]`)**:
   - Maps `CanonicalZorn` (`SplitOctonionEllCircularPeirceBasis`) to `KreinFrame4`
     (`RealDoubledChiralKreinFrame`) via `circularZornToKreinFrame` (transporting the 8 circular
     Peirce vectors onto `plusFrame` / `minusFrame`, intertwining `kappa` with `sheetFlip`, and
     intertwining `uPlus * X - uMinus * X` with `chirality`) and the `(1,3)` parity-twisted
     equivalence `lorentzCircularZornToKreinFrame` (pulling back `chiralKreinForm` to
     `circularPeircePolar` and `2 * wittNorm`).
   - Compares `ellCircularToDoubledFrame ∘ coordinateEquiv` against `circularZornToKreinFrame`
     on the circular Peirce frame (`ellCircularToDoubledFrame_comp_coordinateEquiv_frame`).
   - Instantiates `dualConnectionWithMetric` at `minkowskiEta13 = diag(1, -1, -1, -1)`.

2. **Two Chiral Weyl Representations on `KreinFrame4` & Circular Peirce Channels (`@[rep_depth krein]`)**:
   - Defines `kreinChiralPlusWeyl` and `kreinChiralMinusWeyl` directly on `KreinFrame4`, proves
     intertwining with `sheetFlip`, `chirality`, and `doubleMinkowskiSolder`, and embeds them into
     `SheetAlgebra (Fin 2 → ℂ)` (`kreinSheetRep`) and `Matrix (Fin 4) (Fin 4) ℂ`
     (`kreinBispinorRep`).
   - Pulls back along `lorentzCircularZornToKreinFrame` to `circularSheetRep` and
     `circularBispinorRep`, proving genuine split-octonion Peirce selection (`uPlus`, `uMinus`)
     matches `conePlus`/`coneMinus` and mapping all 8 circular Peirce vectors to Pauli blocks.
   - Proves the `KreinFrame4` trace-metric pullback
     `Tr(kreinBispinorRep u * kreinBispinorRep v) = 2 * chiralKreinForm u v` together with a
     concrete noncommutativity witness.

3. **Gauge–Higgs Connection, Self-Dual Yang–Mills Equations, & Bogomolnyi Identity (`@[rep_depth transport]`)**:
   - Defines `twoSheetKreinConnection` in `SheetAlgebra (Fin 2 → ℂ)` coupling noncommuting
     diagonal potentials `(AL, AR)` with `kreinSheetRep u` and decomposes `D * D` under
     `Γ = invS (firstSheetProjection _)`.
   - Builds `blade2Coeff` and the 4D chiral Hodge star `chiralHodgeStar4` from
     `ExteriorContractionOperatorBridge.contractionOp` on `ExteriorAlgebra ℂ (Fin 4 → ℂ)`, exhibits
     an unconditional helicity-split self-dual non-Abelian solution
     (`F ≠ 0`, `F 0 0 ≠ F 2 2`, `★_χ F = F`, `D_A (★_χ F) = 0`), and establishes the
     two-sheeted Bogomolnyi action identity in `BogomolnyiAlgebraicBoundBridge`.

4. **Inductive Star-Ring Colimit Transport & Unified Synthesis (`@[rep_depth transport, capstone]`)**:
   - Transports `kreinBispinorRep` across arbitrary `StarRingHom`s and
     `CanonicalTwoSheetedInductiveColimit.tailTowerCone`.

## iii. Table of contents

1. Layer 1: Doubled Minkowski-Krein carrier, metric pullback, and dual spin connection
2. Layer 2: Two chiral Weyl representations on `KreinFrame4` and circular Peirce channels
3. Layer 3: Two-sheeted gauge-Higgs connection, self-dual Yang-Mills, and Bogomolnyi identity
4. Layer 4: Inductive star-ring colimit transport and unified synthesis

## iv. References

- `InfoGeometry.Canonical.RealDoubledChiralKreinFrame`
- `InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis`
- `InfoGeometry.Lie.SplitOctonionEllDoubledKreinFrameBridge`
- `InfoGeometry.Canonical.BogomolnyiAlgebraicBoundBridge`
-/

noncomputable section

namespace InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills

open scoped ComplexConjugate
open Matrix
open ExteriorAlgebra
open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements
open InfoGeometry.Canonical.RealDoubledChiralKreinFrame
open InfoGeometry.Canonical.ThermofieldWittSoldering
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionCircularWittForm
open InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge
open InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge
open InfoGeometry.Quantum.PauliSoldering
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.TetraktysZornYangMillsBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
open InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
open InfoGeometry.Canonical.BogomolnyiAlgebraicBoundBridge
open CanonicalTwoSheetedInductiveColimit

private lemma forall_fin2 {P : Fin 2 → Prop} (h0 : P 0) (h1 : P 1) : ∀ i, P i := by
  intro i; fin_cases i; exact h0; exact h1

private lemma forall_fin4 {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) :
    ∀ i, P i := by
  intro i; fin_cases i; exact h0; exact h1; exact h2; exact h3

private lemma forall_fin8 {P : Fin 8 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) : ∀ i, P i := by
  intro i; fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

/-! ## Layer 1: Doubled Minkowski–Krein Carrier, Metric Pullback, & Dual Spin Connection -/

/-- Linear equivalence from the 8D split-octonion circular Peirce carrier
`CanonicalZorn` onto the real doubled chiral Krein frame `KreinFrame4`. -/
@[rep_depth krein]
def circularZornToKreinFrame : CanonicalZorn ≃ₗ[ℝ] KreinFrame4 :=
  coordinateEquiv.trans wittSolderingEquiv.symm

/-- Applying `wittSoldering` recovers the circular Peirce coordinates from
`circularZornToKreinFrame`. -/
@[rep_depth krein]
lemma wittSoldering_circularZornToKreinFrame (X : CanonicalZorn) :
    wittSoldering (circularZornToKreinFrame X) = coordinateEquiv X := by
  change wittSolderingEquiv (wittSolderingEquiv.symm (coordinateEquiv X)) = coordinateEquiv X
  exact wittSolderingEquiv.apply_symm_apply (coordinateEquiv X)

private lemma frameBasis_apply (i j : Fin 4) :
    frameBasis i j = if i = j then (1 : ℝ) else 0 := by
  dsimp [frameBasis]
  rw [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  by_cases hij : i = j <;> simp [hij, eq_comm]

/-- Positive circular Peirce basis vectors `frame 0..3` map onto `plusFrame 0..3`,
and negative circular Peirce basis vectors `frame 4..7` map onto `minusFrame 0..3`. -/
@[rep_depth krein]
lemma circularZornToKreinFrame_frame_blocks (i : Fin 4) :
    circularZornToKreinFrame (frame (Fin.castAdd 4 i)) = plusFrame i ∧
    circularZornToKreinFrame (frame (Fin.addNat i 4)) = minusFrame i := by
  constructor
  · apply wittSoldering_injective
    rw [wittSoldering_circularZornToKreinFrame, coordinateEquiv_apply_frame]
    ext k
    fin_cases i <;> fin_cases k <;>
      simp [plusFrame, wittSoldering_to_doubled_apply, frameBasis_apply]
  · apply wittSoldering_injective
    rw [wittSoldering_circularZornToKreinFrame, coordinateEquiv_apply_frame]
    ext k
    fin_cases i <;> fin_cases k <;>
      simp [minusFrame, wittSoldering_to_doubled_apply, frameBasis_apply]

/-- Comparing the Ell Krein eigenbasis frame map `ellCircularToDoubledFrame ∘ coordinateEquiv`
against the null circular Peirce soldering `circularZornToKreinFrame` on `frame 0..7`:
positive-sector vectors yield half-sums and negative-sector vectors yield signed
half-differences. -/
@[rep_depth krein]
lemma ellCircularToDoubledFrame_comp_coordinateEquiv_frame (i : Fin 4) :
    InfoGeometry.Lie.SplitOctonionEllDoubledKreinFrameBridge.ellCircularToDoubledFrame
        (coordinateEquiv (frame (Fin.castAdd 4 i))) =
      (1 / 2 : ℝ) • (circularZornToKreinFrame (frame (Fin.castAdd 4 i)) +
        circularZornToKreinFrame (frame (Fin.addNat i 4))) ∧
    InfoGeometry.Lie.SplitOctonionEllDoubledKreinFrameBridge.ellCircularToDoubledFrame
        (coordinateEquiv (frame (Fin.addNat i 4))) =
      (InfoGeometry.Lie.SplitOctonionEllCircularKreinOperatorBridge.ellKreinPairSign i / 2) •
        (circularZornToKreinFrame (frame (Fin.castAdd 4 i)) -
          circularZornToKreinFrame (frame (Fin.addNat i 4))) := by
  have hblocks := circularZornToKreinFrame_frame_blocks i
  constructor
  · rw [coordinateEquiv_apply_frame]
    change
      InfoGeometry.Lie.SplitOctonionEllDoubledKreinFrameBridge.ellCircularToDoubledFrame
          (Pi.single
            (InfoGeometry.Lie.SplitOctonionEllCircularKreinOperatorBridge.ellKreinPairIndex i)
            (1 : ℝ)) =
        (1 / 2 : ℝ) • (circularZornToKreinFrame (frame (Fin.castAdd 4 i)) +
          circularZornToKreinFrame (frame (Fin.addNat i 4)))
    rw [Lie.SplitOctonionEllDoubledKreinFrameBridge.ellCircularToDoubledFrame_pair_coordinate,
      hblocks.1, hblocks.2]
  · rw [coordinateEquiv_apply_frame]
    change
      InfoGeometry.Lie.SplitOctonionEllDoubledKreinFrameBridge.ellCircularToDoubledFrame
          (Pi.single
            (InfoGeometry.Lie.SplitOctonionEllCircularKreinOperatorBridge.ellKreinOppositeIndex i)
            (1 : ℝ)) =
        (InfoGeometry.Lie.SplitOctonionEllCircularKreinOperatorBridge.ellKreinPairSign i / 2) •
          (circularZornToKreinFrame (frame (Fin.castAdd 4 i)) -
            circularZornToKreinFrame (frame (Fin.addNat i 4)))
    rw [Lie.SplitOctonionEllDoubledKreinFrameBridge.ellCircularToDoubledFrame_opposite_coordinate,
      hblocks.1, hblocks.2]

/-- The circular sector swap `kappa` intertwines with `sheetFlip` on `KreinFrame4`. -/
@[rep_depth krein]
lemma circularZornToKreinFrame_intertwines_kappa_sheetFlip (X : CanonicalZorn) :
    circularZornToKreinFrame (coordinateEquiv.symm (kappa (coordinateEquiv X))) =
      sheetFlip (circularZornToKreinFrame X) := by
  apply wittSoldering_injective
  have h1 : wittSoldering (circularZornToKreinFrame (coordinateEquiv.symm (kappa (coordinateEquiv X)))) =
      kappa (coordinateEquiv X) := by
    rw [wittSoldering_circularZornToKreinFrame, coordinateEquiv.apply_symm_apply]
  have h2 : wittSoldering (sheetFlip (circularZornToKreinFrame X)) =
      wittSwap (wittSoldering (circularZornToKreinFrame X)) := by
    change wittSoldering (modular_j (E := FourSpace) (circularZornToKreinFrame X)) = _
    exact wittSoldering_intertwines_modular_j (circularZornToKreinFrame X)
  rw [h1, h2, wittSoldering_circularZornToKreinFrame]
  ext i
  fin_cases i <;> rfl

/-- Split-octonion left Peirce grading `uPlus * X - uMinus * X` intertwines
with `chirality` on `KreinFrame4`. -/
@[rep_depth krein]
lemma circularZornToKreinFrame_intertwines_peirce_chirality (X : CanonicalZorn) :
    circularZornToKreinFrame (uPlus * X - uMinus * X) =
      chirality (circularZornToKreinFrame X) := by
  have hBasis : ∀ i : Fin 8,
      circularZornToKreinFrame (uPlus * frame i - uMinus * frame i) =
        chirality (circularZornToKreinFrame (frame i)) := by
    apply forall_fin8
    · rw [show uPlus * frame 0 = frame 0 from uPlus_mul_frame 0,
        show uMinus * frame 0 = 0 from uMinus_mul_frame 0, sub_zero]
      change circularZornToKreinFrame (frame (Fin.castAdd 4 0)) =
        chirality (circularZornToKreinFrame (frame (Fin.castAdd 4 0)))
      rw [(circularZornToKreinFrame_frame_blocks 0).1, chirality_plusFrame]
    · rw [show uPlus * frame 1 = frame 1 from uPlus_mul_frame 1,
        show uMinus * frame 1 = 0 from uMinus_mul_frame 1, sub_zero]
      change circularZornToKreinFrame (frame (Fin.castAdd 4 1)) =
        chirality (circularZornToKreinFrame (frame (Fin.castAdd 4 1)))
      rw [(circularZornToKreinFrame_frame_blocks 1).1, chirality_plusFrame]
    · rw [show uPlus * frame 2 = frame 2 from uPlus_mul_frame 2,
        show uMinus * frame 2 = 0 from uMinus_mul_frame 2, sub_zero]
      change circularZornToKreinFrame (frame (Fin.castAdd 4 2)) =
        chirality (circularZornToKreinFrame (frame (Fin.castAdd 4 2)))
      rw [(circularZornToKreinFrame_frame_blocks 2).1, chirality_plusFrame]
    · rw [show uPlus * frame 3 = frame 3 from uPlus_mul_frame 3,
        show uMinus * frame 3 = 0 from uMinus_mul_frame 3, sub_zero]
      change circularZornToKreinFrame (frame (Fin.castAdd 4 3)) =
        chirality (circularZornToKreinFrame (frame (Fin.castAdd 4 3)))
      rw [(circularZornToKreinFrame_frame_blocks 3).1, chirality_plusFrame]
    · rw [show uPlus * frame 4 = 0 from uPlus_mul_frame 4,
        show uMinus * frame 4 = frame 4 from uMinus_mul_frame 4, zero_sub, map_neg]
      change -circularZornToKreinFrame (frame (Fin.addNat 0 4)) =
        chirality (circularZornToKreinFrame (frame (Fin.addNat 0 4)))
      rw [(circularZornToKreinFrame_frame_blocks 0).2, chirality_minusFrame]
    · rw [show uPlus * frame 5 = 0 from uPlus_mul_frame 5,
        show uMinus * frame 5 = frame 5 from uMinus_mul_frame 5, zero_sub, map_neg]
      change -circularZornToKreinFrame (frame (Fin.addNat 1 4)) =
        chirality (circularZornToKreinFrame (frame (Fin.addNat 1 4)))
      rw [(circularZornToKreinFrame_frame_blocks 1).2, chirality_minusFrame]
    · rw [show uPlus * frame 6 = 0 from uPlus_mul_frame 6,
        show uMinus * frame 6 = frame 6 from uMinus_mul_frame 6, zero_sub, map_neg]
      change -circularZornToKreinFrame (frame (Fin.addNat 2 4)) =
        chirality (circularZornToKreinFrame (frame (Fin.addNat 2 4)))
      rw [(circularZornToKreinFrame_frame_blocks 2).2, chirality_minusFrame]
    · rw [show uPlus * frame 7 = 0 from uPlus_mul_frame 7,
        show uMinus * frame 7 = frame 7 from uMinus_mul_frame 7, zero_sub, map_neg]
      change -circularZornToKreinFrame (frame (Fin.addNat 3 4)) =
        chirality (circularZornToKreinFrame (frame (Fin.addNat 3 4)))
      rw [(circularZornToKreinFrame_frame_blocks 3).2, chirality_minusFrame]
  let L : CanonicalZorn →ₗ[ℝ] KreinFrame4 :=
    circularZornToKreinFrame.toLinearMap.comp
      (leftMultiplication uPlus - leftMultiplication uMinus)
  let R : CanonicalZorn →ₗ[ℝ] KreinFrame4 :=
    chirality.toLinearMap.comp circularZornToKreinFrame.toLinearMap
  have hEq : L = R := by
    apply circularPeirceBasis.ext
    intro i
    change circularZornToKreinFrame (uPlus * circularPeirceBasis i - uMinus * circularPeirceBasis i) =
      chirality (circularZornToKreinFrame (circularPeirceBasis i))
    rw [circularPeirceBasis_apply]
    exact hBasis i
  exact LinearMap.congr_fun hEq X

/-- Spatial parity reflection `diag(1, -1, -1, -1)` on `FourSpace`. -/
@[rep_depth krein]
def lorentzSheetParity : FourSpace ≃ₗ[ℝ] FourSpace where
  toFun x := WithLp.toLp 2 ![x 0, -x 1, -x 2, -x 3]
  invFun x := WithLp.toLp 2 ![x 0, -x 1, -x 2, -x 3]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' r x := by ext i; fin_cases i <;> simp

private lemma lorentzSheetParity_zero (x : FourSpace) : lorentzSheetParity x 0 = x 0 := rfl
private lemma lorentzSheetParity_one (x : FourSpace) : lorentzSheetParity x 1 = -(x 1) := rfl
private lemma lorentzSheetParity_two (x : FourSpace) : lorentzSheetParity x 2 = -(x 2) := rfl
private lemma lorentzSheetParity_three (x : FourSpace) : lorentzSheetParity x 3 = -(x 3) := rfl

private def lorentzTwistKrein : KreinFrame4 ≃ₗ[ℝ] KreinFrame4 where
  toFun u := to_doubled (WithLp.fst u) (lorentzSheetParity (WithLp.snd u))
  invFun v := to_doubled (WithLp.fst v) (lorentzSheetParity.symm (WithLp.snd v))
  left_inv u := by
    apply DoubledSpace.ext
    · rfl
    · simp [lorentzSheetParity.symm_apply_apply]
  right_inv v := by
    apply DoubledSpace.ext
    · rfl
    · simp [lorentzSheetParity.apply_symm_apply]
  map_add' u v := by
    apply DoubledSpace.ext
    · rfl
    · change lorentzSheetParity (WithLp.snd u + WithLp.snd v) =
        lorentzSheetParity (WithLp.snd u) + lorentzSheetParity (WithLp.snd v)
      exact lorentzSheetParity.map_add _ _
  map_smul' r u := by
    apply DoubledSpace.ext
    · rfl
    · change lorentzSheetParity (r • WithLp.snd u) = r • lorentzSheetParity (WithLp.snd u)
      exact lorentzSheetParity.map_smul _ _

/-- Parity-twisted Krein equivalence sending the negative circular sector through
`lorentzSheetParity` so that `chiralKreinForm` pulls back identically to `circularPeircePolar`. -/
@[rep_depth krein]
def lorentzCircularZornToKreinFrame : CanonicalZorn ≃ₗ[ℝ] KreinFrame4 :=
  circularZornToKreinFrame.trans lorentzTwistKrein

private lemma fst_circularZornToKreinFrame (A : CanonicalZorn) (i : Fin 4) :
    WithLp.fst (circularZornToKreinFrame A) i = coordinateEquiv A ⟨i.val, by omega⟩ := by
  have hi := congrFun (wittSoldering_circularZornToKreinFrame A) ⟨i.val, by omega⟩
  simpa [wittSoldering, i.isLt] using hi

private lemma snd_circularZornToKreinFrame (A : CanonicalZorn) (i : Fin 4) :
    WithLp.snd (circularZornToKreinFrame A) i = coordinateEquiv A ⟨i.val + 4, by omega⟩ := by
  have hi := congrFun (wittSoldering_circularZornToKreinFrame A) ⟨i.val + 4, by omega⟩
  have hge : ¬ (i.val + 4 < 4) := by omega
  simpa [wittSoldering, hge] using hi

private lemma fst_circ_0 (A : CanonicalZorn) : WithLp.fst (circularZornToKreinFrame A) 0 = coordinateEquiv A 0 :=
  fst_circularZornToKreinFrame A 0
private lemma fst_circ_1 (A : CanonicalZorn) : WithLp.fst (circularZornToKreinFrame A) 1 = coordinateEquiv A 1 :=
  fst_circularZornToKreinFrame A 1
private lemma fst_circ_2 (A : CanonicalZorn) : WithLp.fst (circularZornToKreinFrame A) 2 = coordinateEquiv A 2 :=
  fst_circularZornToKreinFrame A 2
private lemma fst_circ_3 (A : CanonicalZorn) : WithLp.fst (circularZornToKreinFrame A) 3 = coordinateEquiv A 3 :=
  fst_circularZornToKreinFrame A 3
private lemma snd_circ_0 (A : CanonicalZorn) : WithLp.snd (circularZornToKreinFrame A) 0 = coordinateEquiv A 4 :=
  snd_circularZornToKreinFrame A 0
private lemma snd_circ_1 (A : CanonicalZorn) : WithLp.snd (circularZornToKreinFrame A) 1 = coordinateEquiv A 5 :=
  snd_circularZornToKreinFrame A 1
private lemma snd_circ_2 (A : CanonicalZorn) : WithLp.snd (circularZornToKreinFrame A) 2 = coordinateEquiv A 6 :=
  snd_circularZornToKreinFrame A 2
private lemma snd_circ_3 (A : CanonicalZorn) : WithLp.snd (circularZornToKreinFrame A) 3 = coordinateEquiv A 7 :=
  snd_circularZornToKreinFrame A 3

/-- Exact bilinear and quadratic metric pullback: `chiralKreinForm` along
`lorentzCircularZornToKreinFrame` equals `circularPeircePolar` and `2 * wittNorm`. -/
@[rep_depth krein]
lemma chiralKreinForm_lorentzCircularZornToKreinFrame (X Y : CanonicalZorn) :
    chiralKreinForm (E := FourSpace)
        (lorentzCircularZornToKreinFrame X)
        (lorentzCircularZornToKreinFrame Y) =
      circularPeircePolar (coordinateEquiv X) (coordinateEquiv Y) ∧
    chiralKreinForm (E := FourSpace)
        (lorentzCircularZornToKreinFrame X)
        (lorentzCircularZornToKreinFrame X) =
      2 * wittNorm (coordinateEquiv X) := by
  have hPair : ∀ A B : CanonicalZorn,
      chiralKreinForm (E := FourSpace)
          (lorentzCircularZornToKreinFrame A)
          (lorentzCircularZornToKreinFrame B) =
        circularPeircePolar (coordinateEquiv A) (coordinateEquiv B) := by
    intro A B
    dsimp [lorentzCircularZornToKreinFrame, lorentzTwistKrein]
    rw [chiralKreinForm_to_doubled, PiLp.inner_apply, PiLp.inner_apply,
      Fin.sum_univ_four, Fin.sum_univ_four]
    simp only [RCLike.inner_apply, conj_trivial,
      lorentzSheetParity_zero, lorentzSheetParity_one,
      lorentzSheetParity_two, lorentzSheetParity_three,
      fst_circ_0, fst_circ_1, fst_circ_2, fst_circ_3,
      snd_circ_0, snd_circ_1, snd_circ_2, snd_circ_3]
    simp only [circularPeircePolar]
    ring
  refine ⟨hPair X Y, ?_⟩
  rw [hPair X X]
  simp [circularPeircePolar, wittNorm]
  ring

/-- Diagonal `(1, 3)` Lorentz metric matrix `diag(1, -1, -1, -1)` on `Fin 4`. -/
@[rep_depth krein]
def minkowskiEta13 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, -1, -1, -1]

/-- Determinant, unit invertibility, induced Krein graph metric, and unique
metric-compatible dual spin connection for `minkowskiEta13`. -/
@[rep_depth krein]
lemma minkowskiEta13_metric_and_dualConnection
    (omegaPlus omegaMinus : Matrix (Fin 4) (Fin 4) ℝ) :
    minkowskiEta13.det = -1 ∧
    IsUnit minkowskiEta13.det ∧
    (∀ i j : Fin 4,
      chiralKreinForm (E := FourSpace) (graphSection minkowskiEta13 i) (graphSection minkowskiEta13 j) =
        2 * minkowskiEta13 i j) ∧
    omegaPlus.transpose * minkowskiEta13 +
      minkowskiEta13 * dualConnectionWithMetric minkowskiEta13 omegaPlus = 0 ∧
    (omegaPlus.transpose * minkowskiEta13 + minkowskiEta13 * omegaMinus = 0 →
      omegaMinus = dualConnectionWithMetric minkowskiEta13 omegaPlus) := by
  have hDet : minkowskiEta13.det = -1 := by
    simp [minkowskiEta13, Matrix.det_diagonal, Fin.prod_univ_four]
  have hUnit : IsUnit minkowskiEta13.det := by
    rw [hDet]
    exact isUnit_neg_one
  refine ⟨hDet, hUnit, ?_, dualConnectionWithMetric_compatibility minkowskiEta13 omegaPlus hUnit, ?_⟩
  · intro i j
    rw [graphSection_metric]
    have hSymm : minkowskiEta13 j i = minkowskiEta13 i j := by
      fin_cases i <;> fin_cases j <;> simp [minkowskiEta13]
    rw [hSymm]
    ring
  · intro hCompat
    exact dualConnectionWithMetric_unique minkowskiEta13 omegaPlus omegaMinus hUnit hCompat

/-- Explicit non-commutativity witness on the `Matrix (Fin 4) (Fin 4) ℝ` carrier. -/
@[rep_depth krein]
lemma minkowskiEta13_mat4R_noncomm :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A := by
  refine ⟨minkowskiEta13, !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0], ?_⟩
  intro hEq
  have h01 := congrFun (congrFun hEq 0) 1
  simp [minkowskiEta13, Matrix.mul_apply, Fin.sum_univ_four] at h01
  norm_num at h01

/-! ## Layer 2: Two Chiral Weyl Representations on `KreinFrame4` & Circular Peirce Channels -/

/-- Plus-sheet chiral `2 × 2` Pauli-Weyl representation defined directly on `KreinFrame4`. -/
@[rep_depth krein]
def kreinChiralPlusWeyl : KreinFrame4 →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun u :=
    let x := fst_L (E := FourSpace) u
    pauliSolder2x2 (x 0) (x 1) (x 2) (x 3)
  map_add' u v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliSolder2x2, solder_explicit, map_add, PiLp.add_apply] <;> ring
  map_smul' r u := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliSolder2x2, solder_explicit, map_smul, PiLp.smul_apply, smul_eq_mul] <;> ring

/-- Minus-sheet chiral `2 × 2` Pauli-Weyl representation defined directly on `KreinFrame4`. -/
@[rep_depth krein]
def kreinChiralMinusWeyl : KreinFrame4 →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun u :=
    let y := snd_L (E := FourSpace) u
    pauliSolder2x2 (y 0) (y 1) (y 2) (y 3)
  map_add' u v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliSolder2x2, solder_explicit, map_add, PiLp.add_apply] <;> ring
  map_smul' r u := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliSolder2x2, solder_explicit, map_smul, PiLp.smul_apply, smul_eq_mul] <;> ring

private lemma kreinChiralPlusWeyl_apply (u : KreinFrame4) :
    kreinChiralPlusWeyl u =
      pauliSolder2x2 (WithLp.fst u 0) (WithLp.fst u 1) (WithLp.fst u 2) (WithLp.fst u 3) :=
  rfl

private lemma kreinChiralMinusWeyl_apply (u : KreinFrame4) :
    kreinChiralMinusWeyl u =
      pauliSolder2x2 (WithLp.snd u 0) (WithLp.snd u 1) (WithLp.snd u 2) (WithLp.snd u 3) :=
  rfl

private lemma snd_chirality (u : KreinFrame4) :
    WithLp.snd (chirality u) = -(WithLp.snd u) :=
  rfl

/-- The two Weyl representations on `KreinFrame4` intertwine with `sheetFlip` and
`chirality`, and match `doubleMinkowskiSolder` and its determinant norm difference. -/
@[rep_depth krein]
lemma kreinChiralWeyl_chirality_and_sheetFlip (u : KreinFrame4)
    (t x1 x2 x3 tau y1 y2 y3 : ℝ) :
    let uSolder : KreinFrame4 :=
      to_doubled (WithLp.toLp 2 ![t, x1, x2, x3]) (WithLp.toLp 2 ![tau, y1, y2, y3])
    kreinChiralPlusWeyl (sheetFlip u) = kreinChiralMinusWeyl u ∧
    kreinChiralMinusWeyl (sheetFlip u) = kreinChiralPlusWeyl u ∧
    kreinChiralPlusWeyl (chirality u) = kreinChiralPlusWeyl u ∧
    kreinChiralMinusWeyl (chirality u) = -kreinChiralMinusWeyl u ∧
    Matrix.fromBlocks (kreinChiralPlusWeyl uSolder) 0 0 (kreinChiralMinusWeyl uSolder) =
      doubleMinkowskiSolder t x1 x2 x3 tau y1 y2 y3 ∧
    (kreinChiralPlusWeyl uSolder).det - (kreinChiralMinusWeyl uSolder).det =
      (wittNorm (symmSection t x1 x2 x3 + antiSection tau y1 y2 y3) : ℂ) := by
  intro uSolder
  refine ⟨rfl, rfl, rfl, ?_, rfl, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kreinChiralMinusWeyl_apply, snd_chirality, pauliSolder2x2, solder_explicit] <;> ring
  · exact doubleMinkowskiSolder_det_diff t x1 x2 x3 tau y1 y2 y3

private def sheetFromBlocksLinear :
    (Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ) →ₗ[ℝ] SheetAlgebra (Fin 2 → ℂ) where
  toFun p := !![0, Matrix.toLin' p.1; Matrix.toLin' p.2, 0]
  map_add' a b := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [map_add]
  map_smul' r a := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · simp
    · ext v k; simp [Matrix.toLin'_apply, Complex.real_smul]
    · ext v k; simp [Matrix.toLin'_apply, Complex.real_smul]
    · simp

private def bispinorFromBlocksLinear :
    (Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ) →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℂ where
  toFun p :=
    !![0, 0, p.1 0 0, p.1 0 1;
       0, 0, p.1 1 0, p.1 1 1;
       p.2 0 0, p.2 0 1, 0, 0;
       p.2 1 0, p.2 1 1, 0, 0]
  map_add' a b := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' r a := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Complex.real_smul]

/-- Off-diagonal chiral representation of `KreinFrame4` in
`TetraktysZornYangMillsBridge.SheetAlgebra (Fin 2 → ℂ)`. -/
@[rep_depth krein]
def kreinSheetRep : KreinFrame4 →ₗ[ℝ] SheetAlgebra (Fin 2 → ℂ) :=
  sheetFromBlocksLinear.comp (kreinChiralPlusWeyl.prod kreinChiralMinusWeyl)

/-- Explicit `4 × 4` block bispinor matrix representation of `KreinFrame4`. -/
@[rep_depth krein]
def kreinBispinorRep : KreinFrame4 →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℂ :=
  bispinorFromBlocksLinear.comp (kreinChiralPlusWeyl.prod kreinChiralMinusWeyl)

private lemma kreinSheetRep_apply (u : KreinFrame4) :
    kreinSheetRep u = !![0, Matrix.toLin' (kreinChiralPlusWeyl u);
      Matrix.toLin' (kreinChiralMinusWeyl u), 0] :=
  rfl

private lemma kreinBispinorRep_apply (u : KreinFrame4) :
    kreinBispinorRep u =
      !![0, 0, kreinChiralPlusWeyl u 0 0, kreinChiralPlusWeyl u 0 1;
         0, 0, kreinChiralPlusWeyl u 1 0, kreinChiralPlusWeyl u 1 1;
         kreinChiralMinusWeyl u 0 0, kreinChiralMinusWeyl u 0 1, 0, 0;
         kreinChiralMinusWeyl u 1 0, kreinChiralMinusWeyl u 1 1, 0, 0] :=
  rfl

/-- Pullback of `kreinSheetRep` along `lorentzCircularZornToKreinFrame` onto `CanonicalZorn`. -/
@[rep_depth krein]
def circularSheetRep : CanonicalZorn →ₗ[ℝ] SheetAlgebra (Fin 2 → ℂ) :=
  kreinSheetRep.comp lorentzCircularZornToKreinFrame.toLinearMap

/-- Pullback of `kreinBispinorRep` along `lorentzCircularZornToKreinFrame` onto `CanonicalZorn`. -/
@[rep_depth krein]
def circularBispinorRep : CanonicalZorn →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℂ :=
  kreinBispinorRep.comp lorentzCircularZornToKreinFrame.toLinearMap

private lemma circular_plus_weyl_apply (X : CanonicalZorn) :
    kreinChiralPlusWeyl (lorentzCircularZornToKreinFrame X) =
      pauliSolder2x2 (coordinateEquiv X 0) (coordinateEquiv X 1)
        (coordinateEquiv X 2) (coordinateEquiv X 3) := by
  rw [kreinChiralPlusWeyl_apply]
  change pauliSolder2x2
      (WithLp.fst (circularZornToKreinFrame X) 0)
      (WithLp.fst (circularZornToKreinFrame X) 1)
      (WithLp.fst (circularZornToKreinFrame X) 2)
      (WithLp.fst (circularZornToKreinFrame X) 3) = _
  simp only [fst_circ_0, fst_circ_1, fst_circ_2, fst_circ_3]

private lemma circular_minus_weyl_apply (X : CanonicalZorn) :
    kreinChiralMinusWeyl (lorentzCircularZornToKreinFrame X) =
      pauliSolder2x2 (coordinateEquiv X 4) (-(coordinateEquiv X 5))
        (-(coordinateEquiv X 6)) (-(coordinateEquiv X 7)) := by
  rw [kreinChiralMinusWeyl_apply]
  change pauliSolder2x2
      (lorentzSheetParity (WithLp.snd (circularZornToKreinFrame X)) 0)
      (lorentzSheetParity (WithLp.snd (circularZornToKreinFrame X)) 1)
      (lorentzSheetParity (WithLp.snd (circularZornToKreinFrame X)) 2)
      (lorentzSheetParity (WithLp.snd (circularZornToKreinFrame X)) 3) = _
  simp only [lorentzSheetParity_zero, lorentzSheetParity_one,
    lorentzSheetParity_two, lorentzSheetParity_three,
    snd_circ_0, snd_circ_1, snd_circ_2, snd_circ_3]

private lemma pauli_σ0 : pauliSolder2x2 1 0 0 0 = σ0 := by
  ext r c; fin_cases r <;> fin_cases c <;> simp [pauliSolder2x2, solder_explicit, σ0]

private lemma pauli_σ1 : pauliSolder2x2 0 1 0 0 = σ1 := by
  ext r c; fin_cases r <;> fin_cases c <;> simp [pauliSolder2x2, solder_explicit, σ1]

private lemma pauli_σ2 : pauliSolder2x2 0 0 1 0 = σ2 := by
  ext r c; fin_cases r <;> fin_cases c <;> simp [pauliSolder2x2, solder_explicit, σ2]

private lemma pauli_σ3 : pauliSolder2x2 0 0 0 1 = σ3 := by
  ext r c; fin_cases r <;> fin_cases c <;> simp [pauliSolder2x2, solder_explicit, σ3]

private lemma pauli_neg_σ1 : pauliSolder2x2 0 (-1) 0 0 = -σ1 := by
  ext r c; fin_cases r <;> fin_cases c <;> simp [pauliSolder2x2, solder_explicit, σ1]

private lemma pauli_neg_σ2 : pauliSolder2x2 0 0 (-1) 0 = -σ2 := by
  ext r c; fin_cases r <;> fin_cases c <;> simp [pauliSolder2x2, solder_explicit, σ2]

private lemma pauli_neg_σ3 : pauliSolder2x2 0 0 0 (-1) = -σ3 := by
  ext r c; fin_cases r <;> fin_cases c <;> simp [pauliSolder2x2, solder_explicit, σ3]

private lemma pauli_zero : pauliSolder2x2 0 0 0 0 = 0 := by
  ext r c; fin_cases r <;> fin_cases c <;> simp [pauliSolder2x2, solder_explicit]

/-- Peirce selection and channel mapping of the 8 circular Peirce vectors into `SheetAlgebra (Fin 2 → ℂ)`. -/
@[rep_depth krein]
lemma circularSheetRep_peirce_channels (X : CanonicalZorn) :
    let P := firstSheetProjection (W := Fin 2 → ℂ)
    conePlus P (circularSheetRep X) = circularSheetRep (uPlus * X) ∧
    coneMinus P (circularSheetRep X) = circularSheetRep (uMinus * X) ∧
    genPhi P (circularSheetRep X) (circularSheetRep X) = circularSheetRep X ∧
    circularSheetRep (frame 0) = !![0, Matrix.toLin' σ0; 0, 0] ∧
    circularSheetRep (frame 1) = !![0, Matrix.toLin' σ1; 0, 0] ∧
    circularSheetRep (frame 2) = !![0, Matrix.toLin' σ2; 0, 0] ∧
    circularSheetRep (frame 3) = !![0, Matrix.toLin' σ3; 0, 0] ∧
    circularSheetRep (frame 4) = !![0, 0; Matrix.toLin' σ0, 0] ∧
    circularSheetRep (frame 5) = !![0, 0; Matrix.toLin' (-σ1), 0] ∧
    circularSheetRep (frame 6) = !![0, 0; Matrix.toLin' (-σ2), 0] ∧
    circularSheetRep (frame 7) = !![0, 0; Matrix.toLin' (-σ3), 0] := by
  intro P
  have hPlusProj : ∀ (f : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ),
      (∀ i : Fin 8, f (uPlus * frame i) = f (frame i)) →
      ∀ Z : CanonicalZorn, f (uPlus * Z) = f Z := by
    intro f hf Z
    let L : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := f.comp (leftMultiplication uPlus)
    have hEq : L = f := by
      apply circularPeirceBasis.ext
      intro i
      change f (uPlus * circularPeirceBasis i) = f (circularPeirceBasis i)
      rw [circularPeirceBasis_apply]
      exact hf i
    exact LinearMap.congr_fun hEq Z
  have hPlusAnn : ∀ (f : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ),
      (∀ i : Fin 8, f (uPlus * frame i) = 0) →
      ∀ Z : CanonicalZorn, f (uPlus * Z) = 0 := by
    intro f hf Z
    let L : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := f.comp (leftMultiplication uPlus)
    have hEq : L = 0 := by
      apply circularPeirceBasis.ext
      intro i
      change f (uPlus * circularPeirceBasis i) = 0
      rw [circularPeirceBasis_apply]
      exact hf i
    exact LinearMap.congr_fun hEq Z
  have hMinusProj : ∀ (f : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ),
      (∀ i : Fin 8, f (uMinus * frame i) = f (frame i)) →
      ∀ Z : CanonicalZorn, f (uMinus * Z) = f Z := by
    intro f hf Z
    let L : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := f.comp (leftMultiplication uMinus)
    have hEq : L = f := by
      apply circularPeirceBasis.ext
      intro i
      change f (uMinus * circularPeirceBasis i) = f (circularPeirceBasis i)
      rw [circularPeirceBasis_apply]
      exact hf i
    exact LinearMap.congr_fun hEq Z
  have hMinusAnn : ∀ (f : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ),
      (∀ i : Fin 8, f (uMinus * frame i) = 0) →
      ∀ Z : CanonicalZorn, f (uMinus * Z) = 0 := by
    intro f hf Z
    let L : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := f.comp (leftMultiplication uMinus)
    have hEq : L = 0 := by
      apply circularPeirceBasis.ext
      intro i
      change f (uMinus * circularPeirceBasis i) = 0
      rw [circularPeirceBasis_apply]
      exact hf i
    exact LinearMap.congr_fun hEq Z
  let fP : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    kreinChiralPlusWeyl.comp lorentzCircularZornToKreinFrame.toLinearMap
  let fM : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    kreinChiralMinusWeyl.comp lorentzCircularZornToKreinFrame.toLinearMap
  have hPP : fP (uPlus * X) = fP X := by
    apply hPlusProj fP
    apply forall_fin8
    · rw [show uPlus * frame 0 = frame 0 from uPlus_mul_frame 0]
    · rw [show uPlus * frame 1 = frame 1 from uPlus_mul_frame 1]
    · rw [show uPlus * frame 2 = frame 2 from uPlus_mul_frame 2]
    · rw [show uPlus * frame 3 = frame 3 from uPlus_mul_frame 3]
    · rw [show uPlus * frame 4 = 0 from uPlus_mul_frame 4, map_zero]
      symm
      simp [fP, circular_plus_weyl_apply, pauli_zero]
    · rw [show uPlus * frame 5 = 0 from uPlus_mul_frame 5, map_zero]
      symm
      simp [fP, circular_plus_weyl_apply, pauli_zero]
    · rw [show uPlus * frame 6 = 0 from uPlus_mul_frame 6, map_zero]
      symm
      simp [fP, circular_plus_weyl_apply, pauli_zero]
    · rw [show uPlus * frame 7 = 0 from uPlus_mul_frame 7, map_zero]
      symm
      simp [fP, circular_plus_weyl_apply, pauli_zero]
  have hPM : fP (uMinus * X) = 0 := by
    apply hMinusAnn fP
    apply forall_fin8
    · rw [show uMinus * frame 0 = 0 from uMinus_mul_frame 0, map_zero]
    · rw [show uMinus * frame 1 = 0 from uMinus_mul_frame 1, map_zero]
    · rw [show uMinus * frame 2 = 0 from uMinus_mul_frame 2, map_zero]
    · rw [show uMinus * frame 3 = 0 from uMinus_mul_frame 3, map_zero]
    · rw [show uMinus * frame 4 = frame 4 from uMinus_mul_frame 4]
      simp [fP, circular_plus_weyl_apply, pauli_zero]
    · rw [show uMinus * frame 5 = frame 5 from uMinus_mul_frame 5]
      simp [fP, circular_plus_weyl_apply, pauli_zero]
    · rw [show uMinus * frame 6 = frame 6 from uMinus_mul_frame 6]
      simp [fP, circular_plus_weyl_apply, pauli_zero]
    · rw [show uMinus * frame 7 = frame 7 from uMinus_mul_frame 7]
      simp [fP, circular_plus_weyl_apply, pauli_zero]
  have hMM : fM (uMinus * X) = fM X := by
    apply hMinusProj fM
    apply forall_fin8
    · rw [show uMinus * frame 0 = 0 from uMinus_mul_frame 0, map_zero]
      symm
      simp [fM, circular_minus_weyl_apply, pauli_zero]
    · rw [show uMinus * frame 1 = 0 from uMinus_mul_frame 1, map_zero]
      symm
      simp [fM, circular_minus_weyl_apply, pauli_zero]
    · rw [show uMinus * frame 2 = 0 from uMinus_mul_frame 2, map_zero]
      symm
      simp [fM, circular_minus_weyl_apply, pauli_zero]
    · rw [show uMinus * frame 3 = 0 from uMinus_mul_frame 3, map_zero]
      symm
      simp [fM, circular_minus_weyl_apply, pauli_zero]
    · rw [show uMinus * frame 4 = frame 4 from uMinus_mul_frame 4]
    · rw [show uMinus * frame 5 = frame 5 from uMinus_mul_frame 5]
    · rw [show uMinus * frame 6 = frame 6 from uMinus_mul_frame 6]
    · rw [show uMinus * frame 7 = frame 7 from uMinus_mul_frame 7]
  have hMP : fM (uPlus * X) = 0 := by
    apply hPlusAnn fM
    apply forall_fin8
    · rw [show uPlus * frame 0 = frame 0 from uPlus_mul_frame 0]
      simp [fM, circular_minus_weyl_apply, pauli_zero]
    · rw [show uPlus * frame 1 = frame 1 from uPlus_mul_frame 1]
      simp [fM, circular_minus_weyl_apply, pauli_zero]
    · rw [show uPlus * frame 2 = frame 2 from uPlus_mul_frame 2]
      simp [fM, circular_minus_weyl_apply, pauli_zero]
    · rw [show uPlus * frame 3 = frame 3 from uPlus_mul_frame 3]
      simp [fM, circular_minus_weyl_apply, pauli_zero]
    · rw [show uPlus * frame 4 = 0 from uPlus_mul_frame 4, map_zero]
    · rw [show uPlus * frame 5 = 0 from uPlus_mul_frame 5, map_zero]
    · rw [show uPlus * frame 6 = 0 from uPlus_mul_frame 6, map_zero]
    · rw [show uPlus * frame 7 = 0 from uPlus_mul_frame 7, map_zero]
  have hConeP : conePlus P (circularSheetRep X) = circularSheetRep (uPlus * X) := by
    have hP_eq : kreinChiralPlusWeyl (lorentzCircularZornToKreinFrame (uPlus * X)) =
        kreinChiralPlusWeyl (lorentzCircularZornToKreinFrame X) := hPP
    have hM_eq : kreinChiralMinusWeyl (lorentzCircularZornToKreinFrame (uPlus * X)) = 0 := hMP
    change conePlus P (kreinSheetRep (lorentzCircularZornToKreinFrame X)) =
      kreinSheetRep (lorentzCircularZornToKreinFrame (uPlus * X))
    rw [kreinSheetRep_apply, kreinSheetRep_apply, hP_eq, hM_eq]
    apply Matrix.ext
    apply forall_fin2 <;> apply forall_fin2 <;>
      simp [conePlus, P, firstSheetProjection, Matrix.mul_apply,
        Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_two]
  have hConeM : coneMinus P (circularSheetRep X) = circularSheetRep (uMinus * X) := by
    have hM_eq : kreinChiralMinusWeyl (lorentzCircularZornToKreinFrame (uMinus * X)) =
        kreinChiralMinusWeyl (lorentzCircularZornToKreinFrame X) := hMM
    have hP_eq : kreinChiralPlusWeyl (lorentzCircularZornToKreinFrame (uMinus * X)) = 0 := hPM
    change coneMinus P (kreinSheetRep (lorentzCircularZornToKreinFrame X)) =
      kreinSheetRep (lorentzCircularZornToKreinFrame (uMinus * X))
    rw [kreinSheetRep_apply, kreinSheetRep_apply, hM_eq, hP_eq]
    apply Matrix.ext
    apply forall_fin2 <;> apply forall_fin2 <;>
      simp [coneMinus, P, firstSheetProjection, Matrix.mul_apply,
        Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_two]
  have hPhi : genPhi P (circularSheetRep X) (circularSheetRep X) = circularSheetRep X := by
    change genPhi P (kreinSheetRep (lorentzCircularZornToKreinFrame X))
        (kreinSheetRep (lorentzCircularZornToKreinFrame X)) =
      kreinSheetRep (lorentzCircularZornToKreinFrame X)
    rw [kreinSheetRep_apply]
    apply Matrix.ext
    apply forall_fin2 <;> apply forall_fin2 <;>
      simp [genPhi, conePlus, coneMinus, P, firstSheetProjection, Matrix.mul_apply,
        Matrix.vecMul, dotProduct, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_two]
  have hPosBlock : ∀ (k : Fin 8) (M : Matrix (Fin 2) (Fin 2) ℂ),
      fP (frame k) = M → fM (frame k) = 0 →
      circularSheetRep (frame k) = !![0, Matrix.toLin' M; 0, 0] := by
    intro k M hp hm
    have hp' : kreinChiralPlusWeyl (lorentzCircularZornToKreinFrame (frame k)) = M := hp
    have hm' : kreinChiralMinusWeyl (lorentzCircularZornToKreinFrame (frame k)) = 0 := hm
    change kreinSheetRep (lorentzCircularZornToKreinFrame (frame k)) = !![0, Matrix.toLin' M; 0, 0]
    rw [kreinSheetRep_apply, hp', hm', map_zero]
  have hNegBlock : ∀ (k : Fin 8) (M : Matrix (Fin 2) (Fin 2) ℂ),
      fP (frame k) = 0 → fM (frame k) = M →
      circularSheetRep (frame k) = !![0, 0; Matrix.toLin' M, 0] := by
    intro k M hp hm
    have hp' : kreinChiralPlusWeyl (lorentzCircularZornToKreinFrame (frame k)) = 0 := hp
    have hm' : kreinChiralMinusWeyl (lorentzCircularZornToKreinFrame (frame k)) = M := hm
    change kreinSheetRep (lorentzCircularZornToKreinFrame (frame k)) = !![0, 0; Matrix.toLin' M, 0]
    rw [kreinSheetRep_apply, hp', hm', map_zero]
  refine ⟨hConeP, hConeM, hPhi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hPosBlock 0 σ0
      (by simp [fP, circular_plus_weyl_apply, pauli_σ0])
      (by simp [fM, circular_minus_weyl_apply, pauli_zero])
  · exact hPosBlock 1 σ1
      (by simp [fP, circular_plus_weyl_apply, pauli_σ1])
      (by simp [fM, circular_minus_weyl_apply, pauli_zero])
  · exact hPosBlock 2 σ2
      (by simp [fP, circular_plus_weyl_apply, pauli_σ2])
      (by simp [fM, circular_minus_weyl_apply, pauli_zero])
  · exact hPosBlock 3 σ3
      (by simp [fP, circular_plus_weyl_apply, pauli_σ3])
      (by simp [fM, circular_minus_weyl_apply, pauli_zero])
  · exact hNegBlock 4 σ0
      (by simp [fP, circular_plus_weyl_apply, pauli_zero])
      (by simp [fM, circular_minus_weyl_apply, pauli_σ0])
  · exact hNegBlock 5 (-σ1)
      (by simp [fP, circular_plus_weyl_apply, pauli_zero])
      (by simp [fM, circular_minus_weyl_apply, pauli_neg_σ1])
  · exact hNegBlock 6 (-σ2)
      (by simp [fP, circular_plus_weyl_apply, pauli_zero])
      (by simp [fM, circular_minus_weyl_apply, pauli_neg_σ2])
  · exact hNegBlock 7 (-σ3)
      (by simp [fP, circular_plus_weyl_apply, pauli_zero])
      (by simp [fM, circular_minus_weyl_apply, pauli_neg_σ3])

/-- Noncommutativity of the two Krein Weyl channels and exact metric-trace pullback:
`Tr(kreinBispinorRep u * kreinBispinorRep v) = 2 * chiralKreinForm u v`. -/
@[rep_depth krein]
lemma kreinBispinorRep_metric_trace_and_noncomm (u v : KreinFrame4) :
    kreinChiralPlusWeyl (plusFrame 1) * kreinChiralMinusWeyl (minusFrame 2) ≠
      kreinChiralMinusWeyl (minusFrame 2) * kreinChiralPlusWeyl (plusFrame 1) ∧
    Matrix.trace (kreinBispinorRep u * kreinBispinorRep v) =
      2 * (chiralKreinForm (E := FourSpace) u v : ℂ) ∧
    (kreinChiralPlusWeyl u * kreinChiralMinusWeyl v).det =
      (kreinChiralPlusWeyl u).det * (kreinChiralMinusWeyl v).det := by
  refine ⟨?_, ?_, ?_⟩
  · intro hComm
    have h00 := congrFun (congrFun hComm 0) 0
    have hL : (kreinChiralPlusWeyl (plusFrame 1) * kreinChiralMinusWeyl (minusFrame 2)) 0 0 =
        Complex.I := by
      simp [kreinChiralPlusWeyl_apply, kreinChiralMinusWeyl_apply, pauliSolder2x2, solder_explicit,
        plusFrame, minusFrame, frameBasis_apply, Matrix.mul_apply, Fin.sum_univ_two]
    have hR : (kreinChiralMinusWeyl (minusFrame 2) * kreinChiralPlusWeyl (plusFrame 1)) 0 0 =
        -Complex.I := by
      simp [kreinChiralPlusWeyl_apply, kreinChiralMinusWeyl_apply, pauliSolder2x2, solder_explicit,
        plusFrame, minusFrame, frameBasis_apply, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hL, hR] at h00
    have hTwoI : (2 : ℂ) * Complex.I = 0 := by linear_combination h00
    exact Complex.I_ne_zero ((mul_eq_zero.mp hTwoI).resolve_left (by norm_num))
  · rw [show u = to_doubled (WithLp.fst u) (WithLp.snd u) from by apply DoubledSpace.ext <;> rfl,
      show v = to_doubled (WithLp.fst v) (WithLp.snd v) from by apply DoubledSpace.ext <;> rfl]
    rw [chiralKreinForm_to_doubled, PiLp.inner_apply, PiLp.inner_apply,
      Fin.sum_univ_four, Fin.sum_univ_four]
    rw [kreinBispinorRep_apply, kreinBispinorRep_apply]
    simp [Matrix.trace, Matrix.diag_apply, kreinChiralPlusWeyl_apply, kreinChiralMinusWeyl_apply,
      pauliSolder2x2, solder_explicit, Fin.sum_univ_four, RCLike.inner_apply]
    generalize (WithLp.fst u) 0 = u0
    generalize (WithLp.fst u) 1 = u1
    generalize (WithLp.fst u) 2 = u2
    generalize (WithLp.fst u) 3 = u3
    generalize (WithLp.snd u) 0 = xi0
    generalize (WithLp.snd u) 1 = xi1
    generalize (WithLp.snd u) 2 = xi2
    generalize (WithLp.snd u) 3 = xi3
    generalize (WithLp.fst v) 0 = v0
    generalize (WithLp.fst v) 1 = v1
    generalize (WithLp.fst v) 2 = v2
    generalize (WithLp.fst v) 3 = v3
    generalize (WithLp.snd v) 0 = eta0
    generalize (WithLp.snd v) 1 = eta1
    generalize (WithLp.snd v) 2 = eta2
    generalize (WithLp.snd v) 3 = eta3
    ring_nf
    simp only [Complex.I_sq]
    ring
  · exact Matrix.det_mul _ _

/-- Explicit non-commutativity witness on the `Matrix (Fin 2) (Fin 2) ℂ` Weyl carrier. -/
@[rep_depth krein]
lemma kreinChiralWeyl_mat2C_noncomm :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  ⟨kreinChiralPlusWeyl (plusFrame 1), kreinChiralMinusWeyl (minusFrame 2),
    (kreinBispinorRep_metric_trace_and_noncomm (plusFrame 1) (minusFrame 2)).1⟩

/-- Explicit non-commutativity witness on the `Matrix (Fin 4) (Fin 4) ℂ` bispinor carrier. -/
@[rep_depth krein]
lemma kreinBispinorRep_mat4C_noncomm :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℂ, A * B ≠ B * A := by
  let P4C : Matrix (Fin 4) (Fin 4) ℂ :=
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
  refine ⟨P4C, kreinBispinorRep (plusFrame 0), ?_⟩
  intro hEq
  have h02 := congrFun (congrFun hEq 0) 2
  have hL : (P4C * kreinBispinorRep (plusFrame 0)) 0 2 = 1 := by
    rw [kreinBispinorRep_apply]
    simp [P4C, kreinChiralPlusWeyl_apply, pauliSolder2x2, solder_explicit, plusFrame,
      frameBasis_apply, Matrix.mul_apply, Fin.sum_univ_four]
  have hR : (kreinBispinorRep (plusFrame 0) * P4C) 0 2 = 0 := by
    simp [P4C, Matrix.mul_apply, Fin.sum_univ_four]
  rw [hL, hR] at h02
  exact one_ne_zero h02

/-! ## Layer 3: Two-Sheeted Gauge–Higgs Connection, Self-Dual Yang–Mills Solution, & Bogomolnyi Identity -/

/-- Two-sheeted gauge–Higgs connection in `SheetAlgebra (Fin 2 → ℂ)` coupling
noncommuting diagonal gauge potentials `(AL, AR)` with the Krein Weyl off-diagonal blocks. -/
@[rep_depth transport]
def twoSheetKreinConnection (AL AR : Operator (Fin 2 → ℂ)) (u : KreinFrame4) :
    SheetAlgebra (Fin 2 → ℂ) :=
  !![AL, 0; 0, AR] + kreinSheetRep u

/-- Noncommutative curvature decomposition and `Cl(1,1)` parity separation of
`twoSheetKreinConnection` inside `SheetAlgebra (Fin 2 → ℂ)`. -/
@[rep_depth transport]
lemma twoSheetKreinConnection_curvature_and_parity_split
    (AL AR : Operator (Fin 2 → ℂ)) (u : KreinFrame4) :
    let P := firstSheetProjection (W := Fin 2 → ℂ)
    let Γ := invS P
    let Φp := Matrix.toLin' (kreinChiralPlusWeyl u)
    let Φm := Matrix.toLin' (kreinChiralMinusWeyl u)
    let D := twoSheetKreinConnection AL AR u
    kreinSheetRep u * kreinSheetRep u = genV P (kreinSheetRep u) (kreinSheetRep u) ∧
    D * D = !![AL * AL + Φp * Φm, AL * Φp + Φp * AR;
               Φm * AL + AR * Φm, Φm * Φp + AR * AR] ∧
    (D * D) + Γ * (D * D) * Γ =
      (2 : ℕ) • !![AL * AL + Φp * Φm, 0;
                   0, Φm * Φp + AR * AR] ∧
    (D * D) - Γ * (D * D) * Γ =
      (2 : ℕ) • !![0, AL * Φp + Φp * AR;
                   Φm * AL + AR * Φm, 0] := by
  intro P Γ Φp Φm D
  have hG : Γ = !![1, 0; 0, -1] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Γ, invS, P, firstSheetProjection]
  have hS : kreinSheetRep u = !![0, Φp; Φm, 0] := by
    rw [kreinSheetRep_apply]
  have hD : D = !![AL, Φp; Φm, AR] := by
    dsimp [D, twoSheetKreinConnection]
    rw [hS]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply]
  have hV : kreinSheetRep u * kreinSheetRep u =
      genV P (kreinSheetRep u) (kreinSheetRep u) := by
    rw [hS]
    apply Matrix.ext
    apply forall_fin2 <;> apply forall_fin2 <;>
      simp [genV, anticomm, conePlus, coneMinus, P, firstSheetProjection,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.sub_apply, Matrix.one_apply,
        Fin.sum_univ_two]
  have hL : ∀ x : Operator (Fin 2 → ℂ), (-1 : Operator (Fin 2 → ℂ)) * x = -x := fun x => by
    ext v; rfl
  have hR : ∀ x : Operator (Fin 2 → ℂ), x * (-1 : Operator (Fin 2 → ℂ)) = -x := fun x => by
    ext v; simp
  refine ⟨hV, ?_, ?_, ?_⟩
  · rw [hD]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [hD, hG, two_nsmul]
    apply Matrix.ext
    apply forall_fin2 <;> apply forall_fin2 <;> simp [hL, hR]
  · rw [hD, hG, two_nsmul]
    apply Matrix.ext
    apply forall_fin2 <;> apply forall_fin2 <;> simp [hL, hR] <;> abel

/-- Basis 1-form `dx μ` in `ExteriorAlgebra ℂ (Fin 4 → ℂ)`. -/
@[rep_depth transport]
def extBasisOneForm (μ : Fin 4) : ExteriorAlgebra ℂ (Fin 4 → ℂ) :=
  ExteriorAlgebra.ι ℂ (Pi.single μ (1 : ℂ))

/-- Contraction coefficient linear functional on 2-forms in `ExteriorAlgebra ℂ (Fin 4 → ℂ)`. -/
@[rep_depth transport]
def blade2Coeff (a b : Fin 4) : ExteriorAlgebra ℂ (Fin 4 → ℂ) →ₗ[ℂ] ℂ :=
  (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin 4 → ℂ)).toLinearMap.comp
    ((contractionOp (R := ℂ) (V := Fin 4 → ℂ) (LinearMap.proj b)).comp
      (contractionOp (R := ℂ) (V := Fin 4 → ℂ) (LinearMap.proj a)))

/-- Exact evaluation of `blade2Coeff a b` on basis 2-forms and annihilation on 1-forms and scalars. -/
@[rep_depth transport]
lemma blade2Coeff_eval (a b c d : Fin 4) (z : ℂ) :
    blade2Coeff a b (extBasisOneForm c * extBasisOneForm d) =
      (if a = c then (1 : ℂ) else 0) * (if b = d then (1 : ℂ) else 0) -
        (if a = d then (1 : ℂ) else 0) * (if b = c then (1 : ℂ) else 0) ∧
    blade2Coeff a b (extBasisOneForm c) = 0 ∧
    blade2Coeff a b (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) z) = 0 := by
  have hScal : ∀ s : ℂ, contractionOp (LinearMap.proj b)
      (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) s) = 0 := by
    intro s
    rw [Algebra.algebraMap_eq_smul_one, map_smul, contraction_op_one, smul_zero]
  have h1 : contractionOp (LinearMap.proj a) (extBasisOneForm c) =
      algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) (if a = c then 1 else 0) := by
    simp [extBasisOneForm, contraction_on_generator, Pi.single_apply]
  have hBlade : blade2Coeff a b (extBasisOneForm c * extBasisOneForm d) =
      (if a = c then (1 : ℂ) else 0) * (if b = d then (1 : ℂ) else 0) -
        (if a = d then (1 : ℂ) else 0) * (if b = c then (1 : ℂ) else 0) := by
    dsimp [blade2Coeff, extBasisOneForm]
    change (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra ℂ (Fin 4 → ℂ) →ₐ[ℂ] ℂ)
      (contractionOp (LinearMap.proj b)
        (contractionOp (LinearMap.proj a) (ι ℂ (Pi.single c 1) * ι ℂ (Pi.single d 1)))) = _
    rw [contraction_op_generator_mul]
    simp only [LinearMap.proj_apply, Pi.single_apply, contraction_on_generator,
      Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one,
      map_sub, map_smul, smul_eq_mul, map_one]
  refine ⟨hBlade, ?_, ?_⟩
  · dsimp [blade2Coeff]
    change (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra ℂ (Fin 4 → ℂ) →ₐ[ℂ] ℂ)
      (contractionOp (LinearMap.proj b)
        (contractionOp (LinearMap.proj a) (extBasisOneForm c))) = 0
    rw [h1, hScal, map_zero]
  · dsimp [blade2Coeff]
    change (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra ℂ (Fin 4 → ℂ) →ₐ[ℂ] ℂ)
      (contractionOp (LinearMap.proj b)
        (contractionOp (LinearMap.proj a) (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) z))) = 0
    rw [show contractionOp (LinearMap.proj a) (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) z) = 0 by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, contraction_op_one, smul_zero],
      map_zero, map_zero]

/-- Explicit 4D Lorentzian Hodge star endomorphism on `ExteriorAlgebra ℂ (Fin 4 → ℂ)`
sending `dx₀∧dx₁ ↦ -dx₂∧dx₃`, `dx₂∧dx₃ ↦ dx₀∧dx₁` (and cyclically). -/
@[rep_depth transport]
def lorentzHodgeStar4 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  let e01 := extBasisOneForm 0 * extBasisOneForm 1
  let e02 := extBasisOneForm 0 * extBasisOneForm 2
  let e03 := extBasisOneForm 0 * extBasisOneForm 3
  let e23 := extBasisOneForm 2 * extBasisOneForm 3
  let e31 := extBasisOneForm 3 * extBasisOneForm 1
  let e12 := extBasisOneForm 1 * extBasisOneForm 2
  (LinearMap.smulRight (blade2Coeff 2 3) e01 - LinearMap.smulRight (blade2Coeff 0 1) e23) +
    (LinearMap.smulRight (blade2Coeff 3 1) e02 - LinearMap.smulRight (blade2Coeff 0 2) e31) +
    (LinearMap.smulRight (blade2Coeff 1 2) e03 - LinearMap.smulRight (blade2Coeff 0 3) e12)

/-- Complex chiral Hodge star `chiralHodgeStar4 := (-i) • lorentzHodgeStar4` whose
2-form eigenspaces separate self-dual (`+1`) and anti-self-dual (`-1`) helicities. -/
@[rep_depth transport]
def chiralHodgeStar4 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  (-Complex.I) • lorentzHodgeStar4

private lemma extBasis4_anticomm (μ ν : Fin 4) :
    extBasisOneForm μ * extBasisOneForm ν = -(extBasisOneForm ν * extBasisOneForm μ) := by
  have h := ExteriorAlgebra.ι_sq_zero (R := ℂ)
    ((Pi.single μ (1 : ℂ) : Fin 4 → ℂ) + (Pi.single ν (1 : ℂ) : Fin 4 → ℂ))
  rw [map_add, add_mul, mul_add, mul_add,
    ExteriorAlgebra.ι_sq_zero, ExteriorAlgebra.ι_sq_zero, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

private lemma extBasis4_sq_zero (μ : Fin 4) :
    extBasisOneForm μ * extBasisOneForm μ = 0 :=
  ExteriorAlgebra.ι_sq_zero _

private lemma lorentzHodgeStar4_blade (μ ν : Fin 4) :
    lorentzHodgeStar4 (extBasisOneForm μ * extBasisOneForm ν) =
      match μ, ν with
      | 0, 1 => -(extBasisOneForm 2 * extBasisOneForm 3)
      | 1, 0 => extBasisOneForm 2 * extBasisOneForm 3
      | 0, 2 => -(extBasisOneForm 3 * extBasisOneForm 1)
      | 2, 0 => extBasisOneForm 3 * extBasisOneForm 1
      | 0, 3 => -(extBasisOneForm 1 * extBasisOneForm 2)
      | 3, 0 => extBasisOneForm 1 * extBasisOneForm 2
      | 2, 3 => extBasisOneForm 0 * extBasisOneForm 1
      | 3, 2 => -(extBasisOneForm 0 * extBasisOneForm 1)
      | 3, 1 => extBasisOneForm 0 * extBasisOneForm 2
      | 1, 3 => -(extBasisOneForm 0 * extBasisOneForm 2)
      | 1, 2 => extBasisOneForm 0 * extBasisOneForm 3
      | 2, 1 => -(extBasisOneForm 0 * extBasisOneForm 3)
      | _, _ => 0 := by
  fin_cases μ <;> fin_cases ν <;>
    simp [lorentzHodgeStar4, (blade2Coeff_eval _ _ _ _ 0).1, extBasis4_sq_zero]

private lemma chiralHodgeStar4_blade (μ ν : Fin 4) :
    chiralHodgeStar4 (extBasisOneForm μ * extBasisOneForm ν) =
      match μ, ν with
      | 0, 1 => Complex.I • (extBasisOneForm 2 * extBasisOneForm 3)
      | 1, 0 => (-Complex.I) • (extBasisOneForm 2 * extBasisOneForm 3)
      | 0, 2 => Complex.I • (extBasisOneForm 3 * extBasisOneForm 1)
      | 2, 0 => (-Complex.I) • (extBasisOneForm 3 * extBasisOneForm 1)
      | 0, 3 => Complex.I • (extBasisOneForm 1 * extBasisOneForm 2)
      | 3, 0 => (-Complex.I) • (extBasisOneForm 1 * extBasisOneForm 2)
      | 2, 3 => (-Complex.I) • (extBasisOneForm 0 * extBasisOneForm 1)
      | 3, 2 => Complex.I • (extBasisOneForm 0 * extBasisOneForm 1)
      | 3, 1 => (-Complex.I) • (extBasisOneForm 0 * extBasisOneForm 2)
      | 1, 3 => Complex.I • (extBasisOneForm 0 * extBasisOneForm 2)
      | 1, 2 => (-Complex.I) • (extBasisOneForm 0 * extBasisOneForm 3)
      | 2, 1 => Complex.I • (extBasisOneForm 0 * extBasisOneForm 3)
      | _, _ => 0 := by
  dsimp [chiralHodgeStar4]
  rw [lorentzHodgeStar4_blade μ ν]
  fin_cases μ <;> fin_cases ν <;> simp

/-- Squares of `lorentzHodgeStar4` and `chiralHodgeStar4` on all basis 2-forms. -/
@[rep_depth transport]
lemma hodgeStar4_sq_on_blades (a b : Fin 4) :
    lorentzHodgeStar4 (lorentzHodgeStar4 (extBasisOneForm a * extBasisOneForm b)) =
      -(extBasisOneForm a * extBasisOneForm b) ∧
    chiralHodgeStar4 (chiralHodgeStar4 (extBasisOneForm a * extBasisOneForm b)) =
      extBasisOneForm a * extBasisOneForm b := by
  have hLorentz : lorentzHodgeStar4 (lorentzHodgeStar4 (extBasisOneForm a * extBasisOneForm b)) =
      -(extBasisOneForm a * extBasisOneForm b) := by
    have h01 : lorentzHodgeStar4 (extBasisOneForm 0 * extBasisOneForm 1) =
        -(extBasisOneForm 2 * extBasisOneForm 3) := lorentzHodgeStar4_blade 0 1
    have h10 : lorentzHodgeStar4 (extBasisOneForm 1 * extBasisOneForm 0) =
        extBasisOneForm 2 * extBasisOneForm 3 := lorentzHodgeStar4_blade 1 0
    have h02 : lorentzHodgeStar4 (extBasisOneForm 0 * extBasisOneForm 2) =
        -(extBasisOneForm 3 * extBasisOneForm 1) := lorentzHodgeStar4_blade 0 2
    have h20 : lorentzHodgeStar4 (extBasisOneForm 2 * extBasisOneForm 0) =
        extBasisOneForm 3 * extBasisOneForm 1 := lorentzHodgeStar4_blade 2 0
    have h03 : lorentzHodgeStar4 (extBasisOneForm 0 * extBasisOneForm 3) =
        -(extBasisOneForm 1 * extBasisOneForm 2) := lorentzHodgeStar4_blade 0 3
    have h30 : lorentzHodgeStar4 (extBasisOneForm 3 * extBasisOneForm 0) =
        extBasisOneForm 1 * extBasisOneForm 2 := lorentzHodgeStar4_blade 3 0
    have h23 : lorentzHodgeStar4 (extBasisOneForm 2 * extBasisOneForm 3) =
        extBasisOneForm 0 * extBasisOneForm 1 := lorentzHodgeStar4_blade 2 3
    have h32 : lorentzHodgeStar4 (extBasisOneForm 3 * extBasisOneForm 2) =
        -(extBasisOneForm 0 * extBasisOneForm 1) := lorentzHodgeStar4_blade 3 2
    have h31 : lorentzHodgeStar4 (extBasisOneForm 3 * extBasisOneForm 1) =
        extBasisOneForm 0 * extBasisOneForm 2 := lorentzHodgeStar4_blade 3 1
    have h13 : lorentzHodgeStar4 (extBasisOneForm 1 * extBasisOneForm 3) =
        -(extBasisOneForm 0 * extBasisOneForm 2) := lorentzHodgeStar4_blade 1 3
    have h12 : lorentzHodgeStar4 (extBasisOneForm 1 * extBasisOneForm 2) =
        extBasisOneForm 0 * extBasisOneForm 3 := lorentzHodgeStar4_blade 1 2
    have h21 : lorentzHodgeStar4 (extBasisOneForm 2 * extBasisOneForm 1) =
        -(extBasisOneForm 0 * extBasisOneForm 3) := lorentzHodgeStar4_blade 2 1
    revert a b
    apply forall_fin4
    all_goals
      apply forall_fin4
    · rw [extBasis4_sq_zero, map_zero, map_zero, neg_zero]
    · rw [h01, map_neg, h23]
    · rw [h02, map_neg, h31]
    · rw [h03, map_neg, h12]
    · rw [h10, h23, extBasis4_anticomm 0 1]
    · rw [extBasis4_sq_zero, map_zero, map_zero, neg_zero]
    · rw [h12, h03, extBasis4_anticomm 1 2]
    · rw [h13, map_neg, h02, neg_neg, extBasis4_anticomm 3 1]
    · rw [h20, h31, extBasis4_anticomm 0 2]
    · rw [h21, map_neg, h03, neg_neg, extBasis4_anticomm 1 2]
    · rw [extBasis4_sq_zero, map_zero, map_zero, neg_zero]
    · rw [h23, h01, extBasis4_anticomm 2 3]
    · rw [h30, h12, extBasis4_anticomm 0 3]
    · rw [h31, h02]
    · rw [h32, map_neg, h01, neg_neg, extBasis4_anticomm 2 3]
    · rw [extBasis4_sq_zero, map_zero, map_zero, neg_zero]
  refine ⟨hLorentz, ?_⟩
  dsimp [chiralHodgeStar4]
  simp only [map_smul, smul_smul, hLorentz, smul_neg]
  have hCoef : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by
    calc
      (-Complex.I) * (-Complex.I) = Complex.I ^ 2 := by ring
      _ = -1 := Complex.I_sq
  rw [hCoef, neg_one_smul, neg_neg]

/-- Upper two-sheet idempotent `diag(1, 1, 0, 0)` in `M₄(ExteriorAlgebra ℂ (Fin 4 → ℂ))`. -/
@[rep_depth transport]
def upperSheetIdempotent4 : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Upper-right helicity-split Newman–Penrose 1-form block `(e₀ + e₃, e₁ - i e₂)`
positioned on the outgoing Peirce corner `{0,1} × {2,3}`. -/
@[rep_depth transport]
def helicityUpperOneForm4 : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  let e0 := extBasisOneForm 0
  let e1 := extBasisOneForm 1
  let e2 := extBasisOneForm 2
  let e3 := extBasisOneForm 3
  !![0, 0, e0 + e3, e1 - Complex.I • e2;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Lower-left helicity-split Newman–Penrose 1-form block `(e₁ - i e₂, e₀ - e₃, -(e₁ + i e₂))`
positioned on the incoming Peirce corner `{2,3} × {0,1}`. -/
@[rep_depth transport]
def helicityLowerOneForm4 : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  let e0 := extBasisOneForm 0
  let e1 := extBasisOneForm 1
  let e2 := extBasisOneForm 2
  let e3 := extBasisOneForm 3
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     e1 - Complex.I • e2, e0 - e3, 0, 0;
     0, -(e1 + Complex.I • e2), 0, 0]

/-- Two-sheeted helicity-split circular gauge connection `genPhi P U L` over `ExteriorAlgebra ℂ (Fin 4 → ℂ)`. -/
@[rep_depth transport]
def helicityCircularConnection4 : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  genPhi upperSheetIdempotent4 helicityUpperOneForm4 helicityLowerOneForm4

private lemma chiralHodgeStar4_sd_pair1 :
    let w := (extBasisOneForm 0 + extBasisOneForm 3) * (extBasisOneForm 1 - Complex.I • extBasisOneForm 2)
    chiralHodgeStar4 w = w := by
  intro w
  dsimp [w]
  have hw : (extBasisOneForm 0 + extBasisOneForm 3) * (extBasisOneForm 1 - Complex.I • extBasisOneForm 2) =
      extBasisOneForm 0 * extBasisOneForm 1 -
        Complex.I • (extBasisOneForm 0 * extBasisOneForm 2) -
        extBasisOneForm 1 * extBasisOneForm 3 +
        Complex.I • (extBasisOneForm 2 * extBasisOneForm 3) := by
    simp only [add_mul, mul_sub, mul_smul_comm]
    rw [extBasis4_anticomm 3 1, extBasis4_anticomm 3 2]
    module
  rw [hw, map_add, map_sub, map_sub, map_smul, map_smul,
    chiralHodgeStar4_blade 0 1, chiralHodgeStar4_blade 0 2,
    chiralHodgeStar4_blade 1 3, chiralHodgeStar4_blade 2 3]
  rw [extBasis4_anticomm 3 1]
  simp only [smul_neg, smul_smul]
  rw [show Complex.I * Complex.I = -1 from by rw [← sq, Complex.I_sq],
    show Complex.I * (-Complex.I) = 1 from by ring_nf; rw [Complex.I_sq]; ring]
  module

private lemma chiralHodgeStar4_sd_pair2 :
    let w :=
      (extBasisOneForm 0 + extBasisOneForm 3) * (extBasisOneForm 0 - extBasisOneForm 3) -
      (extBasisOneForm 1 - Complex.I • extBasisOneForm 2) * (extBasisOneForm 1 + Complex.I • extBasisOneForm 2)
    chiralHodgeStar4 w = w := by
  intro w
  dsimp [w]
  have h1 :
      (extBasisOneForm 0 + extBasisOneForm 3) * (extBasisOneForm 0 - extBasisOneForm 3) =
        (-2 : ℂ) • (extBasisOneForm 0 * extBasisOneForm 3) := by
    simp only [add_mul, mul_sub, extBasis4_sq_zero, extBasis4_anticomm 3 0]
    module
  have h2 :
      (extBasisOneForm 1 - Complex.I • extBasisOneForm 2) * (extBasisOneForm 1 + Complex.I • extBasisOneForm 2) =
        (2 * Complex.I) • (extBasisOneForm 1 * extBasisOneForm 2) := by
    simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, extBasis4_sq_zero,
      extBasis4_anticomm 2 1]
    module
  rw [h1, h2, map_sub, map_smul, map_smul, chiralHodgeStar4_blade 0 3, chiralHodgeStar4_blade 1 2]
  simp only [smul_smul]
  rw [show (-2 : ℂ) * Complex.I = -(2 * Complex.I) by ring,
    show (2 * Complex.I) * (-Complex.I) = 2 by ring_nf; rw [Complex.I_sq]; ring]
  module

/-- Unconditional non-Abelian self-dual Yang–Mills solution from the two-sheeted
helicity-split circular connection: nonzero curvature, distinct upper/lower diagonal blocks,
`isSelfDualCurvature chiralHodgeStar4 F`, and `covariantDerivative A 0 (matrixHodgeStar chiralHodgeStar4 F) = 0`. -/
@[rep_depth transport]
lemma helicityCircularConnection4_solves_self_dual_yang_mills :
    let P := upperSheetIdempotent4
    let F := curvatureFromConnection (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))) helicityCircularConnection4
    F ≠ 0 ∧
    F 0 0 ≠ F 2 2 ∧
    F = genV P helicityUpperOneForm4 helicityLowerOneForm4 ∧
    isSelfDualCurvature chiralHodgeStar4 F ∧
    covariantDerivative helicityCircularConnection4 0 (matrixHodgeStar chiralHodgeStar4 F) = 0 := by
  intro P F
  have hP : P * P = P := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [P, upperSheetIdempotent4, Matrix.mul_apply, Fin.sum_univ_four]
  have hBridge := peirce_defect_connection_curvature_and_yang_mills_bridge
    chiralHodgeStar4 (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
    hP helicityUpperOneForm4 helicityLowerOneForm4 helicityCircularConnection4
  have hF : F = genV P helicityUpperOneForm4 helicityLowerOneForm4 := hBridge.2.2.1
  have hCovF : covariantDerivative helicityCircularConnection4 0 F = 0 := by
    rw [hF]
    exact hBridge.2.2.2.1
  have hD : matrixExteriorDerivative (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
      helicityCircularConnection4 = 0 := by
    ext i j; rfl
  have hConnMat : helicityCircularConnection4 =
      !![0, 0, extBasisOneForm 0 + extBasisOneForm 3, extBasisOneForm 1 - Complex.I • extBasisOneForm 2;
         0, 0, 0, 0;
         extBasisOneForm 1 - Complex.I • extBasisOneForm 2, extBasisOneForm 0 - extBasisOneForm 3, 0, 0;
         0, -(extBasisOneForm 1 + Complex.I • extBasisOneForm 2), 0, 0] := by
    apply Matrix.ext
    apply forall_fin4
    all_goals
      apply forall_fin4
    all_goals
      simp [helicityCircularConnection4, genPhi, conePlus, coneMinus, upperSheetIdempotent4,
        helicityUpperOneForm4, helicityLowerOneForm4, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_four]
  have hF_entries : F =
      !![(extBasisOneForm 0 + extBasisOneForm 3) * (extBasisOneForm 1 - Complex.I • extBasisOneForm 2),
         (extBasisOneForm 0 + extBasisOneForm 3) * (extBasisOneForm 0 - extBasisOneForm 3) -
           (extBasisOneForm 1 - Complex.I • extBasisOneForm 2) * (extBasisOneForm 1 + Complex.I • extBasisOneForm 2),
         0, 0;
         0, 0, 0, 0;
         0, 0, (extBasisOneForm 1 - Complex.I • extBasisOneForm 2) * (extBasisOneForm 0 + extBasisOneForm 3), 0;
         0, 0, 0, 0] := by
    dsimp [F, curvatureFromConnection]
    rw [hD, zero_add, hConnMat]
    apply Matrix.ext
    apply forall_fin4
    all_goals
      apply forall_fin4
    all_goals
      simp [Matrix.mul_apply, Fin.sum_univ_four, sub_eq_add_neg] <;> try noncomm_ring
    simp only [extBasis4_sq_zero, zero_add, add_zero, smul_zero]
    rw [extBasis4_anticomm 2 1]
    module
  have hSwap22 :
      (extBasisOneForm 1 - Complex.I • extBasisOneForm 2) * (extBasisOneForm 0 + extBasisOneForm 3) =
        -((extBasisOneForm 0 + extBasisOneForm 3) * (extBasisOneForm 1 - Complex.I • extBasisOneForm 2)) := by
    simp only [sub_mul, mul_add, add_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
    rw [extBasis4_anticomm 1 0, extBasis4_anticomm 1 3, extBasis4_anticomm 2 0, extBasis4_anticomm 2 3]
    module
  have hSD : isSelfDualCurvature chiralHodgeStar4 F := by
    dsimp [isSelfDualCurvature]
    rw [hF_entries]
    apply Matrix.ext
    apply forall_fin4
    all_goals
      apply forall_fin4
    all_goals
      simp [matrixHodgeStar]
    · exact chiralHodgeStar4_sd_pair1
    · rw [← map_sub]; exact chiralHodgeStar4_sd_pair2
    · rw [hSwap22, map_neg, chiralHodgeStar4_sd_pair1]
  have hF00 : F 0 0 =
      (extBasisOneForm 0 + extBasisOneForm 3) * (extBasisOneForm 1 - Complex.I • extBasisOneForm 2) := by
    rw [hF_entries]; rfl
  have hF22 : F 2 2 =
      -((extBasisOneForm 0 + extBasisOneForm 3) * (extBasisOneForm 1 - Complex.I • extBasisOneForm 2)) := by
    rw [hF_entries]; exact hSwap22
  have hF00Ne0 : F 0 0 ≠ 0 := by
    intro hZ
    have hc := congrArg (blade2Coeff 0 1) hZ
    rw [hF00, map_zero] at hc
    simp only [add_mul, mul_sub, map_add, map_sub, mul_smul_comm, map_smul,
      (blade2Coeff_eval _ _ _ _ 0).1] at hc
    norm_num at hc
  have hNe0 : F ≠ 0 := fun hZ => hF00Ne0 (by rw [hZ]; rfl)
  have hBlocksNe : F 0 0 ≠ F 2 2 := by
    intro hEq
    have hc := congrArg (blade2Coeff 0 1) hEq
    rw [hF00, hF22, map_neg] at hc
    simp only [add_mul, mul_sub, map_add, map_sub, mul_smul_comm, map_smul,
      (blade2Coeff_eval _ _ _ _ 0).1] at hc
    norm_num at hc
  have hYM : covariantDerivative helicityCircularConnection4 0 (matrixHodgeStar chiralHodgeStar4 F) = 0 :=
    self_dual_connection_curvature_solves_yang_mills chiralHodgeStar4 helicityCircularConnection4 0 hSD hCovF
  exact ⟨hNe0, hBlocksNe, hF, hSD, hYM⟩

/-- Constructive `HodgeTwoFormData` on `Fin 6 → ℝ` modeling `(e₀₁, e₀₂, e₀₃, e₂₃, e₃₁, e₁₂)`. -/
@[rep_depth transport]
def euclideanTwoFormHodgeData : HodgeTwoFormData (Fin 6 → ℝ) where
  inner u v := ∑ k : Fin 6, u k * v k
  star :=
    { toFun := fun u => ![u 3, u 4, u 5, u 0, u 1, u 2]
      map_add' := fun u v => by funext k; fin_cases k <;> rfl
      map_smul' := fun r u => by funext k; fin_cases k <;> rfl }
  inner_add_left x y z := by simp [Finset.sum_add_distrib, add_mul]
  inner_add_right x y z := by simp [Finset.sum_add_distrib, mul_add]
  inner_smul_left r x y := by simp [Finset.mul_sum, mul_assoc]
  inner_smul_right r x y := by
    simp [Finset.mul_sum]; congr 1; ext k; ring
  symmetric x y := by congr 1; ext k; ring
  positive x := Finset.sum_nonneg fun k _ => mul_self_nonneg (x k)
  star_sq := by ext x k; fin_cases k <;> rfl
  star_isometry x y := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  star_selfAdjoint x y := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring

/-- Embedding of self-dual / anti-self-dual 2-form components `(fPlus, fMinus)` into `Fin 6 → ℝ`. -/
@[rep_depth transport]
def twoSheetEuclideanTwoForm (fPlus fMinus : Fin 3 → ℝ) : Fin 6 → ℝ :=
  ![fPlus 0 + fMinus 0, fPlus 1 + fMinus 1, fPlus 2 + fMinus 2,
    fPlus 0 - fMinus 0, fPlus 1 - fMinus 1, fPlus 2 - fMinus 2]

/-- Two-sheeted Bogomolnyi action decomposition and three-way self-duality equivalence on
`BogomolnyiAlgebraicBoundBridge`: `S - Q = 4 ‖fMinus‖²`, `S + Q = 4 ‖fPlus‖²`, `|Q| ≤ S`,
and `S = Q ↔ ★F = F ↔ fMinus = 0`. -/
@[rep_depth transport]
lemma twoSheetBogomolnyi_action_identity (fPlus fMinus : Fin 3 → ℝ) :
    let F := twoSheetEuclideanTwoForm fPlus fMinus
    euclideanTwoFormHodgeData.star F = twoSheetEuclideanTwoForm fPlus (-fMinus) ∧
    yangMillsEnergy euclideanTwoFormHodgeData F - topologicalPairing euclideanTwoFormHodgeData F =
      4 * ∑ i : Fin 3, fMinus i ^ 2 ∧
    yangMillsEnergy euclideanTwoFormHodgeData F + topologicalPairing euclideanTwoFormHodgeData F =
      4 * ∑ i : Fin 3, fPlus i ^ 2 ∧
    |topologicalPairing euclideanTwoFormHodgeData F| ≤ yangMillsEnergy euclideanTwoFormHodgeData F ∧
    (yangMillsEnergy euclideanTwoFormHodgeData F = topologicalPairing euclideanTwoFormHodgeData F ↔
      euclideanTwoFormHodgeData.star F = F) ∧
    (euclideanTwoFormHodgeData.star F = F ↔ fMinus = 0) := by
  intro F
  have hDef : ∀ u : Fin 6 → ℝ, euclideanTwoFormHodgeData.inner u u = 0 → u = 0 := by
    intro u hu
    have hu' : ∑ k : Fin 6, u k * u k = 0 := hu
    have hk : ∀ k : Fin 6, u k * u k = 0 := fun k =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (u j))).mp hu' k (Finset.mem_univ k)
    funext k
    exact mul_self_eq_zero.mp (hk k)
  have hStarFlip : euclideanTwoFormHodgeData.star F = twoSheetEuclideanTwoForm fPlus (-fMinus) := by
    funext k
    fin_cases k <;> simp [euclideanTwoFormHodgeData, F, twoSheetEuclideanTwoForm, sub_eq_add_neg]
  have hSub : yangMillsEnergy euclideanTwoFormHodgeData F - topologicalPairing euclideanTwoFormHodgeData F =
      4 * ∑ i : Fin 3, fMinus i ^ 2 := by
    dsimp [yangMillsEnergy, topologicalPairing, euclideanTwoFormHodgeData, F, twoSheetEuclideanTwoForm]
    simp only [Fin.sum_univ_six, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hAdd : yangMillsEnergy euclideanTwoFormHodgeData F + topologicalPairing euclideanTwoFormHodgeData F =
      4 * ∑ i : Fin 3, fPlus i ^ 2 := by
    dsimp [yangMillsEnergy, topologicalPairing, euclideanTwoFormHodgeData, F, twoSheetEuclideanTwoForm]
    simp only [Fin.sum_univ_six, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hIffSD : euclideanTwoFormHodgeData.star F = F ↔ fMinus = 0 := by
    rw [hStarFlip]
    constructor
    · intro hEq
      have h0 := congrFun hEq 0
      have h1 := congrFun hEq 1
      have h2 := congrFun hEq 2
      simp only [F, twoSheetEuclideanTwoForm, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Pi.neg_apply] at h0 h1 h2
      funext i
      fin_cases i
      · dsimp; linarith
      · dsimp; linarith
      · dsimp; linarith
    · intro hZero
      subst hZero
      funext k
      fin_cases k <;> simp [F, twoSheetEuclideanTwoForm]
  refine ⟨hStarFlip, hSub, hAdd, bogomolnyi_bound euclideanTwoFormHodgeData F,
    energy_eq_topologicalPairing_iff_selfDual euclideanTwoFormHodgeData hDef F, hIffSD⟩

/-! ## Layer 4: Inductive Star-Ring Colimit Transport & Unified Synthesis -/

/-- The `4 × 4` upper-sheet projection `P4C := !![1,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,0]` is a
self-adjoint idempotent and transports all `kreinBispinorRep u` operators through arbitrary
star-preserving ring homomorphisms and `CanonicalTwoSheetedInductiveColimit.tailTowerCone`. -/
@[rep_depth transport, capstone]
lemma kreinBispinorRep_colimit_transport
    {B : Type*} [Ring B] [StarRing B]
    (φ : Matrix (Fin 4) (Fin 4) ℂ →+* B)
    (hφStar : ∀ M : Matrix (Fin 4) (Fin 4) ℂ, φ (star M) = star (φ M))
    (u : KreinFrame4) (k m : ℕ) :
    let P4C : Matrix (Fin 4) (Fin 4) ℂ :=
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
    let Cone := tailTowerCone (Matrix (Fin 4) (Fin 4) ℂ)
    let P_k : TowerLevel (Matrix (Fin 4) (Fin 4) ℂ) k := (fun _ => 0, P4C)
    let X_k : TowerLevel (Matrix (Fin 4) (Fin 4) ℂ) k := (fun _ => 0, kreinBispinorRep u)
    let Xstar_k : TowerLevel (Matrix (Fin 4) (Fin 4) ℂ) k := (fun _ => 0, star (kreinBispinorRep u))
    let ψ_m := (stepHomIter Cone k m).toRingHom
    let ι_km := (Cone.toColimit (k + m)).toRingHom
    let ι_k := (Cone.toColimit k).toRingHom
    P4C * P4C = P4C ∧
    star P4C = P4C ∧
    opZig (φ P4C) (φ (kreinBispinorRep u)) * opZig (φ P4C) (φ (kreinBispinorRep u)) = 0 ∧
    opQuadraticCoupling (φ P4C) (φ (kreinBispinorRep u)) (star (φ (kreinBispinorRep u))) =
      φ (opQuadraticCoupling P4C (kreinBispinorRep u) (star (kreinBispinorRep u))) ∧
    ι_km (opQuadraticCoupling (ψ_m P_k) (ψ_m X_k) (ψ_m Xstar_k)) =
      opQuadraticCoupling (ι_k P_k) (ι_k X_k) (ι_k Xstar_k) ∧
    ι_km (opSpinDipole (ψ_m P_k) (ψ_m X_k) (ψ_m Xstar_k)) =
      opSpinDipole (ι_k P_k) (ι_k X_k) (ι_k Xstar_k) := by
  intro P4C Cone P_k X_k Xstar_k ψ_m ι_km ι_k
  have hP : P4C * P4C = P4C := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [P4C, Matrix.mul_apply, Fin.sum_univ_four]
  have hPstar : star P4C = P4C := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [P4C, Matrix.star_apply]
  have hStarHom := star_hom_two_sheeted_operator_identities φ hφStar P4C (kreinBispinorRep u) hP hPstar
  have hInter := starRingHom_intertwines_two_sheeted_operators φ hφStar P4C
    (kreinBispinorRep u) (star (kreinBispinorRep u))
  have hQuad :
      opQuadraticCoupling (φ P4C) (φ (kreinBispinorRep u)) (star (φ (kreinBispinorRep u))) =
        φ (opQuadraticCoupling P4C (kreinBispinorRep u) (star (kreinBispinorRep u))) := by
    rw [← hφStar (kreinBispinorRep u)]
    exact hInter.2.2.2.2.2.1.symm
  have hRG := colimit_renormalization_scale_invariance Cone k m P_k X_k Xstar_k X_k
  exact ⟨hP, hPstar, hStarHom.1, hQuad, hRG.2.1, hRG.2.2.1⟩

/-- Master typed bridge unifying the five repository corridors on their actual Lean owners:
doubled Minkowski/Krein metric pullback (`chiralKreinForm`), `KreinFrame4` chirality and sheet
flip, circular Peirce channel mapping in `SheetAlgebra (Fin 2 → ℂ)`, trace metric and noncommuting
gauge–Higgs curvature splitting, unconditional self-dual Yang–Mills solution & Bogomolnyi
saturation. -/
@[rep_depth transport, capstone]
lemma master_doubled_minkowski_circular_peirce_yang_mills
    (X : CanonicalZorn) (AL AR : Operator (Fin 2 → ℂ)) (fPlus fMinus : Fin 3 → ℝ) :
    let u := lorentzCircularZornToKreinFrame X
    let P := firstSheetProjection (W := Fin 2 → ℂ)
    let Γ := invS P
    let Φp := Matrix.toLin' (kreinChiralPlusWeyl u)
    let Φm := Matrix.toLin' (kreinChiralMinusWeyl u)
    let D := twoSheetKreinConnection AL AR u
    let F_sd := curvatureFromConnection (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))) helicityCircularConnection4
    let F_2 := twoSheetEuclideanTwoForm fPlus fMinus
    chiralKreinForm (E := FourSpace) u u = 2 * wittNorm (coordinateEquiv X) ∧
    (conePlus P (circularSheetRep X) = circularSheetRep (uPlus * X) ∧
     coneMinus P (circularSheetRep X) = circularSheetRep (uMinus * X)) ∧
    Matrix.trace (kreinBispinorRep u * kreinBispinorRep u) =
      2 * (chiralKreinForm (E := FourSpace) u u : ℂ) ∧
    (D * D) + Γ * (D * D) * Γ =
      (2 : ℕ) • !![AL * AL + Φp * Φm, 0;
                   0, Φm * Φp + AR * AR] ∧
    (F_sd ≠ 0 ∧
     covariantDerivative helicityCircularConnection4 0 (matrixHodgeStar chiralHodgeStar4 F_sd) = 0 ∧
     (yangMillsEnergy euclideanTwoFormHodgeData F_2 = topologicalPairing euclideanTwoFormHodgeData F_2 ↔
       fMinus = 0)) := by
  intro u P Γ Φp Φm D F_sd F_2
  have h1 := (chiralKreinForm_lorentzCircularZornToKreinFrame X X).2
  have h2 := circularSheetRep_peirce_channels X
  have h3 := (kreinBispinorRep_metric_trace_and_noncomm u u).2.1
  have h4 := (twoSheetKreinConnection_curvature_and_parity_split AL AR u).2.2.1
  have h5a := helicityCircularConnection4_solves_self_dual_yang_mills
  have h5b := twoSheetBogomolnyi_action_identity fPlus fMinus
  exact ⟨h1, ⟨h2.1, h2.2.1⟩, h3, h4, ⟨h5a.1, h5a.2.2.2.2, h5b.2.2.2.2.1.trans h5b.2.2.2.2.2⟩⟩

end InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills

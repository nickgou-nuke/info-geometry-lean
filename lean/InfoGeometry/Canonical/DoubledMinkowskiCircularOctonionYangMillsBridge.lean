/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.RealDoubledChiralKreinFrame
import InfoGeometry.Canonical.ThermofieldWittSoldering
import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
import InfoGeometry.Lie.SplitOctonionCircularWittForm
import InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge
import InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge
import InfoGeometry.OperatorAlgebra.TetraktysZornYangMillsBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
import InfoGeometry.Canonical.BogomolnyiAlgebraicBoundBridge
import InfoGeometry.Canonical.TwoSheetedYangMillsInductiveColimit
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.NoncommRing

/-!
# Typed Bridge: Doubled Minkowski–Krein Carrier, Circular Split-Octonion Chiral Frames, and Two-Sheeted Yang–Mills Curvature

This module constructs explicit maps and kernel-checked compatibility theorems
unifying the five previously separate corridors on their actual repository owners:

1. **Archetype 1 — Doubled Minkowski–Krein Carrier, `Cl(1,1)` Sheet-Chirality, & `(1,3)` Metric Pullback (`@[rep_depth transport]`)**:
   - Explicitly connects `CanonicalZorn` (`SplitOctonionEllCircularPeirceBasis`) to `KreinFrame4`
     (`RealDoubledChiralKreinFrame`) via both the untwisted equivalence `circularZornToKreinFrame`
     (intertwining `kappa` with `sheetFlip` and `uPlus * X - uMinus * X` with `chirality`) and the
     `(1, 3)` parity-twisted equivalence `lorentzCircularZornToKreinFrame` (pulling back `chiralKreinForm`
     identically to `circularPeircePolar` and `2 * wittNorm`), plus instantiating
     `dualConnectionWithMetric` at `minkowskiEta13 = diag(1, -1, -1, -1)`.
   - Proves the `Cl(1,1)` chiral grading `Γ = invS (firstSheetProjection W)` and sheet-flip involution
     `J = sheetFlipMatrix (Operator W)` laws on `TetraktysZornYangMillsBridge.SheetAlgebra W`.

2. **Archetype 2 — Circular Split-Octonion `2 Poles + 3_+ + 3_-` Peirce Frame (`@[rep_depth transport]`)**:
   Consolidates the genuine split-octonion Peirce absorption laws (`uPlus`, `uMinus`, `rootPlus`,
   `rootMinus`) on `CanonicalZorn` together with the longitudinal pole+channel `2 × 2` block
   and transverse `2 × 2` color block norm identity.

3. **Archetype 3 — Double-Chiral Pauli Soldering Bridge on `ℂ² ⊕ ℂ²` (`@[rep_depth transport]`)**:
   Defines `chiralPlusWeyl`, `chiralMinusWeyl`, `chiralMinusBarWeyl`, `circularSheetRep`, and
   `circularBispinorRep` on `CanonicalZorn`; proves genuine left Peirce projector annihilation,
   exact agreement with `SplitOctonionDoubleChiralSolderingBridge.doubleMinkowskiSolder`,
   the 8-vector circular channel table in `SheetAlgebra (Fin 2 → ℂ)`, noncommutativity of mixed
   chiral channels, the `8D` trace–Witt–Krein metric pullback, and the matched Minkowski Clifford
   anticommutator.

4. **Archetype 4 — Operator-Valued Two-Sheet Gauge–Higgs Connection & Parity Split (`@[rep_depth transport]`)**:
   Constructs `twoSheetGaugeHiggsConnection` inside `SheetAlgebra W` with arbitrary noncommuting
   diagonal gauge potentials `(AL, AR)` and circular Peirce off-diagonal channels, decomposing
   `D * D` under `Γ`-conjugation into intra-sheet curvature and inter-sheet covariant derivatives.

5. **Archetype 5 — Contraction-Built 4D Chiral Hodge Star, Self-Dual Yang–Mills Equations, & Bogomolnyi Saturation (`@[rep_depth transport]`)**:
   Constructs `blade2Coeff` and `lorentzHodgeStar4` / `chiralHodgeStar4` on
   `ExteriorAlgebra ℂ (Fin 4 → ℂ)` directly from `ExteriorContractionOperatorBridge.contractionOp`
   and `ExteriorAlgebra.algebraMapInv`, proves `chiralHodgeStar4` coincides with `genSig` on the
   matched circular connection, exhibits an unconditional helicity-split self-dual Yang–Mills
   solution (`F ≠ 0`, `F 0 0 ≠ F 2 2`, `★ F = F`, `D_A (★ F) = 0`), and establishes full two-sheeted
   Bogomolnyi action saturation in `BogomolnyiAlgebraicBoundBridge`.

6. **Colimit Transport & Master Synthesis (`@[rep_depth transport, capstone]`)**:
   Transports `circularBispinorRep` across arbitrary `StarRingHom`s and
   `CanonicalTwoSheetedInductiveColimit.tailTowerCone`.

*Scope boundary*: All theorems here are finite-dimensional, algebraic, exterior-algebraic, or
star-ring colimit structural theorems. No smooth 4-manifold PDE existence, analytic continuum limit,
or continuum Wightman/Osterwalder–Schrader Yang–Mills mass gap is claimed or proved.
-/

noncomputable section

namespace InfoGeometry.Canonical.DoubledMinkowskiCircularOctonionYangMillsBridge

open scoped ComplexConjugate
open Matrix
open ExteriorAlgebra
open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements
open InfoGeometry.Canonical.RealDoubledChiralKreinFrame
open InfoGeometry.Canonical.ThermofieldWittSoldering
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionCircularWittForm
open InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge
open InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge
open InfoGeometry.Quantum.PauliSoldering
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.OperatorAlgebra.TetraktysZornYangMillsBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge
open InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
open InfoGeometry.Canonical.BogomolnyiAlgebraicBoundBridge
open CanonicalTwoSheetedInductiveColimit

/-! ## Archetype 1: Doubled Minkowski–Krein Carrier, `Cl(1,1)` Sheet-Chirality, & Metric Pullback -/

/-- Untwisted linear equivalence between the 8D split-octonion circular Peirce
carrier `CanonicalZorn` and the doubled chiral Krein frame `KreinFrame4`. -/
@[rep_depth transport]
def circularZornToKreinFrame : CanonicalZorn ≃ₗ[ℝ] KreinFrame4 :=
  coordinateEquiv.trans wittSolderingEquiv.symm

-- theorem-class: lower bridge identification
/-- Applying `wittSoldering` recovers circular Peirce coordinates from `circularZornToKreinFrame`. -/
@[rep_depth transport]
theorem wittSoldering_circularZornToKreinFrame (X : CanonicalZorn) :
    wittSoldering (circularZornToKreinFrame X) = coordinateEquiv X := by
  change wittSolderingEquiv (wittSolderingEquiv.symm (coordinateEquiv X)) = coordinateEquiv X
  exact wittSolderingEquiv.apply_symm_apply (coordinateEquiv X)

private lemma frameBasis_apply_eq (a b : Fin 4) :
    frameBasis a b = if b = a then 1 else 0 := by
  simp [frameBasis, EuclideanSpace.basisFun_apply, PiLp.single_apply]

private theorem circularZornToKreinFrame_negative_frame (i : Fin 4) :
    circularZornToKreinFrame (frame (Fin.addNat i 4)) = minusFrame i := by
  apply wittSoldering_injective
  have hleft : wittSoldering (circularZornToKreinFrame (frame (Fin.addNat i 4))) =
      coordinateEquiv (frame (Fin.addNat i 4)) := by
    change wittSolderingEquiv (wittSolderingEquiv.symm
      (coordinateEquiv (frame (Fin.addNat i 4)))) = _
    exact wittSolderingEquiv.apply_symm_apply _
  rw [hleft, coordinateEquiv_apply_frame]
  change Pi.single (Fin.addNat i 4) 1 =
    wittSoldering (to_doubled 0 (frameBasis i) : DoubledSpace V4)
  funext j
  rw [wittSoldering_to_doubled_apply]
  by_cases hj : j.val < 4
  · simp only [hj, ↓reduceDIte, Pi.single_apply]
    split_ifs with h
    · exfalso
      have hv := congrArg Fin.val h
      simp only [Fin.val_addNat] at hv
      omega
    · rfl
  · have hjLower : 4 ≤ j.val := Nat.le_of_not_gt hj
    let j' : Fin 4 := ⟨j.val - 4, by omega⟩
    have hcond : j' = i ↔ j = Fin.addNat i 4 := by
      constructor
      · intro h
        have hv := congrArg Fin.val h
        simp only [j'] at hv
        apply Fin.ext
        simp only [Fin.val_addNat]
        omega
      · intro h
        apply Fin.ext
        have hv := congrArg Fin.val h
        simp only [Fin.val_addNat] at hv
        change j.val - 4 = i.val
        omega
    simp only [hj, ↓reduceDIte, frameBasis_apply_eq]
    by_cases h : (⟨j.val - 4, by omega⟩ : Fin 4) = i
    · have h' := hcond.mp h
      simp [h, h']
    · have h' : j ≠ Fin.addNat i 4 := fun heq => h (hcond.mpr heq)
      simp [h, h']

-- theorem-class: lower bridge identification
/-- Positive circular Peirce vectors `frame 0..3` map to `plusFrame 0..3`, and
negative circular Peirce vectors `frame 4..7` map to `minusFrame 0..3`. -/
@[rep_depth transport]
theorem circularZornToKreinFrame_frame_blocks (i : Fin 4) :
    circularZornToKreinFrame (frame (Fin.castAdd 4 i)) = plusFrame i ∧
    circularZornToKreinFrame (frame (Fin.addNat i 4)) = minusFrame i := by
  constructor
  · apply wittSoldering_injective
    rw [wittSoldering_circularZornToKreinFrame, coordinateEquiv_apply_frame]
    ext j
    rw [plusFrame, wittSoldering_to_doubled_apply, Pi.single_apply]
    by_cases hj : j.val < 4
    · simp only [hj, ↓reduceDIte, frameBasis_apply_eq, Fin.ext_iff, Fin.coe_castAdd]
    · simp only [hj, ↓reduceDIte, PiLp.zero_apply]
      split_ifs with h
      · exfalso
        have hlt := Fin.ext_iff.mp h
        simp only [Fin.coe_castAdd] at hlt
        omega
      · rfl
  · exact circularZornToKreinFrame_negative_frame i

private lemma uPlus_mul_frame_pos (i : Fin 4) :
    uPlus * frame (Fin.castAdd 4 i) = frame (Fin.castAdd 4 i) := by
  fin_cases i <;> exact uPlus_mul_frame _

private lemma uPlus_mul_frame_neg (i : Fin 4) :
    uPlus * frame (Fin.addNat i 4) = 0 := by
  fin_cases i <;> exact uPlus_mul_frame _

private lemma uMinus_mul_frame_pos (i : Fin 4) :
    uMinus * frame (Fin.castAdd 4 i) = 0 := by
  fin_cases i <;> exact uMinus_mul_frame _

private lemma uMinus_mul_frame_neg (i : Fin 4) :
    uMinus * frame (Fin.addNat i 4) = frame (Fin.addNat i 4) := by
  fin_cases i <;> exact uMinus_mul_frame _

-- theorem-class: transport lemma
/-- The circular sector swap `kappa` intertwines with `sheetFlip` on `KreinFrame4`. -/
@[rep_depth transport]
theorem circularZornToKreinFrame_intertwines_kappa_sheetFlip (X : CanonicalZorn) :
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

-- theorem-class: transport lemma
/-- Split-octonion left Peirce grading `uPlus * X - uMinus * X` intertwines
with `chirality` on `KreinFrame4`. -/
@[rep_depth transport]
theorem circularZornToKreinFrame_intertwines_peirce_chirality (X : CanonicalZorn) :
    circularZornToKreinFrame (uPlus * X - uMinus * X) =
      chirality (circularZornToKreinFrame X) := by
  have hBasis : ∀ i : Fin 8,
      circularZornToKreinFrame (uPlus * frame i - uMinus * frame i) =
        chirality (circularZornToKreinFrame (frame i)) := by
    intro i
    by_cases hi : i.val < 4
    · have hiEq : i = Fin.castAdd 4 ⟨i.val, hi⟩ := Fin.ext rfl
      rw [hiEq, uPlus_mul_frame_pos, uMinus_mul_frame_pos, sub_zero,
        (circularZornToKreinFrame_frame_blocks _).1, chirality_plusFrame]
    · have hiEq : i = Fin.addNat ⟨i.val - 4, by omega⟩ 4 := Fin.ext (by dsimp; omega)
      rw [hiEq, uPlus_mul_frame_neg, uMinus_mul_frame_neg, zero_sub, map_neg,
        (circularZornToKreinFrame_frame_blocks _).2, chirality_minusFrame]
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
@[rep_depth transport]
def lorentzSheetParity : FourSpace ≃ₗ[ℝ] FourSpace where
  toFun x := WithLp.toLp 2 ![x 0, -x 1, -x 2, -x 3]
  invFun x := WithLp.toLp 2 ![x 0, -x 1, -x 2, -x 3]
  left_inv x := by
    ext i
    fin_cases i <;> simp
  right_inv x := by
    ext i
    fin_cases i <;> simp
  map_add' x y := by
    ext i
    fin_cases i <;> simp [add_comm]
  map_smul' r x := by
    ext i
    fin_cases i <;> simp

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

/-- Diagonal `(1, 3)` Lorentz metric matrix on `Fin 4`. -/
@[rep_depth transport]
def minkowskiEta13 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, -1, -1, -1]

/-- Parity-twisted Krein equivalence sending the negative circular sector through
`lorentzSheetParity` so that `chiralKreinForm` pulls back identically to `circularPeircePolar`. -/
@[rep_depth transport]
def lorentzCircularZornToKreinFrame : CanonicalZorn ≃ₗ[ℝ] KreinFrame4 :=
  circularZornToKreinFrame.trans lorentzTwistKrein

-- theorem-class: constructive endpoint
/-- Exact bilinear metric pullback and quadratic Witt norm pullback:
the `(1, 3)` parity-twisted `chiralKreinForm` equals `circularPeircePolar` identically
and halves to `wittNorm` on the diagonal. -/
@[rep_depth transport]
theorem chiralKreinForm_lorentzCircularZornToKreinFrame (X Y : CanonicalZorn) :
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
    have hFst : ∀ (C : CanonicalZorn) (i : Fin 4),
        (WithLp.fst (circularZornToKreinFrame C)) i = coordinateEquiv C ⟨i.val, by omega⟩ := by
      intro C i
      have hi := congrFun (wittSoldering_circularZornToKreinFrame C) ⟨i.val, by omega⟩
      simpa [wittSoldering, i.isLt] using hi
    have hSnd : ∀ (C : CanonicalZorn) (i : Fin 4),
        (WithLp.snd (circularZornToKreinFrame C)) i = coordinateEquiv C ⟨i.val + 4, by omega⟩ := by
      intro C i
      have hi := congrFun (wittSoldering_circularZornToKreinFrame C) ⟨i.val + 4, by omega⟩
      have hge : ¬ (i.val + 4 < 4) := by omega
      simpa [wittSoldering, hge] using hi
    have hP0 : ∀ C : CanonicalZorn,
        (lorentzSheetParity (WithLp.snd (circularZornToKreinFrame C))) 0 = coordinateEquiv C 4 := fun C =>
      hSnd C 0
    have hP1 : ∀ C : CanonicalZorn,
        (lorentzSheetParity (WithLp.snd (circularZornToKreinFrame C))) 1 = -coordinateEquiv C 5 := by
      intro C
      change -(WithLp.snd (circularZornToKreinFrame C) 1) = -coordinateEquiv C 5
      rw [hSnd C 1]
      rfl
    have hP2 : ∀ C : CanonicalZorn,
        (lorentzSheetParity (WithLp.snd (circularZornToKreinFrame C))) 2 = -coordinateEquiv C 6 := by
      intro C
      change -(WithLp.snd (circularZornToKreinFrame C) 2) = -coordinateEquiv C 6
      rw [hSnd C 2]
      rfl
    have hP3 : ∀ C : CanonicalZorn,
        (lorentzSheetParity (WithLp.snd (circularZornToKreinFrame C))) 3 = -coordinateEquiv C 7 := by
      intro C
      change -(WithLp.snd (circularZornToKreinFrame C) 3) = -coordinateEquiv C 7
      rw [hSnd C 3]
      rfl
    dsimp only [lorentzCircularZornToKreinFrame, LinearEquiv.trans_apply, lorentzTwistKrein,
      LinearEquiv.coe_mk]
    rw [chiralKreinForm_to_doubled, PiLp.inner_apply, PiLp.inner_apply,
      Fin.sum_univ_four, Fin.sum_univ_four]
    simp only [RCLike.inner_apply, conj_trivial]
    rw [hFst A 0, hFst A 1, hFst A 2, hFst A 3,
      hFst B 0, hFst B 1, hFst B 2, hFst B 3,
      hP0 A, hP1 A, hP2 A, hP3 A,
      hP0 B, hP1 B, hP2 B, hP3 B]
    simp only [circularPeircePolar]
    ring
  refine ⟨hPair X Y, ?_⟩
  rw [hPair X X]
  simp [circularPeircePolar, wittNorm]
  ring

-- theorem-class: constructive endpoint
/-- Determinant, unit invertibility, induced Krein graph metric, and unique
metric-compatible dual spin connection for `minkowskiEta13`. -/
@[rep_depth transport]
theorem minkowskiEta13_metric_and_dualConnection_properties
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

/-- Sheet-flip involution `!![0, 1; 1, 0]` on two-sheeted `2 × 2` operator blocks over any ring `B`. -/
@[rep_depth transport]
def sheetFlipMatrix (B : Type*) [Ring B] : Matrix (Fin 2) (Fin 2) B :=
  !![0, 1; 1, 0]

/-- Second-sheet Peirce projector `1 - firstSheetProjection W` on `SheetAlgebra W`. -/
@[rep_depth transport]
def secondSheetProjection (W : Type*) [AddCommGroup W] [Module ℂ W] : SheetAlgebra W :=
  1 - firstSheetProjection W

private lemma mat2_one {B : Type*} [Zero B] [One B] :
    (1 : Matrix (Fin 2) (Fin 2) B) = !![1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

private lemma mat2_add {B : Type*} [Add B] (a b c d e f g h : B) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) B) + !![e, f; g, h] =
      !![a + e, b + f; c + g, d + h] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private lemma mat2_sub {B : Type*} [Sub B] (a b c d e f g h : B) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) B) - !![e, f; g, h] =
      !![a - e, b - f; c - g, d - h] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private lemma mat2_mul {B : Type*} [Ring B] (a b c d e f g h : B) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) B) * !![e, f; g, h] =
      !![a * e + b * g, a * f + b * h; c * e + d * g, c * f + d * h] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

-- theorem-class: constructive endpoint
/-- `Cl(1,1)` chiral grading and pole-projector resolution inside
`TetraktysZornYangMillsBridge.SheetAlgebra W`:
`Γ = invS (firstSheetProjection W)` and `J = sheetFlipMatrix (Operator W)` satisfy
`Γ² = 1`, `J² = 1`, `Γ J + J Γ = 0`, `J P₊ J = P₋`, `J P₋ J = P₊`, and complete orthogonal
idempotency with `P₊ - P₋ = Γ`. -/
@[rep_depth transport]
theorem sheetAlgebra_cl11_chirality_and_pole_laws
    (W : Type*) [AddCommGroup W] [Module ℂ W] :
    let P_plus := firstSheetProjection (W := W)
    let P_minus := secondSheetProjection (W := W)
    let Γ := invS P_plus
    let J := sheetFlipMatrix (Operator W)
    Γ = !![1, 0; 0, -1] ∧
    Γ * Γ = 1 ∧
    J * J = 1 ∧
    Γ * J + J * Γ = 0 ∧
    J * P_plus * J = P_minus ∧
    J * P_minus * J = P_plus ∧
    P_plus * P_plus = P_plus ∧
    P_minus * P_minus = P_minus ∧
    P_plus * P_minus = 0 ∧
    P_plus + P_minus = 1 ∧
    P_plus - P_minus = Γ := by
  intro P_plus P_minus Γ J
  have hP0 : P_plus = !![1, 0; 0, 0] := rfl
  have hPm : P_minus = !![0, 0; 0, 1] := by
    dsimp [P_minus, secondSheetProjection, P_plus, firstSheetProjection]
    rw [mat2_one, mat2_sub]
    simp only [sub_self, sub_zero, zero_sub]
    rfl
  have hJ : J = !![0, 1; 1, 0] := rfl
  have hG : Γ = !![1, 0; 0, -1] := by
    dsimp [Γ, invS, P_plus, firstSheetProjection]
    rw [mat2_one, mat2_sub]
    simp only [sub_self, sub_zero, zero_sub, sub_neg_eq_add, add_zero]
    rw [mat2_sub]
    simp only [sub_zero, zero_sub]
    rfl
  refine ⟨hG, ?_, ?_, ?_, ?_, ?_, firstSheetProjection_idempotent, ?_, ?_, ?_, ?_⟩
  · rw [hG, mat2_mul, mat2_one]
    simp only [one_mul, mul_zero, add_zero, zero_mul, neg_mul, mul_neg, neg_neg, zero_add]
  · rw [hJ, mat2_mul, mat2_one]
    simp only [zero_mul, one_mul, zero_add, mul_zero, add_zero]
  · rw [hG, hJ, mat2_mul, mat2_mul, mat2_add]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.zero_apply]
  · rw [hJ, hP0, hPm, mat2_mul, mat2_mul]
    simp only [zero_mul, one_mul, mul_zero, add_zero, zero_add]
  · rw [hJ, hPm, hP0, mat2_mul, mat2_mul]
    simp only [zero_mul, one_mul, mul_zero, add_zero, zero_add]
  · rw [hPm, mat2_mul]
    simp only [zero_mul, add_zero, mul_zero, one_mul, zero_add]
  · rw [hP0, hPm, mat2_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.zero_apply]
  · rw [hP0, hPm, mat2_add, mat2_one]
    simp only [add_zero, zero_add]
  · rw [hP0, hPm, hG, mat2_sub]
    simp only [sub_zero, zero_sub]

/-! ## Archetypes 2 & 3: Circular Split-Octonion Peirce Frame & Double-Chiral Pauli Soldering -/

/-- Longitudinal `2 × 2` pole-plus-channel block `!![a, u₁⁺; v₁⁻, b]` extracted from
`CanonicalZorn` in the circular Peirce basis. -/
@[rep_depth transport]
def longitudinalPoleBlock (X : CanonicalZorn) : Matrix (Fin 2) (Fin 2) ℝ :=
  let c := coordinateEquiv X
  !![c 0, c 1; c 5, c 4]

/-- Adjugate `2 × 2` longitudinal block `!![b, -u₁⁺; -v₁⁻, a]` of `CanonicalZorn`. -/
@[rep_depth transport]
def longitudinalPoleAdjugate (X : CanonicalZorn) : Matrix (Fin 2) (Fin 2) ℝ :=
  let c := coordinateEquiv X
  !![c 4, -c 1; -c 5, c 0]

/-- Transverse color-channel `2 × 2` block `!![u₂⁺, u₃⁺; -v₃⁻, v₂⁻]` of `CanonicalZorn`. -/
@[rep_depth transport]
def transverseColorBlock (X : CanonicalZorn) : Matrix (Fin 2) (Fin 2) ℝ :=
  let c := coordinateEquiv X
  !![c 2, c 3; -c 7, c 6]

-- theorem-class: constructive endpoint
/-- Connects the actual `CanonicalZorn` `2 Poles + 3_+ + 3_-` Peirce multiplication table
directly to the longitudinal/transverse `2 × 2` Clifford contraction and split-octonion norm. -/
@[rep_depth transport]
theorem canonicalZorn_circular_peirce_and_longitudinal_transverse_bridge
    (X : CanonicalZorn) (a : Fin 3) :
    uPlus * uPlus = uPlus ∧
    uMinus * uMinus = uMinus ∧
    uPlus * uMinus = 0 ∧
    uPlus + uMinus = 1 ∧
    uPlus * rootPlus a = rootPlus a ∧
    rootPlus a * uMinus = rootPlus a ∧
    uMinus * rootPlus a = 0 ∧
    uMinus * rootMinus a = rootMinus a ∧
    rootMinus a * uPlus = rootMinus a ∧
    uPlus * rootMinus a = 0 ∧
    rootPlus a * rootMinus a = uPlus ∧
    rootMinus a * rootPlus a = uMinus ∧
    longitudinalPoleBlock X * longitudinalPoleAdjugate X =
      (longitudinalPoleBlock X).det • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    Matrix.trace (longitudinalPoleBlock X * longitudinalPoleAdjugate X) =
      2 * (longitudinalPoleBlock X).det ∧
    wittNorm (coordinateEquiv X) =
      (longitudinalPoleBlock X).det - (transverseColorBlock X).det := by
  refine ⟨uPlus_sq, uMinus_sq, uPlus_mul_uMinus, uPlus_add_uMinus,
    uPlus_mul_rootPlus a, rootPlus_mul_uMinus a, uMinus_mul_rootPlus a,
    uMinus_mul_rootMinus a, rootMinus_mul_uPlus a, uPlus_mul_rootMinus a,
    rootPlus_mul_rootMinus a, rootMinus_mul_rootPlus a, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [longitudinalPoleBlock, longitudinalPoleAdjugate, Matrix.det_fin_two,
        Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · simp [longitudinalPoleBlock, longitudinalPoleAdjugate, Matrix.det_fin_two,
      Matrix.trace, Fin.sum_univ_two]
    ring
  · simp [wittNorm, longitudinalPoleBlock, transverseColorBlock, Matrix.det_fin_two]
    ring

private def solderPlusCoordLinear : (Fin 8 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun c := pauliSolder2x2 (c 0) (c 1) (c 2) (c 3)
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliSolder2x2, solder_explicit, Pi.add_apply] <;> ring
  map_smul' r x := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliSolder2x2, solder_explicit, Pi.smul_apply, smul_eq_mul] <;> ring

private def solderMinusCoordLinear : (Fin 8 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun c := pauliSolder2x2 (c 4) (c 5) (c 6) (c 7)
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliSolder2x2, solder_explicit, Pi.add_apply] <;> ring
  map_smul' r x := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliSolder2x2, solder_explicit, Pi.smul_apply, smul_eq_mul] <;> ring

private def solderMinusBarCoordLinear : (Fin 8 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun c := pauliSolder2x2 (c 4) (-c 5) (-c 6) (-c 7)
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliSolder2x2, solder_explicit, Pi.add_apply] <;> ring
  map_smul' r x := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliSolder2x2, solder_explicit, Pi.smul_apply, smul_eq_mul] <;> ring

/-- Upper chiral `2 × 2` Pauli soldering representation on the positive circular
Peirce coordinates `(uPlus, rootPlus 0..2)`. -/
@[rep_depth transport]
def chiralPlusWeyl : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  solderPlusCoordLinear.comp coordinateEquiv.toLinearMap

/-- Lower chiral `2 × 2` Pauli soldering representation on the negative circular
Peirce coordinates `(uMinus, rootMinus 0..2)`. -/
@[rep_depth transport]
def chiralMinusWeyl : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  solderMinusCoordLinear.comp coordinateEquiv.toLinearMap

/-- Space-reflected (conjugate Weyl cofactor) lower chiral `2 × 2` representation
on `(uMinus, -rootMinus 0..2)`. -/
@[rep_depth transport]
def chiralMinusBarWeyl : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  solderMinusBarCoordLinear.comp coordinateEquiv.toLinearMap

private lemma pauliSolder2x2_zero : pauliSolder2x2 0 0 0 0 = 0 := by
  ext r s
  fin_cases r <;> fin_cases s <;> simp [pauliSolder2x2, solder_explicit]

-- theorem-class: constructive endpoint
/-- Split-octonion left Peirce projectors `uPlus` and `uMinus` select and annihilate
the complementary chiral Weyl blocks `chiralPlusWeyl`, `chiralMinusWeyl`, and `chiralMinusBarWeyl`. -/
@[rep_depth transport]
theorem chiralWeyl_peirce_sector_selection (X : CanonicalZorn) :
    chiralPlusWeyl (uPlus * X) = chiralPlusWeyl X ∧
    chiralPlusWeyl (uMinus * X) = 0 ∧
    chiralMinusWeyl (uMinus * X) = chiralMinusWeyl X ∧
    chiralMinusWeyl (uPlus * X) = 0 ∧
    chiralMinusBarWeyl (uMinus * X) = chiralMinusBarWeyl X ∧
    chiralMinusBarWeyl (uPlus * X) = 0 ∧
    chiralPlusWeyl (coordinateEquiv.symm (kappa (coordinateEquiv X))) = chiralMinusWeyl X := by
  have hP1 : ∀ f : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ,
      (∀ i : Fin 8, f (uPlus * frame i) = f (frame i)) →
      f (uPlus * X) = f X := by
    intro f hf
    let L : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
      f.comp (leftMultiplication uPlus)
    have hEq : L = f := by
      apply circularPeirceBasis.ext
      intro i
      change f (uPlus * circularPeirceBasis i) = f (circularPeirceBasis i)
      rw [circularPeirceBasis_apply]
      exact hf i
    exact LinearMap.congr_fun hEq X
  have hP0 : ∀ f : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ,
      (∀ i : Fin 8, f (uPlus * frame i) = 0) →
      f (uPlus * X) = 0 := by
    intro f hf
    let L : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
      f.comp (leftMultiplication uPlus)
    have hEq : L = 0 := by
      apply circularPeirceBasis.ext
      intro i
      change f (uPlus * circularPeirceBasis i) = 0
      rw [circularPeirceBasis_apply]
      exact hf i
    exact LinearMap.congr_fun hEq X
  have hM1 : ∀ f : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ,
      (∀ i : Fin 8, f (uMinus * frame i) = f (frame i)) →
      f (uMinus * X) = f X := by
    intro f hf
    let L : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
      f.comp (leftMultiplication uMinus)
    have hEq : L = f := by
      apply circularPeirceBasis.ext
      intro i
      change f (uMinus * circularPeirceBasis i) = f (circularPeirceBasis i)
      rw [circularPeirceBasis_apply]
      exact hf i
    exact LinearMap.congr_fun hEq X
  have hM0 : ∀ f : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ,
      (∀ i : Fin 8, f (uMinus * frame i) = 0) →
      f (uMinus * X) = 0 := by
    intro f hf
    let L : CanonicalZorn →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
      f.comp (leftMultiplication uMinus)
    have hEq : L = 0 := by
      apply circularPeirceBasis.ext
      intro i
      change f (uMinus * circularPeirceBasis i) = 0
      rw [circularPeirceBasis_apply]
      exact hf i
    exact LinearMap.congr_fun hEq X
  have hPlusNeg : ∀ j : Fin 4, chiralPlusWeyl (frame (Fin.addNat j 4)) = 0 := by
    intro j
    dsimp only [chiralPlusWeyl, LinearMap.comp_apply, LinearEquiv.coe_coe,
      solderPlusCoordLinear, LinearMap.coe_mk, AddHom.coe_mk]
    have hc : ∀ k : Fin 4, coordinateEquiv (frame (Fin.addNat j 4)) (Fin.castAdd 4 k) = 0 := by
      intro k
      rw [coordinateEquiv_apply_frame, Pi.single_apply]
      split_ifs with h
      · exfalso
        have heq := Fin.ext_iff.mp h
        simp only [Fin.coe_castAdd, Fin.coe_addNat] at heq
        omega
      · rfl
    rw [hc 0, hc 1, hc 2, hc 3, pauliSolder2x2_zero]
  have hMinusPos : ∀ j : Fin 4, chiralMinusWeyl (frame (Fin.castAdd 4 j)) = 0 := by
    intro j
    dsimp only [chiralMinusWeyl, LinearMap.comp_apply, LinearEquiv.coe_coe,
      solderMinusCoordLinear, LinearMap.coe_mk, AddHom.coe_mk]
    have hc : ∀ k : Fin 4, coordinateEquiv (frame (Fin.castAdd 4 j)) (Fin.addNat k 4) = 0 := by
      intro k
      rw [coordinateEquiv_apply_frame, Pi.single_apply]
      split_ifs with h
      · exfalso
        have heq := Fin.ext_iff.mp h
        simp only [Fin.coe_castAdd, Fin.coe_addNat] at heq
        omega
      · rfl
    rw [hc 0, hc 1, hc 2, hc 3, pauliSolder2x2_zero]
  have hMinusBarPos : ∀ j : Fin 4, chiralMinusBarWeyl (frame (Fin.castAdd 4 j)) = 0 := by
    intro j
    dsimp only [chiralMinusBarWeyl, LinearMap.comp_apply, LinearEquiv.coe_coe,
      solderMinusBarCoordLinear, LinearMap.coe_mk, AddHom.coe_mk]
    have hc : ∀ k : Fin 4, coordinateEquiv (frame (Fin.castAdd 4 j)) (Fin.addNat k 4) = 0 := by
      intro k
      rw [coordinateEquiv_apply_frame, Pi.single_apply]
      split_ifs with h
      · exfalso
        have heq := Fin.ext_iff.mp h
        simp only [Fin.coe_castAdd, Fin.coe_addNat] at heq
        omega
      · rfl
    rw [hc 0, hc 1, hc 2, hc 3, neg_zero, pauliSolder2x2_zero]
  refine ⟨hP1 chiralPlusWeyl ?_, hM0 chiralPlusWeyl ?_,
    hM1 chiralMinusWeyl ?_, hP0 chiralMinusWeyl ?_,
    hM1 chiralMinusBarWeyl ?_, hP0 chiralMinusBarWeyl ?_, ?_⟩
  · intro i
    by_cases hi : i.val < 4
    · have hiEq : i = Fin.castAdd 4 ⟨i.val, hi⟩ := Fin.ext rfl
      rw [hiEq, uPlus_mul_frame_pos]
    · have hiEq : i = Fin.addNat ⟨i.val - 4, by omega⟩ 4 := Fin.ext (by dsimp; omega)
      rw [hiEq, uPlus_mul_frame_neg, map_zero, hPlusNeg]
  · intro i
    by_cases hi : i.val < 4
    · have hiEq : i = Fin.castAdd 4 ⟨i.val, hi⟩ := Fin.ext rfl
      rw [hiEq, uMinus_mul_frame_pos, map_zero]
    · have hiEq : i = Fin.addNat ⟨i.val - 4, by omega⟩ 4 := Fin.ext (by dsimp; omega)
      rw [hiEq, uMinus_mul_frame_neg, hPlusNeg]
  · intro i
    by_cases hi : i.val < 4
    · have hiEq : i = Fin.castAdd 4 ⟨i.val, hi⟩ := Fin.ext rfl
      rw [hiEq, uMinus_mul_frame_pos, map_zero, hMinusPos]
    · have hiEq : i = Fin.addNat ⟨i.val - 4, by omega⟩ 4 := Fin.ext (by dsimp; omega)
      rw [hiEq, uMinus_mul_frame_neg]
  · intro i
    by_cases hi : i.val < 4
    · have hiEq : i = Fin.castAdd 4 ⟨i.val, hi⟩ := Fin.ext rfl
      rw [hiEq, uPlus_mul_frame_pos, hMinusPos]
    · have hiEq : i = Fin.addNat ⟨i.val - 4, by omega⟩ 4 := Fin.ext (by dsimp; omega)
      rw [hiEq, uPlus_mul_frame_neg, map_zero]
  · intro i
    by_cases hi : i.val < 4
    · have hiEq : i = Fin.castAdd 4 ⟨i.val, hi⟩ := Fin.ext rfl
      rw [hiEq, uMinus_mul_frame_pos, map_zero, hMinusBarPos]
    · have hiEq : i = Fin.addNat ⟨i.val - 4, by omega⟩ 4 := Fin.ext (by dsimp; omega)
      rw [hiEq, uMinus_mul_frame_neg]
  · intro i
    by_cases hi : i.val < 4
    · have hiEq : i = Fin.castAdd 4 ⟨i.val, hi⟩ := Fin.ext rfl
      rw [hiEq, uPlus_mul_frame_pos, hMinusBarPos]
    · have hiEq : i = Fin.addNat ⟨i.val - 4, by omega⟩ 4 := Fin.ext (by dsimp; omega)
      rw [hiEq, uPlus_mul_frame_neg, map_zero]
  · dsimp [chiralPlusWeyl, chiralMinusWeyl, solderPlusCoordLinear, solderMinusCoordLinear]
    simp only [coordinateEquiv.apply_symm_apply, kappa]
    rfl

-- theorem-class: lower bridge identification
/-- Compatibility with `SplitOctonionDoubleChiralSolderingBridge.doubleMinkowskiSolder`
and its determinant difference readout on the `(1,3) ⊕ (3,1)` fixed/anti-fixed projections. -/
@[rep_depth transport]
theorem doubleMinkowskiSolder_compatibility (t x1 x2 x3 tau y1 y2 y3 : ℝ) :
    let X : CanonicalZorn := coordinateEquiv.symm (symmSection t x1 x2 x3 + antiSection tau y1 y2 y3)
    let Xsym : CanonicalZorn :=
      (1 / 2 : ℝ) • (X + coordinateEquiv.symm (kappa (coordinateEquiv X)))
    let Xanti : CanonicalZorn :=
      (1 / 2 : ℝ) • (X - coordinateEquiv.symm (kappa (coordinateEquiv X)))
    Matrix.fromBlocks (chiralPlusWeyl Xsym) 0 0 (chiralPlusWeyl Xanti) =
      doubleMinkowskiSolder t x1 x2 x3 tau y1 y2 y3 ∧
    (chiralPlusWeyl Xsym).det - (chiralPlusWeyl Xanti).det =
      (wittNorm (coordinateEquiv X) : ℂ) := by
  intro X Xsym Xanti
  have hcSym : ∀ k : Fin 8, coordinateEquiv Xsym k = symmSection t x1 x2 x3 k := by
    intro k
    simp only [Xsym, X, map_smul, map_add, LinearEquiv.apply_symm_apply, Pi.smul_apply,
      Pi.add_apply, smul_eq_mul]
    fin_cases k <;> simp [symmSection, antiSection, kappa] <;> ring
  have hcAnti : ∀ k : Fin 8, coordinateEquiv Xanti k = antiSection tau y1 y2 y3 k := by
    intro k
    simp only [Xanti, X, map_smul, map_sub, LinearEquiv.apply_symm_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    fin_cases k <;> simp [symmSection, antiSection, kappa] <;> ring
  have hPlusSym : chiralPlusWeyl Xsym = pauliSolder2x2 t x1 x2 x3 := by
    dsimp [chiralPlusWeyl, solderPlusCoordLinear]
    rw [hcSym 0, hcSym 1, hcSym 2, hcSym 3]
    simp [symmSection]
  have hPlusAnti : chiralPlusWeyl Xanti = pauliSolder2x2 tau y1 y2 y3 := by
    dsimp [chiralPlusWeyl, solderPlusCoordLinear]
    rw [hcAnti 0, hcAnti 1, hcAnti 2, hcAnti 3]
    simp [antiSection]
  rw [hPlusSym, hPlusAnti]
  refine ⟨rfl, ?_⟩
  rw [doubleMinkowskiSolder_det_diff, show coordinateEquiv X = symmSection t x1 x2 x3 + antiSection tau y1 y2 y3 from
    coordinateEquiv.apply_symm_apply _]

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
    · ext v k
      simp [Matrix.toLin'_apply, Complex.real_smul]
    · ext v k
      simp [Matrix.toLin'_apply, Complex.real_smul]
    · simp

private def bispinorFromBlocksLinear :
    (Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ) →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℂ where
  toFun p :=
    !![0, 0, p.1 0 0, p.1 0 1;
       0, 0, p.1 1 0, p.1 1 1;
       p.2 0 0, p.2 0 1, 0, 0;
       p.2 1 0, p.2 1 1, 0, 0]
  map_add' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_smul' r a := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.real_smul]

/-- Off-diagonal chiral representation of `CanonicalZorn` in `TetraktysZornYangMillsBridge.SheetAlgebra (Fin 2 → ℂ)`. -/
@[rep_depth transport]
def circularSheetRep : CanonicalZorn →ₗ[ℝ] SheetAlgebra (Fin 2 → ℂ) :=
  sheetFromBlocksLinear.comp (chiralPlusWeyl.prod chiralMinusBarWeyl)

/-- Explicit `4 × 4` block bispinor matrix realization of `CanonicalZorn`
with `chiralPlusWeyl X` in the upper-right block and `chiralMinusBarWeyl X` in the lower-left block. -/
@[rep_depth transport]
def circularBispinorRep : CanonicalZorn →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℂ :=
  bispinorFromBlocksLinear.comp (chiralPlusWeyl.prod chiralMinusBarWeyl)

private lemma circularSheetRep_apply (X : CanonicalZorn) :
    circularSheetRep X =
      !![0, Matrix.toLin' (chiralPlusWeyl X); Matrix.toLin' (chiralMinusBarWeyl X), 0] := rfl

private lemma sheet_conePlus (A B : Operator (Fin 2 → ℂ)) :
    conePlus (firstSheetProjection (W := Fin 2 → ℂ)) !![0, A; B, 0] = !![0, A; 0, 0] := by
  dsimp only [conePlus, firstSheetProjection]
  rw [mat2_one, mat2_sub]
  simp only [sub_self, sub_zero, zero_sub]
  rw [mat2_mul, mat2_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> (dsimp; noncomm_ring)

private lemma sheet_coneMinus (A B : Operator (Fin 2 → ℂ)) :
    coneMinus (firstSheetProjection (W := Fin 2 → ℂ)) !![0, A; B, 0] = !![0, 0; B, 0] := by
  dsimp only [coneMinus, firstSheetProjection]
  rw [mat2_one, mat2_sub]
  simp only [sub_self, sub_zero, zero_sub]
  rw [mat2_mul, mat2_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> (dsimp; noncomm_ring)

private lemma sheet_genPhi (A B : Operator (Fin 2 → ℂ)) :
    genPhi (firstSheetProjection (W := Fin 2 → ℂ)) !![0, A; B, 0] !![0, A; B, 0] = !![0, A; B, 0] := by
  rw [genPhi, sheet_conePlus, sheet_coneMinus, mat2_add]
  simp only [add_zero, zero_add]

private lemma chiralPlusWeyl_coord_val (X : CanonicalZorn) :
    let c := coordinateEquiv X
    chiralPlusWeyl X = pauliSolder2x2 (c 0) (c 1) (c 2) (c 3) := rfl

private lemma chiralMinusBarWeyl_coord_val (X : CanonicalZorn) :
    let c := coordinateEquiv X
    chiralMinusBarWeyl X = pauliSolder2x2 (c 4) (-c 5) (-c 6) (-c 7) := rfl

private lemma pauliSolder_eval (t x1 x2 x3 : ℝ) :
    pauliSolder2x2 t x1 x2 x3 =
      !![(t : ℂ) + x3, (x1 : ℂ) - Complex.I * x2;
         (x1 : ℂ) + Complex.I * x2, (t : ℂ) - x3] :=
  solder_explicit t x1 x2 x3

-- theorem-class: constructive endpoint
/-- Peirce corner channels of `circularSheetRep` under `P := firstSheetProjection (W := Fin 2 → ℂ)`:
`frame 0..3` land strictly in `conePlus P`, `frame 4..7` land strictly in `coneMinus P`,
left split-octonion multiplication by `uPlus`/`uMinus` matches `conePlus`/`coneMinus`,
and `genPhi P R R = R`. -/
@[rep_depth transport]
theorem circularSheetRep_peirce_channels_and_tetraktys (X : CanonicalZorn) :
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
  have hSel := chiralWeyl_peirce_sector_selection X
  have hPP : chiralPlusWeyl (uPlus * X) = chiralPlusWeyl X := hSel.1
  have hPM : chiralPlusWeyl (uMinus * X) = 0 := hSel.2.1
  have hMM : chiralMinusBarWeyl (uMinus * X) = chiralMinusBarWeyl X := hSel.2.2.2.2.1
  have hMP : chiralMinusBarWeyl (uPlus * X) = 0 := hSel.2.2.2.2.2.1
  have hConeP : conePlus P (circularSheetRep X) = circularSheetRep (uPlus * X) := by
    rw [circularSheetRep_apply X, circularSheetRep_apply (uPlus * X), hPP, hMP, map_zero]
    exact sheet_conePlus _ _
  have hConeM : coneMinus P (circularSheetRep X) = circularSheetRep (uMinus * X) := by
    rw [circularSheetRep_apply X, circularSheetRep_apply (uMinus * X), hPM, hMM, map_zero]
    exact sheet_coneMinus _ _
  have hPhi : genPhi P (circularSheetRep X) (circularSheetRep X) = circularSheetRep X := by
    rw [circularSheetRep_apply X]
    exact sheet_genPhi _ _
  have hFramePos : ∀ (k : Fin 4) (Mplus : Matrix (Fin 2) (Fin 2) ℂ),
      chiralPlusWeyl (frame (Fin.castAdd 4 k)) = Mplus →
      circularSheetRep (frame (Fin.castAdd 4 k)) = !![0, Matrix.toLin' Mplus; 0, 0] := by
    intro k Mp hMp
    rw [circularSheetRep_apply, hMp]
    have h0 : chiralMinusBarWeyl (frame (Fin.castAdd 4 k)) = 0 := by
      rw [chiralMinusBarWeyl_coord_val, coordinateEquiv_apply_frame]
      have hz : ∀ j : Fin 4, (Pi.single (Fin.castAdd 4 k) (1 : ℝ)) (Fin.addNat j 4) = 0 := by
        intro j
        rw [Pi.single_apply]
        split_ifs with h
        · exfalso
          have heq := Fin.ext_iff.mp h
          simp only [Fin.coe_castAdd, Fin.coe_addNat] at heq
          omega
        · rfl
      rw [hz 0, hz 1, hz 2, hz 3, neg_zero, pauliSolder2x2_zero]
    rw [h0, map_zero]
  have hFrameNeg : ∀ (k : Fin 4) (Mminus : Matrix (Fin 2) (Fin 2) ℂ),
      chiralMinusBarWeyl (frame (Fin.addNat k 4)) = Mminus →
      circularSheetRep (frame (Fin.addNat k 4)) = !![0, 0; Matrix.toLin' Mminus, 0] := by
    intro k Mm hMm
    rw [circularSheetRep_apply, hMm]
    have h0 : chiralPlusWeyl (frame (Fin.addNat k 4)) = 0 := by
      rw [chiralPlusWeyl_coord_val, coordinateEquiv_apply_frame]
      have hz : ∀ j : Fin 4, (Pi.single (Fin.addNat k 4) (1 : ℝ)) (Fin.castAdd 4 j) = 0 := by
        intro j
        rw [Pi.single_apply]
        split_ifs with h
        · exfalso
          have heq := Fin.ext_iff.mp h
          simp only [Fin.coe_castAdd, Fin.coe_addNat] at heq
          omega
        · rfl
      rw [hz 0, hz 1, hz 2, hz 3, pauliSolder2x2_zero]
    rw [h0, map_zero]
  refine ⟨hConeP, hConeM, hPhi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hFramePos 0 σ0 (by
      rw [chiralPlusWeyl_coord_val, coordinateEquiv_apply_frame]
      simp only [Fin.castAdd_zero, Pi.single_apply]
      norm_num [pauliSolder_eval]
      ext i j; fin_cases i <;> fin_cases j <;> simp [σ0])
  · exact hFramePos 1 σ1 (by
      rw [chiralPlusWeyl_coord_val, coordinateEquiv_apply_frame]
      simp only [Pi.single_apply]
      norm_num [pauliSolder_eval]
      ext i j; fin_cases i <;> fin_cases j <;> simp [σ1])
  · exact hFramePos 2 σ2 (by
      rw [chiralPlusWeyl_coord_val, coordinateEquiv_apply_frame]
      simp only [Pi.single_apply]
      norm_num [pauliSolder_eval]
      ext i j; fin_cases i <;> fin_cases j <;> simp [σ2])
  · exact hFramePos 3 σ3 (by
      rw [chiralPlusWeyl_coord_val, coordinateEquiv_apply_frame]
      simp only [Pi.single_apply]
      norm_num [pauliSolder_eval]
      ext i j; fin_cases i <;> fin_cases j <;> simp [σ3])
  · exact hFrameNeg 0 σ0 (by
      rw [chiralMinusBarWeyl_coord_val, coordinateEquiv_apply_frame]
      simp only [Pi.single_apply]
      norm_num [pauliSolder_eval]
      ext i j; fin_cases i <;> fin_cases j <;> simp [σ0])
  · exact hFrameNeg 1 (-σ1) (by
      rw [chiralMinusBarWeyl_coord_val, coordinateEquiv_apply_frame]
      simp only [Pi.single_apply]
      norm_num [pauliSolder_eval]
      ext i j; fin_cases i <;> fin_cases j <;> simp [σ1])
  · exact hFrameNeg 2 (-σ2) (by
      rw [chiralMinusBarWeyl_coord_val, coordinateEquiv_apply_frame]
      simp only [Pi.single_apply]
      norm_num [pauliSolder_eval]
      ext i j; fin_cases i <;> fin_cases j <;> simp [σ2])
  · exact hFrameNeg 3 (-σ3) (by
      rw [chiralMinusBarWeyl_coord_val, coordinateEquiv_apply_frame]
      simp only [Pi.single_apply]
      norm_num [pauliSolder_eval]
      ext i j; fin_cases i <;> fin_cases j <;> simp [σ3])

private lemma circularBispinorRep_coord (X : CanonicalZorn) :
    let c := coordinateEquiv X
    circularBispinorRep X =
      !![0, 0, (c 0 : ℂ) + c 3, (c 1 : ℂ) - Complex.I * c 2;
         0, 0, (c 1 : ℂ) + Complex.I * c 2, (c 0 : ℂ) - c 3;
         (c 4 : ℂ) - c 7, -((c 5 : ℂ) - Complex.I * c 6), 0, 0;
         -((c 5 : ℂ) + Complex.I * c 6), (c 4 : ℂ) + c 7, 0, 0] := by
  dsimp only [circularBispinorRep, LinearMap.comp_apply, LinearMap.prod_apply,
    bispinorFromBlocksLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [chiralPlusWeyl_coord_val, chiralMinusBarWeyl_coord_val, pauliSolder_eval, pauliSolder_eval]
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp <;> ring

-- theorem-class: constructive endpoint
/-- Noncommutative algebra properties of the circular chiral representation:
1. Concrete noncommutativity witness between positive channel `frame 1` and negative channel `frame 6`;
2. `8D` Trace–Witt–Krein metric pullback `Tr(circularBispinorRep X * circularBispinorRep Y) = 2 * chiralKreinForm (...)`;
3. Off-diagonal determinant factorization `det(ρ₊(X) * ρ̄₋(X)) = det(ρ₊(X)) * det(ρ̄₋(X))`. -/
@[rep_depth transport]
theorem circularBispinor_noncomm_trace_and_det (X Y : CanonicalZorn) :
    chiralPlusWeyl (frame 1) * chiralMinusBarWeyl (frame 6) ≠
      chiralMinusBarWeyl (frame 6) * chiralPlusWeyl (frame 1) ∧
    Matrix.trace (circularBispinorRep X * circularBispinorRep Y) =
      2 * (chiralKreinForm (E := FourSpace)
        (lorentzCircularZornToKreinFrame X) (lorentzCircularZornToKreinFrame Y) : ℂ) ∧
    (chiralPlusWeyl X * chiralMinusBarWeyl X).det =
      (chiralPlusWeyl X).det * (chiralMinusBarWeyl X).det := by
  refine ⟨?_, ?_, ?_⟩
  · intro hComm
    have h00 := congrFun (congrFun hComm 0) 0
    have h1 : chiralPlusWeyl (frame 1) = !![0, (1 : ℂ); 1, 0] := by
      rw [chiralPlusWeyl_coord_val, coordinateEquiv_apply_frame]
      simp only [Pi.single_apply]
      norm_num [pauliSolder_eval]
    have h6 : chiralMinusBarWeyl (frame 6) = !![0, Complex.I; -Complex.I, 0] := by
      rw [chiralMinusBarWeyl_coord_val, coordinateEquiv_apply_frame]
      simp only [Pi.single_apply]
      norm_num [pauliSolder_eval]
    rw [h1, h6, mat2_mul, mat2_mul] at h00
    dsimp at h00
    have hTwoI : (2 : ℂ) * Complex.I = 0 := by linear_combination -h00
    have hI0 : Complex.I = 0 := (mul_eq_zero.mp hTwoI).resolve_left (by norm_num)
    exact Complex.I_ne_zero hI0
  · rw [(chiralKreinForm_lorentzCircularZornToKreinFrame X Y).1]
    rw [circularBispinorRep_coord X, circularBispinorRep_coord Y]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_four,
      circularPeircePolar]
    dsimp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    generalize coordinateEquiv X 0 = x0
    generalize coordinateEquiv X 1 = x1
    generalize coordinateEquiv X 2 = x2
    generalize coordinateEquiv X 3 = x3
    generalize coordinateEquiv X 4 = x4
    generalize coordinateEquiv X 5 = x5
    generalize coordinateEquiv X 6 = x6
    generalize coordinateEquiv X 7 = x7
    generalize coordinateEquiv Y 0 = y0
    generalize coordinateEquiv Y 1 = y1
    generalize coordinateEquiv Y 2 = y2
    generalize coordinateEquiv Y 3 = y3
    generalize coordinateEquiv Y 4 = y4
    generalize coordinateEquiv Y 5 = y5
    generalize coordinateEquiv Y 6 = y6
    generalize coordinateEquiv Y 7 = y7
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  · exact Matrix.det_mul (chiralPlusWeyl X) (chiralMinusBarWeyl X)

-- theorem-class: constructive endpoint
/-- On the matched Minkowski diagonal embedding `u ↦ (u, u)`, the anticommutator of two
`circularBispinorRep` operators closes strictly to a scalar multiple of the identity
controlled by `circularPeircePolar`. -/
@[rep_depth transport]
theorem circularBispinor_matched_clifford_anticommutator (u w : Fin 4 → ℝ) :
    let X := coordinateEquiv.symm (minkowskiDiagonalEmbedding u)
    let Y := coordinateEquiv.symm (minkowskiDiagonalEmbedding w)
    circularBispinorRep X * circularBispinorRep Y +
      circularBispinorRep Y * circularBispinorRep X =
      (circularPeircePolar (minkowskiDiagonalEmbedding u) (minkowskiDiagonalEmbedding w) : ℂ) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  intro X Y
  have hX : ∀ k : Fin 8, coordinateEquiv X k = minkowskiDiagonalEmbedding u k := fun k =>
    congrFun (coordinateEquiv.apply_symm_apply _) k
  have hY : ∀ k : Fin 8, coordinateEquiv Y k = minkowskiDiagonalEmbedding w k := fun k =>
    congrFun (coordinateEquiv.apply_symm_apply _) k
  rw [circularBispinorRep_coord X, circularBispinorRep_coord Y]
  simp only [hX, hY, minkowskiDiagonalEmbedding, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
      Fin.sum_univ_four, circularPeircePolar, Complex.real_smul]; dsimp only)
  all_goals
    try (norm_num; done)
  all_goals
    generalize u 0 = u0
    generalize u 1 = u1
    generalize u 2 = u2
    generalize u 3 = u3
    generalize w 0 = w0
    generalize w 1 = w1
    generalize w 2 = w2
    generalize w 3 = w3
    push_cast
    ring_nf
    try rw [Complex.I_sq]
    ring

/-! ## Archetype 4: Operator-Valued Two-Sheet Gauge–Higgs Connection & Parity Split -/

/-- Two-sheeted gauge–Higgs connection operator in `TetraktysZornYangMillsBridge.SheetAlgebra W`
with intra-sheet chiral gauge potentials `(AL, AR)` on the diagonal and off-diagonal
inter-sheet Higgs/soldering operators `(PhiPlus, PhiMinus)`. -/
@[rep_depth transport]
def twoSheetGaugeHiggsConnection {W : Type*} [AddCommGroup W] [Module ℂ W]
    (AL AR PhiPlus PhiMinus : Operator W) : SheetAlgebra W :=
  !![AL, PhiPlus; PhiMinus, AR]

-- theorem-class: constructive endpoint
/-- Noncommutative curvature decomposition and `Cl(1,1)` parity separation of
`twoSheetGaugeHiggsConnection` inside `SheetAlgebra W`:
`D = !![AL, 0; 0, AR] + circularSheetRep X` couples diagonal gauge fields with the
circular Peirce Weyl operators, and `D * D` splits under `Γ = invS (firstSheetProjection W)`
into even intra-sheet curvature and odd inter-sheet covariant derivatives. -/
@[rep_depth transport]
theorem twoSheetGaugeHiggsConnection_curvature_and_parity_split
    (AL AR PhiPlus PhiMinus : Operator (Fin 2 → ℂ)) (X : CanonicalZorn) :
    let D := twoSheetGaugeHiggsConnection AL AR PhiPlus PhiMinus
    let Γ := invS (firstSheetProjection (W := Fin 2 → ℂ))
    !![AL, 0; 0, AR] + circularSheetRep X =
      twoSheetGaugeHiggsConnection AL AR
        (Matrix.toLin' (chiralPlusWeyl X)) (Matrix.toLin' (chiralMinusBarWeyl X)) ∧
    D * D = !![AL * AL + PhiPlus * PhiMinus, AL * PhiPlus + PhiPlus * AR;
               PhiMinus * AL + AR * PhiMinus, PhiMinus * PhiPlus + AR * AR] ∧
    (D * D) + Γ * (D * D) * Γ =
      (2 : ℕ) • !![AL * AL + PhiPlus * PhiMinus, 0;
                   0, PhiMinus * PhiPlus + AR * AR] ∧
    (D * D) - Γ * (D * D) * Γ =
      (2 : ℕ) • !![0, AL * PhiPlus + PhiPlus * AR;
                   PhiMinus * AL + AR * PhiMinus, 0] := by
  intro D Γ
  have hG : Γ = !![1, 0; 0, -1] :=
    (sheetAlgebra_cl11_chirality_and_pole_laws (Fin 2 → ℂ)).1
  have hAdd : !![AL, 0; 0, AR] + circularSheetRep X =
      twoSheetGaugeHiggsConnection AL AR
        (Matrix.toLin' (chiralPlusWeyl X)) (Matrix.toLin' (chiralMinusBarWeyl X)) := by
    rw [circularSheetRep_apply, mat2_add]
    simp only [add_zero, zero_add]
    rfl
  have hDD : D * D = !![AL * AL + PhiPlus * PhiMinus, AL * PhiPlus + PhiPlus * AR;
      PhiMinus * AL + AR * PhiMinus, PhiMinus * PhiPlus + AR * AR] := by
    dsimp [D, twoSheetGaugeHiggsConnection]
    exact mat2_mul AL PhiPlus PhiMinus AR AL PhiPlus PhiMinus AR
  refine ⟨hAdd, hDD, ?_, ?_⟩
  · rw [hDD, hG, mat2_mul, mat2_mul, mat2_add, two_nsmul, mat2_add]
    ext i j
    fin_cases i <;> fin_cases j <;> (dsimp; noncomm_ring)
  · rw [hDD, hG, mat2_mul, mat2_mul, mat2_sub, two_nsmul, mat2_add]
    ext i j
    fin_cases i <;> fin_cases j <;> (dsimp; noncomm_ring)

/-! ## Archetype 5: Contraction-Built 4D Chiral Hodge Star, Self-Dual Yang–Mills, & Bogomolnyi Action -/

/-- Basis 1-form `dx μ` in `ExteriorAlgebra ℂ (Fin m → ℂ)`. -/
@[rep_depth transport]
def extBasisOneForm (m : ℕ) (μ : Fin m) : ExteriorAlgebra ℂ (Fin m → ℂ) :=
  ExteriorAlgebra.ι ℂ (Pi.single μ (1 : ℂ))

/-- Contraction coefficient linear functional on 2-forms in `ExteriorAlgebra ℂ (Fin 4 → ℂ)`. -/
@[rep_depth transport]
def blade2Coeff (a b : Fin 4) :
    ExteriorAlgebra ℂ (Fin 4 → ℂ) →ₗ[ℂ] ℂ :=
  (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin 4 → ℂ)).toLinearMap.comp
    ((contractionOp (R := ℂ) (V := Fin 4 → ℂ) (LinearMap.proj b)).comp
      (contractionOp (R := ℂ) (V := Fin 4 → ℂ) (LinearMap.proj a)))

private lemma contract2_blade {m : ℕ} (a b c d : Fin m) :
    ExteriorAlgebra.algebraMapInv
        (contractionOp (R := ℂ) (V := Fin m → ℂ) (LinearMap.proj b)
          (contractionOp (R := ℂ) (V := Fin m → ℂ) (LinearMap.proj a)
            (extBasisOneForm m c * extBasisOneForm m d))) =
      (if a = c then (1 : ℂ) else 0) * (if b = d then (1 : ℂ) else 0) -
        (if a = d then (1 : ℂ) else 0) * (if b = c then (1 : ℂ) else 0) := by
  dsimp only [extBasisOneForm]
  rw [contraction_op_generator_mul, contraction_on_generator,
    Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one,
    map_sub, map_smul, map_smul,
    contraction_on_generator, contraction_on_generator,
    AlgHom.map_sub, map_smul, map_smul,
    ExteriorAlgebra.algebraMap_leftInverse, ExteriorAlgebra.algebraMap_leftInverse]
  simp only [LinearMap.proj_apply, Pi.single_apply, smul_eq_mul]
  ring

-- theorem-class: constructive endpoint
/-- Exact evaluation of `blade2Coeff a b` on basis 2-forms `dx c * dx d` and annihilation on 1-forms and scalars. -/
@[rep_depth transport]
theorem blade2Coeff_eval (a b c d : Fin 4) (z : ℂ) :
    blade2Coeff a b (extBasisOneForm 4 c * extBasisOneForm 4 d) =
      (if a = c then (1 : ℂ) else 0) * (if b = d then (1 : ℂ) else 0) -
        (if a = d then (1 : ℂ) else 0) * (if b = c then (1 : ℂ) else 0) ∧
    blade2Coeff a b (extBasisOneForm 4 c) = 0 ∧
    blade2Coeff a b (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) z) = 0 := by
  have hScal : ∀ s : ℂ,
      contractionOp (R := ℂ) (V := Fin 4 → ℂ) (LinearMap.proj b)
        (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) s) = 0 := by
    intro s
    rw [Algebra.algebraMap_eq_smul_one, map_smul, contraction_op_one, smul_zero]
  have h1 : contractionOp (R := ℂ) (V := Fin 4 → ℂ) (LinearMap.proj a) (extBasisOneForm 4 c) =
      algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) (if a = c then 1 else 0) := by
    dsimp only [extBasisOneForm]
    rw [contraction_on_generator]
    simp only [LinearMap.proj_apply, Pi.single_apply]
  refine ⟨contract2_blade a b c d, ?_, ?_⟩
  · dsimp only [blade2Coeff, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [h1, hScal, map_zero]
  · dsimp only [blade2Coeff, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [show contractionOp (R := ℂ) (V := Fin 4 → ℂ) (LinearMap.proj a)
        (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) z) = 0 by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, contraction_op_one, smul_zero],
      map_zero, map_zero]

/-- Explicit 4D Lorentzian Hodge star endomorphism on `ExteriorAlgebra ℂ (Fin 4 → ℂ)`
sending `dx₀∧dx₁ ↦ -dx₂∧dx₃`, `dx₂∧dx₃ ↦ dx₀∧dx₁` (and cyclically). -/
@[rep_depth transport]
def lorentzHodgeStar4 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  let e01 := extBasisOneForm 4 0 * extBasisOneForm 4 1
  let e02 := extBasisOneForm 4 0 * extBasisOneForm 4 2
  let e03 := extBasisOneForm 4 0 * extBasisOneForm 4 3
  let e23 := extBasisOneForm 4 2 * extBasisOneForm 4 3
  let e31 := extBasisOneForm 4 3 * extBasisOneForm 4 1
  let e12 := extBasisOneForm 4 1 * extBasisOneForm 4 2
  (LinearMap.smulRight (blade2Coeff 2 3) e01 - LinearMap.smulRight (blade2Coeff 0 1) e23) +
    (LinearMap.smulRight (blade2Coeff 3 1) e02 - LinearMap.smulRight (blade2Coeff 0 2) e31) +
    (LinearMap.smulRight (blade2Coeff 1 2) e03 - LinearMap.smulRight (blade2Coeff 0 3) e12)

/-- Complex chiral Hodge star `chiralHodgeStar4 := (-i) • lorentzHodgeStar4`, whose
2-form eigenspaces separate self-dual (`+1`) and anti-self-dual (`-1`) helicities. -/
@[rep_depth transport]
def chiralHodgeStar4 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  (-Complex.I) • lorentzHodgeStar4

private lemma extBasis4_sq (μ : Fin 4) :
    extBasisOneForm 4 μ * extBasisOneForm 4 μ = 0 :=
  ExteriorAlgebra.ι_sq_zero _

private lemma extBasis4_anticomm (μ ν : Fin 4) :
    extBasisOneForm 4 μ * extBasisOneForm 4 ν =
      -(extBasisOneForm 4 ν * extBasisOneForm 4 μ) := by
  have h := ExteriorAlgebra.ι_sq_zero (R := ℂ)
    ((Pi.single μ (1 : ℂ) : Fin 4 → ℂ) + (Pi.single ν (1 : ℂ) : Fin 4 → ℂ))
  rw [map_add, add_mul, mul_add, mul_add,
    ExteriorAlgebra.ι_sq_zero, ExteriorAlgebra.ι_sq_zero, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

private lemma lorentzHodgeStar4_blade (μ ν : Fin 4) :
    lorentzHodgeStar4 (extBasisOneForm 4 μ * extBasisOneForm 4 ν) =
      match μ, ν with
      | 0, 1 => -(extBasisOneForm 4 2 * extBasisOneForm 4 3)
      | 1, 0 => extBasisOneForm 4 2 * extBasisOneForm 4 3
      | 0, 2 => -(extBasisOneForm 4 3 * extBasisOneForm 4 1)
      | 2, 0 => extBasisOneForm 4 3 * extBasisOneForm 4 1
      | 0, 3 => -(extBasisOneForm 4 1 * extBasisOneForm 4 2)
      | 3, 0 => extBasisOneForm 4 1 * extBasisOneForm 4 2
      | 2, 3 => extBasisOneForm 4 0 * extBasisOneForm 4 1
      | 3, 2 => -(extBasisOneForm 4 0 * extBasisOneForm 4 1)
      | 3, 1 => extBasisOneForm 4 0 * extBasisOneForm 4 2
      | 1, 3 => -(extBasisOneForm 4 0 * extBasisOneForm 4 2)
      | 1, 2 => extBasisOneForm 4 0 * extBasisOneForm 4 3
      | 2, 1 => -(extBasisOneForm 4 0 * extBasisOneForm 4 3)
      | _, _ => 0 := by
  fin_cases μ <;> fin_cases ν
  all_goals
    try (rw [extBasis4_sq, map_zero]; rfl)
  all_goals
    simp only [lorentzHodgeStar4, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smulRight_apply, (blade2Coeff_eval _ _ _ _ 0).1]
    norm_num
    generalize extBasisOneForm 4 0 * extBasisOneForm 4 1 = b01
    generalize extBasisOneForm 4 0 * extBasisOneForm 4 2 = b02
    generalize extBasisOneForm 4 0 * extBasisOneForm 4 3 = b03
    generalize extBasisOneForm 4 2 * extBasisOneForm 4 3 = b23
    generalize extBasisOneForm 4 3 * extBasisOneForm 4 1 = b31
    generalize extBasisOneForm 4 1 * extBasisOneForm 4 2 = b12
    module

-- theorem-class: constructive endpoint
/-- Squares of `lorentzHodgeStar4` and `chiralHodgeStar4` on all basis 2-forms `dx a * dx b`. -/
@[rep_depth transport]
theorem hodgeStar4_sq_on_blades (a b : Fin 4) :
    lorentzHodgeStar4 (lorentzHodgeStar4 (extBasisOneForm 4 a * extBasisOneForm 4 b)) =
      -(extBasisOneForm 4 a * extBasisOneForm 4 b) ∧
    chiralHodgeStar4 (chiralHodgeStar4 (extBasisOneForm 4 a * extBasisOneForm 4 b)) =
      extBasisOneForm 4 a * extBasisOneForm 4 b := by
  have hLorentz : ∀ x y : Fin 4,
      lorentzHodgeStar4 (lorentzHodgeStar4 (extBasisOneForm 4 x * extBasisOneForm 4 y)) =
        -(extBasisOneForm 4 x * extBasisOneForm 4 y) := by
    intro x y
    fin_cases x <;> fin_cases y
    · rw [extBasis4_sq, map_zero, map_zero, neg_zero]
    · simp only [lorentzHodgeStar4_blade, map_neg]
    · simp only [lorentzHodgeStar4_blade, map_neg]
    · simp only [lorentzHodgeStar4_blade, map_neg]
    · simp only [lorentzHodgeStar4_blade, map_neg, neg_neg, extBasis4_anticomm 1 0]
    · rw [extBasis4_sq, map_zero, map_zero, neg_zero]
    · simp only [lorentzHodgeStar4_blade, map_neg]
    · simp only [lorentzHodgeStar4_blade, map_neg, neg_neg, extBasis4_anticomm 1 3]
    · simp only [lorentzHodgeStar4_blade, map_neg, neg_neg, extBasis4_anticomm 2 0]
    · simp only [lorentzHodgeStar4_blade, map_neg, neg_neg, extBasis4_anticomm 2 1]
    · rw [extBasis4_sq, map_zero, map_zero, neg_zero]
    · simp only [lorentzHodgeStar4_blade, map_neg]
    · simp only [lorentzHodgeStar4_blade, map_neg, neg_neg, extBasis4_anticomm 3 0]
    · simp only [lorentzHodgeStar4_blade, map_neg]
    · simp only [lorentzHodgeStar4_blade, map_neg, neg_neg, extBasis4_anticomm 3 2]
    · rw [extBasis4_sq, map_zero, map_zero, neg_zero]
  have hChiral : chiralHodgeStar4 (chiralHodgeStar4 (extBasisOneForm 4 a * extBasisOneForm 4 b)) =
      extBasisOneForm 4 a * extBasisOneForm 4 b := by
    dsimp [chiralHodgeStar4]
    simp only [map_smul, LinearMap.smul_apply, smul_smul, hLorentz a b, smul_neg]
    have hCoef : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by
      calc
        (-Complex.I) * (-Complex.I) = Complex.I ^ 2 := by ring
        _ = -1 := Complex.I_sq
    rw [hCoef, neg_one_smul, neg_neg]
  exact ⟨hLorentz a b, hChiral⟩

/-- Upper two-sheet idempotent `diag(1, 1, 0, 0)` over any ring `R`. -/
@[rep_depth transport]
def upperSheetIdempotent (R : Type*) [Ring R] : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

private lemma upperSheetIdempotent_sq (R : Type*) [Ring R] :
    upperSheetIdempotent R * upperSheetIdempotent R = upperSheetIdempotent R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperSheetIdempotent, Matrix.mul_apply, Fin.sum_univ_four]

private lemma oneSub_upperSheetIdempotent (R : Type*) [Ring R] :
    (1 : Matrix (Fin 4) (Fin 4) R) - upperSheetIdempotent R =
      !![0, 0, 0, 0;
         0, 0, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperSheetIdempotent, Matrix.sub_apply, Matrix.one_apply]

private lemma upperSheet_left_mul {R : Type*} [Ring R] (M : Matrix (Fin 4) (Fin 4) R) :
    upperSheetIdempotent R * M =
      !![M 0 0, M 0 1, M 0 2, M 0 3;
         M 1 0, M 1 1, M 1 2, M 1 3;
         0,     0,     0,     0;
         0,     0,     0,     0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperSheetIdempotent, Matrix.mul_apply, Fin.sum_univ_four]

private lemma oneSub_upperSheet_left_mul {R : Type*} [Ring R] (M : Matrix (Fin 4) (Fin 4) R) :
    ((1 : Matrix (Fin 4) (Fin 4) R) - upperSheetIdempotent R) * M =
      !![0,     0,     0,     0;
         0,     0,     0,     0;
         M 2 0, M 2 1, M 2 2, M 2 3;
         M 3 0, M 3 1, M 3 2, M 3 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oneSub_upperSheetIdempotent, Matrix.mul_apply, Fin.sum_univ_four]

private lemma mat4_mul {R : Type*} [Ring R]
    (A B : Matrix (Fin 4) (Fin 4) R) (i j : Fin 4) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j + A i 3 * B 3 j := by
  simp only [Matrix.mul_apply, Fin.sum_univ_four, add_assoc]

private lemma conePlus_upperSheet_blocks {R : Type*} [Ring R] (a b c d : R) :
    conePlus (upperSheetIdempotent R)
      !![0, 0, a, b;
         0, 0, c, d;
         0, 0, 0, 0;
         0, 0, 0, 0] =
      !![0, 0, a, b;
         0, 0, c, d;
         0, 0, 0, 0;
         0, 0, 0, 0] := by
  rw [conePlus, upperSheet_left_mul, oneSub_upperSheetIdempotent]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (rw [mat4_mul]; dsimp; noncomm_ring)

private lemma coneMinus_upperSheet_blocks {R : Type*} [Ring R] (e f g h : R) :
    coneMinus (upperSheetIdempotent R)
      !![0, 0, 0, 0;
         0, 0, 0, 0;
         e, f, 0, 0;
         g, h, 0, 0] =
      !![0, 0, 0, 0;
         0, 0, 0, 0;
         e, f, 0, 0;
         g, h, 0, 0] := by
  rw [coneMinus, oneSub_upperSheet_left_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (rw [mat4_mul]; simp only [upperSheetIdempotent]; dsimp; noncomm_ring)

private lemma genPhi_upperSheet_blocks {R : Type*} [Ring R] (a b c d e f g h : R) :
    genPhi (upperSheetIdempotent R)
        !![0, 0, a, b; 0, 0, c, d; 0, 0, 0, 0; 0, 0, 0, 0]
        !![0, 0, 0, 0; 0, 0, 0, 0; e, f, 0, 0; g, h, 0, 0] =
      !![0, 0, a, b;
         0, 0, c, d;
         e, f, 0, 0;
         g, h, 0, 0] := by
  rw [genPhi, conePlus_upperSheet_blocks, coneMinus_upperSheet_blocks]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.add_apply]; dsimp; noncomm_ring)

private lemma genV_upperSheet_blocks {R : Type*} [Ring R] (a b c d e f g h : R) :
    genV (upperSheetIdempotent R)
        !![0, 0, a, b; 0, 0, c, d; 0, 0, 0, 0; 0, 0, 0, 0]
        !![0, 0, 0, 0; 0, 0, 0, 0; e, f, 0, 0; g, h, 0, 0] =
      !![a * e + b * g, a * f + b * h, 0, 0;
         c * e + d * g, c * f + d * h, 0, 0;
         0, 0, e * a + f * c, e * b + f * d;
         0, 0, g * a + h * c, g * b + h * d] := by
  rw [genV, anticomm, conePlus_upperSheet_blocks, coneMinus_upperSheet_blocks]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.add_apply, mat4_mul]; dsimp; noncomm_ring)

private lemma genSig_upperSheet_blocks {R : Type*} [Ring R] (a b c d e f g h : R) :
    genSig (upperSheetIdempotent R)
        !![0, 0, a, b; 0, 0, c, d; 0, 0, 0, 0; 0, 0, 0, 0]
        !![0, 0, 0, 0; 0, 0, 0, 0; e, f, 0, 0; g, h, 0, 0] =
      !![a * e + b * g, a * f + b * h, 0, 0;
         c * e + d * g, c * f + d * h, 0, 0;
         0, 0, -(e * a + f * c), -(e * b + f * d);
         0, 0, -(g * a + h * c), -(g * b + h * d)] := by
  rw [genSig, InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
    conePlus_upperSheet_blocks, coneMinus_upperSheet_blocks]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.sub_apply, mat4_mul]; dsimp; noncomm_ring)

/-- Circular `8`-channel Pauli soldering `1`-form block for `frame 0..3`
placed in the upper-right Peirce corner over `ExteriorAlgebra ℂ (Fin 8 → ℂ)`. -/
@[rep_depth transport]
def upperCircularOneForm8 : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 8 → ℂ)) :=
  let e0 := extBasisOneForm 8 0
  let e1 := extBasisOneForm 8 1
  let e2 := extBasisOneForm 8 2
  let e3 := extBasisOneForm 8 3
  !![0, 0, e0 + e3, e1 - Complex.I • e2;
     0, 0, e1 + Complex.I • e2, e0 - e3;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Circular `8`-channel bar-Pauli soldering `1`-form block for `frame 4..7`
placed in the lower-left Peirce corner over `ExteriorAlgebra ℂ (Fin 8 → ℂ)`. -/
@[rep_depth transport]
def lowerCircularBarOneForm8 : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 8 → ℂ)) :=
  let e4 := extBasisOneForm 8 4
  let e5 := extBasisOneForm 8 5
  let e6 := extBasisOneForm 8 6
  let e7 := extBasisOneForm 8 7
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     e4 - e7, -(e5 - Complex.I • e6), 0, 0;
     -(e5 + Complex.I • e6), e4 + e7, 0, 0]

/-- `4 × 4` block-off-diagonal circular gauge connection over the `8D` exterior algebra. -/
@[rep_depth transport]
def circularDoubledConnection8 : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 8 → ℂ)) :=
  let e0 := extBasisOneForm 8 0
  let e1 := extBasisOneForm 8 1
  let e2 := extBasisOneForm 8 2
  let e3 := extBasisOneForm 8 3
  let e4 := extBasisOneForm 8 4
  let e5 := extBasisOneForm 8 5
  let e6 := extBasisOneForm 8 6
  let e7 := extBasisOneForm 8 7
  !![0, 0, e0 + e3, e1 - Complex.I • e2;
     0, 0, e1 + Complex.I • e2, e0 - e3;
     e4 - e7, -(e5 - Complex.I • e6), 0, 0;
     -(e5 + Complex.I • e6), e4 + e7, 0, 0]

-- theorem-class: constructive endpoint
/-- The `8`-channel circular gauge connection equals `genPhi P upperCircularOneForm8 lowerCircularBarOneForm8`,
has algebraic curvature `genV`, obeys covariant Bianchi `D_A F_A = 0`, and has nonzero `(0,0)` curvature. -/
@[rep_depth transport]
theorem circularDoubledConnection8_curvature_bianchi_nonzero :
    let P := upperSheetIdempotent (ExteriorAlgebra ℂ (Fin 8 → ℂ))
    P * P = P ∧
    circularDoubledConnection8 = genPhi P upperCircularOneForm8 lowerCircularBarOneForm8 ∧
    curvatureFromConnection (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 8 → ℂ))) circularDoubledConnection8 =
      genV P upperCircularOneForm8 lowerCircularBarOneForm8 ∧
    covariantDerivative circularDoubledConnection8 (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 8 → ℂ)))
      (curvatureFromConnection (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 8 → ℂ))) circularDoubledConnection8) = 0 ∧
    curvatureFromConnection (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 8 → ℂ))) circularDoubledConnection8 ≠ 0 := by
  intro P
  have hP : P * P = P := upperSheetIdempotent_sq (ExteriorAlgebra ℂ (Fin 8 → ℂ))
  have hPhi : circularDoubledConnection8 = genPhi P upperCircularOneForm8 lowerCircularBarOneForm8 := by
    dsimp [P, circularDoubledConnection8, upperCircularOneForm8, lowerCircularBarOneForm8]
    rw [genPhi_upperSheet_blocks]
  have hBridge := peirce_defect_connection_curvature_and_yang_mills_bridge
    (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 8 → ℂ)))
    (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 8 → ℂ)))
    hP upperCircularOneForm8 lowerCircularBarOneForm8 circularDoubledConnection8
  have hCurv0 : curvatureFromConnection 0 circularDoubledConnection8 =
      genV P upperCircularOneForm8 lowerCircularBarOneForm8 := by
    rw [hPhi]
    exact hBridge.2.2.1
  have hBianchi0 : covariantDerivative circularDoubledConnection8 0
      (curvatureFromConnection 0 circularDoubledConnection8) = 0 := by
    rw [hPhi, hBridge.2.2.1]
    exact hBridge.2.2.2.1
  have hNe0 : curvatureFromConnection (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 8 → ℂ))) circularDoubledConnection8 ≠ 0 := by
    intro hZero
    let eval0 : (Fin 8 → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj 0
    let eval4 : (Fin 8 → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj 4
    let pick04 : ExteriorAlgebra ℂ (Fin 8 → ℂ) →ₗ[ℂ] ℂ :=
      ExteriorAlgebra.algebraMapInv.toLinearMap.comp
        ((contractionOp (R := ℂ) (V := Fin 8 → ℂ) eval4).comp
          (contractionOp (R := ℂ) (V := Fin 8 → ℂ) eval0))
    have hentry := congrArg (fun M => pick04 (M 0 0)) hZero
    simp only [Matrix.zero_apply, map_zero] at hentry
    have hD : matrixExteriorDerivative (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 8 → ℂ)))
        circularDoubledConnection8 = 0 := by
      ext i j; rfl
    have h00 : (curvatureFromConnection (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 8 → ℂ)))
        circularDoubledConnection8) 0 0 =
        (extBasisOneForm 8 0 + extBasisOneForm 8 3) * (extBasisOneForm 8 4 - extBasisOneForm 8 7) +
        (extBasisOneForm 8 1 - Complex.I • extBasisOneForm 8 2) *
          (-(extBasisOneForm 8 5 + Complex.I • extBasisOneForm 8 6)) := by
      unfold curvatureFromConnection
      rw [hD, zero_add, mat4_mul]
      rfl
    have hOneZero : ∀ a b : Fin 8,
        pick04 (extBasisOneForm 8 a * extBasisOneForm 8 b) =
          (if (0 : Fin 8) = a then (1 : ℂ) else 0) * (if (4 : Fin 8) = b then (1 : ℂ) else 0) -
            (if (0 : Fin 8) = b then (1 : ℂ) else 0) * (if (4 : Fin 8) = a then (1 : ℂ) else 0) :=
      fun a b => contract2_blade (m := 8) 0 4 a b
    rw [h00] at hentry
    simp only [add_mul, mul_sub, sub_mul, map_add, map_sub, map_neg,
      smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul, hOneZero] at hentry
    norm_num at hentry
  exact ⟨hP, hPhi, hCurv0, hBianchi0, hNe0⟩

/-- Cotangent pullback linear map collapsing the positive and negative circular sectors
`(0..3)` and `(4..7)` onto `Fin 4 → ℂ`. -/
@[rep_depth transport]
def cotangentMatchedPullback : (Fin 8 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun w k := w (Fin.castAdd 4 k) + w (Fin.addNat k 4)
  map_add' u v := by
    funext k
    simp [Pi.add_apply]
    ring
  map_smul' c u := by
    funext k
    simp [Pi.smul_apply, smul_eq_mul]
    ring

/-- Functorial `ℂ`-algebra homomorphism from `8D` circular exterior forms onto
`4D` Minkowski exterior forms. -/
@[rep_depth transport]
def matchedCotangentMap :
    ExteriorAlgebra ℂ (Fin 8 → ℂ) →ₐ[ℂ] ExteriorAlgebra ℂ (Fin 4 → ℂ) :=
  ExteriorAlgebra.map cotangentMatchedPullback

/-- Upper matched `4D` Pauli soldering `1`-form block. -/
@[rep_depth transport]
def upperMatchedOneForm4 : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  upperCircularOneForm8.map matchedCotangentMap

/-- Lower matched `4D` bar-Pauli soldering `1`-form block. -/
@[rep_depth transport]
def lowerMatchedBarOneForm4 : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  lowerCircularBarOneForm8.map matchedCotangentMap

/-- Matched `4D` circular Minkowski connection pulled back from `circularDoubledConnection8`. -/
@[rep_depth transport]
def matchedCircularConnection4 : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  circularDoubledConnection8.map matchedCotangentMap

private lemma hStar01 :
    chiralHodgeStar4 (extBasisOneForm 4 0 * extBasisOneForm 4 1) =
      Complex.I • (extBasisOneForm 4 2 * extBasisOneForm 4 3) := by
  dsimp [chiralHodgeStar4]
  rw [lorentzHodgeStar4_blade 0 1]
  simp only [map_neg, LinearMap.smul_apply, smul_neg, neg_smul, neg_neg]

private lemma hStar02 :
    chiralHodgeStar4 (extBasisOneForm 4 0 * extBasisOneForm 4 2) =
      Complex.I • (extBasisOneForm 4 3 * extBasisOneForm 4 1) := by
  dsimp [chiralHodgeStar4]
  rw [lorentzHodgeStar4_blade 0 2]
  simp only [map_neg, LinearMap.smul_apply, smul_neg, neg_smul, neg_neg]

private lemma hStar03 :
    chiralHodgeStar4 (extBasisOneForm 4 0 * extBasisOneForm 4 3) =
      Complex.I • (extBasisOneForm 4 1 * extBasisOneForm 4 2) := by
  dsimp [chiralHodgeStar4]
  rw [lorentzHodgeStar4_blade 0 3]
  simp only [map_neg, LinearMap.smul_apply, smul_neg, neg_smul, neg_neg]

private lemma hStar23 :
    chiralHodgeStar4 (extBasisOneForm 4 2 * extBasisOneForm 4 3) =
      (-Complex.I) • (extBasisOneForm 4 0 * extBasisOneForm 4 1) := by
  dsimp [chiralHodgeStar4]
  rw [lorentzHodgeStar4_blade 2 3]
  rfl

private lemma hStar31 :
    chiralHodgeStar4 (extBasisOneForm 4 3 * extBasisOneForm 4 1) =
      (-Complex.I) • (extBasisOneForm 4 0 * extBasisOneForm 4 2) := by
  dsimp [chiralHodgeStar4]
  rw [lorentzHodgeStar4_blade 3 1]
  rfl

private lemma hStar12 :
    chiralHodgeStar4 (extBasisOneForm 4 1 * extBasisOneForm 4 2) =
      (-Complex.I) • (extBasisOneForm 4 0 * extBasisOneForm 4 3) := by
  dsimp [chiralHodgeStar4]
  rw [lorentzHodgeStar4_blade 1 2]
  rfl

-- theorem-class: constructive endpoint
/-- Chiral Hodge–Spin-Dipole Theorem on `matchedCircularConnection4`:
applying `chiralHodgeStar4` entrywise to `curvatureFromConnection 0 matchedCircularConnection4`
produces the exact Peirce Spin-Dipole operator `genSig`, separating the self-dual
upper `2 × 2` chiral curvature sheet from the anti-self-dual lower `2 × 2` chiral
curvature sheet, with zero covariant divergence under `invS P * ★ F`. -/
@[rep_depth transport]
theorem matchedCircularConnection4_chiralHodge_eq_genSig :
    let P := upperSheetIdempotent (ExteriorAlgebra ℂ (Fin 4 → ℂ))
    let F := curvatureFromConnection (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))) matchedCircularConnection4
    F = genV P upperMatchedOneForm4 lowerMatchedBarOneForm4 ∧
    matrixHodgeStar chiralHodgeStar4 F =
      genSig P upperMatchedOneForm4 lowerMatchedBarOneForm4 ∧
    matrixHodgeStar chiralHodgeStar4 F = invS P * F ∧
    covariantDerivative matchedCircularConnection4 0 (invS P * matrixHodgeStar chiralHodgeStar4 F) = 0 := by
  intro P F
  have hP : P * P = P := upperSheetIdempotent_sq (ExteriorAlgebra ℂ (Fin 4 → ℂ))
  have hMapFormPos : ∀ k : Fin 4,
      matchedCotangentMap (extBasisOneForm 8 (Fin.castAdd 4 k)) = extBasisOneForm 4 k := by
    intro k
    dsimp [matchedCotangentMap, extBasisOneForm]
    rw [ExteriorAlgebra.map_apply_ι]
    congr 1
    funext m
    fin_cases k <;> fin_cases m <;> simp [cotangentMatchedPullback, Pi.single_apply]
  have hMapFormNeg : ∀ k : Fin 4,
      matchedCotangentMap (extBasisOneForm 8 (Fin.addNat k 4)) = extBasisOneForm 4 k := by
    intro k
    dsimp [matchedCotangentMap, extBasisOneForm]
    rw [ExteriorAlgebra.map_apply_ι]
    congr 1
    funext m
    fin_cases k <;> fin_cases m <;> simp [cotangentMatchedPullback, Pi.single_apply]
  have hUpper : upperMatchedOneForm4 =
      !![0, 0, extBasisOneForm 4 0 + extBasisOneForm 4 3, extBasisOneForm 4 1 - Complex.I • extBasisOneForm 4 2;
         0, 0, extBasisOneForm 4 1 + Complex.I • extBasisOneForm 4 2, extBasisOneForm 4 0 - extBasisOneForm 4 3;
         0, 0, 0, 0;
         0, 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [upperMatchedOneForm4, upperCircularOneForm8, Matrix.map_apply,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        Fin.isValue, map_add, map_sub, map_smul, map_zero,
        hMapFormPos 0, hMapFormPos 1, hMapFormPos 2, hMapFormPos 3]
    all_goals rfl
  have hLower : lowerMatchedBarOneForm4 =
      !![0, 0, 0, 0;
         0, 0, 0, 0;
         extBasisOneForm 4 0 - extBasisOneForm 4 3, -(extBasisOneForm 4 1 - Complex.I • extBasisOneForm 4 2), 0, 0;
         -(extBasisOneForm 4 1 + Complex.I • extBasisOneForm 4 2), extBasisOneForm 4 0 + extBasisOneForm 4 3, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [lowerMatchedBarOneForm4, lowerCircularBarOneForm8, Matrix.map_apply,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        Fin.isValue, map_add, map_sub, map_neg, map_smul, map_zero,
        hMapFormNeg 0, hMapFormNeg 1, hMapFormNeg 2, hMapFormNeg 3]
    all_goals rfl
  have hConn : matchedCircularConnection4 =
      !![0, 0, extBasisOneForm 4 0 + extBasisOneForm 4 3, extBasisOneForm 4 1 - Complex.I • extBasisOneForm 4 2;
         0, 0, extBasisOneForm 4 1 + Complex.I • extBasisOneForm 4 2, extBasisOneForm 4 0 - extBasisOneForm 4 3;
         extBasisOneForm 4 0 - extBasisOneForm 4 3, -(extBasisOneForm 4 1 - Complex.I • extBasisOneForm 4 2), 0, 0;
         -(extBasisOneForm 4 1 + Complex.I • extBasisOneForm 4 2), extBasisOneForm 4 0 + extBasisOneForm 4 3, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [matchedCircularConnection4, circularDoubledConnection8, Matrix.map_apply,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        Fin.isValue, map_add, map_sub, map_neg, map_smul, map_zero,
        hMapFormPos 0, hMapFormPos 1, hMapFormPos 2, hMapFormPos 3,
        hMapFormNeg 0, hMapFormNeg 1, hMapFormNeg 2, hMapFormNeg 3]
    all_goals rfl
  have hPhi : matchedCircularConnection4 = genPhi P upperMatchedOneForm4 lowerMatchedBarOneForm4 := by
    rw [hConn, hUpper, hLower]
    exact (genPhi_upperSheet_blocks _ _ _ _ _ _ _ _).symm
  have hBridge := peirce_defect_connection_curvature_and_yang_mills_bridge
    chiralHodgeStar4 (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
    hP upperMatchedOneForm4 lowerMatchedBarOneForm4 matchedCircularConnection4
  have hF : F = genV P upperMatchedOneForm4 lowerMatchedBarOneForm4 := by
    dsimp [F]
    rw [hPhi]
    exact hBridge.2.2.1
  have hFExplicit : F =
      let d0 := extBasisOneForm 4 0
      let d1 := extBasisOneForm 4 1
      let d2 := extBasisOneForm 4 2
      let d3 := extBasisOneForm 4 3
      let a := d0 + d3; let b := d1 - Complex.I • d2
      let c := d1 + Complex.I • d2; let d := d0 - d3
      let e := d; let f := -b; let g := -c; let h := a
      !![a * e + b * g, a * f + b * h, 0, 0;
         c * e + d * g, c * f + d * h, 0, 0;
         0, 0, e * a + f * c, e * b + f * d;
         0, 0, g * a + h * c, g * b + h * d] := by
    rw [hF, hUpper, hLower]
    exact genV_upperSheet_blocks _ _ _ _ _ _ _ _
  have hSigExplicit : genSig P upperMatchedOneForm4 lowerMatchedBarOneForm4 =
      let d0 := extBasisOneForm 4 0
      let d1 := extBasisOneForm 4 1
      let d2 := extBasisOneForm 4 2
      let d3 := extBasisOneForm 4 3
      let a := d0 + d3; let b := d1 - Complex.I • d2
      let c := d1 + Complex.I • d2; let d := d0 - d3
      let e := d; let f := -b; let g := -c; let h := a
      !![a * e + b * g, a * f + b * h, 0, 0;
         c * e + d * g, c * f + d * h, 0, 0;
         0, 0, -(e * a + f * c), -(e * b + f * d);
         0, 0, -(g * a + h * c), -(g * b + h * d)] := by
    rw [hUpper, hLower]
    exact genSig_upperSheet_blocks _ _ _ _ _ _ _ _
  have hI2 : Complex.I * Complex.I = (-1 : ℂ) := by rw [← sq, Complex.I_sq]
  have hAnti13 := extBasis4_anticomm 1 3
  have hAnti32 := extBasis4_anticomm 3 2
  have hAnti21 := extBasis4_anticomm 2 1
  have hAnti10 := extBasis4_anticomm 1 0
  have hAnti20 := extBasis4_anticomm 2 0
  have hAnti30 := extBasis4_anticomm 3 0
  have hStarEqSig : matrixHodgeStar chiralHodgeStar4 F =
      genSig P upperMatchedOneForm4 lowerMatchedBarOneForm4 := by
    rw [hFExplicit, hSigExplicit]
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp only [matrixHodgeStar, Matrix.of_apply]
    all_goals
      try exact map_zero chiralHodgeStar4
    all_goals
      try exact (map_zero chiralHodgeStar4).trans neg_zero.symm
    all_goals
      dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      repeat
        first
        | rw [add_mul]
        | rw [mul_add]
        | rw [sub_mul]
        | rw [mul_sub]
        | rw [neg_mul]
        | rw [mul_neg]
        | rw [smul_mul_assoc]
        | rw [mul_smul_comm]
        | rw [map_add]
        | rw [map_sub]
        | rw [map_neg]
        | rw [map_smul]
        | rw [extBasis4_sq]
        | rw [mul_zero]
        | rw [zero_mul]
        | rw [smul_zero]
        | rw [map_zero]
        | rw [hAnti10]
        | rw [hAnti20]
        | rw [hAnti30]
        | rw [hAnti32]
        | rw [hAnti13]
        | rw [hAnti21]
        | rw [hStar01]
        | rw [hStar02]
        | rw [hStar03]
        | rw [hStar23]
        | rw [hStar31]
        | rw [hStar12]
        | rw [smul_smul]
        | rw [hI2]
      generalize extBasisOneForm 4 0 * extBasisOneForm 4 1 = b01
      generalize extBasisOneForm 4 0 * extBasisOneForm 4 2 = b02
      generalize extBasisOneForm 4 0 * extBasisOneForm 4 3 = b03
      generalize extBasisOneForm 4 2 * extBasisOneForm 4 3 = b23
      generalize extBasisOneForm 4 3 * extBasisOneForm 4 1 = b31
      generalize extBasisOneForm 4 1 * extBasisOneForm 4 2 = b12
      module
  have hSigEqInvS : genSig P upperMatchedOneForm4 lowerMatchedBarOneForm4 = invS P * F := by
    rw [hF]
    exact (peirce_spin_dipole_factorization hP upperMatchedOneForm4 lowerMatchedBarOneForm4).1
  have hCov : covariantDerivative matchedCircularConnection4 0 (invS P * matrixHodgeStar chiralHodgeStar4 F) = 0 := by
    rw [hStarEqSig, hSigEqInvS]
    have hInvSq : invS P * invS P = 1 := (archetype_A2_peirce_cartan_grading_and_tangent_closure hP
      upperMatchedOneForm4 lowerMatchedBarOneForm4).1
    rw [← mul_assoc, hInvSq, one_mul, hF, hPhi]
    exact hBridge.2.2.2.1
  exact ⟨hF, hStarEqSig, hStarEqSig.trans hSigEqInvS, hCov⟩

/-- Helicity-split Newman–Penrose longitudinal pole `1`-form block `(dx 0 ± dx 3)` in the
upper-right Peirce corner over `ExteriorAlgebra ℂ (Fin 4 → ℂ)`. -/
@[rep_depth transport]
def longitudinalPoleOneForm4 : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  let uPlusForm := extBasisOneForm 4 0 + extBasisOneForm 4 3
  let uMinusForm := extBasisOneForm 4 0 - extBasisOneForm 4 3
  !![0, 0, 0, uPlusForm;
     0, 0, uMinusForm, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Helicity-split Newman–Penrose transverse circular root `1`-form block `(dx 1 ± i dx 2)`
in the lower-left Peirce corner over `ExteriorAlgebra ℂ (Fin 4 → ℂ)`. -/
@[rep_depth transport]
def transverseRootOneForm4 : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  let rPlusForm := extBasisOneForm 4 1 + Complex.I • extBasisOneForm 4 2
  let rMinusForm := extBasisOneForm 4 1 - Complex.I • extBasisOneForm 4 2
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, rPlusForm, 0, 0;
     rMinusForm, 0, 0, 0]

/-- Two-sheeted helicity-split self-dual circular gauge connection `genPhi P U L`. -/
@[rep_depth transport]
def helicityCircularConnection4 : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  genPhi (upperSheetIdempotent (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
    longitudinalPoleOneForm4 transverseRootOneForm4

-- theorem-class: capstone consumer theorem
/-- Unconditional non-Abelian self-dual Yang–Mills solution from the two-sheeted
helicity-split circular connection: nonzero curvature, distinct noncommuting upper/lower
curvature blocks, `isSelfDualCurvature chiralHodgeStar4 F`, and
`covariantDerivative A 0 (matrixHodgeStar chiralHodgeStar4 F) = 0`. -/
@[rep_depth transport, capstone]
theorem helicityCircularConnection4_solves_self_dual_yang_mills :
    let P := upperSheetIdempotent (ExteriorAlgebra ℂ (Fin 4 → ℂ))
    let F := curvatureFromConnection (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))) helicityCircularConnection4
    F ≠ 0 ∧
    F 0 0 ≠ F 2 2 ∧
    F = genV P longitudinalPoleOneForm4 transverseRootOneForm4 ∧
    isSelfDualCurvature chiralHodgeStar4 F ∧
    covariantDerivative helicityCircularConnection4 0 (matrixHodgeStar chiralHodgeStar4 F) = 0 := by
  intro P F
  have hP : P * P = P := upperSheetIdempotent_sq (ExteriorAlgebra ℂ (Fin 4 → ℂ))
  have hBridge := peirce_defect_connection_curvature_and_yang_mills_bridge
    chiralHodgeStar4 (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
    hP longitudinalPoleOneForm4 transverseRootOneForm4 helicityCircularConnection4
  have hF : F = genV P longitudinalPoleOneForm4 transverseRootOneForm4 := hBridge.2.2.1
  have hCovF : covariantDerivative helicityCircularConnection4 0 F = 0 := by
    rw [hF]
    exact hBridge.2.2.2.1
  have hFExplicit : F =
      let uPlus := extBasisOneForm 4 0 + extBasisOneForm 4 3
      let uMinus := extBasisOneForm 4 0 - extBasisOneForm 4 3
      let rPlus := extBasisOneForm 4 1 + Complex.I • extBasisOneForm 4 2
      let rMinus := extBasisOneForm 4 1 - Complex.I • extBasisOneForm 4 2
      !![uPlus * rMinus, 0, 0, 0;
         0, uMinus * rPlus, 0, 0;
         0, 0, rPlus * uMinus, 0;
         0, 0, 0, rMinus * uPlus] := by
    rw [hF]
    dsimp [longitudinalPoleOneForm4, transverseRootOneForm4]
    rw [genV_upperSheet_blocks]
    simp only [mul_zero, zero_mul, add_zero, zero_add]
  have hI2 : Complex.I * Complex.I = (-1 : ℂ) := by rw [← sq, Complex.I_sq]
  have hAnti13 := extBasis4_anticomm 1 3
  have hAnti32 := extBasis4_anticomm 3 2
  have hAnti21 := extBasis4_anticomm 2 1
  have hAnti10 := extBasis4_anticomm 1 0
  have hAnti20 := extBasis4_anticomm 2 0
  have hAnti30 := extBasis4_anticomm 3 0
  have hSD : isSelfDualCurvature chiralHodgeStar4 F := by
    dsimp [isSelfDualCurvature]
    rw [hFExplicit]
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp only [matrixHodgeStar, Matrix.of_apply]
    all_goals
      try exact map_zero chiralHodgeStar4
    all_goals
      dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      repeat
        first
        | rw [add_mul]
        | rw [mul_add]
        | rw [sub_mul]
        | rw [mul_sub]
        | rw [neg_mul]
        | rw [mul_neg]
        | rw [smul_mul_assoc]
        | rw [mul_smul_comm]
        | rw [map_add]
        | rw [map_sub]
        | rw [map_neg]
        | rw [map_smul]
        | rw [extBasis4_sq]
        | rw [mul_zero]
        | rw [zero_mul]
        | rw [smul_zero]
        | rw [map_zero]
        | rw [hAnti10]
        | rw [hAnti20]
        | rw [hAnti30]
        | rw [hAnti32]
        | rw [hAnti13]
        | rw [hAnti21]
        | rw [hStar01]
        | rw [hStar02]
        | rw [hStar03]
        | rw [hStar23]
        | rw [hStar31]
        | rw [hStar12]
        | rw [smul_smul]
        | rw [hI2]
      generalize extBasisOneForm 4 0 * extBasisOneForm 4 1 = b01
      generalize extBasisOneForm 4 0 * extBasisOneForm 4 2 = b02
      generalize extBasisOneForm 4 0 * extBasisOneForm 4 3 = b03
      generalize extBasisOneForm 4 2 * extBasisOneForm 4 3 = b23
      generalize extBasisOneForm 4 3 * extBasisOneForm 4 1 = b31
      generalize extBasisOneForm 4 1 * extBasisOneForm 4 2 = b12
      module
  have hF00 : F 0 0 =
      (extBasisOneForm 4 0 + extBasisOneForm 4 3) * (extBasisOneForm 4 1 - Complex.I • extBasisOneForm 4 2) := by
    rw [hFExplicit]
    rfl
  have hF22 : F 2 2 =
      (extBasisOneForm 4 1 + Complex.I • extBasisOneForm 4 2) * (extBasisOneForm 4 0 - extBasisOneForm 4 3) := by
    rw [hFExplicit]
    rfl
  have hF00Ne0 : F 0 0 ≠ 0 := by
    intro hZ
    have hc := congrArg (blade2Coeff 0 1) hZ
    rw [hF00, map_zero] at hc
    simp only [add_mul, mul_sub, map_add, map_sub, mul_smul_comm, map_smul, smul_eq_mul,
      (blade2Coeff_eval _ _ _ _ 0).1] at hc
    norm_num at hc
  have hNe0 : F ≠ 0 := fun hZ => hF00Ne0 (by rw [hZ]; rfl)
  have hBlocksNe : F 0 0 ≠ F 2 2 := by
    intro hEq
    have hc := congrArg (blade2Coeff 0 1) hEq
    rw [hF00, hF22] at hc
    simp only [add_mul, mul_sub, mul_add, map_add, map_sub, mul_smul_comm, smul_mul_assoc,
      map_smul, smul_eq_mul, (blade2Coeff_eval _ _ _ _ 0).1] at hc
    norm_num at hc
  have hYM : covariantDerivative helicityCircularConnection4 0 (matrixHodgeStar chiralHodgeStar4 F) = 0 :=
    self_dual_connection_curvature_solves_yang_mills chiralHodgeStar4 helicityCircularConnection4 0 hSD hCovF
  exact ⟨hNe0, hBlocksNe, hF, hSD, hYM⟩

/-- Constructive `HodgeTwoFormData` over the `6D` space of real `4D` Euclidean 2-forms
`(e₀₁, e₀₂, e₀₃, e₂₃, e₃₁, e₁₂)` using the Hodge swap involution. -/
@[rep_depth transport]
def euclideanTwoFormHodgeData : HodgeTwoFormData (Fin 6 → ℝ) where
  inner u v := ∑ k : Fin 6, u k * v k
  star :=
    { toFun := fun u => ![u 3, u 4, u 5, u 0, u 1, u 2]
      map_add' := fun u v => by
        funext k; fin_cases k <;> rfl
      map_smul' := fun r u => by
        funext k; fin_cases k <;> rfl }
  inner_add_left x y z := by
    simp [Finset.sum_add_distrib, add_mul]
  inner_add_right x y z := by
    simp [Finset.sum_add_distrib, mul_add]
  inner_smul_left r x y := by
    simp [Finset.mul_sum, mul_assoc]
  inner_smul_right r x y := by
    simp [Finset.mul_sum]
    congr 1; ext k; ring
  symmetric x y := by
    congr 1; ext k; ring
  positive x := Finset.sum_nonneg fun k _ => mul_self_nonneg (x k)
  star_sq := by
    ext x k
    fin_cases k <;> rfl
  star_isometry x y := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  star_selfAdjoint x y := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring

/-- Embedding of two-sheeted chiral 2-form doublets `(fPlus, fMinus)` into `Fin 6 → ℝ`
so that `euclideanTwoFormHodgeData.star` sends `(fPlus, fMinus) ↦ (fPlus, -fMinus)`. -/
@[rep_depth transport]
def twoSheetEuclideanTwoForm (fPlus fMinus : Fin 3 → ℝ) : Fin 6 → ℝ :=
  ![fPlus 0 + fMinus 0, fPlus 1 + fMinus 1, fPlus 2 + fMinus 2,
    fPlus 0 - fMinus 0, fPlus 1 - fMinus 1, fPlus 2 - fMinus 2]

-- theorem-class: constructive endpoint
/-- Full two-sheeted Bogomolnyi action decomposition and three-way self-duality equivalence
on `BogomolnyiAlgebraicBoundBridge` (`euclideanTwoFormHodgeData`):
`S - Q = 4 ‖fMinus‖²`, `S + Q = 4 ‖fPlus‖²`, `|Q| ≤ S`, and `S = Q ↔ ★F = F ↔ fMinus = 0`. -/
@[rep_depth transport]
theorem twoSheetEuclideanTwoForm_bogomolnyi_saturation (fPlus fMinus : Fin 3 → ℝ) :
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
    change (∑ j : Fin 6, u j * u j) = 0 at hu
    have hk : ∀ k : Fin 6, u k * u k = 0 := fun k =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (u j))).mp hu k (Finset.mem_univ k)
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
      funext i
      fin_cases i
      · have hi := congrFun hEq 0
        simp [F, twoSheetEuclideanTwoForm] at hi
        linarith
      · have hi := congrFun hEq 1
        simp [F, twoSheetEuclideanTwoForm] at hi
        linarith
      · have hi := congrFun hEq 2
        simp [F, twoSheetEuclideanTwoForm] at hi
        linarith
    · intro hZero
      subst hZero
      funext k
      fin_cases k <;> simp [F, twoSheetEuclideanTwoForm]
  refine ⟨hStarFlip, hSub, hAdd, bogomolnyi_bound euclideanTwoFormHodgeData F,
    energy_eq_topologicalPairing_iff_selfDual euclideanTwoFormHodgeData hDef F, hIffSD⟩

/-! ## Layer 6: Star-Ring Colimit Transport & Unified Synthesis -/

-- theorem-class: capstone consumer theorem
/-- The complex `4 × 4` upper-sheet projection `P4C := upperSheetIdempotent ℂ` is a
self-adjoint idempotent (`P4C * P4C = P4C` and `star P4C = P4C`) and transports all
two-sheeted circular bispinor operators `circularBispinorRep X` through both arbitrary
`StarRingHom`s and `CanonicalTwoSheetedInductiveColimit.tailTowerCone`. -/
@[rep_depth transport, capstone]
theorem circularBispinor_starHom_and_colimit_transport
    {B : Type*} [Ring B] [StarRing B]
    (φ : Matrix (Fin 4) (Fin 4) ℂ →+* B)
    (hφStar : ∀ M : Matrix (Fin 4) (Fin 4) ℂ, φ (star M) = star (φ M))
    (X : CanonicalZorn) (k m : ℕ) :
    let P4C := upperSheetIdempotent ℂ
    let Cone := tailTowerCone (Matrix (Fin 4) (Fin 4) ℂ)
    let P_k : TowerLevel (Matrix (Fin 4) (Fin 4) ℂ) k := (fun _ => 0, P4C)
    let X_k : TowerLevel (Matrix (Fin 4) (Fin 4) ℂ) k := (fun _ => 0, circularBispinorRep X)
    let Xstar_k : TowerLevel (Matrix (Fin 4) (Fin 4) ℂ) k := (fun _ => 0, star (circularBispinorRep X))
    let ψ_m := (stepHomIter Cone k m).toRingHom
    let ι_km := (Cone.toColimit (k + m)).toRingHom
    let ι_k := (Cone.toColimit k).toRingHom
    P4C * P4C = P4C ∧
    star P4C = P4C ∧
    opZig (φ P4C) (φ (circularBispinorRep X)) * opZig (φ P4C) (φ (circularBispinorRep X)) = 0 ∧
    opQuadraticCoupling (φ P4C) (φ (circularBispinorRep X)) (star (φ (circularBispinorRep X))) =
      φ (opQuadraticCoupling P4C (circularBispinorRep X) (star (circularBispinorRep X))) ∧
    ι_km (opQuadraticCoupling (ψ_m P_k) (ψ_m X_k) (ψ_m Xstar_k)) =
      opQuadraticCoupling (ι_k P_k) (ι_k X_k) (ι_k Xstar_k) ∧
    ι_km (opSpinDipole (ψ_m P_k) (ψ_m X_k) (ψ_m Xstar_k)) =
      opSpinDipole (ι_k P_k) (ι_k X_k) (ι_k Xstar_k) := by
  intro P4C Cone P_k X_k Xstar_k ψ_m ι_km ι_k
  have hP : P4C * P4C = P4C := upperSheetIdempotent_sq ℂ
  have hPstar : star P4C = P4C := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P4C, upperSheetIdempotent, Matrix.star_apply]
  have hStarHom := star_hom_two_sheeted_operator_identities φ hφStar P4C (circularBispinorRep X) hP hPstar
  have hInter := starRingHom_intertwines_two_sheeted_operators φ hφStar P4C
    (circularBispinorRep X) (star (circularBispinorRep X))
  have hCoupling :
      opQuadraticCoupling (φ P4C) (φ (circularBispinorRep X)) (star (φ (circularBispinorRep X))) =
        φ (opQuadraticCoupling P4C (circularBispinorRep X) (star (circularBispinorRep X))) := by
    rw [← hφStar (circularBispinorRep X)]
    exact hInter.2.2.2.2.2.1.symm
  have hRG := colimit_renormalization_scale_invariance Cone k m P_k X_k Xstar_k X_k
  exact ⟨hP, hPstar, hStarHom.1, hCoupling, hRG.2.1, hRG.2.2.1⟩

-- theorem-class: capstone consumer theorem
/-- Unified synthesis joining the five disconnected repository corridors on their actual
carriers: doubled Krein `Cl(1,1)` frame and `(1,3)` pullback, circular split-octonion
Peirce channels, double-chiral `ℂ² ⊕ ℂ²` Pauli trace/norm contraction, noncommutative two-sheet
gauge–Higgs curvature splitting, and unconditional self-dual Yang–Mills solution & Bogomolnyi
saturation. -/
@[rep_depth transport, capstone]
theorem master_doubled_minkowski_circular_octonion_yang_mills_bridge
    (X Y : CanonicalZorn) (a : Fin 3) (AL AR : Operator (Fin 2 → ℂ))
    (fPlus fMinus : Fin 3 → ℝ) :
    let P_sheet := firstSheetProjection (W := Fin 2 → ℂ)
    let Γ_sheet := invS P_sheet
    let J_sheet := sheetFlipMatrix (Operator (Fin 2 → ℂ))
    let D := twoSheetGaugeHiggsConnection AL AR
      (Matrix.toLin' (chiralPlusWeyl X)) (Matrix.toLin' (chiralMinusBarWeyl X))
    let F_sd := curvatureFromConnection (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))) helicityCircularConnection4
    let F_2 := twoSheetEuclideanTwoForm fPlus fMinus
    (chiralKreinForm (E := FourSpace)
        (lorentzCircularZornToKreinFrame X)
        (lorentzCircularZornToKreinFrame Y) =
      circularPeircePolar (coordinateEquiv X) (coordinateEquiv Y) ∧
     Γ_sheet * J_sheet + J_sheet * Γ_sheet = 0) ∧
    (uPlus * rootPlus a = rootPlus a ∧ uMinus * rootMinus a = rootMinus a) ∧
    (Matrix.trace (circularBispinorRep X * circularBispinorRep Y) =
      2 * (chiralKreinForm (E := FourSpace)
        (lorentzCircularZornToKreinFrame X) (lorentzCircularZornToKreinFrame Y) : ℂ) ∧
     wittNorm (coordinateEquiv X) =
      (longitudinalPoleBlock X).det - (transverseColorBlock X).det) ∧
    ((D * D) + Γ_sheet * (D * D) * Γ_sheet =
      (2 : ℕ) • !![AL * AL + Matrix.toLin' (chiralPlusWeyl X) * Matrix.toLin' (chiralMinusBarWeyl X), 0;
                   0, Matrix.toLin' (chiralMinusBarWeyl X) * Matrix.toLin' (chiralPlusWeyl X) + AR * AR]) ∧
    (F_sd ≠ 0 ∧
     covariantDerivative helicityCircularConnection4 0 (matrixHodgeStar chiralHodgeStar4 F_sd) = 0 ∧
     (yangMillsEnergy euclideanTwoFormHodgeData F_2 = topologicalPairing euclideanTwoFormHodgeData F_2 ↔
       fMinus = 0)) := by
  intro P_sheet Γ_sheet J_sheet D F_sd F_2
  have h1 := (chiralKreinForm_lorentzCircularZornToKreinFrame X Y).1
  have h1b := (sheetAlgebra_cl11_chirality_and_pole_laws (Fin 2 → ℂ)).2.2.2.1
  have h2 := canonicalZorn_circular_peirce_and_longitudinal_transverse_bridge X a
  have h3 := circularBispinor_noncomm_trace_and_det X Y
  have h4 := twoSheetGaugeHiggsConnection_curvature_and_parity_split AL AR
    (Matrix.toLin' (chiralPlusWeyl X)) (Matrix.toLin' (chiralMinusBarWeyl X)) X
  have h5a := helicityCircularConnection4_solves_self_dual_yang_mills
  have h5b := twoSheetEuclideanTwoForm_bogomolnyi_saturation fPlus fMinus
  exact ⟨⟨h1, h1b⟩,
    ⟨h2.2.2.2.2.1, h2.2.2.2.2.2.2.2.1⟩,
    ⟨h3.2.1, h2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩,
    h4.2.2.1,
    ⟨h5a.1, h5a.2.2.2.2, h5b.2.2.2.2.1.trans h5b.2.2.2.2.2⟩⟩

end InfoGeometry.Canonical.DoubledMinkowskiCircularOctonionYangMillsBridge

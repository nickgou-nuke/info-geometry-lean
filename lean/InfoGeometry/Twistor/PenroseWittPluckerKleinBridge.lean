/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Twistor.PenroseZornWittBoundary
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.CanonicalZornPhasePluckerProjection
import InfoGeometry.Twistor.PhaseNativePluckerBridge
import InfoGeometry.Projective.KleinQuadricPlucker
import InfoGeometry.Algebra.ZornAlternativeLaws
import InfoGeometry.Canonical.ZornMatrixVectorCarrierBridge
import InfoGeometry.Algebra.SuperGrassmannianClifford
import InfoGeometry.Projective.ExteriorPowerPluckerBridge
import InfoGeometry.Canonical.DecomposableBivector
import Mathlib.Tactic
import Mathlib.Tactic

/-!
# Plücker and Klein Readout of the Witt-Polarized Penrose-to-Zorn Map

This module formalizes the exact bridge between:
1. **The Witt-Polarized Penrose Twistor Map**:
   $$Z \in \text{Twistor4} \mapsto \text{penroseWittZornMap } Z \in \text{CZ}$$
2. **The Off-Diagonal Canonical Zorn Phase**:
   $$\text{offDiagonalPhase } (\text{cartesianZornLinearEquiv } (\text{penroseWittZornMap } Z))$$
3. **The Native Plücker 6-Vector**:
   $$\text{penroseWittPlucker6 } Z \in \text{Plucker6 } \mathbb{R}$$

## Core Mathematical Theorems Verified:
1. **Explicit Plücker Coordinate Readout**:
   - $p_{01} = \operatorname{Im}(\omega_0) + \operatorname{Im}(\pi_0)$
   - $p_{02} = \operatorname{Re}(\omega_1) + \operatorname{Re}(\pi_1)$
   - $p_{03} = \operatorname{Im}(\omega_1) + \operatorname{Im}(\pi_1)$
   - $p_{12} = -\operatorname{Im}(\omega_1) + \operatorname{Im}(\pi_1)$
   - $p_{13} = \operatorname{Re}(\omega_1) - \operatorname{Re}(\pi_1)$
   - $p_{23} = -\operatorname{Im}(\omega_0) + \operatorname{Im}(\pi_0)$

2. **Zorn Determinant vs. Klein Quadric Decomposition**:
   $$\det_Z(\text{penroseWittZornMap } Z) = u_+ \cdot u_- - \text{kleinQ}(\text{penroseWittPlucker6 } Z)$$
   where $u_+ = \operatorname{Re}(\omega_0) + \operatorname{Re}(\pi_0)$ and $u_- = \operatorname{Re}(\omega_0) - \operatorname{Re}(\pi_0)$ are the diagonal Witt coordinates.

3. **Off-Diagonal Null Equivalence**:
   For twistors with vanishing diagonal product $u_+ \cdot u_- = 0$,
   $$\det_Z(\text{penroseWittZornMap } Z) = 0 \iff \text{kleinQ}(\text{penroseWittPlucker6 } Z) = 0$$

All proofs are complete in native Mathlib 4 with zero proof holes and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.Twistor.PenroseWittPluckerKleinBridge

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.PenroseTwistor
open InfoGeometry.Twistor.ChiralTwistorSheets
open InfoGeometry.Twistor.PenroseZornWittBoundary
open InfoGeometry.Twistor.CanonicalZornPhasePluckerProjection
open InfoGeometry.Twistor.PhaseNativePluckerBridge
open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

/-- The native real Plücker 6-vector extracted from the Witt-polarized Penrose-to-Zorn map. -/
def penroseWittPlucker6 (Z : Twistor4) : Plucker6 ℝ where
  p01 := (Z.1 0).im + (Z.2 0).im
  p02 := (Z.1 1).re + (Z.2 1).re
  p03 := (Z.1 1).im + (Z.2 1).im
  p12 := -(Z.1 1).im + (Z.2 1).im
  p13 := (Z.1 1).re - (Z.2 1).re
  p23 := -(Z.1 0).im + (Z.2 0).im

/-- 🏆 THEOREM: The extracted Plücker 6-vector coincides with the canonical off-diagonal phase projection. -/
theorem penroseWittPlucker6_eq_phaseToPlucker6 (Z : Twistor4) :
    penroseWittPlucker6 Z =
      phaseToPlucker6
        (![(Z.1 0).im + (Z.2 0).im, (Z.1 1).re + (Z.2 1).re, (Z.1 1).im + (Z.2 1).im],
         ![-(Z.1 0).im + (Z.2 0).im, -(Z.1 1).re + (Z.2 1).re, -(Z.1 1).im + (Z.2 1).im]) := by
  dsimp [penroseWittPlucker6, phaseToPlucker6]
  ext <;> ring

/-- 🏆 THEOREM: The Klein quadric evaluation on the Witt-polarized Plücker 6-vector. -/
theorem kleinQ_penroseWittPlucker6 (Z : Twistor4) :
    kleinQ (penroseWittPlucker6 Z) =
      ((Z.1 0).im + (Z.2 0).im) * (-(Z.1 0).im + (Z.2 0).im) -
      ((Z.1 1).re + (Z.2 1).re) * ((Z.1 1).re - (Z.2 1).re) +
      ((Z.1 1).im + (Z.2 1).im) * (-(Z.1 1).im + (Z.2 1).im) :=
  rfl

/-- Positive diagonal Witt coordinate $u_+ = \operatorname{Re}(\omega_0) + \operatorname{Re}(\pi_0)$. -/
def wittUplus (Z : Twistor4) : ℝ := (Z.1 0).re + (Z.2 0).re

/-- Negative diagonal Witt coordinate $u_- = \operatorname{Re}(\omega_0) - \operatorname{Re}(\pi_0)$. -/
def wittUminus (Z : Twistor4) : ℝ := (Z.1 0).re - (Z.2 0).re

/-- 🏆 MASTER THEOREM: The Zorn reduced norm decomposes into the diagonal Witt product minus the Klein quadric. -/
theorem penroseWittZorn_norm_eq_diagonal_sub_kleinQ (Z : Twistor4) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        (penroseWittZornMap Z) =
      wittUplus Z * wittUminus Z - kleinQ (penroseWittPlucker6 Z) := by
  rw [penroseWittZorn_norm_eq_splitSignature]
  dsimp [penroseRealSplitSignature, wittUplus, wittUminus, kleinQ, penroseWittPlucker6]
  ring

/-- 🏆 THEOREM: Off-diagonal null equivalence on the Klein quadric. -/
theorem offDiagonal_null_iff_klein_null (Z : Twistor4)
    (h_diag : wittUplus Z * wittUminus Z = 0) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        (penroseWittZornMap Z) = 0 ↔
      kleinQ (penroseWittPlucker6 Z) = 0 := by
  rw [penroseWittZorn_norm_eq_diagonal_sub_kleinQ, h_diag, zero_sub]
  constructor
  · intro h
    linarith
  · intro h
    rw [h, neg_zero]


/-! ## Part A: Exact Bridge to `ZornAlternativeLaws.zornPluckerLineMatrix` -/

section ZornPluckerLineBridge

/-- Transport `penroseWittZornMap Z : CZ` to the `ZornVectorMatrix ℝ` carrier. -/
def penroseWittZornVectorMatrix (Z : Twistor4) :
    InfoGeometry.Algebra.ZornVectorMatrix ℝ :=
  InfoGeometry.Canonical.zornMatrixToVector (penroseWittZornMap Z)

/-- Explicit coordinate evaluation of `penroseWittZornVectorMatrix Z` in terms of `wittUplus`,
`wittUminus`, and the Witt-polarized imaginary/real spinor combinations. -/
theorem penroseWittZornVectorMatrix_apply (Z : Twistor4) :
    penroseWittZornVectorMatrix Z =
      ⟨wittUplus Z,
        ![(Z.1 0).im + (Z.2 0).im, (Z.1 1).re + (Z.2 1).re, (Z.1 1).im + (Z.2 1).im],
        ![-(Z.1 0).im + (Z.2 0).im, -(Z.1 1).re + (Z.2 1).re, -(Z.1 1).im + (Z.2 1).im],
        wittUminus Z⟩ := by
  have hc : ∀ i : Fin 8,
      InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.circularCoordinate
          (InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv.symm
            (penroseWittZornMap Z)) i =
        penroseWittCoordinates Z i := by
    intro i
    change InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.circularCoordinate
        (InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv.symm
          (real8CircularPeirceEquiv (penroseWittCoordinates Z))) i = _
    rw [circularPeirceBasis_coordinate_eq_equivFun]
    exact congrFun (circularPeirce_coordinates_real8 (penroseWittCoordinates Z)) i
  have ha : (penroseWittZornMap Z).a = wittUplus Z := by
    have h0 := hc 0
    simp [InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.circularCoordinate,
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv_symm_apply,
      penroseWittCoordinates] at h0
    dsimp [wittUplus]
    linarith
  have hb : (penroseWittZornMap Z).b = wittUminus Z := by
    have h4 := hc 4
    simp [InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.circularCoordinate,
      InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv_symm_apply,
      penroseWittCoordinates] at h4
    dsimp [wittUminus]
    linarith
  have hx : (penroseWittZornMap Z).x =
      ![(Z.1 0).im + (Z.2 0).im, (Z.1 1).re + (Z.2 1).re, (Z.1 1).im + (Z.2 1).im] := by
    ext i
    have hxi := (offDiagonalPhase_circular_coordinates (penroseWittZornMap Z) i).1
    fin_cases i
    · simpa [penroseWittCoordinates] using hxi.trans (hc 1)
    · simpa [penroseWittCoordinates] using hxi.trans (hc 2)
    · simpa [penroseWittCoordinates] using hxi.trans (hc 3)
  have hy : (penroseWittZornMap Z).y =
      ![-(Z.1 0).im + (Z.2 0).im, -(Z.1 1).re + (Z.2 1).re, -(Z.1 1).im + (Z.2 1).im] := by
    ext i
    have hyi := (offDiagonalPhase_circular_coordinates (penroseWittZornMap Z) i).2
    fin_cases i
    · simpa [penroseWittCoordinates] using hyi.trans (hc 5)
    · simpa [penroseWittCoordinates] using hyi.trans (hc 6)
    · simpa [penroseWittCoordinates] using hyi.trans (hc 7)
  dsimp [penroseWittZornVectorMatrix, InfoGeometry.Canonical.zornMatrixToVector]
  rw [ha, hb, hx, hy]

/-- Off-diagonal projection of `penroseWittZornVectorMatrix Z` agrees with `plucker6ToPhase
(penroseWittPlucker6 Z)`. -/
theorem offDiagonalPart_penroseWittZornVectorMatrix (Z : Twistor4) :
    InfoGeometry.Algebra.ZornVectorMatrix.offDiagonalPart (penroseWittZornVectorMatrix Z) =
      ⟨0, (plucker6ToPhase (penroseWittPlucker6 Z)).1,
        (plucker6ToPhase (penroseWittPlucker6 Z)).2, 0⟩ := by
  rw [penroseWittZornVectorMatrix_apply]
  dsimp [InfoGeometry.Algebra.ZornVectorMatrix.offDiagonalPart,
    plucker6ToPhase, penroseWittPlucker6]
  congr 1
  ext i; fin_cases i <;> simp [sub_eq_add_neg, add_comm]

/-- `ZornAlternativeLaws.zornPluckerLineMatrix x y` matches the off-diagonal Zorn vector-matrix
of `pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩` over any `[CommRing R]`. -/
theorem plucker6_offDiagonal_eq_zornPluckerLineMatrix {R : Type*} [CommRing R] (x y : Fin 4 → R) :
    InfoGeometry.Algebra.ZornVectorMatrix.zornPluckerLineMatrix x y =
      ⟨0,
        ![(pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩).p01,
          (pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩).p02,
          (pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩).p03],
        ![(pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩).p23,
          -(pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩).p13,
          (pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩).p12],
        0⟩ := by
  dsimp [InfoGeometry.Algebra.ZornVectorMatrix.zornPluckerLineMatrix,
    InfoGeometry.Algebra.ZornVectorMatrix.zornPluckerRad,
    InfoGeometry.Algebra.ZornVectorMatrix.zornPluckerTrans,
    pluckerLine]
  congr 1
  · ext i; fin_cases i <;> simp [mul_comm]
  · ext i; fin_cases i <;> simp [mul_comm]

/-- Real specialization of `plucker6_offDiagonal_eq_zornPluckerLineMatrix` matching `plucker6ToPhase`. -/
theorem plucker6_offDiagonal_eq_zornPluckerLineMatrix_real (x y : Fin 4 → ℝ) :
    InfoGeometry.Algebra.ZornVectorMatrix.zornPluckerLineMatrix x y =
      ⟨0,
        (plucker6ToPhase (pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩)).1,
        (plucker6ToPhase (pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩)).2,
        0⟩ := by
  rw [plucker6_offDiagonal_eq_zornPluckerLineMatrix]
  rfl

/-- Over `ℝ`, a `Plucker6 ℝ` satisfies the Klein quadric `kleinQ P = 0` iff its off-diagonal
Zorn matrix is realized as a projective line matrix `zornPluckerLineMatrix x y` across
all 6 coordinate charts. -/
theorem kleinQ_zero_iff_exists_zornPluckerLineMatrix (P : Plucker6 ℝ) :
    kleinQ P = 0 ↔
      ∃ x y : Fin 4 → ℝ,
        InfoGeometry.Algebra.ZornVectorMatrix.zornPluckerLineMatrix x y =
          ⟨0, (plucker6ToPhase P).1, (plucker6ToPhase P).2, 0⟩ := by
  constructor
  · intro hK
    let B : InfoGeometry.Canonical.FierzKleinFoundation.Bivector4 :=
      ⟨P.p01, P.p02, P.p03, P.p12, P.p13, P.p23⟩
    have hB : InfoGeometry.Canonical.FierzKleinFoundation.kleinForm B = 0 := by
      simpa [B, InfoGeometry.Canonical.FierzKleinFoundation.kleinForm, kleinQ] using hK
    obtain ⟨u, v, huv⟩ :=
      (InfoGeometry.Projective.ExteriorPowerPluckerBridge.kleinForm_eq_zero_iff_exists_wedge B).1 hB
    let x : Fin 4 → ℝ := ![u .t, u .x, u .y, u .z]
    let y : Fin 4 → ℝ := ![v .t, v .x, v .y, v .z]
    refine ⟨x, y, ?_⟩
    rw [plucker6_offDiagonal_eq_zornPluckerLineMatrix_real]
    have hP : pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩ = P := by
      have h01 := congrArg InfoGeometry.Canonical.FierzKleinFoundation.Bivector4.p01 huv
      have h02 := congrArg InfoGeometry.Canonical.FierzKleinFoundation.Bivector4.p02 huv
      have h03 := congrArg InfoGeometry.Canonical.FierzKleinFoundation.Bivector4.p03 huv
      have h12 := congrArg InfoGeometry.Canonical.FierzKleinFoundation.Bivector4.p12 huv
      have h13 := congrArg InfoGeometry.Canonical.FierzKleinFoundation.Bivector4.p13 huv
      have h23 := congrArg InfoGeometry.Canonical.FierzKleinFoundation.Bivector4.p23 huv
      ext
      · simpa [x, y, pluckerLine, B, InfoGeometry.Canonical.FierzKleinFoundation.wedgeVec4] using h01
      · simpa [x, y, pluckerLine, B, InfoGeometry.Canonical.FierzKleinFoundation.wedgeVec4] using h02
      · simpa [x, y, pluckerLine, B, InfoGeometry.Canonical.FierzKleinFoundation.wedgeVec4] using h03
      · simpa [x, y, pluckerLine, B, InfoGeometry.Canonical.FierzKleinFoundation.wedgeVec4] using h12
      · simpa [x, y, pluckerLine, B, InfoGeometry.Canonical.FierzKleinFoundation.wedgeVec4] using h13
      · simpa [x, y, pluckerLine, B, InfoGeometry.Canonical.FierzKleinFoundation.wedgeVec4] using h23
    rw [hP]
  · rintro ⟨x, y, hxy⟩
    rw [plucker6_offDiagonal_eq_zornPluckerLineMatrix_real] at hxy
    have h1 := congrArg InfoGeometry.Algebra.ZornVectorMatrix.v hxy
    have h2 := congrArg InfoGeometry.Algebra.ZornVectorMatrix.w hxy
    have hP : pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩ = P := by
      have hv0 := congrFun h1 0
      have hv1 := congrFun h1 1
      have hv2 := congrFun h1 2
      have hw0 := congrFun h2 0
      have hw1 := congrFun h2 1
      have hw2 := congrFun h2 2
      ext
      · simpa [plucker6ToPhase] using hv0
      · simpa [plucker6ToPhase] using hv1
      · simpa [plucker6ToPhase] using hv2
      · simpa [plucker6ToPhase] using hw2
      · have hw1' : -((pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩).p13) = -P.p13 := by
          simpa [plucker6ToPhase] using hw1
        linarith
      · simpa [plucker6ToPhase] using hw0
    rw [← hP]
    exact kleinQ_pluckerLine _ _

/-- A Witt-polarized Penrose twistor `Z` satisfies `kleinQ (penroseWittPlucker6 Z) = 0` iff
the off-diagonal part of `penroseWittZornVectorMatrix Z` is a Dahm simple line matrix
`zornPluckerLineMatrix x y`. -/
theorem penroseWittZorn_offDiagonal_eq_zornPluckerLineMatrix_iff (Z : Twistor4) :
    kleinQ (penroseWittPlucker6 Z) = 0 ↔
      ∃ x y : Fin 4 → ℝ,
        InfoGeometry.Algebra.ZornVectorMatrix.zornPluckerLineMatrix x y =
          InfoGeometry.Algebra.ZornVectorMatrix.offDiagonalPart (penroseWittZornVectorMatrix Z) := by
  rw [offDiagonalPart_penroseWittZornVectorMatrix]
  exact kleinQ_zero_iff_exists_zornPluckerLineMatrix (penroseWittPlucker6 Z)

/-- When a twistor `Z` is diagonally and Witt-null (`wittUplus Z * wittUminus Z = 0` and
`detZ (penroseWittZornMap Z) = 0`), its off-diagonal part is realized by a simple projective
line matrix `zornPluckerLineMatrix x y` that is square-zero nilpotent and isotropic. -/
theorem penroseWittZorn_null_offDiagonal_square_zero (Z : Twistor4)
    (h_diag : wittUplus Z * wittUminus Z = 0)
    (h_det : InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        (penroseWittZornMap Z) = 0) :
    ∃ x y : Fin 4 → ℝ,
      InfoGeometry.Algebra.ZornVectorMatrix.zornPluckerLineMatrix x y =
        InfoGeometry.Algebra.ZornVectorMatrix.offDiagonalPart (penroseWittZornVectorMatrix Z) ∧
      InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.zornPluckerLineMatrix x y)
        (InfoGeometry.Algebra.ZornVectorMatrix.zornPluckerLineMatrix x y) =
          InfoGeometry.Algebra.ZornVectorMatrix.zero ∧
      InfoGeometry.Algebra.ZornVectorMatrix.norm
        (InfoGeometry.Algebra.ZornVectorMatrix.zornPluckerLineMatrix x y) = 0 := by
  have hK : kleinQ (penroseWittPlucker6 Z) = 0 :=
    (offDiagonal_null_iff_klein_null Z h_diag).1 h_det
  obtain ⟨x, y, hxy⟩ := (penroseWittZorn_offDiagonal_eq_zornPluckerLineMatrix_iff Z).1 hK
  have hnil := InfoGeometry.Algebra.ZornVectorMatrix.dahm_simple_plucker_line_null_square_and_unipotent_inversion
    x y 1 0 0
  exact ⟨x, y, hxy, hnil.2.1, hnil.1⟩

end ZornPluckerLineBridge

/-! ## Part B: Generalized Clifford–Exterior Bivector Decomposability & `Cl(2,2)` Sobczyk Bridge -/

section GeneralCliffordPlucker

open InfoGeometry.Algebra.SuperGrassmannianClifford

/-- Over any `[CommRing R] [Invertible (2 : R)]` and arbitrary quadratic space `(V, Q)`,
the metric interior contraction of a decomposable bivector `ι u * ι v` by `w` lies in
`span {ι u, ι v}`: `w ⌟ (ι u ∧ ι v) = ⟨w, u⟩ ι v - ⟨w, v⟩ ι u`. -/
theorem interiorProduct_decomposable_bivector
    {R V : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup V] [Module R V]
    (Q : QuadraticForm R V) (w u v : V) :
    interiorProduct Q w (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) =
      metricInner Q w u • ExteriorAlgebra.ι R v -
        metricInner Q w v • ExteriorAlgebra.ι R u := by
  have hsymm :
      (cliffordExteriorEquiv Q).symm (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) =
        CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v -
          algebraMap R (CliffordAlgebra Q) (metricInner Q u v) := by
    rw [cliffordExteriorEquiv_symm_ι_mul]
    have hv : (cliffordExteriorEquiv Q).symm (ExteriorAlgebra.ι R v) =
        CliffordAlgebra.ι Q v := by
      apply (cliffordExteriorEquiv Q).injective
      simp [cliffordExteriorEquiv]
    rw [hv, CliffordAlgebra.contractLeft_ι]
    rfl
  rw [interiorProduct, hsymm, map_sub, map_sub]
  have hcone : CliffordAlgebra.contractLeft (QuadraticMap.associated Q w)
      (algebraMap R (CliffordAlgebra Q) (metricInner Q u v)) = 0 := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, CliffordAlgebra.contractLeft_one, smul_zero]
  rw [hcone, map_zero, sub_zero, CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι]
  have hmap_smul_alg : ∀ (c : R) (x : CliffordAlgebra Q),
      cliffordExteriorEquiv Q (algebraMap R (CliffordAlgebra Q) c * x) =
        c • cliffordExteriorEquiv Q x := by
    intro c x
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul]
  have hu : cliffordExteriorEquiv Q (CliffordAlgebra.ι Q u) = ExteriorAlgebra.ι R u := by
    simp [cliffordExteriorEquiv]
  have hv : cliffordExteriorEquiv Q (CliffordAlgebra.ι Q v) = ExteriorAlgebra.ι R v := by
    simp [cliffordExteriorEquiv]
  rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, map_sub, map_smul, map_smul, hu, hv]
  rfl

/-- **Generalized Sobczyk Plücker Relation (Eq. 5)** over arbitrary `(R, V, Q)`:
for every decomposable bivector `B = ι u * ι v` and every vector `w : V`,
`(w ⌟ B) ∧ B = 0`. -/
theorem outerProduct_interiorProduct_decomposable_eq_zero
    {R V : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup V] [Module R V]
    (Q : QuadraticForm R V) (w u v : V) :
    outerProduct
        (interiorProduct Q w (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v))
        (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) = 0 := by
  rw [interiorProduct_decomposable_bivector]
  dsimp [outerProduct]
  rw [sub_mul, smul_mul_assoc, smul_mul_assoc]
  have h1 : ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) = 0 := by
    have hanti := outerProduct_vectors_anticommute (R := R) v u
    dsimp [outerProduct] at hanti
    calc
      ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v)
          = (ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u) * ExteriorAlgebra.ι R v := by
              rw [mul_assoc]
      _ = (-(ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v)) * ExteriorAlgebra.ι R v := by
              rw [hanti]
      _ = -(ExteriorAlgebra.ι R u * (ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R v)) := by
              noncomm_ring
      _ = -(ExteriorAlgebra.ι R u * 0) := by rw [ExteriorAlgebra.ι_sq_zero]
      _ = 0 := by simp
  have h2 : ExteriorAlgebra.ι R u * (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) = 0 := by
    rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
  rw [h1, h2, smul_zero, smul_zero, sub_self]

/-- **Generalized Sobczyk Geometric-Square Law (Theorem 2, forward)** over arbitrary `(R, V, Q)`:
the Clifford geometric square of any decomposable bivector `B = ι u * ι v` is purely scalar,
equal to `(⟨u, v⟩² - Q u * Q v) • 1`. -/
theorem geometricProduct_decomposable_bivector_self
    {R V : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup V] [Module R V]
    (Q : QuadraticForm R V) (u v : V) :
    geometricProduct Q
        (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v)
        (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) =
      algebraMap R (ExteriorTower R V)
        ((metricInner Q u v) ^ 2 - Q u * Q v) := by
  have hsymm :
      (cliffordExteriorEquiv Q).symm (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) =
        CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v -
          algebraMap R (CliffordAlgebra Q) (metricInner Q u v) := by
    rw [cliffordExteriorEquiv_symm_ι_mul]
    have hv : (cliffordExteriorEquiv Q).symm (ExteriorAlgebra.ι R v) =
        CliffordAlgebra.ι Q v := by
      apply (cliffordExteriorEquiv Q).injective
      simp [cliffordExteriorEquiv]
    rw [hv, CliffordAlgebra.contractLeft_ι]
    rfl
  have hpolar : QuadraticMap.polar Q u v = 2 * metricInner Q u v := by
    have h2 : (2 • QuadraticMap.associated Q) u v = Q.polarBilin u v := by
      rw [QuadraticMap.two_nsmul_associated (S := R)]
    change (2 : ℕ) • metricInner Q u v = QuadraticMap.polar Q u v at h2
    rw [nsmul_eq_mul, Nat.cast_ofNat] at h2
    exact h2.symm
  have hswap : CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q u =
      algebraMap R (CliffordAlgebra Q) (2 * metricInner Q u v) -
        CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v := by
    have hadd := CliffordAlgebra.ι_mul_ι_add_swap (Q := Q) u v
    rw [hpolar] at hadd
    exact eq_sub_of_add_eq' hadd
  have hsq_cl :
      (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v -
          algebraMap R (CliffordAlgebra Q) (metricInner Q u v)) *
        (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v -
          algebraMap R (CliffordAlgebra Q) (metricInner Q u v)) =
        algebraMap R (CliffordAlgebra Q) ((metricInner Q u v) ^ 2 - Q u * Q v) := by
    let α := metricInner Q u v
    have hquad :
        (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) *
          (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) =
          algebraMap R (CliffordAlgebra Q) (2 * α) *
            (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) -
            algebraMap R (CliffordAlgebra Q) (Q u * Q v) := by
      calc
        (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) *
            (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v)
            = CliffordAlgebra.ι Q u * (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q u) *
                CliffordAlgebra.ι Q v := by noncomm_ring
        _ = CliffordAlgebra.ι Q u *
              (algebraMap R (CliffordAlgebra Q) (2 * α) -
                CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) *
              CliffordAlgebra.ι Q v := by rw [hswap]
        _ = algebraMap R (CliffordAlgebra Q) (2 * α) *
              (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) -
              (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q u) *
                (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v) := by
              rw [mul_sub, sub_mul, ← (Algebra.commutes (2 * α) (CliffordAlgebra.ι Q u))]
              noncomm_ring
        _ = algebraMap R (CliffordAlgebra Q) (2 * α) *
              (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) -
              algebraMap R (CliffordAlgebra Q) (Q u * Q v) := by
              rw [CliffordAlgebra.ι_sq_scalar, CliffordAlgebra.ι_sq_scalar,
                ← map_mul (algebraMap R (CliffordAlgebra Q))]
    calc
      (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v -
          algebraMap R (CliffordAlgebra Q) α) *
        (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v -
          algebraMap R (CliffordAlgebra Q) α)
          = (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) *
              (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) -
            algebraMap R (CliffordAlgebra Q) (2 * α) *
              (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) +
            algebraMap R (CliffordAlgebra Q) (α ^ 2) := by
              rw [mul_sub, sub_mul, sub_mul, ← map_mul (algebraMap R (CliffordAlgebra Q)), ← sq]
              have h2α : algebraMap R (CliffordAlgebra Q) (2 * α) =
                  algebraMap R (CliffordAlgebra Q) α + algebraMap R (CliffordAlgebra Q) α := by
                rw [two_mul, map_add]
              have hcomm :
                  (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) *
                    algebraMap R (CliffordAlgebra Q) α =
                    algebraMap R (CliffordAlgebra Q) α *
                      (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) :=
                (Algebra.commutes _ _).symm
              rw [h2α, add_mul, hcomm]
              noncomm_ring
      _ = algebraMap R (CliffordAlgebra Q) (α ^ 2 - Q u * Q v) := by
            rw [hquad, map_sub]
            abel
  rw [geometricProduct, hsymm, hsq_cl]
  simp [cliffordExteriorEquiv, Algebra.algebraMap_eq_smul_one]

/-- Iterated isometric exterior embedding `SplitExteriorStage n →ₗ[ℝ] SplitExteriorStage (n + k)`
for arbitrary tower height `n + k`. -/
noncomputable def splitStageExteriorTowerMap (n : ℕ) :
    (k : ℕ) → SplitExteriorStage n →ₗ[ℝ] SplitExteriorStage (n + k)
  | 0 => LinearMap.id
  | k + 1 => (splitStageExteriorMap (n + k)).comp (splitStageExteriorTowerMap n k)

/-- The iterated exterior tower embedding preserves `geometricProduct` across arbitrary
split-signature stages `n → n + k`. -/
theorem splitStageExteriorTowerMap_geometricProduct (n k : ℕ)
    (x y : SplitExteriorStage n) :
    splitStageExteriorTowerMap n k
        (geometricProduct (InfoGeometry.CliffordTower.Qsplit n) x y) =
      geometricProduct (InfoGeometry.CliffordTower.Qsplit (n + k))
        (splitStageExteriorTowerMap n k x) (splitStageExteriorTowerMap n k y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change splitStageExteriorMap (n + k) (splitStageExteriorTowerMap n k
        (geometricProduct (InfoGeometry.CliffordTower.Qsplit n) x y)) =
      geometricProduct (InfoGeometry.CliffordTower.Qsplit (n + k + 1))
        (splitStageExteriorMap (n + k) (splitStageExteriorTowerMap n k x))
        (splitStageExteriorMap (n + k) (splitStageExteriorTowerMap n k y))
    rw [ih, splitStageExteriorMap_geometricProduct]

end GeneralCliffordPlucker

/-! ## Part C: `SplitExteriorStage 2` (`Cl(2,2)`) Plücker–Clifford & Sobczyk Lemma 2 Bridge -/

section SplitExterior2Sobczyk

open InfoGeometry.CliffordTower
open InfoGeometry.Algebra.SuperGrassmannianClifford

private noncomputable instance splitTwoInvertible : Invertible (2 : ℝ) :=
  invertibleOfNonzero (by norm_num)

/-- Orthonormal split `(2,2)` basis vectors `e₀, e₁, e₂, e₃` of `SplitSpace 2`. -/
def splitSpace2Vec : Fin 4 → SplitSpace 2
  | 0 => ((1, 0), ((0, 0), 0))
  | 1 => ((0, 1), ((0, 0), 0))
  | 2 => ((0, 0), ((1, 0), 0))
  | 3 => ((0, 0), ((0, 1), 0))

/-- Split `(2,2)` signature signs `(+1, -1, +1, -1)` of the basis `splitSpace2Vec`. -/
def splitSign : Fin 4 → ℝ
  | 0 => 1
  | 1 => -1
  | 2 => 1
  | 3 => -1

/-- Coordinate linear equivalence `SplitSpace 2 ≃ₗ[ℝ] (Fin 4 → ℝ)`. -/
def splitSpace2Fin4Equiv : SplitSpace 2 ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun v := ![v.1.1, v.1.2, v.2.1.1, v.2.1.2]
  invFun x := ((x 0, x 1), ((x 2, x 3), 0))
  left_inv v := by
    rcases v with ⟨⟨a, b⟩, ⟨⟨c, d⟩, z⟩⟩
    refine Prod.ext rfl (Prod.ext rfl (funext fun i => Fin.elim0 i))
  right_inv x := by
    ext i
    fin_cases i <;> rfl
  map_add' u v := by
    ext i
    fin_cases i <;> simp
  map_smul' c v := by
    ext i
    fin_cases i <;> simp

/-- Linear equivalence `SplitSpace 2 ≃ₗ[ℝ] FierzKleinFoundation.Vec4`. -/
def splitSpace2ToFierzVec4 :
    SplitSpace 2 ≃ₗ[ℝ] InfoGeometry.Canonical.FierzKleinFoundation.Vec4 where
  toFun v i := match i with
    | .t => v.1.1
    | .x => v.1.2
    | .y => v.2.1.1
    | .z => v.2.1.2
  invFun f := ((f .t, f .x), ((f .y, f .z), 0))
  left_inv v := by
    rcases v with ⟨⟨a, b⟩, ⟨⟨c, d⟩, z⟩⟩
    refine Prod.ext rfl (Prod.ext rfl (funext fun i => Fin.elim0 i))
  right_inv f := by
    ext i
    cases i <;> rfl
  map_add' u v := by
    ext i
    cases i <;> simp
  map_smul' c v := by
    ext i
    cases i <;> simp

/-- Explicit basis `(Fin 4)` of `SplitSpace 2`. -/
noncomputable def splitSpace2Basis : Module.Basis (Fin 4) ℝ (SplitSpace 2) :=
  (Pi.basisFun ℝ (Fin 4)).map splitSpace2Fin4Equiv.symm

@[simp] theorem splitSpace2Basis_apply (i : Fin 4) :
    splitSpace2Basis i = splitSpace2Vec i := by
  rw [splitSpace2Basis, Module.Basis.map_apply, Pi.basisFun_apply]
  fin_cases i <;> rfl

theorem splitSpace2Vec_linearIndependent : LinearIndependent ℝ splitSpace2Vec := by
  rw [show splitSpace2Vec = ⇑splitSpace2Basis from funext fun i => (splitSpace2Basis_apply i).symm]
  exact splitSpace2Basis.linearIndependent

private theorem qsplit2_apply (x : SplitSpace 2) :
    Qsplit 2 x = x.1.1 * x.1.1 - x.1.2 * x.1.2 + (x.2.1.1 * x.2.1.1 - x.2.1.2 * x.2.1.2) := by
  change Qsplit (0 + 1 + 1) x = _
  rw [Qsplit_succ_apply, Qsplit_succ_apply, Qsplit_zero_apply]
  simp

@[simp] theorem qsplit2_splitSpace2Vec (i : Fin 4) :
    Qsplit 2 (splitSpace2Vec i) = splitSign i := by
  rw [qsplit2_apply]
  fin_cases i <;> simp [splitSpace2Vec, splitSign]

@[simp] theorem metricInner_splitSpace2Vec (i j : Fin 4) :
    metricInner (Qsplit 2) (splitSpace2Vec i) (splitSpace2Vec j) =
      if i = j then splitSign i else 0 := by
  dsimp [metricInner]
  have hq : ∀ x y : SplitSpace 2,
      QuadraticMap.associated (Qsplit 2) x y =
        (splitSign 0 * (splitSpace2Fin4Equiv x 0 * splitSpace2Fin4Equiv y 0) +
          splitSign 1 * (splitSpace2Fin4Equiv x 1 * splitSpace2Fin4Equiv y 1) +
          splitSign 2 * (splitSpace2Fin4Equiv x 2 * splitSpace2Fin4Equiv y 2) +
          splitSign 3 * (splitSpace2Fin4Equiv x 3 * splitSpace2Fin4Equiv y 3)) := by
    intro x y
    rw [QuadraticMap.associated_apply, qsplit2_apply, qsplit2_apply, qsplit2_apply]
    simp [splitSign, splitSpace2Fin4Equiv]
    ring
  rw [hq]
  fin_cases i <;> fin_cases j <;> simp [splitSpace2Vec, splitSign, splitSpace2Fin4Equiv]

/-- Embed a `Plucker6 ℝ` coordinate 6-vector into `ExteriorGrade ℝ (SplitSpace 2) 2`. -/
noncomputable def plucker6ToSplitExterior2 (P : Plucker6 ℝ) : ExteriorGrade ℝ (SplitSpace 2) 2 :=
  P.p01 • exteriorPower.ιMulti ℝ 2 ![splitSpace2Vec 0, splitSpace2Vec 1] +
  P.p02 • exteriorPower.ιMulti ℝ 2 ![splitSpace2Vec 0, splitSpace2Vec 2] +
  P.p03 • exteriorPower.ιMulti ℝ 2 ![splitSpace2Vec 0, splitSpace2Vec 3] +
  P.p12 • exteriorPower.ιMulti ℝ 2 ![splitSpace2Vec 1, splitSpace2Vec 2] +
  P.p13 • exteriorPower.ιMulti ℝ 2 ![splitSpace2Vec 1, splitSpace2Vec 3] +
  P.p23 • exteriorPower.ιMulti ℝ 2 ![splitSpace2Vec 2, splitSpace2Vec 3]

/-- Canonical unit bivector `eᵢ ∧ eⱼ` in `SplitExteriorStage 2`. -/
private abbrev eWedge (i j : Fin 4) : SplitExteriorStage 2 :=
  ExteriorAlgebra.ι ℝ (splitSpace2Vec i) * ExteriorAlgebra.ι ℝ (splitSpace2Vec j)

theorem plucker6ToSplitExterior2_val (P : Plucker6 ℝ) :
    (plucker6ToSplitExterior2 P).val =
      P.p01 • eWedge 0 1 + P.p02 • eWedge 0 2 + P.p03 • eWedge 0 3 +
      P.p12 • eWedge 1 2 + P.p13 • eWedge 1 3 + P.p23 • eWedge 2 3 := by
  dsimp [plucker6ToSplitExterior2]
  simp only [ExteriorAlgebra.ιMulti_apply]
  simp [List.ofFn_succ, eWedge]

/-- `plucker6ToSplitExterior2` maps `pluckerLine x y` to the literal exterior 2-blade
`exteriorPower.ιMulti ℝ 2 ![x', y']` in `SplitSpace 2`. -/
theorem pluckerLine_toSplitExterior2 (x y : InfoGeometry.Projective.KleinQuadricPlucker.Vec4 ℝ) :
    plucker6ToSplitExterior2 (pluckerLine x y) =
      exteriorPower.ιMulti ℝ 2
        ![splitSpace2Fin4Equiv.symm ![x.x0, x.x1, x.x2, x.x3],
          splitSpace2Fin4Equiv.symm ![y.x0, y.x1, y.x2, y.x3]] := by
  let u := splitSpace2Fin4Equiv.symm ![x.x0, x.x1, x.x2, x.x3]
  let v := splitSpace2Fin4Equiv.symm ![y.x0, y.x1, y.x2, y.x3]
  have hu : u = x.x0 • splitSpace2Vec 0 + x.x1 • splitSpace2Vec 1 +
      x.x2 • splitSpace2Vec 2 + x.x3 • splitSpace2Vec 3 := by
    ext <;> simp [u, splitSpace2Fin4Equiv, splitSpace2Vec]
  have hv : v = y.x0 • splitSpace2Vec 0 + y.x1 • splitSpace2Vec 1 +
      y.x2 • splitSpace2Vec 2 + y.x3 • splitSpace2Vec 3 := by
    ext <;> simp [v, splitSpace2Fin4Equiv, splitSpace2Vec]
  apply Subtype.ext
  rw [plucker6ToSplitExterior2_val]
  change _ = (exteriorPower.ιMulti ℝ 2 ![u, v] : SplitExteriorStage 2)
  rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Fin.succ_zero_eq_one, Matrix.cons_val_one]
  rw [hu, hv, map_add, map_add, map_add, map_add, map_add, map_add,
    map_smul, map_smul, map_smul, map_smul, map_smul, map_smul, map_smul, map_smul]
  have hsq : ∀ i : Fin 4,
      ExteriorAlgebra.ι ℝ (splitSpace2Vec i) * ExteriorAlgebra.ι ℝ (splitSpace2Vec i) = 0 :=
    fun i => ExteriorAlgebra.ι_sq_zero _
  have hanti : ∀ i j : Fin 4,
      ExteriorAlgebra.ι ℝ (splitSpace2Vec j) * ExteriorAlgebra.ι ℝ (splitSpace2Vec i) =
        -(ExteriorAlgebra.ι ℝ (splitSpace2Vec i) * ExteriorAlgebra.ι ℝ (splitSpace2Vec j)) := by
    intro i j
    have h := outerProduct_vectors_anticommute (R := ℝ) (splitSpace2Vec j) (splitSpace2Vec i)
    exact h
  dsimp [pluckerLine, eWedge]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  rw [hsq 0, hsq 1, hsq 2, hsq 3]
  rw [hanti 0 1, hanti 0 2, hanti 0 3, hanti 1 2, hanti 1 3, hanti 2 3]
  simp only [smul_zero, add_zero, zero_add, smul_add, smul_neg, sub_eq_add_neg]
  simp only [smul_smul, mul_comm y.x0, mul_comm y.x1, mul_comm y.x2, mul_comm y.x3]
  module

/-- Oriented unit 4-volume pseudoscalar `e₀ ∧ e₁ ∧ e₂ ∧ e₃` in `SplitExteriorStage 2`. -/
def splitVolume4 : SplitExteriorStage 2 :=
  ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) *
    ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 3)

/-- The 4-volume pseudoscalar `splitVolume4` is nonzero in `SplitExteriorStage 2`, proved via
`DecomposableBivector.exteriorPower_ιMulti_ne_zero_of_linearIndependent`. -/
theorem splitVolume4_ne_zero : splitVolume4 ≠ 0 := by
  have hne := InfoGeometry.Canonical.exteriorPower_ιMulti_ne_zero_of_linearIndependent
    splitSpace2Vec splitSpace2Vec_linearIndependent
  intro hzero
  apply hne
  apply Subtype.ext
  change (exteriorPower.ιMulti ℝ 4 splitSpace2Vec : SplitExteriorStage 2) = 0
  rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  simpa [splitVolume4, mul_assoc] using hzero

/-- Split `(2,2)` squared norm `p₀₁² - p₀₂² + p₀₃² + p₁₂² - p₁₃² + p₂₃²` on `Plucker6 ℝ`. -/

private noncomputable def clE0 : SplitExteriorStage 2 :=
  ExteriorAlgebra.ι ℝ (splitSpace2Vec 0)

private noncomputable def clE1 : SplitExteriorStage 2 :=
  ExteriorAlgebra.ι ℝ (splitSpace2Vec 1)

/-- Explicit anticommutation noncommutativity witness in `SplitExteriorStage 2`:
`clE0 * clE1 + clE1 * clE0 = 0`. -/
theorem splitExterior2_e0_e1_anticomm : clE0 * clE1 + clE1 * clE0 = 0 := by
  dsimp [clE0, clE1]
  have h := outerProduct_vectors_anticommute (R := ℝ) (splitSpace2Vec 1) (splitSpace2Vec 0)
  dsimp [outerProduct] at h
  rw [h, add_neg_cancel]

def splitBivectorNormSq (P : Plucker6 ℝ) : ℝ :=
  P.p01 ^ 2 - P.p02 ^ 2 + P.p03 ^ 2 + P.p12 ^ 2 - P.p13 ^ 2 + P.p23 ^ 2

/-- Exterior square of any Plücker bivector in `SplitExteriorStage 2` equals
`(2 * kleinQ P) • splitVolume4`. -/
theorem splitExterior2_outerProduct_self (P : Plucker6 ℝ) :
    outerProduct (plucker6ToSplitExterior2 P).val (plucker6ToSplitExterior2 P).val =
      (2 * kleinQ P) • splitVolume4 := by
  rw [plucker6ToSplitExterior2_val]
  dsimp [outerProduct, kleinQ]
  have hsq : ∀ i : Fin 4,
      ExteriorAlgebra.ι ℝ (splitSpace2Vec i) * ExteriorAlgebra.ι ℝ (splitSpace2Vec i) = 0 :=
    fun i => ExteriorAlgebra.ι_sq_zero _
  have hanti : ∀ i j : Fin 4,
      ExteriorAlgebra.ι ℝ (splitSpace2Vec j) * ExteriorAlgebra.ι ℝ (splitSpace2Vec i) =
        -(ExteriorAlgebra.ι ℝ (splitSpace2Vec i) * ExteriorAlgebra.ι ℝ (splitSpace2Vec j)) :=
    fun i j => outerProduct_vectors_anticommute (R := ℝ) (splitSpace2Vec j) (splitSpace2Vec i)
  have hpair_zero : ∀ a b c d : Fin 4,
      (a = c ∨ a = d ∨ b = c ∨ b = d) → eWedge a b * eWedge c d = 0 := by
    intro a b c d hor
    have hcomm_e : ∀ x y : Fin 4,
        eWedge x y = -(eWedge y x) := fun x y => hanti y x
    rcases hor with rfl | rfl | rfl | rfl
    · calc eWedge a b * eWedge a d
          = ExteriorAlgebra.ι ℝ (splitSpace2Vec a) *
              (ExteriorAlgebra.ι ℝ (splitSpace2Vec b) * ExteriorAlgebra.ι ℝ (splitSpace2Vec a)) *
              ExteriorAlgebra.ι ℝ (splitSpace2Vec d) := by noncomm_ring
        _ = ExteriorAlgebra.ι ℝ (splitSpace2Vec a) *
              (-(ExteriorAlgebra.ι ℝ (splitSpace2Vec a) * ExteriorAlgebra.ι ℝ (splitSpace2Vec b))) *
              ExteriorAlgebra.ι ℝ (splitSpace2Vec d) := by rw [hanti a b]
        _ = -((ExteriorAlgebra.ι ℝ (splitSpace2Vec a) * ExteriorAlgebra.ι ℝ (splitSpace2Vec a)) *
              (ExteriorAlgebra.ι ℝ (splitSpace2Vec b) * ExteriorAlgebra.ι ℝ (splitSpace2Vec d))) := by
              noncomm_ring
        _ = 0 := by rw [hsq a]; simp
    · calc eWedge a b * eWedge c a
          = -(eWedge a b * eWedge a c) := by rw [hcomm_e c a]; simp [mul_neg]
        _ = -(ExteriorAlgebra.ι ℝ (splitSpace2Vec a) *
              (ExteriorAlgebra.ι ℝ (splitSpace2Vec b) * ExteriorAlgebra.ι ℝ (splitSpace2Vec a)) *
              ExteriorAlgebra.ι ℝ (splitSpace2Vec c)) := by noncomm_ring
        _ = -(ExteriorAlgebra.ι ℝ (splitSpace2Vec a) *
              (-(ExteriorAlgebra.ι ℝ (splitSpace2Vec a) * ExteriorAlgebra.ι ℝ (splitSpace2Vec b))) *
              ExteriorAlgebra.ι ℝ (splitSpace2Vec c)) := by rw [hanti a b]
        _ = (ExteriorAlgebra.ι ℝ (splitSpace2Vec a) * ExteriorAlgebra.ι ℝ (splitSpace2Vec a)) *
              (ExteriorAlgebra.ι ℝ (splitSpace2Vec b) * ExteriorAlgebra.ι ℝ (splitSpace2Vec c)) := by
              noncomm_ring
        _ = 0 := by rw [hsq a]; simp
    · calc eWedge a b * eWedge b d
          = ExteriorAlgebra.ι ℝ (splitSpace2Vec a) *
              (ExteriorAlgebra.ι ℝ (splitSpace2Vec b) * ExteriorAlgebra.ι ℝ (splitSpace2Vec b)) *
              ExteriorAlgebra.ι ℝ (splitSpace2Vec d) := by noncomm_ring
        _ = 0 := by rw [hsq b]; simp
    · calc eWedge a b * eWedge c b
          = -(eWedge a b * eWedge b c) := by rw [hcomm_e c b]; simp [mul_neg]
        _ = -(ExteriorAlgebra.ι ℝ (splitSpace2Vec a) *
              (ExteriorAlgebra.ι ℝ (splitSpace2Vec b) * ExteriorAlgebra.ι ℝ (splitSpace2Vec b)) *
              ExteriorAlgebra.ι ℝ (splitSpace2Vec c)) := by noncomm_ring
        _ = 0 := by rw [hsq b]; simp
  have h0123 : eWedge 0 1 * eWedge 2 3 = splitVolume4 := by
    dsimp [eWedge, splitVolume4]; noncomm_ring
  have h2301 : eWedge 2 3 * eWedge 0 1 = splitVolume4 := by
    calc eWedge 2 3 * eWedge 0 1
        = ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) *
            (ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 0)) *
            ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) := by dsimp [eWedge]; noncomm_ring
      _ = -(ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) *
            ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 1)) := by
            rw [hanti 0 3]; noncomm_ring
      _ = ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) *
            ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) := by
            rw [hanti 0 2]; noncomm_ring
      _ = -(ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) *
            ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 3)) := by
            rw [mul_assoc (ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 2)),
              hanti 1 3]; noncomm_ring
      _ = splitVolume4 := by
            rw [mul_assoc (ExteriorAlgebra.ι ℝ (splitSpace2Vec 0)), hanti 1 2]; dsimp [splitVolume4]; noncomm_ring
  have h0213 : eWedge 0 2 * eWedge 1 3 = -splitVolume4 := by
    dsimp [eWedge, splitVolume4]
    calc (ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 2)) *
          (ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 3))
        = ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) *
            (ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 1)) *
            ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) := by noncomm_ring
      _ = -splitVolume4 := by rw [hanti 1 2]; dsimp [splitVolume4]; noncomm_ring
  have h1302 : eWedge 1 3 * eWedge 0 2 = -splitVolume4 := by
    calc eWedge 1 3 * eWedge 0 2
        = ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) *
            (ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 0)) *
            ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) := by dsimp [eWedge]; noncomm_ring
      _ = -(ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) *
            ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 2)) := by
            rw [hanti 0 3]; noncomm_ring
      _ = ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) *
            ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) := by
            rw [hanti 0 1]; noncomm_ring
      _ = -splitVolume4 := by
            rw [mul_assoc (ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 1)),
              hanti 2 3]; dsimp [splitVolume4]; noncomm_ring
  have h0312 : eWedge 0 3 * eWedge 1 2 = splitVolume4 := by
    calc eWedge 0 3 * eWedge 1 2
        = ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) *
            (ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 1)) *
            ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) := by dsimp [eWedge]; noncomm_ring
      _ = -(ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) *
            ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 2)) := by
            rw [hanti 1 3]; noncomm_ring
      _ = splitVolume4 := by
            rw [mul_assoc (ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 1)),
              hanti 2 3]; dsimp [splitVolume4]; noncomm_ring
  have h1203 : eWedge 1 2 * eWedge 0 3 = splitVolume4 := by
    calc eWedge 1 2 * eWedge 0 3
        = ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) *
            (ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 0)) *
            ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) := by dsimp [eWedge]; noncomm_ring
      _ = -(ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) *
            ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 3)) := by
            rw [hanti 0 2]; noncomm_ring
      _ = splitVolume4 := by rw [hanti 0 1]; dsimp [splitVolume4]; noncomm_ring
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  rw [hpair_zero 0 1 0 1 (Or.inl rfl), hpair_zero 0 1 0 2 (Or.inl rfl),
      hpair_zero 0 1 0 3 (Or.inl rfl), hpair_zero 0 1 1 2 (Or.inr (Or.inr (Or.inl rfl))),
      hpair_zero 0 1 1 3 (Or.inr (Or.inr (Or.inl rfl))),
      hpair_zero 0 2 0 1 (Or.inl rfl), hpair_zero 0 2 0 2 (Or.inl rfl),
      hpair_zero 0 2 0 3 (Or.inl rfl), hpair_zero 0 2 1 2 (Or.inr (Or.inr (Or.inr rfl))),
      hpair_zero 0 2 2 3 (Or.inr (Or.inr (Or.inl rfl))),
      hpair_zero 0 3 0 1 (Or.inl rfl), hpair_zero 0 3 0 2 (Or.inl rfl),
      hpair_zero 0 3 0 3 (Or.inl rfl), hpair_zero 0 3 1 3 (Or.inr (Or.inr (Or.inr rfl))),
      hpair_zero 0 3 2 3 (Or.inr (Or.inr (Or.inr rfl))),
      hpair_zero 1 2 0 1 (Or.inr (Or.inl rfl)),
      hpair_zero 1 2 0 2 (Or.inr (Or.inr (Or.inr rfl))),
      hpair_zero 1 2 1 2 (Or.inl rfl), hpair_zero 1 2 1 3 (Or.inl rfl),
      hpair_zero 1 2 2 3 (Or.inr (Or.inr (Or.inl rfl))),
      hpair_zero 1 3 0 1 (Or.inr (Or.inl rfl)),
      hpair_zero 1 3 0 3 (Or.inr (Or.inr (Or.inr rfl))),
      hpair_zero 1 3 1 2 (Or.inl rfl), hpair_zero 1 3 1 3 (Or.inl rfl),
      hpair_zero 1 3 2 3 (Or.inr (Or.inr (Or.inr rfl))),
      hpair_zero 2 3 0 2 (Or.inr (Or.inl rfl)),
      hpair_zero 2 3 0 3 (Or.inr (Or.inr (Or.inr rfl))),
      hpair_zero 2 3 1 2 (Or.inr (Or.inl rfl)),
      hpair_zero 2 3 1 3 (Or.inr (Or.inr (Or.inr rfl))),
      hpair_zero 2 3 2 3 (Or.inl rfl)]
  rw [h0123, h2301, h0213, h1302, h0312, h1203]
  simp only [smul_zero, add_zero, zero_add, smul_neg, smul_smul]
  rw [mul_comm P.p12 P.p03, mul_comm P.p13 P.p02, mul_comm P.p23 P.p01]
  module

/-- Helper: Clifford image of an orthogonal basis bivector `e_i ∧ e_j` (`i ≠ j`) in `Cl(2,2)`. -/
private theorem clifford_symm_eWedge {i j : Fin 4} (hij : i ≠ j) :
    (cliffordExteriorEquiv (Qsplit 2)).symm (eWedge i j) =
      CliffordAlgebra.ι (Qsplit 2) (splitSpace2Vec i) *
        CliffordAlgebra.ι (Qsplit 2) (splitSpace2Vec j) := by
  dsimp [eWedge]
  rw [cliffordExteriorEquiv_symm_ι_mul]
  have hj : (cliffordExteriorEquiv (Qsplit 2)).symm (ExteriorAlgebra.ι ℝ (splitSpace2Vec j)) =
      CliffordAlgebra.ι (Qsplit 2) (splitSpace2Vec j) := by
    apply (cliffordExteriorEquiv (Qsplit 2)).injective
    simp [cliffordExteriorEquiv]
  rw [hj, CliffordAlgebra.contractLeft_ι]
  have hinner : QuadraticMap.associated (Qsplit 2) (splitSpace2Vec i) (splitSpace2Vec j) = 0 := by
    simpa [metricInner, hij] using metricInner_splitSpace2Vec i j
  rw [hinner, map_zero, sub_zero]

/-- **Sobczyk `Cl(2,2)` Geometric-Product Square & Klein-Obstruction Pseudoscalar Theorem**:
for any `P : Plucker6 ℝ` with `B = (plucker6ToSplitExterior2 P).val`,
$$B *_{\mathrm{Cl}} B = \mathrm{splitBivectorNormSq}(P) \cdot 1 + (2\,\mathrm{kleinQ}(P)) \cdot (e_0 \wedge e_1 \wedge e_2 \wedge e_3).$$ -/
theorem splitExterior2_geometricProduct_self (P : Plucker6 ℝ) :
    geometricProduct (Qsplit 2) (plucker6ToSplitExterior2 P).val (plucker6ToSplitExterior2 P).val =
      algebraMap ℝ (SplitExteriorStage 2) (splitBivectorNormSq P) +
        (2 * kleinQ P) • splitVolume4 := by
  let c (i : Fin 4) : CliffordAlgebra (Qsplit 2) :=
    CliffordAlgebra.ι (Qsplit 2) (splitSpace2Vec i)
  have hc_sq : ∀ i : Fin 4, c i * c i = algebraMap ℝ (CliffordAlgebra (Qsplit 2)) (splitSign i) := by
    intro i
    dsimp [c]
    rw [CliffordAlgebra.ι_sq_scalar, qsplit2_splitSpace2Vec]
  have hc_anti : ∀ {i j : Fin 4}, i ≠ j → c j * c i = -(c i * c j) := by
    intro i j hij
    dsimp [c]
    have hadd := CliffordAlgebra.ι_mul_ι_add_swap (Q := Qsplit 2) (splitSpace2Vec i) (splitSpace2Vec j)
    have hpol : QuadraticMap.polar (Qsplit 2) (splitSpace2Vec i) (splitSpace2Vec j) = 0 := by
      have h2 : QuadraticMap.polar (Qsplit 2) (splitSpace2Vec i) (splitSpace2Vec j) =
          2 * metricInner (Qsplit 2) (splitSpace2Vec i) (splitSpace2Vec j) := by
        dsimp [metricInner]
        rw [QuadraticMap.associated_apply]
        change QuadraticMap.polar (Qsplit 2) (splitSpace2Vec i) (splitSpace2Vec j) =
          2 * (⅟(2 : ℝ) * QuadraticMap.polar (Qsplit 2) (splitSpace2Vec i) (splitSpace2Vec j))
        rw [← mul_assoc, mul_invOf_self, one_mul]
      rw [h2, metricInner_splitSpace2Vec]
      simp [hij]
    rw [hpol, map_zero] at hadd
    exact eq_neg_of_add_eq_zero_right hadd
  have hB_cl :
      (cliffordExteriorEquiv (Qsplit 2)).symm (plucker6ToSplitExterior2 P).val =
        P.p01 • (c 0 * c 1) + P.p02 • (c 0 * c 2) + P.p03 • (c 0 * c 3) +
        P.p12 • (c 1 * c 2) + P.p13 • (c 1 * c 3) + P.p23 • (c 2 * c 3) := by
    rw [plucker6ToSplitExterior2_val]
    simp only [map_add, map_smul,
      clifford_symm_eWedge (by decide : (0 : Fin 4) ≠ 1),
      clifford_symm_eWedge (by decide : (0 : Fin 4) ≠ 2),
      clifford_symm_eWedge (by decide : (0 : Fin 4) ≠ 3),
      clifford_symm_eWedge (by decide : (1 : Fin 4) ≠ 2),
      clifford_symm_eWedge (by decide : (1 : Fin 4) ≠ 3),
      clifford_symm_eWedge (by decide : (2 : Fin 4) ≠ 3)]
    rfl
  have hvol_cl :
      (cliffordExteriorEquiv (Qsplit 2)).symm splitVolume4 = c 0 * c 1 * c 2 * c 3 := by
    have h23 : (cliffordExteriorEquiv (Qsplit 2)).symm (eWedge 2 3) = c 2 * c 3 :=
      clifford_symm_eWedge (by decide : (2 : Fin 4) ≠ 3)
    have h123 : (cliffordExteriorEquiv (Qsplit 2)).symm
        (ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) * eWedge 2 3) = c 1 * (c 2 * c 3) := by
      rw [cliffordExteriorEquiv_symm_ι_mul, h23]
      dsimp [c]
      rw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι]
      have h12 : QuadraticMap.associated (Qsplit 2) (splitSpace2Vec 1) (splitSpace2Vec 2) = 0 := by
        simpa [metricInner] using metricInner_splitSpace2Vec 1 2
      have h13 : QuadraticMap.associated (Qsplit 2) (splitSpace2Vec 1) (splitSpace2Vec 3) = 0 := by
        simpa [metricInner] using metricInner_splitSpace2Vec 1 3
      rw [h12, h13, map_zero, zero_smul, mul_zero, sub_zero, sub_zero]
    have h0123 : (cliffordExteriorEquiv (Qsplit 2)).symm
        (ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) *
          (ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) * eWedge 2 3)) =
        c 0 * (c 1 * (c 2 * c 3)) := by
      rw [cliffordExteriorEquiv_symm_ι_mul, h123]
      dsimp [c]
      rw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι_mul,
        CliffordAlgebra.contractLeft_ι]
      have h01 : QuadraticMap.associated (Qsplit 2) (splitSpace2Vec 0) (splitSpace2Vec 1) = 0 := by
        simpa [metricInner] using metricInner_splitSpace2Vec 0 1
      have h02 : QuadraticMap.associated (Qsplit 2) (splitSpace2Vec 0) (splitSpace2Vec 2) = 0 := by
        simpa [metricInner] using metricInner_splitSpace2Vec 0 2
      have h03 : QuadraticMap.associated (Qsplit 2) (splitSpace2Vec 0) (splitSpace2Vec 3) = 0 := by
        simpa [metricInner] using metricInner_splitSpace2Vec 0 3
      rw [h01, h02, h03, map_zero, zero_smul, zero_smul, mul_zero, sub_zero, mul_zero, sub_zero,
        sub_zero]
    have hsplit : splitVolume4 = ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) *
        (ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) * eWedge 2 3) := by
      dsimp [splitVolume4, eWedge]; noncomm_ring
    rw [hsplit, h0123]
    noncomm_ring
  apply (cliffordExteriorEquiv (Qsplit 2)).symm.injective
  rw [geometricProduct_toClifford, map_add, map_smul, hB_cl, hvol_cl]
  have h10 : c 1 * c 0 = -(c 0 * c 1) := hc_anti (by decide)
  have h20 : c 2 * c 0 = -(c 0 * c 2) := hc_anti (by decide)
  have h30 : c 3 * c 0 = -(c 0 * c 3) := hc_anti (by decide)
  have h21 : c 2 * c 1 = -(c 1 * c 2) := hc_anti (by decide)
  have h31 : c 3 * c 1 = -(c 1 * c 3) := hc_anti (by decide)
  have h32 : c 3 * c 2 = -(c 2 * c 3) := hc_anti (by decide)
  have h_scalar : (cliffordExteriorEquiv (Qsplit 2)).symm
      (algebraMap ℝ (SplitExteriorStage 2) (splitBivectorNormSq P)) =
      algebraMap ℝ (CliffordAlgebra (Qsplit 2)) (splitBivectorNormSq P) := by
    simp [cliffordExteriorEquiv, Algebra.algebraMap_eq_smul_one]
  rw [h_scalar]
  have hsq01 : (c 0 * c 1) * (c 0 * c 1) = algebraMap ℝ (CliffordAlgebra (Qsplit 2)) 1 := by
    calc (c 0 * c 1) * (c 0 * c 1)
        = c 0 * (c 1 * c 0) * c 1 := by noncomm_ring
      _ = -(c 0 * c 0 * (c 1 * c 1)) := by rw [h10]; noncomm_ring
      _ = -(algebraMap ℝ _ (splitSign 0) * algebraMap ℝ _ (splitSign 1)) := by
            rw [hc_sq 0, hc_sq 1]
      _ = algebraMap ℝ _ 1 := by rw [← map_mul]; simp [splitSign]
  have hsq02 : (c 0 * c 2) * (c 0 * c 2) = algebraMap ℝ (CliffordAlgebra (Qsplit 2)) (-1) := by
    calc (c 0 * c 2) * (c 0 * c 2)
        = c 0 * (c 2 * c 0) * c 2 := by noncomm_ring
      _ = -(c 0 * c 0 * (c 2 * c 2)) := by rw [h20]; noncomm_ring
      _ = -(algebraMap ℝ _ (splitSign 0) * algebraMap ℝ _ (splitSign 2)) := by
            rw [hc_sq 0, hc_sq 2]
      _ = algebraMap ℝ _ (-1) := by rw [← map_mul]; simp [splitSign]
  have hsq03 : (c 0 * c 3) * (c 0 * c 3) = algebraMap ℝ (CliffordAlgebra (Qsplit 2)) 1 := by
    calc (c 0 * c 3) * (c 0 * c 3)
        = c 0 * (c 3 * c 0) * c 3 := by noncomm_ring
      _ = -(c 0 * c 0 * (c 3 * c 3)) := by rw [h30]; noncomm_ring
      _ = -(algebraMap ℝ _ (splitSign 0) * algebraMap ℝ _ (splitSign 3)) := by
            rw [hc_sq 0, hc_sq 3]
      _ = algebraMap ℝ _ 1 := by rw [← map_mul]; simp [splitSign]
  have hsq12 : (c 1 * c 2) * (c 1 * c 2) = algebraMap ℝ (CliffordAlgebra (Qsplit 2)) 1 := by
    calc (c 1 * c 2) * (c 1 * c 2)
        = c 1 * (c 2 * c 1) * c 2 := by noncomm_ring
      _ = -(c 1 * c 1 * (c 2 * c 2)) := by rw [h21]; noncomm_ring
      _ = -(algebraMap ℝ _ (splitSign 1) * algebraMap ℝ _ (splitSign 2)) := by
            rw [hc_sq 1, hc_sq 2]
      _ = algebraMap ℝ _ 1 := by rw [← map_mul]; simp [splitSign]
  have hsq13 : (c 1 * c 3) * (c 1 * c 3) = algebraMap ℝ (CliffordAlgebra (Qsplit 2)) (-1) := by
    calc (c 1 * c 3) * (c 1 * c 3)
        = c 1 * (c 3 * c 1) * c 3 := by noncomm_ring
      _ = -(c 1 * c 1 * (c 3 * c 3)) := by rw [h31]; noncomm_ring
      _ = -(algebraMap ℝ _ (splitSign 1) * algebraMap ℝ _ (splitSign 3)) := by
            rw [hc_sq 1, hc_sq 3]
      _ = algebraMap ℝ _ (-1) := by rw [← map_mul]; simp [splitSign]
  have hsq23 : (c 2 * c 3) * (c 2 * c 3) = algebraMap ℝ (CliffordAlgebra (Qsplit 2)) 1 := by
    calc (c 2 * c 3) * (c 2 * c 3)
        = c 2 * (c 3 * c 2) * c 3 := by noncomm_ring
      _ = -(c 2 * c 2 * (c 3 * c 3)) := by rw [h32]; noncomm_ring
      _ = -(algebraMap ℝ _ (splitSign 2) * algebraMap ℝ _ (splitSign 3)) := by
            rw [hc_sq 2, hc_sq 3]
      _ = algebraMap ℝ _ 1 := by rw [← map_mul]; simp [splitSign]
  -- Pairs sharing exactly one index anticommute in Cl(2,2): (c_i c_j)(c_i c_k) + (c_i c_k)(c_i c_j) = 0
  have hanti_shared : ∀ a b d : Fin 4, a ≠ b → a ≠ d → b ≠ d →
      (c a * c b) * (c a * c d) + (c a * c d) * (c a * c b) = 0 := by
    intro a b d hab had hbd
    have hba := hc_anti hab
    have hda := hc_anti had
    have hdb := hc_anti hbd
    calc
      (c a * c b) * (c a * c d) + (c a * c d) * (c a * c b)
          = c a * (c b * c a) * c d + c a * (c d * c a) * c b := by noncomm_ring
      _ = -(c a * c a) * (c b * c d) - (c a * c a) * (c d * c b) := by
            rw [hba, hda]; noncomm_ring
      _ = -(c a * c a) * (c b * c d + c d * c b) := by noncomm_ring
      _ = -(c a * c a) * (c b * c d - c b * c d) := by rw [hdb]; noncomm_ring
      _ = 0 := by simp
  have h01_23 : (c 0 * c 1) * (c 2 * c 3) = c 0 * c 1 * c 2 * c 3 := by noncomm_ring
  have h23_01 : (c 2 * c 3) * (c 0 * c 1) = c 0 * c 1 * c 2 * c 3 := by
    calc (c 2 * c 3) * (c 0 * c 1)
        = c 2 * (c 3 * c 0) * c 1 := by noncomm_ring
      _ = -(c 2 * c 0 * c 3 * c 1) := by rw [h30]; noncomm_ring
      _ = c 0 * c 2 * c 3 * c 1 := by rw [h20]; noncomm_ring
      _ = -(c 0 * c 2 * (c 1 * c 3)) := by rw [mul_assoc (c 0 * c 2), h31]; noncomm_ring
      _ = -(c 0 * (c 2 * c 1) * c 3) := by noncomm_ring
      _ = c 0 * (c 1 * c 2) * c 3 := by rw [h21]; noncomm_ring
      _ = c 0 * c 1 * c 2 * c 3 := by noncomm_ring
  have h02_13 : (c 0 * c 2) * (c 1 * c 3) = -(c 0 * c 1 * c 2 * c 3) := by
    calc (c 0 * c 2) * (c 1 * c 3)
        = c 0 * (c 2 * c 1) * c 3 := by noncomm_ring
      _ = -(c 0 * c 1 * c 2 * c 3) := by rw [h21]; noncomm_ring
  have h13_02 : (c 1 * c 3) * (c 0 * c 2) = -(c 0 * c 1 * c 2 * c 3) := by
    calc (c 1 * c 3) * (c 0 * c 2)
        = c 1 * (c 3 * c 0) * c 2 := by noncomm_ring
      _ = -(c 1 * c 0 * c 3 * c 2) := by rw [h30]; noncomm_ring
      _ = c 0 * c 1 * (c 3 * c 2) := by rw [h10]; noncomm_ring
      _ = -(c 0 * c 1 * c 2 * c 3) := by rw [h32]; noncomm_ring
  have h03_12 : (c 0 * c 3) * (c 1 * c 2) = c 0 * c 1 * c 2 * c 3 := by
    calc (c 0 * c 3) * (c 1 * c 2)
        = c 0 * (c 3 * c 1) * c 2 := by noncomm_ring
      _ = -(c 0 * c 1 * (c 3 * c 2)) := by rw [h31]; noncomm_ring
      _ = c 0 * c 1 * c 2 * c 3 := by rw [h32]; noncomm_ring
  have h12_03 : (c 1 * c 2) * (c 0 * c 3) = c 0 * c 1 * c 2 * c 3 := by
    calc (c 1 * c 2) * (c 0 * c 3)
        = c 1 * (c 2 * c 0) * c 3 := by noncomm_ring
      _ = -(c 1 * c 0 * c 2 * c 3) := by rw [h20]; noncomm_ring
      _ = c 0 * c 1 * c 2 * c 3 := by rw [h10]; noncomm_ring
  have hpair_zero_cl : ∀ a b d : Fin 4, a ≠ b → a ≠ d → b ≠ d →
      ∀ r s : ℝ, r • (c a * c b) * (s • (c a * c d)) + s • (c a * c d) * (r • (c a * c b)) = 0 := by
    intro a b d hab had hbd r s
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm s r, ← smul_add, hanti_shared a b d hab had hbd, smul_zero]
  have h01' : c 0 * c 1 = -(c 1 * c 0) := hc_anti (by decide)
  have h02' : c 0 * c 2 = -(c 2 * c 0) := hc_anti (by decide)
  have h03' : c 0 * c 3 = -(c 3 * c 0) := hc_anti (by decide)
  have h12' : c 1 * c 2 = -(c 2 * c 1) := hc_anti (by decide)
  have h13' : c 1 * c 3 = -(c 3 * c 1) := hc_anti (by decide)
  have h23' : c 2 * c 3 = -(c 3 * c 2) := hc_anti (by decide)
  have h01_12 : (c 0 * c 1) * (c 1 * c 2) + (c 1 * c 2) * (c 0 * c 1) = 0 := by
    calc (c 0 * c 1) * (c 1 * c 2) + (c 1 * c 2) * (c 0 * c 1)
        = (-(c 1 * c 0)) * (c 1 * c 2) + (c 1 * c 2) * (-(c 1 * c 0)) := by rw [h01']
      _ = -((c 1 * c 0) * (c 1 * c 2) + (c 1 * c 2) * (c 1 * c 0)) := by noncomm_ring
      _ = 0 := by rw [hanti_shared 1 0 2 (by decide) (by decide) (by decide), neg_zero]
  have h01_13 : (c 0 * c 1) * (c 1 * c 3) + (c 1 * c 3) * (c 0 * c 1) = 0 := by
    calc (c 0 * c 1) * (c 1 * c 3) + (c 1 * c 3) * (c 0 * c 1)
        = (-(c 1 * c 0)) * (c 1 * c 3) + (c 1 * c 3) * (-(c 1 * c 0)) := by rw [h01']
      _ = -((c 1 * c 0) * (c 1 * c 3) + (c 1 * c 3) * (c 1 * c 0)) := by noncomm_ring
      _ = 0 := by rw [hanti_shared 1 0 3 (by decide) (by decide) (by decide), neg_zero]
  have h02_12 : (c 0 * c 2) * (c 1 * c 2) + (c 1 * c 2) * (c 0 * c 2) = 0 := by
    calc (c 0 * c 2) * (c 1 * c 2) + (c 1 * c 2) * (c 0 * c 2)
        = (-(c 2 * c 0)) * (-(c 2 * c 1)) + (-(c 2 * c 1)) * (-(c 2 * c 0)) := by
            rw [h02', h12']
      _ = (c 2 * c 0) * (c 2 * c 1) + (c 2 * c 1) * (c 2 * c 0) := by noncomm_ring
      _ = 0 := hanti_shared 2 0 1 (by decide) (by decide) (by decide)
  have h02_23 : (c 0 * c 2) * (c 2 * c 3) + (c 2 * c 3) * (c 0 * c 2) = 0 := by
    calc (c 0 * c 2) * (c 2 * c 3) + (c 2 * c 3) * (c 0 * c 2)
        = (-(c 2 * c 0)) * (c 2 * c 3) + (c 2 * c 3) * (-(c 2 * c 0)) := by rw [h02']
      _ = -((c 2 * c 0) * (c 2 * c 3) + (c 2 * c 3) * (c 2 * c 0)) := by noncomm_ring
      _ = 0 := by rw [hanti_shared 2 0 3 (by decide) (by decide) (by decide), neg_zero]
  have h03_13 : (c 0 * c 3) * (c 1 * c 3) + (c 1 * c 3) * (c 0 * c 3) = 0 := by
    calc (c 0 * c 3) * (c 1 * c 3) + (c 1 * c 3) * (c 0 * c 3)
        = (-(c 3 * c 0)) * (-(c 3 * c 1)) + (-(c 3 * c 1)) * (-(c 3 * c 0)) := by
            rw [h03', h13']
      _ = (c 3 * c 0) * (c 3 * c 1) + (c 3 * c 1) * (c 3 * c 0) := by noncomm_ring
      _ = 0 := hanti_shared 3 0 1 (by decide) (by decide) (by decide)
  have h03_23 : (c 0 * c 3) * (c 2 * c 3) + (c 2 * c 3) * (c 0 * c 3) = 0 := by
    calc (c 0 * c 3) * (c 2 * c 3) + (c 2 * c 3) * (c 0 * c 3)
        = (-(c 3 * c 0)) * (-(c 3 * c 2)) + (-(c 3 * c 2)) * (-(c 3 * c 0)) := by
            rw [h03', h23']
      _ = (c 3 * c 0) * (c 3 * c 2) + (c 3 * c 2) * (c 3 * c 0) := by noncomm_ring
      _ = 0 := hanti_shared 3 0 2 (by decide) (by decide) (by decide)
  have h12_23 : (c 1 * c 2) * (c 2 * c 3) + (c 2 * c 3) * (c 1 * c 2) = 0 := by
    calc (c 1 * c 2) * (c 2 * c 3) + (c 2 * c 3) * (c 1 * c 2)
        = (-(c 2 * c 1)) * (c 2 * c 3) + (c 2 * c 3) * (-(c 2 * c 1)) := by rw [h12']
      _ = -((c 2 * c 1) * (c 2 * c 3) + (c 2 * c 3) * (c 2 * c 1)) := by noncomm_ring
      _ = 0 := by rw [hanti_shared 2 1 3 (by decide) (by decide) (by decide), neg_zero]
  have h13_23 : (c 1 * c 3) * (c 2 * c 3) + (c 2 * c 3) * (c 1 * c 3) = 0 := by
    calc (c 1 * c 3) * (c 2 * c 3) + (c 2 * c 3) * (c 1 * c 3)
        = (-(c 3 * c 1)) * (-(c 3 * c 2)) + (-(c 3 * c 2)) * (-(c 3 * c 1)) := by
            rw [h13', h23']
      _ = (c 3 * c 1) * (c 3 * c 2) + (c 3 * c 2) * (c 3 * c 1) := by noncomm_ring
      _ = 0 := hanti_shared 3 1 2 (by decide) (by decide) (by decide)
  have h01_02 := hanti_shared 0 1 2 (by decide) (by decide) (by decide)
  have h01_03 := hanti_shared 0 1 3 (by decide) (by decide) (by decide)
  have h02_03 := hanti_shared 0 2 3 (by decide) (by decide) (by decide)
  have h12_13 := hanti_shared 1 2 3 (by decide) (by decide) (by decide)
  have hcross_cancel :
      (P.p01 • (c 0 * c 1)) * (P.p02 • (c 0 * c 2)) + (P.p02 • (c 0 * c 2)) * (P.p01 • (c 0 * c 1)) = 0 ∧
      (P.p01 • (c 0 * c 1)) * (P.p03 • (c 0 * c 3)) + (P.p03 • (c 0 * c 3)) * (P.p01 • (c 0 * c 1)) = 0 ∧
      (P.p02 • (c 0 * c 2)) * (P.p03 • (c 0 * c 3)) + (P.p03 • (c 0 * c 3)) * (P.p02 • (c 0 * c 2)) = 0 ∧
      (P.p12 • (c 1 * c 2)) * (P.p13 • (c 1 * c 3)) + (P.p13 • (c 1 * c 3)) * (P.p12 • (c 1 * c 2)) = 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [smul_mul_assoc, mul_smul_comm, smul_smul]; rw [mul_comm P.p02 P.p01, ← smul_add, h01_02, smul_zero]
    · simp only [smul_mul_assoc, mul_smul_comm, smul_smul]; rw [mul_comm P.p03 P.p01, ← smul_add, h01_03, smul_zero]
    · simp only [smul_mul_assoc, mul_smul_comm, smul_smul]; rw [mul_comm P.p03 P.p02, ← smul_add, h02_03, smul_zero]
    · simp only [smul_mul_assoc, mul_smul_comm, smul_smul]; rw [mul_comm P.p13 P.p12, ← smul_add, h12_13, smul_zero]
  have h2_cancel :
      (c 0 * c 1) * (c 0 * c 2) = -((c 0 * c 2) * (c 0 * c 1)) ∧
      (c 0 * c 1) * (c 0 * c 3) = -((c 0 * c 3) * (c 0 * c 1)) ∧
      (c 0 * c 2) * (c 0 * c 3) = -((c 0 * c 3) * (c 0 * c 2)) ∧
      (c 1 * c 2) * (c 1 * c 3) = -((c 1 * c 3) * (c 1 * c 2)) ∧
      (c 0 * c 1) * (c 1 * c 2) = -((c 1 * c 2) * (c 0 * c 1)) ∧
      (c 0 * c 1) * (c 1 * c 3) = -((c 1 * c 3) * (c 0 * c 1)) ∧
      (c 0 * c 2) * (c 1 * c 2) = -((c 1 * c 2) * (c 0 * c 2)) ∧
      (c 0 * c 2) * (c 2 * c 3) = -((c 2 * c 3) * (c 0 * c 2)) ∧
      (c 0 * c 3) * (c 1 * c 3) = -((c 1 * c 3) * (c 0 * c 3)) ∧
      (c 0 * c 3) * (c 2 * c 3) = -((c 2 * c 3) * (c 0 * c 3)) ∧
      (c 1 * c 2) * (c 2 * c 3) = -((c 2 * c 3) * (c 1 * c 2)) ∧
      (c 1 * c 3) * (c 2 * c 3) = -((c 2 * c 3) * (c 1 * c 3)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact eq_neg_of_add_eq_zero_left h01_02 |>.trans (by noncomm_ring)
    · exact eq_neg_of_add_eq_zero_left h01_03 |>.trans (by noncomm_ring)
    · exact eq_neg_of_add_eq_zero_left h02_03 |>.trans (by noncomm_ring)
    · exact eq_neg_of_add_eq_zero_left h12_13 |>.trans (by noncomm_ring)
    · exact eq_neg_of_add_eq_zero_left h01_12 |>.trans (by noncomm_ring)
    · exact eq_neg_of_add_eq_zero_left h01_13 |>.trans (by noncomm_ring)
    · exact eq_neg_of_add_eq_zero_left h02_12 |>.trans (by noncomm_ring)
    · exact eq_neg_of_add_eq_zero_left h02_23 |>.trans (by noncomm_ring)
    · exact eq_neg_of_add_eq_zero_left h03_13 |>.trans (by noncomm_ring)
    · exact eq_neg_of_add_eq_zero_left h03_23 |>.trans (by noncomm_ring)
    · exact eq_neg_of_add_eq_zero_left h12_23 |>.trans (by noncomm_ring)
    · exact eq_neg_of_add_eq_zero_left h13_23 |>.trans (by noncomm_ring)
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  rw [hsq01, hsq02, hsq03, hsq12, hsq13, hsq23,
    h01_23, h23_01, h02_13, h13_02, h03_12, h12_03,
    h2_cancel.1, h2_cancel.2.1, h2_cancel.2.2.1, h2_cancel.2.2.2.1,
    h2_cancel.2.2.2.2.1, h2_cancel.2.2.2.2.2.1, h2_cancel.2.2.2.2.2.2.1,
    h2_cancel.2.2.2.2.2.2.2.1, h2_cancel.2.2.2.2.2.2.2.2.1,
    h2_cancel.2.2.2.2.2.2.2.2.2.1, h2_cancel.2.2.2.2.2.2.2.2.2.2.1,
    h2_cancel.2.2.2.2.2.2.2.2.2.2.2]
  dsimp [splitBivectorNormSq, kleinQ]
  simp only [Algebra.algebraMap_eq_smul_one, smul_neg, smul_add, smul_smul]
  simp only [mul_comm P.p02 P.p01, mul_comm P.p03 P.p01, mul_comm P.p03 P.p02,
    mul_comm P.p13 P.p12, mul_comm P.p12 P.p01, mul_comm P.p13 P.p01,
    mul_comm P.p12 P.p02, mul_comm P.p23 P.p02, mul_comm P.p13 P.p03,
    mul_comm P.p23 P.p03, mul_comm P.p23 P.p12, mul_comm P.p23 P.p13]
  module

/-- **Klein-Quadric Decomposability iff Scalar Clifford Square**:
in `Cl(2,2)`, the geometric square `B *_{Cl} B` is purely scalar iff `kleinQ P = 0`. -/
theorem splitExterior2_decomposable_iff_geometricProduct_scalar (P : Plucker6 ℝ) :
    (∃ c : ℝ,
      geometricProduct (Qsplit 2) (plucker6ToSplitExterior2 P).val
        (plucker6ToSplitExterior2 P).val =
        algebraMap ℝ (SplitExteriorStage 2) c) ↔
      kleinQ P = 0 := by
  constructor
  · rintro ⟨c, hc⟩
    rw [splitExterior2_geometricProduct_self] at hc
    have h4 : (2 * kleinQ P) • splitVolume4 =
        algebraMap ℝ (SplitExteriorStage 2) (c - splitBivectorNormSq P) := by
      rw [map_sub]
      exact eq_sub_of_add_eq' hc
    have hdeg1 : algebraMap ℝ (SplitExteriorStage 2) (c - splitBivectorNormSq P) ∈
        ExteriorGrade ℝ (SplitSpace 2) 0 := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.one_le.mp le_rfl)
    have hdeg4 : splitVolume4 ∈ ExteriorGrade ℝ (SplitSpace 2) 4 := by
      have hmem := (exteriorPower.ιMulti ℝ 4 splitSpace2Vec).property
      have heq : (exteriorPower.ιMulti ℝ 4 splitSpace2Vec : SplitExteriorStage 2) =
          splitVolume4 := by
        rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
        simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
        dsimp [splitVolume4]
        noncomm_ring
      rwa [heq] at hmem
    have hmem4 : (2 * kleinQ P) • splitVolume4 ∈ ExteriorGrade ℝ (SplitSpace 2) 4 :=
      Submodule.smul_mem _ _ hdeg4
    have hmem0 : (2 * kleinQ P) • splitVolume4 ∈ ExteriorGrade ℝ (SplitSpace 2) 0 := by
      rwa [h4]
    have hl0 := ExteriorAlgebra.GradedAlgebra.liftι_eq ℝ (SplitSpace 2) 0 ⟨_, hmem0⟩
    have hl4 := ExteriorAlgebra.GradedAlgebra.liftι_eq ℝ (SplitSpace 2) 4 ⟨_, hmem4⟩
    have heq_ds : DirectSum.of (fun i => ⋀[ℝ]^i (SplitSpace 2)) 0 ⟨_, hmem0⟩ =
        DirectSum.of (fun i => ⋀[ℝ]^i (SplitSpace 2)) 4 ⟨_, hmem4⟩ :=
      hl0.symm.trans hl4
    have h4val : (⟨(2 * kleinQ P) • splitVolume4, hmem4⟩ : ⋀[ℝ]^4 (SplitSpace 2)) = 0 := by
      have hcomp := congrArg (fun d : DirectSum ℕ (fun i => ⋀[ℝ]^i (SplitSpace 2)) => d 4) heq_ds
      simp at hcomp
      exact hcomp.symm
    have hzero : (2 * kleinQ P) • splitVolume4 = 0 := congrArg Subtype.val h4val
    rcases smul_eq_zero.mp hzero with hk | hvol
    · linarith
    · exact absurd hvol splitVolume4_ne_zero
  · intro hK
    refine ⟨splitBivectorNormSq P, ?_⟩
    rw [splitExterior2_geometricProduct_self, hK, mul_zero, zero_smul, add_zero]

/-- Vector-valued contraction map `SplitSpace 2 →ₗ[ℝ] SplitSpace 2` representing
`v ↦ v ⌟ B` via the 4×4 matrix in `{e₀, e₁, e₂, e₃}`:
$$M(P) = \begin{pmatrix}
0 & p_{01} & -p_{02} & p_{03} \\
p_{01} & 0 & -p_{12} & p_{13} \\
p_{02} & -p_{12} & 0 & p_{23} \\
p_{03} & -p_{13} & p_{23} & 0
\end{pmatrix}.$$ -/
def splitBivectorContractionMatrix (P : Plucker6 ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, P.p01, -P.p02, P.p03;
     P.p01, 0, -P.p12, P.p13;
     P.p02, -P.p12, 0, P.p23;
     P.p03, -P.p13, P.p23, 0]

/-- Vector-valued metric contraction operator `v ↦ v ⌟ B` on `SplitSpace 2`. -/
noncomputable def splitBivectorContractionVec (P : Plucker6 ℝ) : SplitSpace 2 →ₗ[ℝ] SplitSpace 2 :=
  splitSpace2Fin4Equiv.symm.toLinearMap.comp
    ((Matrix.toLin' (splitBivectorContractionMatrix P)).comp splitSpace2Fin4Equiv.toLinearMap)

/-- The exterior-1 embedding of `splitBivectorContractionVec P v` equals the Clifford interior
product `interiorProduct (Qsplit 2) v (plucker6ToSplitExterior2 P).val` for every `v : SplitSpace 2`. -/
theorem exteriorIota_splitBivectorContractionVec (P : Plucker6 ℝ) (v : SplitSpace 2) :
    ExteriorAlgebra.ι ℝ (splitBivectorContractionVec P v) =
      interiorProduct (Qsplit 2) v (plucker6ToSplitExterior2 P).val := by
  have hint_basis : ∀ k : Fin 4,
      ExteriorAlgebra.ι ℝ (splitBivectorContractionVec P (splitSpace2Vec k)) =
        interiorProduct (Qsplit 2) (splitSpace2Vec k) (plucker6ToSplitExterior2 P).val := by
    intro k
    rw [plucker6ToSplitExterior2_val]
    have hlin : ∀ (a b : ℝ) (x y : SplitExteriorStage 2),
        interiorProduct (Qsplit 2) (splitSpace2Vec k) (a • x + b • y) =
          a • interiorProduct (Qsplit 2) (splitSpace2Vec k) x +
            b • interiorProduct (Qsplit 2) (splitSpace2Vec k) y := by
      intro a b x y
      dsimp [interiorProduct]
      rw [map_add, map_add, map_smul, map_smul, map_smul, map_smul,
        map_add, map_smul, map_smul]
    simp only [interiorProduct, map_add, map_smul]
    have hint_e : ∀ i j : Fin 4,
        cliffordExteriorEquiv (Qsplit 2)
          (CliffordAlgebra.contractLeft (QuadraticMap.associated (Qsplit 2) (splitSpace2Vec k))
            ((cliffordExteriorEquiv (Qsplit 2)).symm (eWedge i j))) =
          splitSign k •
            ((if k = i then ExteriorAlgebra.ι ℝ (splitSpace2Vec j) else 0) -
             (if k = j then ExteriorAlgebra.ι ℝ (splitSpace2Vec i) else 0)) := by
      intro i j
      change interiorProduct (Qsplit 2) (splitSpace2Vec k) (eWedge i j) = _
      rw [interiorProduct_decomposable_bivector, metricInner_splitSpace2Vec,
        metricInner_splitSpace2Vec]
      by_cases hki : k = i
      · subst hki
        by_cases hkj : k = j
        · subst hkj; simp
        · simp [hkj]
      · by_cases hkj : k = j
        · subst hkj; simp [hki]
        · simp [hki, hkj]
    rw [hint_e 0 1, hint_e 0 2, hint_e 0 3, hint_e 1 2, hint_e 1 3, hint_e 2 3]
    fin_cases k
    · change ExteriorAlgebra.ι ℝ (splitBivectorContractionVec P (splitSpace2Vec 0)) = _
      have hvec : splitBivectorContractionVec P (splitSpace2Vec 0) =
          P.p01 • splitSpace2Vec 1 + P.p02 • splitSpace2Vec 2 + P.p03 • splitSpace2Vec 3 := by
        apply splitSpace2Fin4Equiv.injective
        ext i; fin_cases i <;>
          simp [splitBivectorContractionVec, splitBivectorContractionMatrix, splitSpace2Vec,
            splitSpace2Fin4Equiv, Matrix.toLin'_apply, Matrix.mulVec]
      rw [hvec, map_add, map_add, map_smul, map_smul, map_smul]
      simp [splitSign]
    · change ExteriorAlgebra.ι ℝ (splitBivectorContractionVec P (splitSpace2Vec 1)) = _
      have hvec : splitBivectorContractionVec P (splitSpace2Vec 1) =
          P.p01 • splitSpace2Vec 0 + (-P.p12) • splitSpace2Vec 2 + (-P.p13) • splitSpace2Vec 3 := by
        apply splitSpace2Fin4Equiv.injective
        ext i; fin_cases i <;>
          simp [splitBivectorContractionVec, splitBivectorContractionMatrix, splitSpace2Vec,
            splitSpace2Fin4Equiv, Matrix.toLin'_apply, Matrix.mulVec]
      rw [hvec, map_add, map_add, map_smul, map_smul, map_smul]
      simp [splitSign]
    · change ExteriorAlgebra.ι ℝ (splitBivectorContractionVec P (splitSpace2Vec 2)) = _
      have hvec : splitBivectorContractionVec P (splitSpace2Vec 2) =
          (-P.p02) • splitSpace2Vec 0 + (-P.p12) • splitSpace2Vec 1 + P.p23 • splitSpace2Vec 3 := by
        apply splitSpace2Fin4Equiv.injective
        ext i; fin_cases i <;>
          simp [splitBivectorContractionVec, splitBivectorContractionMatrix, splitSpace2Vec,
            splitSpace2Fin4Equiv, Matrix.toLin'_apply, Matrix.mulVec]
      rw [hvec, map_add, map_add, map_smul, map_smul, map_smul]
      simp [splitSign]
    · change ExteriorAlgebra.ι ℝ (splitBivectorContractionVec P (splitSpace2Vec 3)) = _
      have hvec : splitBivectorContractionVec P (splitSpace2Vec 3) =
          P.p03 • splitSpace2Vec 0 + P.p13 • splitSpace2Vec 1 + P.p23 • splitSpace2Vec 2 := by
        apply splitSpace2Fin4Equiv.injective
        ext i; fin_cases i <;>
          simp [splitBivectorContractionVec, splitBivectorContractionMatrix, splitSpace2Vec,
            splitSpace2Fin4Equiv, Matrix.toLin'_apply, Matrix.mulVec]
      rw [hvec, map_add, map_add, map_smul, map_smul, map_smul]
      simp [splitSign]
  have hv : v = splitSpace2Fin4Equiv v 0 • splitSpace2Vec 0 +
      splitSpace2Fin4Equiv v 1 • splitSpace2Vec 1 +
      splitSpace2Fin4Equiv v 2 • splitSpace2Vec 2 +
      splitSpace2Fin4Equiv v 3 • splitSpace2Vec 3 := by
    apply splitSpace2Fin4Equiv.injective
    ext i; fin_cases i <;> simp [splitSpace2Vec, splitSpace2Fin4Equiv]
  rw [hv]
  simp only [map_add, map_smul]
  rw [hint_basis 0, hint_basis 1, hint_basis 2, hint_basis 3]
  have hint_add : ∀ x y : SplitSpace 2,
      interiorProduct (Qsplit 2) (x + y) (plucker6ToSplitExterior2 P).val =
        interiorProduct (Qsplit 2) x (plucker6ToSplitExterior2 P).val +
          interiorProduct (Qsplit 2) y (plucker6ToSplitExterior2 P).val := by
    intro x y
    dsimp [interiorProduct]
    rw [map_add, map_add, LinearMap.add_apply, map_add]
  have hint_smul : ∀ (r : ℝ) (x : SplitSpace 2),
      interiorProduct (Qsplit 2) (r • x) (plucker6ToSplitExterior2 P).val =
        r • interiorProduct (Qsplit 2) x (plucker6ToSplitExterior2 P).val := by
    intro r x
    dsimp [interiorProduct]
    rw [map_smul, map_smul, LinearMap.smul_apply, map_smul]
  rw [hint_add, hint_add, hint_add, hint_smul, hint_smul, hint_smul, hint_smul]

/-- Determinant of the `4 × 4` contraction matrix `splitBivectorContractionMatrix P` equals
`(kleinQ P)^2`. -/
theorem det_splitBivectorContractionMatrix (P : Plucker6 ℝ) :
    Matrix.det (splitBivectorContractionMatrix P) = (kleinQ P) ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, Fin.succAbove, Matrix.det_fin_three,
    splitBivectorContractionMatrix, kleinQ]
  ring

/-- **Sobczyk Plücker Relation in `Cl(2,2)` (Eq. 5)**:
`(v ⌟ B) ∧ B = 0` for all `v : SplitSpace 2` iff `kleinQ P = 0`. -/
theorem sobczyk_plucker_relation_iff_kleinQ (P : Plucker6 ℝ) :
    (∀ v : SplitSpace 2,
      outerProduct (interiorProduct (Qsplit 2) v (plucker6ToSplitExterior2 P).val)
        (plucker6ToSplitExterior2 P).val = 0) ↔
      kleinQ P = 0 := by
  constructor
  · intro h
    have h0 := h (splitSpace2Vec 0)
    have hvec0 : splitBivectorContractionVec P (splitSpace2Vec 0) =
        P.p01 • splitSpace2Vec 1 + P.p02 • splitSpace2Vec 2 + P.p03 • splitSpace2Vec 3 := by
      apply splitSpace2Fin4Equiv.injective
      ext i; fin_cases i <;>
        simp [splitBivectorContractionVec, splitBivectorContractionMatrix, splitSpace2Vec,
          splitSpace2Fin4Equiv, Matrix.toLin'_apply, Matrix.mulVec]
    have hprod :
        outerProduct (interiorProduct (Qsplit 2) (splitSpace2Vec 0)
          (plucker6ToSplitExterior2 P).val) (plucker6ToSplitExterior2 P).val =
          (kleinQ P) •
            (ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) *
             ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) *
             ExteriorAlgebra.ι ℝ (splitSpace2Vec 3)) := by
      rw [← exteriorIota_splitBivectorContractionVec, hvec0, map_add, map_add,
        map_smul, map_smul, map_smul, plucker6ToSplitExterior2_val]
      dsimp [outerProduct, kleinQ, eWedge]
      have hsq : ∀ a : Fin 4,
          ExteriorAlgebra.ι ℝ (splitSpace2Vec a) * ExteriorAlgebra.ι ℝ (splitSpace2Vec a) = 0 :=
        fun a => ExteriorAlgebra.ι_sq_zero _
      have hanti : ∀ a b : Fin 4,
          ExteriorAlgebra.ι ℝ (splitSpace2Vec b) * ExteriorAlgebra.ι ℝ (splitSpace2Vec a) =
            -(ExteriorAlgebra.ι ℝ (splitSpace2Vec a) * ExteriorAlgebra.ι ℝ (splitSpace2Vec b)) :=
        fun a b => outerProduct_vectors_anticommute (R := ℝ) (splitSpace2Vec b) (splitSpace2Vec a)
      have htriple0 : ∀ a b c : Fin 4,
          (a = b ∨ a = c) →
            ExteriorAlgebra.ι ℝ (splitSpace2Vec a) *
              (ExteriorAlgebra.ι ℝ (splitSpace2Vec b) * ExteriorAlgebra.ι ℝ (splitSpace2Vec c)) = 0 := by
        intro a b c hor
        rcases hor with rfl | rfl
        · rw [← mul_assoc, hsq a, zero_mul]
        · calc
            ExteriorAlgebra.ι ℝ (splitSpace2Vec a) *
                (ExteriorAlgebra.ι ℝ (splitSpace2Vec b) * ExteriorAlgebra.ι ℝ (splitSpace2Vec a))
                = (ExteriorAlgebra.ι ℝ (splitSpace2Vec a) * ExteriorAlgebra.ι ℝ (splitSpace2Vec b)) *
                    ExteriorAlgebra.ι ℝ (splitSpace2Vec a) := by rw [mul_assoc]
            _ = (-(ExteriorAlgebra.ι ℝ (splitSpace2Vec b) * ExteriorAlgebra.ι ℝ (splitSpace2Vec a))) *
                    ExteriorAlgebra.ι ℝ (splitSpace2Vec a) := by rw [hanti b a]
            _ = -(ExteriorAlgebra.ι ℝ (splitSpace2Vec b) *
                    (ExteriorAlgebra.ι ℝ (splitSpace2Vec a) * ExteriorAlgebra.ι ℝ (splitSpace2Vec a))) := by
                    noncomm_ring
            _ = 0 := by rw [hsq a]; simp
      have he1_02 :
          ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) *
            (ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 2)) =
            -(ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) *
              ExteriorAlgebra.ι ℝ (splitSpace2Vec 2)) := by
        rw [← mul_assoc, hanti 0 1]; noncomm_ring
      have he2_01 :
          ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) *
            (ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 1)) =
            ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) *
              ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) := by
        rw [← mul_assoc, hanti 0 2, neg_mul, mul_assoc, hanti 1 2]; noncomm_ring
      have he1_03 :
          ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) *
            (ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 3)) =
            -(ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) *
              ExteriorAlgebra.ι ℝ (splitSpace2Vec 3)) := by
        rw [← mul_assoc, hanti 0 1]; noncomm_ring
      have he3_01 :
          ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) *
            (ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 1)) =
            ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) *
              ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) := by
        rw [← mul_assoc, hanti 0 3, neg_mul, mul_assoc, hanti 1 3]; noncomm_ring
      have he2_03 :
          ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) *
            (ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 3)) =
            -(ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) *
              ExteriorAlgebra.ι ℝ (splitSpace2Vec 3)) := by
        rw [← mul_assoc, hanti 0 2]; noncomm_ring
      have he3_02 :
          ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) *
            (ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 2)) =
            ExteriorAlgebra.ι ℝ (splitSpace2Vec 0) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) *
              ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) := by
        rw [← mul_assoc, hanti 0 3, neg_mul, mul_assoc, hanti 2 3]; noncomm_ring
      have he1_23 :
          ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) *
            (ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 3)) =
            ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) *
              ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) := by noncomm_ring
      have he2_13 :
          ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) *
            (ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 3)) =
            -(ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) *
              ExteriorAlgebra.ι ℝ (splitSpace2Vec 3)) := by
        rw [← mul_assoc, hanti 1 2]; noncomm_ring
      have he3_12 :
          ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) *
            (ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 2)) =
            ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) * ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) *
              ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) := by
        rw [← mul_assoc, hanti 1 3, neg_mul, mul_assoc, hanti 2 3]; noncomm_ring
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
      rw [htriple0 1 0 1 (Or.inr rfl), htriple0 1 1 2 (Or.inl rfl),
        htriple0 1 1 3 (Or.inl rfl),
        htriple0 2 0 2 (Or.inr rfl), htriple0 2 1 2 (Or.inr rfl),
        htriple0 2 2 3 (Or.inl rfl),
        htriple0 3 0 3 (Or.inr rfl), htriple0 3 1 3 (Or.inr rfl),
        htriple0 3 2 3 (Or.inr rfl)]
      rw [he1_02, he2_01, he1_03, he3_01, he2_03, he3_02, he1_23, he2_13, he3_12]
      simp only [smul_zero, add_zero, zero_add, smul_neg]
      have hcomm012 : P.p01 * P.p02 = P.p02 * P.p01 := mul_comm _ _
      have hcomm013 : P.p01 * P.p03 = P.p03 * P.p01 := mul_comm _ _
      have hcomm023 : P.p02 * P.p03 = P.p03 * P.p02 := mul_comm _ _
      have hcomm2301 : P.p23 * P.p01 = P.p01 * P.p23 := mul_comm _ _
      have hcomm1302 : P.p13 * P.p02 = P.p02 * P.p13 := mul_comm _ _
      have hcomm1203 : P.p12 * P.p03 = P.p03 * P.p12 := mul_comm _ _
      simp only [smul_smul, smul_add, smul_neg, add_smul]
      rw [hcomm012, hcomm013, hcomm023, hcomm2301, hcomm1302, hcomm1203]
      module
    rw [hprod] at h0
    have hne :
        ExteriorAlgebra.ι ℝ (splitSpace2Vec 1) *
          ExteriorAlgebra.ι ℝ (splitSpace2Vec 2) *
          ExteriorAlgebra.ι ℝ (splitSpace2Vec 3) ≠ 0 := by
      let sub3 : Fin 3 → SplitSpace 2 := ![splitSpace2Vec 1, splitSpace2Vec 2, splitSpace2Vec 3]
      have hli3 : LinearIndependent ℝ sub3 := by
        have hinj : Function.Injective (Fin.succ : Fin 3 → Fin 4) := Fin.succ_injective 3
        have hsub : sub3 = splitSpace2Vec ∘ Fin.succ := by
          funext i; fin_cases i <;> rfl
        rw [hsub]
        exact splitSpace2Vec_linearIndependent.comp Fin.succ hinj
      have hne3 := InfoGeometry.Canonical.exteriorPower_ιMulti_ne_zero_of_linearIndependent sub3 hli3
      intro hz
      apply hne3
      apply Subtype.ext
      change (exteriorPower.ιMulti ℝ 3 sub3 : SplitExteriorStage 2) = 0
      rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
      simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
      simpa [sub3, mul_assoc] using hz
    rcases smul_eq_zero.mp h0 with hK | htriv
    · exact hK
    · exact absurd htriv hne
  · intro hK v
    obtain ⟨x, y, hxy⟩ := (kleinQ_zero_iff_exists_zornPluckerLineMatrix P).1 hK
    have hP : pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩ = P := by
      rw [plucker6_offDiagonal_eq_zornPluckerLineMatrix_real] at hxy
      have h1 := congrArg InfoGeometry.Algebra.ZornVectorMatrix.v hxy
      have h2 := congrArg InfoGeometry.Algebra.ZornVectorMatrix.w hxy
      ext
      · simpa [plucker6ToPhase] using congrFun h1 0
      · simpa [plucker6ToPhase] using congrFun h1 1
      · simpa [plucker6ToPhase] using congrFun h1 2
      · simpa [plucker6ToPhase] using congrFun h2 2
      · have hw1 : -((pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩).p13) = -P.p13 := by
          simpa [plucker6ToPhase] using congrFun h2 1
        linarith
      · simpa [plucker6ToPhase] using congrFun h2 0
    have hB : (plucker6ToSplitExterior2 P).val =
        ExteriorAlgebra.ι ℝ (splitSpace2Fin4Equiv.symm ![x 0, x 1, x 2, x 3]) *
          ExteriorAlgebra.ι ℝ (splitSpace2Fin4Equiv.symm ![y 0, y 1, y 2, y 3]) := by
      rw [← hP]
      have hline := congrArg Subtype.val
        (pluckerLine_toSplitExterior2 ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩)
      simpa [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
        List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] using hline
    rw [hB]
    exact outerProduct_interiorProduct_decomposable_eq_zero (Qsplit 2) v _ _

/-- **Sobczyk Lemma 2 (Non-Decomposable Rank-4 Case)**:
whenever `kleinQ P ≠ 0`, the contraction map `v ↦ v ⌟ B` is surjective (`finrank = 4`). -/
theorem splitBivectorContraction_finrank_eq_four_of_kleinQ_ne_zero
    (P : Plucker6 ℝ) (hK : kleinQ P ≠ 0) :
    Module.finrank ℝ (LinearMap.range (splitBivectorContractionVec P)) = 4 := by
  have hdet : Matrix.det (splitBivectorContractionMatrix P) ≠ 0 := by
    rw [det_splitBivectorContractionMatrix]
    exact pow_ne_zero 2 hK
  have hu : IsUnit (Matrix.det (splitBivectorContractionMatrix P)) := isUnit_iff_ne_zero.mpr hdet
  let hinv : Invertible (splitBivectorContractionMatrix P) := Matrix.invertibleOfIsUnitDet _ hu
  let eM : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
    Matrix.toLinearEquiv' (splitBivectorContractionMatrix P) hinv
  have hrange_M : LinearMap.range (Matrix.toLin' (splitBivectorContractionMatrix P)) = ⊤ := by
    change LinearMap.range eM.toLinearMap = ⊤
    exact LinearEquiv.range eM
  have hrange : LinearMap.range (splitBivectorContractionVec P) = ⊤ := by
    dsimp [splitBivectorContractionVec]
    rw [LinearMap.range_comp, LinearMap.range_comp, splitSpace2Fin4Equiv.range,
      Submodule.map_top, hrange_M, Submodule.map_top, splitSpace2Fin4Equiv.symm.range]
  rw [hrange, finrank_top]
  have hfin : Module.finrank ℝ (SplitSpace 2) = Module.finrank ℝ (Fin 4 → ℝ) :=
    splitSpace2Fin4Equiv.finrank_eq
  rw [hfin, Module.finrank_fin_fun]

private lemma finrank_range_eq_two_of_two_generators
    (P : Plucker6 ℝ) (i j : Fin 4)
    (hli : LinearIndependent ℝ ![Matrix.toLin' (splitBivectorContractionMatrix P) (Pi.single i 1),
      Matrix.toLin' (splitBivectorContractionMatrix P) (Pi.single j 1)])
    (hspan : ∀ k : Fin 4,
      Matrix.toLin' (splitBivectorContractionMatrix P) (Pi.single k 1) ∈
        Submodule.span ℝ {
          Matrix.toLin' (splitBivectorContractionMatrix P) (Pi.single i 1),
          Matrix.toLin' (splitBivectorContractionMatrix P) (Pi.single j 1) }) :
    Module.finrank ℝ (LinearMap.range (splitBivectorContractionVec P)) = 2 := by
  let L := Matrix.toLin' (splitBivectorContractionMatrix P)
  have hrange_L : LinearMap.range L =
      Submodule.span ℝ {L (Pi.single i 1), L (Pi.single j 1)} := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      have hx : x = ∑ k : Fin 4, x k • Pi.single k (1 : ℝ) := by
        ext m; simp [Finset.sum_apply, Pi.single_apply]
      rw [hx, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hspan k)
    · apply Submodule.span_le.2
      rintro y (rfl | rfl)
      · exact ⟨Pi.single i 1, rfl⟩
      · exact ⟨Pi.single j 1, rfl⟩
  have hfin_L : Module.finrank ℝ (LinearMap.range L) = 2 := by
    rw [hrange_L]
    have hsp : Submodule.span ℝ {L (Pi.single i 1), L (Pi.single j 1)} =
        Submodule.span ℝ (Set.range ![L (Pi.single i 1), L (Pi.single j 1)]) := by
      congr 1
      ext y
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact or_congr eq_comm eq_comm
    rw [hsp, finrank_span_eq_card hli, Fintype.card_fin]
  have hcomp : LinearMap.range (splitBivectorContractionVec P) =
      (LinearMap.range L).map splitSpace2Fin4Equiv.symm.toLinearMap := by
    dsimp [splitBivectorContractionVec, L]
    rw [LinearMap.range_comp, LinearMap.range_comp, splitSpace2Fin4Equiv.range, Submodule.map_top]
  rw [hcomp]
  rw [LinearEquiv.finrank_map_eq splitSpace2Fin4Equiv.symm (LinearMap.range L)]
  exact hfin_L

/-- **Sobczyk Lemma 2 (Decomposable Rank-2 Case)**:
whenever `P ≠ ⟨0,0,0,0,0,0⟩` and `kleinQ P = 0`, the contraction map `v ↦ v ⌟ B` has
rank `2` (`Module.finrank ℝ (LinearMap.range (splitBivectorContractionVec P)) = 2`). -/
theorem splitBivectorContraction_finrank_eq_two_of_ne_zero_of_kleinQ_zero
    (P : Plucker6 ℝ) (hP : P ≠ ⟨0, 0, 0, 0, 0, 0⟩) (hK : kleinQ P = 0) :
    Module.finrank ℝ (LinearMap.range (splitBivectorContractionVec P)) = 2 := by
  have hK' : P.p01 * P.p23 - P.p02 * P.p13 + P.p03 * P.p12 = 0 := hK
  let L := Matrix.toLin' (splitBivectorContractionMatrix P)
  have hcol : ∀ k : Fin 4, L (Pi.single k 1) = fun r => splitBivectorContractionMatrix P r k := by
    intro k
    ext r
    simp [L, Matrix.toLin'_apply, Matrix.mulVec]
  by_cases hp01 : P.p01 ≠ 0
  · refine finrank_range_eq_two_of_two_generators P 0 1 ?_ ?_
    · rw [Fintype.linearIndependent_iff]
      intro g hg
      have h0 : g 1 * P.p01 = 0 := by
        simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          Fin.sum_univ_four, splitBivectorContractionMatrix] using congrFun hg 0
      have h1 : g 0 * P.p01 = 0 := by
        simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          Fin.sum_univ_four, splitBivectorContractionMatrix] using congrFun hg 1
      have hg1 : g 1 = 0 := (mul_eq_zero.mp h0).resolve_right hp01
      have hg0 : g 0 = 0 := (mul_eq_zero.mp h1).resolve_right hp01
      intro m; fin_cases m <;> assumption
    · intro k
      fin_cases k
      · exact Submodule.subset_span (Set.mem_insert _ _)
      · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      · have hcomb : L (Pi.single 2 1) =
            (-P.p12 / P.p01) • L (Pi.single 0 1) + (-P.p02 / P.p01) • L (Pi.single 1 1) := by
          ext r; fin_cases r <;>
            simp [hcol, splitBivectorContractionMatrix] <;> field_simp <;> linarith
        change L (Pi.single 2 1) ∈ _
        rw [hcomb]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
          (Submodule.smul_mem _ _ (Submodule.subset_span
            (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
      · have hcomb : L (Pi.single 3 1) =
            (P.p13 / P.p01) • L (Pi.single 0 1) + (P.p03 / P.p01) • L (Pi.single 1 1) := by
          ext r; fin_cases r <;>
            simp [hcol, splitBivectorContractionMatrix] <;> field_simp <;> linarith
        change L (Pi.single 3 1) ∈ _
        rw [hcomb]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
          (Submodule.smul_mem _ _ (Submodule.subset_span
            (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  · by_cases hp02 : P.p02 ≠ 0
    · refine finrank_range_eq_two_of_two_generators P 0 2 ?_ ?_
      · rw [Fintype.linearIndependent_iff]
        intro g hg
        have h0 : g 1 * (-P.p02) = 0 := by
          simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
            Fin.sum_univ_four, splitBivectorContractionMatrix] using congrFun hg 0
        have h2 : g 0 * P.p02 = 0 := by
          simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
            Fin.sum_univ_four, splitBivectorContractionMatrix] using congrFun hg 2
        have hg1 : g 1 = 0 := (mul_eq_zero.mp h0).resolve_right (neg_ne_zero.mpr hp02)
        have hg0 : g 0 = 0 := (mul_eq_zero.mp h2).resolve_right hp02
        intro m; fin_cases m <;> assumption
      · intro k
        fin_cases k
        · exact Submodule.subset_span (Set.mem_insert _ _)
        · have hcomb : L (Pi.single 1 1) =
              (-P.p12 / P.p02) • L (Pi.single 0 1) + (-P.p01 / P.p02) • L (Pi.single 2 1) := by
            ext r; fin_cases r <;>
              simp [hcol, splitBivectorContractionMatrix] <;> field_simp <;> linarith
          change L (Pi.single 1 1) ∈ _
          rw [hcomb]
          exact Submodule.add_mem _
            (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
            (Submodule.smul_mem _ _ (Submodule.subset_span
              (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
        · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        · have hcomb : L (Pi.single 3 1) =
              (P.p23 / P.p02) • L (Pi.single 0 1) + (-P.p03 / P.p02) • L (Pi.single 2 1) := by
            ext r; fin_cases r <;>
              simp [hcol, splitBivectorContractionMatrix] <;> field_simp <;> linarith
          change L (Pi.single 3 1) ∈ _
          rw [hcomb]
          exact Submodule.add_mem _
            (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
            (Submodule.smul_mem _ _ (Submodule.subset_span
              (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    · by_cases hp03 : P.p03 ≠ 0
      · refine finrank_range_eq_two_of_two_generators P 0 3 ?_ ?_
        · rw [Fintype.linearIndependent_iff]
          intro g hg
          have h0 : g 1 * P.p03 = 0 := by
            simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
              Fin.sum_univ_four, splitBivectorContractionMatrix] using congrFun hg 0
          have h3 : g 0 * P.p03 = 0 := by
            simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
              Fin.sum_univ_four, splitBivectorContractionMatrix] using congrFun hg 3
          have hg1 : g 1 = 0 := (mul_eq_zero.mp h0).resolve_right hp03
          have hg0 : g 0 = 0 := (mul_eq_zero.mp h3).resolve_right hp03
          intro m; fin_cases m <;> assumption
        · intro k
          fin_cases k
          · exact Submodule.subset_span (Set.mem_insert _ _)
          · have hcomb : L (Pi.single 1 1) =
                (-P.p13 / P.p03) • L (Pi.single 0 1) + (P.p01 / P.p03) • L (Pi.single 3 1) := by
              ext r; fin_cases r <;>
                simp [hcol, splitBivectorContractionMatrix] <;> field_simp <;> linarith
            change L (Pi.single 1 1) ∈ _
            rw [hcomb]
            exact Submodule.add_mem _
              (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
              (Submodule.smul_mem _ _ (Submodule.subset_span
                (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
          · have hcomb : L (Pi.single 2 1) =
                (P.p23 / P.p03) • L (Pi.single 0 1) + (-P.p02 / P.p03) • L (Pi.single 3 1) := by
              ext r; fin_cases r <;>
                simp [hcol, splitBivectorContractionMatrix] <;> field_simp <;> linarith
            change L (Pi.single 2 1) ∈ _
            rw [hcomb]
            exact Submodule.add_mem _
              (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
              (Submodule.smul_mem _ _ (Submodule.subset_span
                (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
          · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      · have h01 : P.p01 = 0 := not_ne_iff.mp hp01
        have h02 : P.p02 = 0 := not_ne_iff.mp hp02
        have h03 : P.p03 = 0 := not_ne_iff.mp hp03
        by_cases hp12 : P.p12 ≠ 0
        · refine finrank_range_eq_two_of_two_generators P 1 2 ?_ ?_
          · rw [Fintype.linearIndependent_iff]
            intro g hg
            have h1 : g 1 * (-P.p12) = 0 := by
              simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
                Fin.sum_univ_four, splitBivectorContractionMatrix] using congrFun hg 1
            have h2 : g 0 * (-P.p12) = 0 := by
              simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
                Fin.sum_univ_four, splitBivectorContractionMatrix] using congrFun hg 2
            have hg1 : g 1 = 0 := (mul_eq_zero.mp h1).resolve_right (neg_ne_zero.mpr hp12)
            have hg0 : g 0 = 0 := (mul_eq_zero.mp h2).resolve_right (neg_ne_zero.mpr hp12)
            intro m; fin_cases m <;> assumption
          · intro k
            fin_cases k
            · have hcomb : L (Pi.single 0 1) =
                  (-P.p02 / P.p12) • L (Pi.single 1 1) + (-P.p01 / P.p12) • L (Pi.single 2 1) := by
                ext r; fin_cases r <;>
                  simp [hcol, splitBivectorContractionMatrix, h01, h02, h03]
              change L (Pi.single 0 1) ∈ _
              rw [hcomb]
              exact Submodule.add_mem _
                (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
                (Submodule.smul_mem _ _ (Submodule.subset_span
                  (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
            · exact Submodule.subset_span (Set.mem_insert _ _)
            · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
            · have hcomb : L (Pi.single 3 1) =
                  (-P.p23 / P.p12) • L (Pi.single 1 1) + (-P.p13 / P.p12) • L (Pi.single 2 1) := by
                ext r
                fin_cases r <;>
                  simp [hcol, splitBivectorContractionMatrix, h01, h02, h03] <;>
                  field_simp [hp12]
                ring
              change L (Pi.single 3 1) ∈ _
              rw [hcomb]
              exact Submodule.add_mem _
                (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
                (Submodule.smul_mem _ _ (Submodule.subset_span
                  (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
        · have h12 : P.p12 = 0 := not_ne_iff.mp hp12
          by_cases hp13 : P.p13 ≠ 0
          · refine finrank_range_eq_two_of_two_generators P 1 3 ?_ ?_
            · rw [Fintype.linearIndependent_iff]
              intro g hg
              have h1 : g 1 * P.p13 = 0 := by
                simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
                  Fin.sum_univ_four, splitBivectorContractionMatrix] using congrFun hg 1
              have h3 : g 0 * (-P.p13) = 0 := by
                simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
                  Fin.sum_univ_four, splitBivectorContractionMatrix] using congrFun hg 3
              have hg1 : g 1 = 0 := (mul_eq_zero.mp h1).resolve_right hp13
              have hg0 : g 0 = 0 := (mul_eq_zero.mp h3).resolve_right (neg_ne_zero.mpr hp13)
              intro m; fin_cases m <;> assumption
            · intro k
              fin_cases k
              · have hcomb : L (Pi.single 0 1) = (0 : ℝ) • L (Pi.single 1 1) := by
                  ext r; fin_cases r <;>
                    simp [hcol, splitBivectorContractionMatrix, h01, h02, h03, h12]
                change L (Pi.single 0 1) ∈ _
                rw [hcomb]
                exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
              · exact Submodule.subset_span (Set.mem_insert _ _)
              · have hcomb : L (Pi.single 2 1) =
                    (-P.p23 / P.p13) • L (Pi.single 1 1) + (P.p12 / P.p13) • L (Pi.single 3 1) := by
                  ext r
                  fin_cases r <;>
                    simp [hcol, splitBivectorContractionMatrix, h01, h02, h03, h12]
                  field_simp
                change L (Pi.single 2 1) ∈ _
                rw [hcomb]
                exact Submodule.add_mem _
                  (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
                  (Submodule.smul_mem _ _ (Submodule.subset_span
                    (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
              · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
          · have h13 : P.p13 = 0 := not_ne_iff.mp hp13
            have hp23 : P.p23 ≠ 0 := by
              intro h23
              apply hP
              ext <;> assumption
            refine finrank_range_eq_two_of_two_generators P 2 3 ?_ ?_
            · rw [Fintype.linearIndependent_iff]
              intro g hg
              have h2 : g 1 * P.p23 = 0 := by
                simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
                  Fin.sum_univ_four, splitBivectorContractionMatrix] using congrFun hg 2
              have h3 : g 0 * P.p23 = 0 := by
                simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
                  Fin.sum_univ_four, splitBivectorContractionMatrix] using congrFun hg 3
              have hg1 : g 1 = 0 := (mul_eq_zero.mp h2).resolve_right hp23
              have hg0 : g 0 = 0 := (mul_eq_zero.mp h3).resolve_right hp23
              intro m; fin_cases m <;> assumption
            · intro k
              fin_cases k
              · have hcomb : L (Pi.single 0 1) = (0 : ℝ) • L (Pi.single 2 1) := by
                  ext r; fin_cases r <;>
                    simp [hcol, splitBivectorContractionMatrix, h01, h02, h03, h12, h13]
                change L (Pi.single 0 1) ∈ _
                rw [hcomb]
                exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
              · have hcomb : L (Pi.single 1 1) = (0 : ℝ) • L (Pi.single 2 1) := by
                  ext r; fin_cases r <;>
                    simp [hcol, splitBivectorContractionMatrix, h01, h02, h03, h12, h13]
                change L (Pi.single 1 1) ∈ _
                rw [hcomb]
                exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
              · exact Submodule.subset_span (Set.mem_insert _ _)
              · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- **Sobczyk Lemma 2 (Rank-2 Decomposability Dichotomy)**:
for any nonzero `P : Plucker6 ℝ`, `B = (plucker6ToSplitExterior2 P).val` is a decomposable
2-blade `ι u * ι v` iff the metric contraction operator `v ↦ v ⌟ B` has rank `2` (whereas
`kleinQ P ≠ 0` jumps the rank to `4`). -/
theorem sobczyk_lemma2_decomposable_iff_contraction_finrank
    (P : Plucker6 ℝ) (hP : P ≠ ⟨0, 0, 0, 0, 0, 0⟩) :
    Module.finrank ℝ (LinearMap.range (splitBivectorContractionVec P)) = 2 ↔
      ∃ u v : SplitSpace 2,
        (plucker6ToSplitExterior2 P).val =
          outerProduct (ExteriorAlgebra.ι ℝ u) (ExteriorAlgebra.ι ℝ v) := by
  constructor
  · intro hrank
    have hK : kleinQ P = 0 := by
      by_contra hne
      have h4 := splitBivectorContraction_finrank_eq_four_of_kleinQ_ne_zero P hne
      omega
    obtain ⟨x, y, hxy⟩ := (kleinQ_zero_iff_exists_zornPluckerLineMatrix P).1 hK
    have hP_line : pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩ = P := by
      rw [plucker6_offDiagonal_eq_zornPluckerLineMatrix_real] at hxy
      have h1 := congrArg InfoGeometry.Algebra.ZornVectorMatrix.v hxy
      have h2 := congrArg InfoGeometry.Algebra.ZornVectorMatrix.w hxy
      ext
      · simpa [plucker6ToPhase] using congrFun h1 0
      · simpa [plucker6ToPhase] using congrFun h1 1
      · simpa [plucker6ToPhase] using congrFun h1 2
      · simpa [plucker6ToPhase] using congrFun h2 2
      · have hw1 : -((pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩).p13) = -P.p13 := by
          simpa [plucker6ToPhase] using congrFun h2 1
        linarith
      · simpa [plucker6ToPhase] using congrFun h2 0
    refine ⟨splitSpace2Fin4Equiv.symm ![x 0, x 1, x 2, x 3],
      splitSpace2Fin4Equiv.symm ![y 0, y 1, y 2, y 3], ?_⟩
    rw [← hP_line]
    have hline := congrArg Subtype.val
      (pluckerLine_toSplitExterior2 ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩)
    simpa [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
      List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, outerProduct] using hline
  · rintro ⟨u, v, hB⟩
    have hrel : ∀ w : SplitSpace 2,
        outerProduct (interiorProduct (Qsplit 2) w (plucker6ToSplitExterior2 P).val)
          (plucker6ToSplitExterior2 P).val = 0 := by
      intro w
      rw [hB]
      exact outerProduct_interiorProduct_decomposable_eq_zero (Qsplit 2) w u v
    have hK : kleinQ P = 0 := (sobczyk_plucker_relation_iff_kleinQ P).1 hrel
    exact splitBivectorContraction_finrank_eq_two_of_ne_zero_of_kleinQ_zero P hP hK





/-- **End-to-End Penrose–Witt–Zorn–Clifford–Sobczyk Equivalence**:
for any Penrose twistor `Z : Twistor4`, with `B := (plucker6ToSplitExterior2 (penroseWittPlucker6 Z)).val`,
the following five algebraic/geometric decomposability characterizations are equivalent:
1. `kleinQ (penroseWittPlucker6 Z) = 0`;
2. `outerProduct B B = 0` in `SplitExteriorStage 2`;
3. `∃ c : ℝ, geometricProduct (Qsplit 2) B B = algebraMap ℝ _ c` in `Cl(2,2)`;
4. `∃ u v : SplitSpace 2, B = outerProduct (ExteriorAlgebra.ι ℝ u) (ExteriorAlgebra.ι ℝ v)`;
5. `∃ x y : Fin 4 → ℝ, zornPluckerLineMatrix x y = offDiagonalPart (penroseWittZornVectorMatrix Z)`
   (with square-zero nilpotence and zero Zorn norm). -/
theorem penroseWittPlucker6_sobczyk_clifford_zorn_equivalence (Z : Twistor4) :
    let P := penroseWittPlucker6 Z
    let B := (plucker6ToSplitExterior2 P).val
    (kleinQ P = 0 ↔ outerProduct B B = 0) ∧
    (kleinQ P = 0 ↔ ∃ c : ℝ, geometricProduct (Qsplit 2) B B =
      algebraMap ℝ (SplitExteriorStage 2) c) ∧
    (kleinQ P = 0 ↔ ∃ u v : SplitSpace 2,
      B = outerProduct (ExteriorAlgebra.ι ℝ u) (ExteriorAlgebra.ι ℝ v)) ∧
    (kleinQ P = 0 ↔ ∃ x y : Fin 4 → ℝ,
      InfoGeometry.Algebra.ZornVectorMatrix.zornPluckerLineMatrix x y =
        InfoGeometry.Algebra.ZornVectorMatrix.offDiagonalPart
          (penroseWittZornVectorMatrix Z) ∧
      InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.zornPluckerLineMatrix x y)
        (InfoGeometry.Algebra.ZornVectorMatrix.zornPluckerLineMatrix x y) =
          InfoGeometry.Algebra.ZornVectorMatrix.zero ∧
      InfoGeometry.Algebra.ZornVectorMatrix.norm
        (InfoGeometry.Algebra.ZornVectorMatrix.zornPluckerLineMatrix x y) = 0) := by
  intro P B
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro hK
      dsimp [B]
      rw [splitExterior2_outerProduct_self, hK, mul_zero, zero_smul]
    · intro hB
      dsimp [B] at hB
      rw [splitExterior2_outerProduct_self] at hB
      rcases smul_eq_zero.mp hB with h2K | hvol
      · linarith
      · exact absurd hvol splitVolume4_ne_zero
  · exact (splitExterior2_decomposable_iff_geometricProduct_scalar P).symm
  · constructor
    · intro hK
      obtain ⟨x, y, hxy⟩ := (kleinQ_zero_iff_exists_zornPluckerLineMatrix P).1 hK
      have hP_line : pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩ = P := by
        rw [plucker6_offDiagonal_eq_zornPluckerLineMatrix_real] at hxy
        have h1 := congrArg InfoGeometry.Algebra.ZornVectorMatrix.v hxy
        have h2 := congrArg InfoGeometry.Algebra.ZornVectorMatrix.w hxy
        ext
        · simpa [plucker6ToPhase] using congrFun h1 0
        · simpa [plucker6ToPhase] using congrFun h1 1
        · simpa [plucker6ToPhase] using congrFun h1 2
        · simpa [plucker6ToPhase] using congrFun h2 2
        · have hw1 : -((pluckerLine ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩).p13) = -P.p13 := by
            simpa [plucker6ToPhase] using congrFun h2 1
          linarith
        · simpa [plucker6ToPhase] using congrFun h2 0
      refine ⟨splitSpace2Fin4Equiv.symm ![x 0, x 1, x 2, x 3],
        splitSpace2Fin4Equiv.symm ![y 0, y 1, y 2, y 3], ?_⟩
      dsimp [B]
      rw [← hP_line]
      have hline := congrArg Subtype.val
        (pluckerLine_toSplitExterior2 ⟨x 0, x 1, x 2, x 3⟩ ⟨y 0, y 1, y 2, y 3⟩)
      simpa [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
        List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, outerProduct] using hline
    · rintro ⟨u, v, huv⟩
      have hrel : ∀ w : SplitSpace 2,
          outerProduct (interiorProduct (Qsplit 2) w B) B = 0 := by
        intro w
        rw [huv]
        exact outerProduct_interiorProduct_decomposable_eq_zero (Qsplit 2) w u v
      exact (sobczyk_plucker_relation_iff_kleinQ P).1 hrel
  · constructor
    · intro hK
      obtain ⟨x, y, hxy⟩ := (penroseWittZorn_offDiagonal_eq_zornPluckerLineMatrix_iff Z).1 hK
      have hnil := InfoGeometry.Algebra.ZornVectorMatrix.dahm_simple_plucker_line_null_square_and_unipotent_inversion
        x y 1 0 0
      exact ⟨x, y, hxy, hnil.2.1, hnil.1⟩
    · rintro ⟨x, y, hxy, _, _⟩
      exact (penroseWittZorn_offDiagonal_eq_zornPluckerLineMatrix_iff Z).2 ⟨x, y, hxy⟩

end SplitExterior2Sobczyk

end InfoGeometry.Twistor.PenroseWittPluckerKleinBridge

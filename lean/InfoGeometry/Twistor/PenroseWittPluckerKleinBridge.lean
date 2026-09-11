/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Twistor.PenroseZornWittBoundary
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.CanonicalZornPhasePluckerProjection
import InfoGeometry.Twistor.PhaseNativePluckerBridge
import InfoGeometry.Projective.KleinQuadricPlucker
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

All proofs are complete in native Mathlib 4 with 0 `sorry`s and 0 custom axioms.
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

end InfoGeometry.Twistor.PenroseWittPluckerKleinBridge

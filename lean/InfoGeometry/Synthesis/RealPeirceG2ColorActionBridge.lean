/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis
import InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge
import InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
import InfoGeometry.Synthesis.Cl55TwistorSplitSedenionColorBridge
import InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
import InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
import InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge

/-!
# Real Peirce-Aligned $\mathfrak{sl}_3(\mathbb{R})$ Color Action on Split-Zorn and Split-Sedenion Coordinates

This module identifies the real infinitesimal $\mathfrak{sl}_3(\mathbb{R})$ color action in direct
Peirce coordinates $(a, b; u, v)$ on `ZornSplitOctonion ℝ` and its diagonal Cayley–Dickson lift to
`SplitSedenion ℝ`, and compares it with the repository's Fock-order Günaydin–Gürsey chart by an
explicit transition map:

1. **Direct Peirce Chart (`peirceAlignedZornGGEquiv`)**:
   - Maps the two Peirce diagonal scalars $(a, b)$ to the lepton singlet pair and the off-diagonal
     3-vectors $(u, v)$ to the quark triplet and antiquark antitriplet.
2. **Exact $\mathfrak{sl}_3(\mathbb{R})$ Color Action (`zornG2Derivation_realColor_action` & `peirceAlignedZornGGEquiv_intertwines_realColor`)**:
   - Proves that on the 8-parameter trace-zero slice `realColorParameters L hL`, `zornG2Derivation`
     annihilates the Peirce diagonal $(a, b) \mapsto (0, 0)$ and acts by $(L u, -L^{\mathsf{T}} v)$ on
     the off-diagonal slots, intertwining `peirceAlignedZornToGG` with `evenColorTransform L`.
3. **Transition to the Fock-Order Chart (`zornToLeptonQuarkMultiplet_eq_transition` & `fockOrderGG_realColor_action`)**:
   - Relates `peirceAlignedZornToGG` and `zornToLeptonQuarkMultiplet` by `peirceToFockOrderGG` and
     exhibits an explicit basis witness `peirceAndFockOrderCharts_differ`.
4. **Diagonal Split-Sedenion Lift (`sedenionG2Derivation_realColor_action` & `sedenionPeirceAligned_intertwines_realColor`)**:
   - Lifts the 8-parameter $\mathfrak{sl}_3(\mathbb{R})$ color derivation diagonally via
     `sedenionG2Derivation` to `SplitSedenion ℝ = ZornSplitOctonion ℝ × ZornSplitOctonion ℝ`,
     intertwining both sheets with `evenColorTransform L` and preserving the quark–antiquark
     bilinear pairing on each sheet.
-/

set_option autoImplicit false

noncomputable section
open scoped Matrix BigOperators

namespace InfoGeometry.Synthesis.RealPeirceG2ColorActionBridge

open InfoGeometry.Algebra
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
open InfoGeometry.Synthesis.Cl55TwistorSplitSedenionColorBridge
open InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
open InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis

/-- Explicit $3 \times 3$ non-commutativity witness on `Matrix (Fin 3) (Fin 3) ℝ` (`T16`). -/
theorem realPeirce_colorMat3_noncomm :
    colorGenJ12 * colorGenK13 ≠ colorGenK13 * colorGenJ12 :=
  colorGenJ12_mul_colorGenK13_ne_comm

/-- Direct Peirce chart: diagonal entries are singlets; the upper and lower
Zorn vector slots are the triplet and antitriplet. -/
def peirceAlignedZornToGG (z : ZornSplitOctonion ℝ) : GunaydinGurseyMultiplet ℝ :=
  (![z.a, z.b], (z.u, z.v))

/-- Inverse of the direct Peirce chart. -/
def peirceAlignedGGToZorn (m : GunaydinGurseyMultiplet ℝ) : ZornSplitOctonion ℝ :=
  ⟨m.1 0, m.2.1, m.2.2, m.1 1⟩

/-- Left inverse law for `peirceAlignedZornToGG` and `peirceAlignedGGToZorn`. -/
theorem peirceAlignedZornToGG_left_inv (m : GunaydinGurseyMultiplet ℝ) :
    peirceAlignedZornToGG (peirceAlignedGGToZorn m) = m := by
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · apply Prod.ext <;> funext i <;> rfl

/-- Right inverse law for `peirceAlignedZornToGG` and `peirceAlignedGGToZorn`. -/
theorem peirceAlignedGGToZorn_right_inv (z : ZornSplitOctonion ℝ) :
    peirceAlignedGGToZorn (peirceAlignedZornToGG z) = z := by
  cases z
  rfl

/-- Equivalence of carriers in the direct Peirce coordinate order. -/
def peirceAlignedZornGGEquiv : ZornSplitOctonion ℝ ≃ GunaydinGurseyMultiplet ℝ where
  toFun := peirceAlignedZornToGG
  invFun := peirceAlignedGGToZorn
  left_inv := peirceAlignedGGToZorn_right_inv
  right_inv := peirceAlignedZornToGG_left_inv

/-- `peirceAlignedZornToGG` is additive with respect to `zornAdd`. -/
theorem peirceAlignedZornToGG_add (x y : ZornSplitOctonion ℝ) :
    peirceAlignedZornToGG (zornAdd x y) =
      peirceAlignedZornToGG x + peirceAlignedZornToGG y := by
  ext <;> simp [peirceAlignedZornToGG, zornAdd]

/-- `peirceAlignedZornToGG` is $\mathbb{R}$-homogeneous with respect to `zornSmul`. -/
theorem peirceAlignedZornToGG_smul (r : ℝ) (x : ZornSplitOctonion ℝ) :
    peirceAlignedZornToGG (zornSmul r x) =
      r • peirceAlignedZornToGG x := by
  ext <;> simp [peirceAlignedZornToGG, zornSmul]

/-- Select the eight derivation parameters corresponding to a trace-zero real
matrix in the Peirce stabilizer. -/
def realColorParameters (L : Matrix (Fin 3) (Fin 3) ℝ)
    (hL : Matrix.trace L = 0) : Params :=
  sl3Parameters (⟨L, hL⟩ : SL3)

private theorem parameterAction_realColor_action
    (L : Matrix (Fin 3) (Fin 3) ℝ) (hL : Matrix.trace L = 0)
    (X : ZornVectorMatrix ℝ) :
    parameterAction (realColorParameters L hL) X =
      ⟨0, L.mulVec X.v, (-Lᵀ).mulVec X.w, 0⟩ := by
  have hdiag : L 0 0 = -L 1 1 - L 2 2 := by
    have ht := hL
    simp [Matrix.trace, Fin.sum_univ_three] at ht
    linarith
  apply ZornVectorMatrix.ext
  · simp [parameterAction, realColorParameters, sl3Parameters]
  · funext i
    fin_cases i
    all_goals simp_all [parameterAction, realColorParameters, sl3Parameters,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    all_goals ring_nf
    all_goals simp
  · funext i
    fin_cases i
    all_goals simp_all [parameterAction, realColorParameters, sl3Parameters,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply]
    all_goals ring_nf
  · simp [parameterAction, realColorParameters, sl3Parameters]

/-- On the selected trace-zero parameter slice, the transported split-$G_2$
derivation fixes both Peirce diagonal coordinates and acts by `L` and
`-Lᵀ` on the two off-diagonal vector slots. -/
theorem zornG2Derivation_realColor_action
    (L : Matrix (Fin 3) (Fin 3) ℝ) (hL : Matrix.trace L = 0)
    (z : ZornSplitOctonion ℝ) :
    zornG2Derivation (realColorParameters L hL) z =
      ⟨0, L.mulVec z.u, (-Lᵀ).mulVec z.v, 0⟩ := by
  cases z
  simp [zornG2Derivation, zornVectorMatrixEquiv,
    zornVectorMatrixToSplitOctonion, splitOctonionToZornVectorMatrix,
    parameterAction_realColor_action]

/-- The direct Peirce chart intertwines this derivation slice with the real
infinitesimal `evenColorTransform` on the Günaydin–Gürsey carrier. -/
theorem peirceAlignedZornGGEquiv_intertwines_realColor
    (L : Matrix (Fin 3) (Fin 3) ℝ) (hL : Matrix.trace L = 0)
    (z : ZornSplitOctonion ℝ) :
    peirceAlignedZornToGG (zornG2Derivation (realColorParameters L hL) z) =
      evenColorTransform L (peirceAlignedZornToGG z) := by
  rw [zornG2Derivation_realColor_action]
  ext i <;> fin_cases i <;> rfl

/-- Coordinate transition from the direct Peirce chart to the established
Fock-order Günaydin–Gürsey chart. -/
def peirceToFockOrderGG (m : GunaydinGurseyMultiplet ℝ) :
    GunaydinGurseyMultiplet ℝ :=
  zornToLeptonQuarkMultiplet (peirceAlignedGGToZorn m)

/-- The two charts are related by the explicit transition map. -/
theorem zornToLeptonQuarkMultiplet_eq_transition (z : ZornSplitOctonion ℝ) :
    zornToLeptonQuarkMultiplet z =
      peirceToFockOrderGG (peirceAlignedZornToGG z) := by
  simp [peirceToFockOrderGG, peirceAlignedZornToGG,
    peirceAlignedGGToZorn, zornToLeptonQuarkMultiplet,
    zornToFin8, gunaydinGurseySplit]

/-- In the Fock-order chart, the transported derivation is the conjugate of the
direct Peirce-coordinate color action by the chart transition. -/
theorem fockOrderGG_realColor_action
    (L : Matrix (Fin 3) (Fin 3) ℝ) (hL : Matrix.trace L = 0)
    (z : ZornSplitOctonion ℝ) :
    zornToLeptonQuarkMultiplet
        (zornG2Derivation (realColorParameters L hL) z) =
      peirceToFockOrderGG
        (evenColorTransform L (peirceAlignedZornToGG z)) := by
  rw [zornToLeptonQuarkMultiplet_eq_transition,
    peirceAlignedZornGGEquiv_intertwines_realColor]

/-- A basis vector witnesses that the direct Peirce chart and the Fock-order
chart are genuinely different coordinate identifications. -/
theorem peirceAndFockOrderCharts_differ :
    peirceAlignedZornToGG
        (⟨0, ![1, 0, 0], ![0, 0, 0], 0⟩ : ZornSplitOctonion ℝ) ≠
      zornToLeptonQuarkMultiplet
        (⟨0, ![1, 0, 0], ![0, 0, 0], 0⟩ : ZornSplitOctonion ℝ) := by
  intro h
  have hq := congrArg (fun m : GunaydinGurseyMultiplet ℝ => m.2.1 0) h
  norm_num [peirceAlignedZornToGG, zornToLeptonQuarkMultiplet,
    zornToFin8, gunaydinGurseySplit] at hq

/-- Doubled direct Peirce chart on `SplitSedenion ℝ = ZornSplitOctonion ℝ × ZornSplitOctonion ℝ`. -/
def sedenionPeirceAlignedToGG (X : SplitSedenion ℝ) :
    GunaydinGurseyMultiplet ℝ × GunaydinGurseyMultiplet ℝ :=
  (peirceAlignedZornToGG X.1, peirceAlignedZornToGG X.2)

/-- On the 8-parameter $\mathfrak{sl}_3(\mathbb{R})$ color slice, the lifted split-sedenion
derivation `sedenionG2Derivation` acts diagonally by $(L, -L^{\mathsf{T}})$ on the off-diagonal
quark/antiquark vectors of both octonion sheets while annihilating all four Peirce diagonal scalars. -/
theorem sedenionG2Derivation_realColor_action
    (L : Matrix (Fin 3) (Fin 3) ℝ) (hL : Matrix.trace L = 0)
    (X : SplitSedenion ℝ) :
    sedenionG2Derivation (realColorParameters L hL) X =
      (⟨0, L.mulVec X.1.u, (-Lᵀ).mulVec X.1.v, 0⟩,
       ⟨0, L.mulVec X.2.u, (-Lᵀ).mulVec X.2.v, 0⟩) := by
  unfold sedenionG2Derivation
  simp [InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly.cdLift,
    zornG2Derivation_realColor_action]

/-- The doubled Peirce chart intertwines `sedenionG2Derivation (realColorParameters L hL)`
with `(evenColorTransform L, evenColorTransform L)` across both sheets of `SplitSedenion ℝ`,
and infinitesimally preserves the quark–antiquark dot pairing on each sheet. -/
theorem sedenionPeirceAligned_intertwines_realColor
    (L : Matrix (Fin 3) (Fin 3) ℝ) (hL : Matrix.trace L = 0)
    (X : SplitSedenion ℝ) :
    sedenionPeirceAlignedToGG (sedenionG2Derivation (realColorParameters L hL) X) =
      (evenColorTransform L (peirceAlignedZornToGG X.1),
       evenColorTransform L (peirceAlignedZornToGG X.2)) ∧
    (∑ a : Fin 3, ((zornG2Derivation (realColorParameters L hL) X.1).u a * X.1.v a +
      X.1.u a * (zornG2Derivation (realColorParameters L hL) X.1).v a) = 0) ∧
    (∑ a : Fin 3, ((zornG2Derivation (realColorParameters L hL) X.2).u a * X.2.v a +
      X.2.u a * (zornG2Derivation (realColorParameters L hL) X.2).v a) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold sedenionPeirceAlignedToGG sedenionG2Derivation
    simp [InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly.cdLift,
      peirceAlignedZornGGEquiv_intertwines_realColor]
  · rw [zornG2Derivation_realColor_action L hL X.1]
    exact evenColorTransform_preserves_quark_antiquark_pairing L (peirceAlignedZornToGG X.1)
  · rw [zornG2Derivation_realColor_action L hL X.2]
    exact evenColorTransform_preserves_quark_antiquark_pairing L (peirceAlignedZornToGG X.2)

end InfoGeometry.Synthesis.RealPeirceG2ColorActionBridge

end

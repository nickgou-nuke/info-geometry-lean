/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.WeylZornMajoranaZeroMode
import InfoGeometry.Canonical.ZornBdGPhaseFlowBridge
import InfoGeometry.Canonical.MajoranaPHSZeroMode

/-! The actual right-regular Majorana generator intertwines with the Nambu
sheet exchange through the existing one-mode CAR equivalence. -/

noncomputable section

namespace InfoGeometry.Twistor.WeylZornMajoranaNambu

open InfoGeometry.Krein
open InfoGeometry.Canonical.SplitOctonionRightRegularBraid
open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
open InfoGeometry.Canonical.ZornBdGPhaseFlowBridge
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.MajoranaPHSZeroMode
open InfoGeometry.Twistor.WeylZornMajoranaOperatorAction
open InfoGeometry.OperatorAlgebra.RealWeylAdjointSpinRepresentation
open InfoGeometry.Twistor.RealWeylCircularZornAction
open InfoGeometry.Twistor.PenroseCanonicalZornSoldering
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

/-- The occupation grading of the same Zorn CAR mode. -/
def zornModeGrading (i : Fin 3) :
    InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.EndCZ :=
  (rightRegularCARPair i).cre * (rightRegularCARPair i).ann -
    (rightRegularCARPair i).ann * (rightRegularCARPair i).cre

/-- The occupation grading reads out as the fundamental Nambu sheet sign. -/
theorem zornModeGrading_intertwines_nambu (i : Fin 3) (x : DoubledSpace Multiplicity) :
    zornModeGrading i (doubledZornEquiv i x) =
      doubledZornEquiv i (spectral_epsilon x) := by
  exact grading_intertwiner i x

/-- On the Zorn unit, the right-regular CAR grading reads the negative split axis. -/
theorem zornModeGrading_one (i : Fin 3) :
    zornModeGrading i 1 =
      -InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit := by
  change ((1 * InfoGeometry.Lie.SplitOctonionEllPolarization.rootMinus i) *
        InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus i) -
      ((1 * InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus i) *
        InfoGeometry.Lie.SplitOctonionEllPolarization.rootMinus i) = _
  have hleft (z : InfoGeometry.Canonical.ZornMatrix ℝ) : 1 * z = z :=
    InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.one_zMul z
  rw [hleft, hleft,
    InfoGeometry.Lie.SplitOctonionEllCrossChannel.rootMinus_mul_rootPlus,
    InfoGeometry.Lie.SplitOctonionEllCrossChannel.rootPlus_mul_rootMinus]
  rw [← InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus_sub_uMinus]
  abel

/-- Exact circular-basis coordinates of the Zorn unit. -/
theorem circular_unit_coordinates :
    circularPeirceBasis.equivFun (1 : InfoGeometry.Canonical.ZornMatrix ℝ) =
      ![1, 0, 0, 0, 1, 0, 0, 0] := by
  rw [← circularPeirceBasis_coordinate_eq_equivFun]
  funext i
  fin_cases i <;> norm_num [circularCoordinate, cartesianZornLinearEquiv]

/-- The unit occupies the positive Weyl sector for this readout. -/
theorem weylChirality_one :
    weylChirality (1 : InfoGeometry.Canonical.ZornMatrix ℝ) = 1 := by
  apply zornWeylEquiv.injective
  simp only [weylChirality, LinearEquiv.apply_symm_apply]
  have h : (zornWeylEquiv (1 : InfoGeometry.Canonical.ZornMatrix ℝ)).2 = 0 := by
    change (twistorWeylEquiv (penroseRealPeirceEquiv.symm
      (circularPeirceBasis.equivFun (1 : InfoGeometry.Canonical.ZornMatrix ℝ)))).2 = 0
    rw [circular_unit_coordinates]
    funext i
    fin_cases i <;> rfl
  apply Prod.ext
  · rfl
  · simp only [h, neg_zero]

/-- The Weyl chirality differs from every chosen one-mode CAR grading. -/
theorem weylChirality_ne_modeGrading_on_one (i : Fin 3) :
    weylChirality (1 : InfoGeometry.Canonical.ZornMatrix ℝ) ≠ zornModeGrading i 1 := by
  rw [weylChirality_one, zornModeGrading_one]
  intro h
  have ha := congrArg InfoGeometry.Canonical.ZornMatrix.a h
  norm_num [InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit] at ha

/-- The simultaneous Weyl transforms retain the same Nambu readout. -/
theorem spin_grading_intertwines_nambu
    (g : SL2C) (i : Fin 3) (x : DoubledSpace Multiplicity) :
    spinConjugation g (zornModeGrading i)
        (InfoGeometry.Twistor.RealWeylCircularZornAction.zornWeylAction g (doubledZornEquiv i x)) =
      InfoGeometry.Twistor.RealWeylCircularZornAction.zornWeylAction g
        (doubledZornEquiv i (spectral_epsilon x)) := by
  rw [spinConjugation_intertwines, zornModeGrading_intertwines_nambu]

/-- The Majorana operator is odd for its own CAR grading. -/
theorem zornModeGrading_anticommutes_majorana (i : Fin 3) :
    zornModeGrading i * majorana i + majorana i * zornModeGrading i = 0 := by
  change ((rightRegularCARPair i).cre * (rightRegularCARPair i).ann -
      (rightRegularCARPair i).ann * (rightRegularCARPair i).cre) *
      ((rightRegularCARPair i).cre + (rightRegularCARPair i).ann) +
    ((rightRegularCARPair i).cre + (rightRegularCARPair i).ann) *
      ((rightRegularCARPair i).cre * (rightRegularCARPair i).ann -
        (rightRegularCARPair i).ann * (rightRegularCARPair i).cre) = 0
  have hc := (rightRegularCARPair i).cre_sq
  have ha := (rightRegularCARPair i).ann_sq
  calc
    _ = (rightRegularCARPair i).cre * ((rightRegularCARPair i).ann * (rightRegularCARPair i).ann) -
        (rightRegularCARPair i).ann * ((rightRegularCARPair i).cre * (rightRegularCARPair i).cre) +
        ((rightRegularCARPair i).cre * (rightRegularCARPair i).cre) * (rightRegularCARPair i).ann -
        ((rightRegularCARPair i).ann * (rightRegularCARPair i).ann) * (rightRegularCARPair i).cre := by
          noncomm_ring
    _ = 0 := by rw [hc, ha]; simp

/-- The transformed Majorana operator remains odd for the transformed grading. -/
theorem spin_transformed_grading_anticommutes (g : SL2C) (i : Fin 3) :
    spinConjugation g (zornModeGrading i) * spinConjugation g (majorana i) +
      spinConjugation g (majorana i) * spinConjugation g (zornModeGrading i) = 0 := by
  simpa only [map_add, map_mul, map_zero] using
    congrArg (spinConjugation g) (zornModeGrading_anticommutes_majorana i)

set_option maxHeartbeats 800000 in
theorem majorana_intertwines_nambu_swap (i : Fin 3) (x : DoubledSpace Multiplicity) :
    majorana i (doubledZornEquiv i x) =
      doubledZornEquiv i (modular_j x) := by
  change (rightRegularCARPair i).cre (doubledZornEquiv i x) +
      (rightRegularCARPair i).ann (doubledZornEquiv i x) = _
  rw [creation_intertwiner, annihilation_intertwiner, ← map_add]
  have h := congrArg (fun T : DoubledSpace Multiplicity →L[ℝ] DoubledSpace Multiplicity => T x)
    (concrete_majorana_swap_eq_modular_j (E := Multiplicity))
  simp only [add_apply] at h
  rw [h]

theorem spin_majorana_intertwines_nambu_swap
    (g : SL2C) (i : Fin 3) (x : DoubledSpace Multiplicity) :
    spinConjugation g (majorana i)
        (InfoGeometry.Twistor.RealWeylCircularZornAction.zornWeylAction g (doubledZornEquiv i x)) =
      InfoGeometry.Twistor.RealWeylCircularZornAction.zornWeylAction g
        (doubledZornEquiv i (modular_j x)) := by
  rw [spinConjugation_intertwines, majorana_intertwines_nambu_swap]

end InfoGeometry.Twistor.WeylZornMajoranaNambu

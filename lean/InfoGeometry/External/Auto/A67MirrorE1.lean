import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# A=67 Mirror E1 Formalization

Formal core extracted from PRL 103, 052501 (2009):
`67As/67Se`, the `9/2+ -> 7/2-` E1 mirror doublet, and its
isovector/isoscalar amplitude split.
-/

noncomputable section

namespace A67MirrorE1

structure MirrorPair where
  A : ℕ
  protonRichZ : ℕ
  neutronRichZ : ℕ
  protonRichN : ℕ
  neutronRichN : ℕ

def As67Se67 : MirrorPair where
  A := 67
  protonRichZ := 33
  neutronRichZ := 34
  protonRichN := 34
  neutronRichN := 33

def mirrorChargesExchange (P : MirrorPair) : Prop :=
  P.protonRichZ = P.neutronRichN ∧ P.neutronRichZ = P.protonRichN

theorem As67Se67_is_mirror : mirrorChargesExchange As67Se67 := by
  norm_num [mirrorChargesExchange, As67Se67]

def spinDenominator (twoJi : ℕ) : ℚ :=
  twoJi + 1

def E1PlusBE1 (twoJi : ℕ) (MIV MIS : ℚ) : ℚ :=
  ((MIV + MIS) ^ 2) / spinDenominator twoJi

def E1MinusBE1 (twoJi : ℕ) (MIV MIS : ℚ) : ℚ :=
  ((MIV - MIS) ^ 2) / spinDenominator twoJi

def twoJi_9half : ℕ := 9

theorem spinDenominator_9half : spinDenominator twoJi_9half = 10 := by
  norm_num [spinDenominator, twoJi_9half]

def MIV_725_717 : ℚ := 29 / 10000

def MIS_725_717 : ℚ := 9 / 10000

def BE1_As67_725_model : ℚ :=
  E1PlusBE1 twoJi_9half MIV_725_717 MIS_725_717

def BE1_Se67_717_model : ℚ :=
  E1MinusBE1 twoJi_9half MIV_725_717 MIS_725_717

theorem BE1_As67_725_exact :
    BE1_As67_725_model = 361 / 250000000 := by
  norm_num [BE1_As67_725_model, E1PlusBE1, spinDenominator,
    twoJi_9half, MIV_725_717, MIS_725_717]

theorem BE1_Se67_717_exact :
    BE1_Se67_717_model = 1 / 2500000 := by
  norm_num [BE1_Se67_717_model, E1MinusBE1, spinDenominator,
    twoJi_9half, MIV_725_717, MIS_725_717]

def BE1_725_717_ratio : ℚ :=
  BE1_As67_725_model / BE1_Se67_717_model

theorem BE1_725_717_ratio_exact :
    BE1_725_717_ratio = 361 / 100 := by
  norm_num [BE1_725_717_ratio, BE1_As67_725_model, BE1_Se67_717_model,
    E1PlusBE1, E1MinusBE1, spinDenominator, twoJi_9half,
    MIV_725_717, MIS_725_717]

def isoscalarFraction_725_717 : ℚ :=
  MIS_725_717 / MIV_725_717

theorem isoscalarFraction_725_717_exact :
    isoscalarFraction_725_717 = 9 / 29 := by
  norm_num [isoscalarFraction_725_717, MIS_725_717, MIV_725_717]

theorem isoscalarFraction_725_717_in_PRL_window :
    (3 / 10 : ℚ) < isoscalarFraction_725_717 ∧
      isoscalarFraction_725_717 < (2 / 5 : ℚ) := by
  norm_num [isoscalarFraction_725_717, MIS_725_717, MIV_725_717]

theorem coherent_interference_asymmetry :
    BE1_Se67_717_model < BE1_As67_725_model := by
  norm_num [BE1_As67_725_model, BE1_Se67_717_model,
    E1PlusBE1, E1MinusBE1, spinDenominator, twoJi_9half,
    MIV_725_717, MIS_725_717]

def tau_As67_9half_ns : ℚ := 7 / 10

def tau_Se67_9half_ns : ℚ := 3 / 2

theorem lifetime_order_9half :
    tau_As67_9half_ns < tau_Se67_9half_ns := by
  norm_num [tau_As67_9half_ns, tau_Se67_9half_ns]

def MIV_319_303_lower : ℚ := 45 / 10000
def MIV_319_303_upper : ℚ := 64 / 10000
def MIS_319_303_lower : ℚ := 27 / 10000
def MIS_319_303_upper : ℚ := 45 / 10000

def inSecondDoubletIVInterval (x : ℚ) : Prop :=
  MIV_319_303_lower < x ∧ x < MIV_319_303_upper

def inSecondDoubletISInterval (x : ℚ) : Prop :=
  MIS_319_303_lower < x ∧ x < MIS_319_303_upper

theorem second_doublet_intervals_nonempty :
    inSecondDoubletIVInterval (11 / 2000) ∧
      inSecondDoubletISInterval (9 / 2500) := by
  norm_num [inSecondDoubletIVInterval, inSecondDoubletISInterval,
    MIV_319_303_lower, MIV_319_303_upper,
    MIS_319_303_lower, MIS_319_303_upper]

def IVGMRCoefficient (A : ℚ) (e R deltaE0 : ℚ) : ℚ :=
  ((A - 1) * e ^ 2) / (4 * R * deltaE0)

def IVGMROneBodyRadial (ri R : ℚ) : ℚ :=
  ri ^ 3 / R ^ 2

def IVGMRTwoBodyRadial (ri rj R : ℚ) : ℚ :=
  ri * rj ^ 2 / R ^ 3

def inducedIsoscalarE1Kernel (A e R deltaE0 ri rj : ℚ) : ℚ :=
  IVGMRCoefficient A e R deltaE0 *
    (IVGMROneBodyRadial ri R + IVGMRTwoBodyRadial ri rj R)

theorem IVGMR_unit_kernel_A67 :
    inducedIsoscalarE1Kernel 67 1 1 20 1 1 = 33 / 20 := by
  norm_num [inducedIsoscalarE1Kernel, IVGMRCoefficient,
    IVGMROneBodyRadial, IVGMRTwoBodyRadial]

theorem IVGMR_unit_kernel_positive_A67 :
    0 < inducedIsoscalarE1Kernel 67 1 1 20 1 1 := by
  norm_num [inducedIsoscalarE1Kernel, IVGMRCoefficient,
    IVGMROneBodyRadial, IVGMRTwoBodyRadial]

def formalSummary : Prop :=
  mirrorChargesExchange As67Se67 ∧
    BE1_725_717_ratio = 361 / 100 ∧
    (3 / 10 : ℚ) < isoscalarFraction_725_717 ∧
    isoscalarFraction_725_717 < (2 / 5 : ℚ) ∧
    0 < inducedIsoscalarE1Kernel 67 1 1 20 1 1

theorem formalSummary_proved : formalSummary := by
  refine ⟨As67Se67_is_mirror, BE1_725_717_ratio_exact, ?_, ?_,
    IVGMR_unit_kernel_positive_A67⟩
  · exact isoscalarFraction_725_717_in_PRL_window.1
  · exact isoscalarFraction_725_717_in_PRL_window.2

end A67MirrorE1

end noncomputable section

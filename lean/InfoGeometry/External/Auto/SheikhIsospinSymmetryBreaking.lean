import Mathlib.Tactic

noncomputable section

namespace SheikhIsospinSymmetryBreaking

def twoTz (N Z : ℤ) : ℤ :=
  N - Z

def Tz (N Z : ℚ) : ℚ :=
  (N - Z) / 2

theorem twoTz_self_conjugate (A : ℤ) : twoTz A A = 0 := by
  simp [twoTz]

theorem Tz_self_conjugate (A : ℚ) : Tz A A = 0 := by
  simp [Tz]

def upQuarkMassMeV : ℚ := 219 / 100
def downQuarkMassMeV : ℚ := 467 / 100
def strangeQuarkMassMeV : ℚ := 94

def qcdIsoscalarMassPart : ℚ :=
  (upQuarkMassMeV + downQuarkMassMeV) / 2

def qcdIsovectorMassPart : ℚ :=
  (upQuarkMassMeV - downQuarkMassMeV) / 2

theorem down_minus_up_quark_mass :
    downQuarkMassMeV - upQuarkMassMeV = 62 / 25 := by
  norm_num [downQuarkMassMeV, upQuarkMassMeV]

theorem qcd_isoscalar_mass_exact :
    qcdIsoscalarMassPart = 343 / 100 := by
  norm_num [qcdIsoscalarMassPart, upQuarkMassMeV, downQuarkMassMeV]

theorem qcd_isovector_mass_exact :
    qcdIsovectorMassPart = -31 / 25 := by
  norm_num [qcdIsovectorMassPart, upQuarkMassMeV, downQuarkMassMeV]

theorem qcd_u_entry_reconstructs :
    qcdIsoscalarMassPart + qcdIsovectorMassPart = upQuarkMassMeV := by
  norm_num [qcdIsoscalarMassPart, qcdIsovectorMassPart,
    upQuarkMassMeV, downQuarkMassMeV]

theorem qcd_d_entry_reconstructs :
    qcdIsoscalarMassPart - qcdIsovectorMassPart = downQuarkMassMeV := by
  norm_num [qcdIsoscalarMassPart, qcdIsovectorMassPart,
    upQuarkMassMeV, downQuarkMassMeV]

def tau3_up : ℚ := 1
def tau3_down : ℚ := -1

def qcdMassEntry (tau3 : ℚ) : ℚ :=
  qcdIsoscalarMassPart + qcdIsovectorMassPart * tau3

theorem qcd_mass_matrix_up_down_diagonal :
    qcdMassEntry tau3_up = upQuarkMassMeV ∧
      qcdMassEntry tau3_down = downQuarkMassMeV := by
  constructor <;>
    norm_num [qcdMassEntry, tau3_up, tau3_down, qcdIsoscalarMassPart,
      qcdIsovectorMassPart, upQuarkMassMeV, downQuarkMassMeV]

def tzNeutron : ℚ := 1 / 2
def tzProton : ℚ := -1 / 2

def henleyClassI (a b tauDot : ℚ) : ℚ :=
  a + b * tauDot

def henleyClassII (c tau3i tau3j tauDot : ℚ) : ℚ :=
  c * (tau3i * tau3j - tauDot / 3)

def henleyClassIII (d tau3i tau3j : ℚ) : ℚ :=
  d * (tau3i + tau3j)

theorem henley_classIII_np_vanishes (d : ℚ) :
    henleyClassIII d tzNeutron tzProton = 0 := by
  norm_num [henleyClassIII, tzNeutron, tzProton]

theorem henley_classIII_nn_pp_are_opposite (d : ℚ) :
    henleyClassIII d tzNeutron tzNeutron +
      henleyClassIII d tzProton tzProton = 0 := by
  unfold henleyClassIII tzNeutron tzProton
  ring

def IMME (a b c Tz : ℚ) : ℚ :=
  a + b * Tz + c * Tz ^ 2

theorem IMME_mirror_difference (a b c t : ℚ) :
    IMME a b c t - IMME a b c (-t) = 2 * b * t := by
  unfold IMME
  ring

theorem IMME_mirror_sum (a b c t : ℚ) :
    IMME a b c t + IMME a b c (-t) = 2 * a + 2 * c * t ^ 2 := by
  unfold IMME
  ring

abbrev IsodoubletMassSplit := String × String × ℚ × ℚ

namespace IsodoubletMassSplit

def neutronRich (p : IsodoubletMassSplit) : String := p.1
def protonRich (p : IsodoubletMassSplit) : String := p.2.1
def neutronRichMass (p : IsodoubletMassSplit) : ℚ := p.2.2.1
def protonRichMass (p : IsodoubletMassSplit) : ℚ := p.2.2.2

end IsodoubletMassSplit

def massSplitting (p : IsodoubletMassSplit) : ℚ :=
  IsodoubletMassSplit.neutronRichMass p - IsodoubletMassSplit.protonRichMass p

def neutronProtonSplit : IsodoubletMassSplit :=
  ("n", "p", 93957 / 100, 93828 / 100)

def H3He3Split : IsodoubletMassSplit :=
  ("3H", "3He", 280894 / 100, 280842 / 100)

def He5Li5Split : IsodoubletMassSplit :=
  ("5He", "5Li", 466787 / 100, 466766 / 100)

def Li7Be7Split : IsodoubletMassSplit :=
  ("7Li", "7Be", 653389 / 100, 653424 / 100)

theorem neutron_proton_mass_split_exact :
    massSplitting neutronProtonSplit = 129 / 100 := by
  norm_num [massSplitting, IsodoubletMassSplit.neutronRichMass,
    IsodoubletMassSplit.protonRichMass, neutronProtonSplit]

theorem H3_He3_mass_split_exact :
    massSplitting H3He3Split = 13 / 25 := by
  norm_num [massSplitting, IsodoubletMassSplit.neutronRichMass,
    IsodoubletMassSplit.protonRichMass, H3He3Split]

theorem He5_Li5_mass_split_exact :
    massSplitting He5Li5Split = 21 / 100 := by
  norm_num [massSplitting, IsodoubletMassSplit.neutronRichMass,
    IsodoubletMassSplit.protonRichMass, He5Li5Split]

theorem Li7_Be7_mass_split_exact :
    massSplitting Li7Be7Split = -7 / 20 := by
  norm_num [massSplitting, IsodoubletMassSplit.neutronRichMass,
    IsodoubletMassSplit.protonRichMass, Li7Be7Split]

def chargeSymmetryEigenvalue_T0 : ℤ := 1
def chargeSymmetryEigenvalue_T1 : ℤ := -1

theorem charge_symmetry_neutral_T0_T1 :
    chargeSymmetryEigenvalue_T0 = 1 ∧ chargeSymmetryEigenvalue_T1 = -1 := by
  exact ⟨rfl, rfl⟩

end SheikhIsospinSymmetryBreaking

end noncomputable section

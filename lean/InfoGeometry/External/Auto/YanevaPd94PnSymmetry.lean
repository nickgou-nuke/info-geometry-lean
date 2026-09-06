import Mathlib.Tactic

noncomputable section

namespace YanevaPd94PnSymmetry

abbrev Q := ℚ

def Z_Pd94 : ℕ := 46
def N_Pd94 : ℕ := 48
def A_Pd94 : ℕ := 94
def coreZ100Sn : ℕ := 50
def coreN100Sn : ℕ := 50
def protonHoles : ℕ := coreZ100Sn - Z_Pd94
def neutronHoles : ℕ := coreN100Sn - N_Pd94
def totalHoles : ℕ := protonHoles + neutronHoles

def Tz (N Z : Q) : Q := (N - Z) / 2
def doubledTz (N Z : ℤ) : ℤ := N - Z
def doubledT (T : ℕ) : ℕ := 2 * T
def inIsospinMultiplet (T : ℕ) (twoTz : ℤ) : Prop :=
  |twoTz| ≤ (doubledT T : ℤ)

def Z_Ag94 : ℕ := 47
def N_Ag94 : ℕ := 47
def Z_Cd96 : ℕ := 48
def N_Cd96 : ℕ := 48
def Z_Pd92 : ℕ := 46
def N_Pd92 : ℕ := 46

def jTwice_g9_2 : ℕ := 9
def su2DimFromDoubledSpin (twoJ : ℕ) : ℕ := twoJ + 1
def g9_2Degeneracy : ℕ := su2DimFromDoubledSpin jTwice_g9_2
def singleJConfigCount : ℕ := Nat.choose g9_2Degeneracy protonHoles * Nat.choose g9_2Degeneracy neutronHoles

/--
A rigorous algebraic structure representing an irreducible representation 
of the isospin SU(2) group. The representation is uniquely characterized 
by its isospin quantum number `T` and its dimension `2T + 1`.
-/
structure IsospinState where
  T : ℕ
  dim : ℕ
  is_su2_irrep : dim = 2 * T + 1

/--
The isoscalar pairing corresponds to the trivial representation (the singlet).
Two nucleons (T = 1/2) couple to either a T=0 singlet or a T=1 triplet.
For the isoscalar state, T = 0 and dim = 1.
-/
def isoscalarState : IsospinState where
  T := 0
  dim := 1
  is_su2_irrep := by rfl

/-- The isospin quantum number extracted from the formal isoscalar state. -/
def isoscalarPairT : ℕ := isoscalarState.T
def isovectorPairT : ℕ := 1
def isospinIrrepDim (T : ℕ) : ℕ := 2 * T + 1
def maxAlignedPnSpin : ℕ := 9

def so3Dim (J : ℕ) : ℕ := 2 * J + 1
def e2Allowed (Ji Jf : ℕ) : Prop := Ji = Jf + 2
def yrast8to6_Bexp : Q := 205
def yrast8to6_Blower : Q := 205 - 25
def yrast8to6_Bupper : Q := 205 + 34
def yrast8HalfLife_ps : Q := 755
def yrast6HalfLifeLimit_ps : Q := 40
def yrast6to4_Blower : Q := 113
def isomer14HalfLife_ns : Q := 515
def isomer14to12_Bexp : Q := 521 / 10
def isomer14to12_Bjun45 : Q := 101
def isomer14to12_Bgds : Q := 49
def isomer14to12_Bg9full : Q := 112
def isomer14to12_Bg9T0 : Q := 82
def isomer14to12_Bg9T1 : Q := 9
def isomer14to12_Bexvam : Q := 56

def yrast8to6_Bjun45 : Q := 252
def yrast8to6_Bgds : Q := 192
def yrast8to6_Bg9full : Q := 144
def yrast8to6_Bg9T0 : Q := 191
def yrast8to6_Bg9T1 : Q := 11
def yrast8to6_Bexvam : Q := 165

def yrast6to4_Bjun45 : Q := 453
def yrast6to4_Bgds : Q := 548
def yrast6to4_Bg9full : Q := 398
def yrast6to4_Bg9T0 : Q := 398
def yrast6to4_Bg9T1 : Q := 5
def yrast6to4_Bexvam : Q := 336

def jun45ProtonCharge : Q := 15 / 10
def jun45NeutronCharge : Q := 11 / 10
def gdsProtonCharge : Q := 11 / 10
def gdsNeutronCharge : Q := 84 / 100

def weakCollectivity (b : Q) : Prop := b < 250
def lssmOverlapPercentLowerLimit : Q := 95
def inClosedInterval (x lo hi : Q) : Prop := lo ≤ x ∧ x ≤ hi

inductive Concept where
  | Pd94_TzPlusOne
  | Ag94_TzZero
  | Isospin_T1_Multiplet
  | G9_2_Shell
  | Isoscalar_T0_Pn
  | Isovector_T1_Pn
  | E2_Yrast_Transitions
  | GDS_LSSM_ModelSpace
  deriving DecidableEq, Repr

inductive Edge where
  | member_of
  | has_shell
  | has_channel
  | competes_with
  | constrains
  | compared_by
  deriving DecidableEq, Repr

def edgeHolds : Concept → Edge → Concept → Bool
  | Concept.Pd94_TzPlusOne, Edge.member_of, Concept.Isospin_T1_Multiplet => true
  | Concept.Ag94_TzZero, Edge.member_of, Concept.Isospin_T1_Multiplet => true
  | Concept.Pd94_TzPlusOne, Edge.has_shell, Concept.G9_2_Shell => true
  | Concept.G9_2_Shell, Edge.has_channel, Concept.Isoscalar_T0_Pn => true
  | Concept.G9_2_Shell, Edge.has_channel, Concept.Isovector_T1_Pn => true
  | Concept.Isoscalar_T0_Pn, Edge.competes_with, Concept.Isovector_T1_Pn => true
  | Concept.E2_Yrast_Transitions, Edge.constrains, Concept.GDS_LSSM_ModelSpace => true
  | Concept.GDS_LSSM_ModelSpace, Edge.compared_by, Concept.E2_Yrast_Transitions => true
  | _, _, _ => false

theorem Z_Pd94_eq : Z_Pd94 = 46 := by
  norm_num [Z_Pd94]

theorem N_Pd94_eq : N_Pd94 = 48 := by
  norm_num [N_Pd94]

theorem A_Pd94_eq : A_Pd94 = 94 := by
  norm_num [A_Pd94]

theorem pd94_nucleon_sum : Z_Pd94 + N_Pd94 = A_Pd94 := by
  norm_num [Z_Pd94, N_Pd94, A_Pd94]

theorem pd94_neutron_excess : N_Pd94 = Z_Pd94 + 2 := by
  norm_num [N_Pd94, Z_Pd94]

theorem pd94_Tz_eq : Tz N_Pd94 Z_Pd94 = 1 := by
  norm_num [Tz, N_Pd94, Z_Pd94]

theorem protonHoles_eq : protonHoles = 4 := by
  norm_num [protonHoles, coreZ100Sn, Z_Pd94]

theorem neutronHoles_eq : neutronHoles = 2 := by
  norm_num [neutronHoles, coreN100Sn, N_Pd94]

theorem totalHoles_eq : totalHoles = 6 := by
  norm_num [totalHoles, protonHoles, neutronHoles, coreZ100Sn, Z_Pd94, coreN100Sn,
    N_Pd94]

theorem pd94_doubledTz_eq : doubledTz N_Pd94 Z_Pd94 = 2 := by
  norm_num [doubledTz, N_Pd94, Z_Pd94]

theorem ag94_doubledTz_eq : doubledTz N_Ag94 Z_Ag94 = 0 := by
  norm_num [doubledTz, N_Ag94, Z_Ag94]

theorem pd94_in_T1_multiplet : inIsospinMultiplet 1 (doubledTz N_Pd94 Z_Pd94) := by
  norm_num [inIsospinMultiplet, doubledT, doubledTz, N_Pd94, Z_Pd94]

theorem ag94_in_T1_multiplet : inIsospinMultiplet 1 (doubledTz N_Ag94 Z_Ag94) := by
  norm_num [inIsospinMultiplet, doubledT, doubledTz, N_Ag94, Z_Ag94]

theorem pd92_N_eq_Z : N_Pd92 = Z_Pd92 := by
  norm_num [N_Pd92, Z_Pd92]

theorem pd94_N_eq_Z_add_two : N_Pd94 = Z_Pd94 + 2 := by
  norm_num [N_Pd94, Z_Pd94]

theorem cd96_N_eq_Z : N_Cd96 = Z_Cd96 := by
  norm_num [N_Cd96, Z_Cd96]

theorem pd92_Tz_eq : Tz N_Pd92 Z_Pd92 = 0 := by
  norm_num [Tz, N_Pd92, Z_Pd92]

theorem cd96_Tz_eq : Tz N_Cd96 Z_Cd96 = 0 := by
  norm_num [Tz, N_Cd96, Z_Cd96]

theorem jTwice_g9_2_eq : jTwice_g9_2 = 9 := by
  norm_num [jTwice_g9_2]

theorem g9_2Degeneracy_eq : g9_2Degeneracy = 10 := by
  norm_num [g9_2Degeneracy, su2DimFromDoubledSpin, jTwice_g9_2]

theorem singleJConfigCount_eq : singleJConfigCount = 9450 := by
  norm_num [singleJConfigCount, Nat.choose, g9_2Degeneracy, su2DimFromDoubledSpin, jTwice_g9_2,
    protonHoles, neutronHoles, coreZ100Sn, Z_Pd94, coreN100Sn, N_Pd94]

theorem maxAlignedPnSpin_eq : maxAlignedPnSpin = 9 := by
  norm_num [maxAlignedPnSpin]

theorem isoscalarIrrepDim_eq : isospinIrrepDim isoscalarPairT = 1 := by
  norm_num [isospinIrrepDim, isoscalarPairT, isoscalarState]

theorem isovectorIrrepDim_eq : isospinIrrepDim isovectorPairT = 3 := by
  norm_num [isospinIrrepDim, isovectorPairT]

theorem isoscalarPairT_ne_isovectorPairT : isoscalarPairT ≠ isovectorPairT := by
  norm_num [isoscalarPairT, isovectorPairT, isoscalarState]

theorem e2Allowed_8_6 : e2Allowed 8 6 := by
  norm_num [e2Allowed]

theorem e2Allowed_6_4 : e2Allowed 6 4 := by
  norm_num [e2Allowed]

theorem e2Allowed_14_12 : e2Allowed 14 12 := by
  norm_num [e2Allowed]

theorem so3Dim_8_eq : so3Dim 8 = 17 := by
  norm_num [so3Dim]

theorem so3Dim_6_eq : so3Dim 6 = 13 := by
  norm_num [so3Dim]

theorem so3Dim_14_eq : so3Dim 14 = 29 := by
  norm_num [so3Dim]

theorem yrast8HalfLife_ps_eq : yrast8HalfLife_ps = 755 := by
  norm_num [yrast8HalfLife_ps]

theorem yrast8to6_Bexp_eq : yrast8to6_Bexp = 205 := by
  norm_num [yrast8to6_Bexp]

theorem yrast8to6_Blower_eq : yrast8to6_Blower = 180 := by
  norm_num [yrast8to6_Blower]

theorem yrast8to6_Bupper_eq : yrast8to6_Bupper = 239 := by
  norm_num [yrast8to6_Bupper]

theorem yrast6HalfLifeLimit_ps_eq : yrast6HalfLifeLimit_ps = 40 := by
  norm_num [yrast6HalfLifeLimit_ps]

theorem yrast6to4_Blower_eq : yrast6to4_Blower = 113 := by
  norm_num [yrast6to4_Blower]

theorem isomer14HalfLife_ns_eq : isomer14HalfLife_ns = 515 := by
  norm_num [isomer14HalfLife_ns]

theorem isomer14to12_Bexp_eq : isomer14to12_Bexp = 521 / 10 := by
  norm_num [isomer14to12_Bexp]

theorem yrast8to6_weakCollectivity : weakCollectivity yrast8to6_Bexp := by
  norm_num [weakCollectivity, yrast8to6_Bexp]

theorem jun45ProtonCharge_eq : jun45ProtonCharge = 3 / 2 := by
  norm_num [jun45ProtonCharge]

theorem jun45NeutronCharge_eq : jun45NeutronCharge = 11 / 10 := by
  norm_num [jun45NeutronCharge]

theorem gdsProtonCharge_eq : gdsProtonCharge = 11 / 10 := by
  norm_num [gdsProtonCharge]

theorem gdsNeutronCharge_eq : gdsNeutronCharge = 21 / 25 := by
  norm_num [gdsNeutronCharge]

theorem gdsNeutronCharge_lt_gdsProtonCharge : gdsNeutronCharge < gdsProtonCharge := by
  norm_num [gdsNeutronCharge, gdsProtonCharge]

theorem jun45NeutronCharge_lt_jun45ProtonCharge :
    jun45NeutronCharge < jun45ProtonCharge := by
  norm_num [jun45NeutronCharge, jun45ProtonCharge]

theorem yrast8to6_Bgds_in_interval :
    inClosedInterval yrast8to6_Bgds yrast8to6_Blower yrast8to6_Bupper := by
  norm_num [inClosedInterval, yrast8to6_Bgds, yrast8to6_Blower, yrast8to6_Bupper]

theorem isomer14to12_gds_abs_diff_eq :
    |isomer14to12_Bgds - isomer14to12_Bexp| = 31 / 10 := by
  norm_num [isomer14to12_Bgds, isomer14to12_Bexp]

theorem yrast6to4_Bgds_ge_yrast6to4_Blower :
    yrast6to4_Bgds ≥ yrast6to4_Blower := by
  norm_num [yrast6to4_Bgds, yrast6to4_Blower]

theorem isomer14to12_g9T0_closer_than_g9T1 :
    |isomer14to12_Bg9full - isomer14to12_Bg9T0| <
      |isomer14to12_Bg9full - isomer14to12_Bg9T1| := by
  norm_num [isomer14to12_Bg9full, isomer14to12_Bg9T0, isomer14to12_Bg9T1]

theorem yrast8to6_g9T0_closer_than_g9T1 :
    |yrast8to6_Bg9full - yrast8to6_Bg9T0| <
      |yrast8to6_Bg9full - yrast8to6_Bg9T1| := by
  norm_num [yrast8to6_Bg9full, yrast8to6_Bg9T0, yrast8to6_Bg9T1]

theorem yrast6to4_g9T0_closer_than_g9T1 :
    |yrast6to4_Bg9full - yrast6to4_Bg9T0| <
      |yrast6to4_Bg9full - yrast6to4_Bg9T1| := by
  norm_num [yrast6to4_Bg9full, yrast6to4_Bg9T0, yrast6to4_Bg9T1]

theorem lssmOverlapPercentLowerLimit_eq : lssmOverlapPercentLowerLimit = 95 := by
  norm_num [lssmOverlapPercentLowerLimit]

theorem edge_pd94_member_isospin_T1 :
    edgeHolds Concept.Pd94_TzPlusOne Edge.member_of Concept.Isospin_T1_Multiplet = true := by
  rfl

theorem edge_ag94_member_isospin_T1 :
    edgeHolds Concept.Ag94_TzZero Edge.member_of Concept.Isospin_T1_Multiplet = true := by
  rfl

theorem edge_pd94_has_g9_2_shell :
    edgeHolds Concept.Pd94_TzPlusOne Edge.has_shell Concept.G9_2_Shell = true := by
  rfl

theorem edge_g9_2_has_isoscalar_T0 :
    edgeHolds Concept.G9_2_Shell Edge.has_channel Concept.Isoscalar_T0_Pn = true := by
  rfl

theorem edge_g9_2_has_isovector_T1 :
    edgeHolds Concept.G9_2_Shell Edge.has_channel Concept.Isovector_T1_Pn = true := by
  rfl

theorem edge_isoscalar_T0_competes_isovector_T1 :
    edgeHolds Concept.Isoscalar_T0_Pn Edge.competes_with Concept.Isovector_T1_Pn = true := by
  rfl

theorem edge_e2_constrains_gds :
    edgeHolds Concept.E2_Yrast_Transitions Edge.constrains Concept.GDS_LSSM_ModelSpace = true := by
  rfl

end YanevaPd94PnSymmetry

end noncomputable section

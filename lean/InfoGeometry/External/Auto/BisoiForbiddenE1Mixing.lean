import Mathlib.Tactic

noncomputable section

namespace BisoiForbiddenE1Mixing

structure SelfConjugateNucleus where
  A : ℕ
  Z : ℕ
  N : ℕ

def P30 : SelfConjugateNucleus where A := 30; Z := 15; N := 15
def S32 : SelfConjugateNucleus where A := 32; Z := 16; N := 16
def Cl34 : SelfConjugateNucleus where A := 34; Z := 17; N := 17
def Ar36 : SelfConjugateNucleus where A := 36; Z := 18; N := 18

def selfConjugate (X : SelfConjugateNucleus) : Prop := X.Z = X.N

theorem P30_self : selfConjugate P30 := by norm_num [selfConjugate, P30]
theorem S32_self : selfConjugate S32 := by norm_num [selfConjugate, S32]
theorem Cl34_self : selfConjugate Cl34 := by norm_num [selfConjugate, Cl34]
theorem Ar36_self : selfConjugate Ar36 := by norm_num [selfConjugate, Ar36]

def forbiddenE1Amplitude (bi bf M01 M10 : ℚ) : ℚ :=
  -(bi * M01 + bf * M10)

def equalMixingAmplitude (Mexp M01 M10 : ℚ) : ℚ :=
  Mexp / (M01 + M10)

def mixingProbability (Mexp M01 M10 : ℚ) : ℚ :=
  (equalMixingAmplitude Mexp M01 M10) ^ 2

theorem equal_mixing_reconstructs
    {Mexp M01 M10 : ℚ} (h : M01 + M10 ≠ 0) :
    equalMixingAmplitude Mexp M01 M10 * (M01 + M10) = Mexp := by
  rw [equalMixingAmplitude]
  field_simp [h]

def Mexp_P30 : ℚ := 138 / 10000
def M01_P30 : ℚ := -228 / 10000
def M10_P30 : ℚ := 801 / 10000
def b2_P30 : ℚ := mixingProbability Mexp_P30 M01_P30 M10_P30

def Mexp_S32 : ℚ := 162 / 10000
def M01_S32 : ℚ := 1086 / 10000
def M10_S32 : ℚ := -127 / 10000
def b2_S32 : ℚ := mixingProbability Mexp_S32 M01_S32 M10_S32

def Mexp_Cl34 : ℚ := 160 / 100000
def M01_Cl34 : ℚ := 819 / 100000
def M10_Cl34 : ℚ := 2533 / 100000
def b2_Cl34 : ℚ := mixingProbability Mexp_Cl34 M01_Cl34 M10_Cl34

def Mexp_Ar36 : ℚ := 38 / 10000
def M01_Ar36 : ℚ := -144 / 10000
def M10_Ar36 : ℚ := -233 / 10000
def b2_Ar36 : ℚ := mixingProbability Mexp_Ar36 M01_Ar36 M10_Ar36

theorem b2_P30_exact :
    b2_P30 = 2116 / 36481 := by
  norm_num [b2_P30, mixingProbability, equalMixingAmplitude,
    Mexp_P30, M01_P30, M10_P30]

theorem b2_S32_exact :
    b2_S32 = 26244 / 919681 := by
  norm_num [b2_S32, mixingProbability, equalMixingAmplitude,
    Mexp_S32, M01_S32, M10_S32]

theorem b2_Cl34_exact :
    b2_Cl34 = 400 / 175561 := by
  norm_num [b2_Cl34, mixingProbability, equalMixingAmplitude,
    Mexp_Cl34, M01_Cl34, M10_Cl34]

theorem b2_Ar36_exact :
    b2_Ar36 = 1444 / 142129 := by
  norm_num [b2_Ar36, mixingProbability, equalMixingAmplitude,
    Mexp_Ar36, M01_Ar36, M10_Ar36]

def percent (x : ℚ) : ℚ := 100 * x

theorem P30_percent_window :
    (57 / 10 : ℚ) < percent b2_P30 ∧ percent b2_P30 < (59 / 10 : ℚ) := by
  norm_num [percent, b2_P30, mixingProbability, equalMixingAmplitude,
    Mexp_P30, M01_P30, M10_P30]

theorem S32_percent_window :
    (28 / 10 : ℚ) < percent b2_S32 ∧ percent b2_S32 < (29 / 10 : ℚ) := by
  norm_num [percent, b2_S32, mixingProbability, equalMixingAmplitude,
    Mexp_S32, M01_S32, M10_S32]

theorem Cl34_percent_window :
    (22 / 100 : ℚ) < percent b2_Cl34 ∧ percent b2_Cl34 < (24 / 100 : ℚ) := by
  norm_num [percent, b2_Cl34, mixingProbability, equalMixingAmplitude,
    Mexp_Cl34, M01_Cl34, M10_Cl34]

theorem Ar36_percent_window :
    (100 / 100 : ℚ) < percent b2_Ar36 ∧ percent b2_Ar36 < (102 / 100 : ℚ) := by
  norm_num [percent, b2_Ar36, mixingProbability, equalMixingAmplitude,
    Mexp_Ar36, M01_Ar36, M10_Ar36]

def finalStatePureMixingProbability (Mexp M01 : ℚ) : ℚ :=
  (Mexp / M01) ^ 2

def pureFinalDeviation (full pure : ℚ) : ℚ :=
  (pure - full) / full

end BisoiForbiddenE1Mixing

end noncomputable section

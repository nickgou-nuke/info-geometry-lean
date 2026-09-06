import Mathlib.Tactic

namespace WarehamNullBasis55

abbrev SplitPair := Rat × Rat

namespace SplitPair

abbrev p (x : SplitPair) : Rat := x.1

abbrev m (x : SplitPair) : Rat := x.2

end SplitPair

abbrev V55 := SplitPair × SplitPair × SplitPair × SplitPair × SplitPair

namespace V55

abbrev x0 (x : V55) : SplitPair := x.1
abbrev x1 (x : V55) : SplitPair := x.2.1
abbrev x2 (x : V55) : SplitPair := x.2.2.1
abbrev x3 (x : V55) : SplitPair := x.2.2.2.1
abbrev x4 (x : V55) : SplitPair := x.2.2.2.2

abbrev mk (x0 x1 x2 x3 x4 : SplitPair) : V55 := (x0, x1, x2, x3, x4)

end V55

def q11 (x : SplitPair) : Rat := x.p * x.p - x.m * x.m

def Q55 (x : V55) : Rat := q11 x.x0 + q11 x.x1 + q11 x.x2 + q11 x.x3 + q11 x.x4

def e : SplitPair := (1, 0)
def ebar : SplitPair := (0, 1)
def n : SplitPair := (1, 1)
def nbar : SplitPair := (1, -1)

def pairAdd (a b : SplitPair) : SplitPair := (a.p + b.p, a.m + b.m)
def pairNeg (a : SplitPair) : SplitPair := (-a.p, -a.m)
def pairSub (a b : SplitPair) : SplitPair := pairAdd a (pairNeg b)
def bil11 (a b : SplitPair) : Rat := a.p * b.p - a.m * b.m

def reflectE (x : SplitPair) : SplitPair := (-x.p, x.m)

def nAt0 : V55 := V55.mk n (0, 0) (0, 0) (0, 0) (0, 0)
def nAt1 : V55 := V55.mk (0, 0) n (0, 0) (0, 0) (0, 0)
def nAt2 : V55 := V55.mk (0, 0) (0, 0) n (0, 0) (0, 0)
def nAt3 : V55 := V55.mk (0, 0) (0, 0) (0, 0) n (0, 0)
def nAt4 : V55 := V55.mk (0, 0) (0, 0) (0, 0) (0, 0) n

def nbarAt0 : V55 := V55.mk nbar (0, 0) (0, 0) (0, 0) (0, 0)
def nbarAt1 : V55 := V55.mk (0, 0) nbar (0, 0) (0, 0) (0, 0)
def nbarAt2 : V55 := V55.mk (0, 0) (0, 0) nbar (0, 0) (0, 0)
def nbarAt3 : V55 := V55.mk (0, 0) (0, 0) (0, 0) nbar (0, 0)
def nbarAt4 : V55 := V55.mk (0, 0) (0, 0) (0, 0) (0, 0) nbar

def nColl : V55 := V55.mk n n n n n
def nbarColl : V55 := V55.mk nbar nbar nbar nbar nbar

def reflectColl (x : V55) : V55 :=
  V55.mk (reflectE x.x0) (reflectE x.x1) (reflectE x.x2) (reflectE x.x3) (reflectE x.x4)

theorem e_sq : q11 e = 1 := by norm_num [q11, e]
theorem ebar_sq : q11 ebar = -1 := by norm_num [q11, ebar]
theorem e_orth_ebar : bil11 e ebar = 0 := by norm_num [bil11, e, ebar]

theorem n_null : q11 n = 0 := by norm_num [q11, n]
theorem nbar_null : q11 nbar = 0 := by norm_num [q11, nbar]
theorem n_dot_nbar : bil11 n nbar = 2 := by norm_num [bil11, n, nbar]

theorem reflect_n : reflectE n = pairNeg nbar := by
  norm_num [reflectE, pairNeg, n, nbar]
theorem reflect_nbar : reflectE nbar = pairNeg n := by
  norm_num [reflectE, pairNeg, n, nbar]

theorem nAt0_null : Q55 nAt0 = 0 := by norm_num [V55.x0, V55.x1, V55.x2, V55.x3, V55.x4, Q55, q11, nAt0, n]
theorem nAt1_null : Q55 nAt1 = 0 := by norm_num [V55.x0, V55.x1, V55.x2, V55.x3, V55.x4, Q55, q11, nAt1, n]
theorem nAt2_null : Q55 nAt2 = 0 := by norm_num [V55.x0, V55.x1, V55.x2, V55.x3, V55.x4, Q55, q11, nAt2, n]
theorem nAt3_null : Q55 nAt3 = 0 := by norm_num [V55.x0, V55.x1, V55.x2, V55.x3, V55.x4, Q55, q11, nAt3, n]
theorem nAt4_null : Q55 nAt4 = 0 := by norm_num [V55.x0, V55.x1, V55.x2, V55.x3, V55.x4, Q55, q11, nAt4, n]

theorem nbarAt0_null : Q55 nbarAt0 = 0 := by norm_num [V55.x0, V55.x1, V55.x2, V55.x3, V55.x4, Q55, q11, nbarAt0, nbar]
theorem nbarAt1_null : Q55 nbarAt1 = 0 := by norm_num [V55.x0, V55.x1, V55.x2, V55.x3, V55.x4, Q55, q11, nbarAt1, nbar]
theorem nbarAt2_null : Q55 nbarAt2 = 0 := by norm_num [V55.x0, V55.x1, V55.x2, V55.x3, V55.x4, Q55, q11, nbarAt2, nbar]
theorem nbarAt3_null : Q55 nbarAt3 = 0 := by norm_num [V55.x0, V55.x1, V55.x2, V55.x3, V55.x4, Q55, q11, nbarAt3, nbar]
theorem nbarAt4_null : Q55 nbarAt4 = 0 := by norm_num [V55.x0, V55.x1, V55.x2, V55.x3, V55.x4, Q55, q11, nbarAt4, nbar]

theorem nColl_null : Q55 nColl = 0 := by norm_num [V55.x0, V55.x1, V55.x2, V55.x3, V55.x4, Q55, q11, nColl, n]
theorem nbarColl_null : Q55 nbarColl = 0 := by norm_num [V55.x0, V55.x1, V55.x2, V55.x3, V55.x4, Q55, q11, nbarColl, nbar]
theorem reflectColl_nColl : reflectColl nColl =
    V55.mk (pairNeg nbar) (pairNeg nbar) (pairNeg nbar) (pairNeg nbar) (pairNeg nbar) := by
    norm_num [V55.x0, V55.x1, V55.x2, V55.x3, V55.x4, reflectColl, reflectE, pairNeg, nColl, n, nbar]
theorem reflectColl_nbarColl : reflectColl nbarColl =
    V55.mk (pairNeg n) (pairNeg n) (pairNeg n) (pairNeg n) (pairNeg n) := by
    norm_num [V55.x0, V55.x1, V55.x2, V55.x3, V55.x4, reflectColl, reflectE, pairNeg, nbarColl, n, nbar]

inductive SpinSector where | v | s | c deriving Repr, DecidableEq

def RT (σ : SpinSector) : SpinSector :=
  match σ with
  | SpinSector.v => SpinSector.v
  | SpinSector.s => SpinSector.c
  | SpinSector.c => SpinSector.s

def mass (m0 dP dT : Rat) : SpinSector → Rat
  | SpinSector.v => m0 * m0
  | SpinSector.s => m0 * m0 + dP + dT
  | SpinSector.c => m0 * m0 + dP - dT

theorem RT_swaps_semispinors : RT SpinSector.s = SpinSector.c ∧ RT SpinSector.c = SpinSector.s := by
  constructor
  · exact Eq.refl SpinSector.c
  · exact Eq.refl SpinSector.s

theorem mass_split_example : mass 0 (1/4) (1/25) SpinSector.s ≠ mass 0 (1/4) (1/25) SpinSector.c := by
  intro h
  norm_num [mass] at h

end WarehamNullBasis55

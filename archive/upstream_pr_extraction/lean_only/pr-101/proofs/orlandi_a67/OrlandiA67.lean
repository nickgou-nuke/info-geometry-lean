import Mathlib

namespace OrlandiA67

def tauAs : Rat := 7 / 10
def tauSe : Rat := 13 / 10
def BE1As1 : Rat := 13 / 10
def BE1Se1 : Rat := 1
def BE1As2 : Rat := (81 / 10) / 1000000
def BE1Se2 : Rat := (17 / 10) / 1000000

theorem tau_ratio : tauSe / tauAs = 13 / 7 := by
  norm_num [tauSe, tauAs]

theorem BE1_first_ratio : BE1As1 / BE1Se1 = 13 / 10 := by
  norm_num [BE1As1, BE1Se1]

theorem BE1_second_ratio : BE1As2 / BE1Se2 = 81 / 17 := by
  norm_num [BE1As2, BE1Se2]

theorem BE1_second_delta : BE1As2 - BE1Se2 = (32 / 5) / 1000000 := by
  norm_num [BE1As2, BE1Se2]

structure MirrorDatum where
  A : Nat
  Z1 : Nat
  Z2 : Nat
  tau1 : Rat
  tau2 : Rat
  be1a : Rat
  be1b : Rat

 def a67 : MirrorDatum where
  A := 67
  Z1 := 33
  Z2 := 34
  tau1 := tauAs
  tau2 := tauSe
  be1a := BE1As2
  be1b := BE1Se2

end OrlandiA67

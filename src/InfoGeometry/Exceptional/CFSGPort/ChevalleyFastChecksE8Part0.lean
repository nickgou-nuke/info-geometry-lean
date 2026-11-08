/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyFastChecks

public section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem e8_conjRange_0_1 : conjRange .E8 0 1 = true := by decide +kernel
theorem e8_conjRange_1_2 : conjRange .E8 1 2 = true := by decide +kernel
theorem e8_conjRange_2_3 : conjRange .E8 2 3 = true := by decide +kernel
theorem e8_conjRange_3_4 : conjRange .E8 3 4 = true := by decide +kernel
theorem e8_conjRange_4_5 : conjRange .E8 4 5 = true := by decide +kernel
theorem e8_conjRange_5_6 : conjRange .E8 5 6 = true := by decide +kernel
theorem e8_conjRange_6_7 : conjRange .E8 6 7 = true := by decide +kernel
theorem e8_conjRange_7_8 : conjRange .E8 7 8 = true := by decide +kernel
theorem e8_conjRange_8_9 : conjRange .E8 8 9 = true := by decide +kernel
theorem e8_conjRange_9_10 : conjRange .E8 9 10 = true := by decide +kernel
theorem e8_conjRange_10_11 : conjRange .E8 10 11 = true := by decide +kernel
theorem e8_conjRange_11_12 : conjRange .E8 11 12 = true := by decide +kernel
theorem e8_conjRange_12_13 : conjRange .E8 12 13 = true := by decide +kernel
theorem e8_conjRange_13_14 : conjRange .E8 13 14 = true := by decide +kernel
theorem e8_conjRange_14_15 : conjRange .E8 14 15 = true := by decide +kernel
theorem e8_conjRange_15_16 : conjRange .E8 15 16 = true := by decide +kernel
theorem e8_conjRange_16_17 : conjRange .E8 16 17 = true := by decide +kernel
theorem e8_conjRange_17_18 : conjRange .E8 17 18 = true := by decide +kernel
theorem e8_conjRange_18_19 : conjRange .E8 18 19 = true := by decide +kernel
theorem e8_conjRange_19_20 : conjRange .E8 19 20 = true := by decide +kernel
theorem e8_conjRange_20_21 : conjRange .E8 20 21 = true := by decide +kernel
theorem e8_conjRange_21_22 : conjRange .E8 21 22 = true := by decide +kernel
theorem e8_conjRange_22_23 : conjRange .E8 22 23 = true := by decide +kernel
theorem e8_conjRange_23_24 : conjRange .E8 23 24 = true := by decide +kernel
theorem e8_conjRange_24_25 : conjRange .E8 24 25 = true := by decide +kernel
theorem e8_conjRange_25_26 : conjRange .E8 25 26 = true := by decide +kernel
theorem e8_conjRange_26_27 : conjRange .E8 26 27 = true := by decide +kernel
theorem e8_conjRange_27_28 : conjRange .E8 27 28 = true := by decide +kernel
theorem e8_conjRange_28_29 : conjRange .E8 28 29 = true := by decide +kernel
theorem e8_conjRange_29_30 : conjRange .E8 29 30 = true := by decide +kernel
theorem e8_conjRange_30_31 : conjRange .E8 30 31 = true := by decide +kernel
theorem e8_conjRange_31_32 : conjRange .E8 31 32 = true := by decide +kernel
theorem e8_conjRange_32_33 : conjRange .E8 32 33 = true := by decide +kernel
theorem e8_conjRange_33_34 : conjRange .E8 33 34 = true := by decide +kernel
theorem e8_conjRange_34_35 : conjRange .E8 34 35 = true := by decide +kernel
theorem e8_conjRange_35_36 : conjRange .E8 35 36 = true := by decide +kernel
theorem e8_conjRange_36_37 : conjRange .E8 36 37 = true := by decide +kernel
theorem e8_conjRange_37_38 : conjRange .E8 37 38 = true := by decide +kernel
theorem e8_conjRange_38_39 : conjRange .E8 38 39 = true := by decide +kernel
theorem e8_conjRange_39_40 : conjRange .E8 39 40 = true := by decide +kernel

/-- E₈ Weyl-conjugation range 0–40, assembled from one-root certificates. -/
theorem conjRange_E8_part0 : conjRange .E8 0 40 = true := by
  have h1 : conjRange .E8 0 1 = true := e8_conjRange_0_1
  have h2 : conjRange .E8 0 2 = true :=
    conjRange_trans (by omega) (by omega) h1 e8_conjRange_1_2
  have h3 : conjRange .E8 0 3 = true :=
    conjRange_trans (by omega) (by omega) h2 e8_conjRange_2_3
  have h4 : conjRange .E8 0 4 = true :=
    conjRange_trans (by omega) (by omega) h3 e8_conjRange_3_4
  have h5 : conjRange .E8 0 5 = true :=
    conjRange_trans (by omega) (by omega) h4 e8_conjRange_4_5
  have h6 : conjRange .E8 0 6 = true :=
    conjRange_trans (by omega) (by omega) h5 e8_conjRange_5_6
  have h7 : conjRange .E8 0 7 = true :=
    conjRange_trans (by omega) (by omega) h6 e8_conjRange_6_7
  have h8 : conjRange .E8 0 8 = true :=
    conjRange_trans (by omega) (by omega) h7 e8_conjRange_7_8
  have h9 : conjRange .E8 0 9 = true :=
    conjRange_trans (by omega) (by omega) h8 e8_conjRange_8_9
  have h10 : conjRange .E8 0 10 = true :=
    conjRange_trans (by omega) (by omega) h9 e8_conjRange_9_10
  have h11 : conjRange .E8 0 11 = true :=
    conjRange_trans (by omega) (by omega) h10 e8_conjRange_10_11
  have h12 : conjRange .E8 0 12 = true :=
    conjRange_trans (by omega) (by omega) h11 e8_conjRange_11_12
  have h13 : conjRange .E8 0 13 = true :=
    conjRange_trans (by omega) (by omega) h12 e8_conjRange_12_13
  have h14 : conjRange .E8 0 14 = true :=
    conjRange_trans (by omega) (by omega) h13 e8_conjRange_13_14
  have h15 : conjRange .E8 0 15 = true :=
    conjRange_trans (by omega) (by omega) h14 e8_conjRange_14_15
  have h16 : conjRange .E8 0 16 = true :=
    conjRange_trans (by omega) (by omega) h15 e8_conjRange_15_16
  have h17 : conjRange .E8 0 17 = true :=
    conjRange_trans (by omega) (by omega) h16 e8_conjRange_16_17
  have h18 : conjRange .E8 0 18 = true :=
    conjRange_trans (by omega) (by omega) h17 e8_conjRange_17_18
  have h19 : conjRange .E8 0 19 = true :=
    conjRange_trans (by omega) (by omega) h18 e8_conjRange_18_19
  have h20 : conjRange .E8 0 20 = true :=
    conjRange_trans (by omega) (by omega) h19 e8_conjRange_19_20
  have h21 : conjRange .E8 0 21 = true :=
    conjRange_trans (by omega) (by omega) h20 e8_conjRange_20_21
  have h22 : conjRange .E8 0 22 = true :=
    conjRange_trans (by omega) (by omega) h21 e8_conjRange_21_22
  have h23 : conjRange .E8 0 23 = true :=
    conjRange_trans (by omega) (by omega) h22 e8_conjRange_22_23
  have h24 : conjRange .E8 0 24 = true :=
    conjRange_trans (by omega) (by omega) h23 e8_conjRange_23_24
  have h25 : conjRange .E8 0 25 = true :=
    conjRange_trans (by omega) (by omega) h24 e8_conjRange_24_25
  have h26 : conjRange .E8 0 26 = true :=
    conjRange_trans (by omega) (by omega) h25 e8_conjRange_25_26
  have h27 : conjRange .E8 0 27 = true :=
    conjRange_trans (by omega) (by omega) h26 e8_conjRange_26_27
  have h28 : conjRange .E8 0 28 = true :=
    conjRange_trans (by omega) (by omega) h27 e8_conjRange_27_28
  have h29 : conjRange .E8 0 29 = true :=
    conjRange_trans (by omega) (by omega) h28 e8_conjRange_28_29
  have h30 : conjRange .E8 0 30 = true :=
    conjRange_trans (by omega) (by omega) h29 e8_conjRange_29_30
  have h31 : conjRange .E8 0 31 = true :=
    conjRange_trans (by omega) (by omega) h30 e8_conjRange_30_31
  have h32 : conjRange .E8 0 32 = true :=
    conjRange_trans (by omega) (by omega) h31 e8_conjRange_31_32
  have h33 : conjRange .E8 0 33 = true :=
    conjRange_trans (by omega) (by omega) h32 e8_conjRange_32_33
  have h34 : conjRange .E8 0 34 = true :=
    conjRange_trans (by omega) (by omega) h33 e8_conjRange_33_34
  have h35 : conjRange .E8 0 35 = true :=
    conjRange_trans (by omega) (by omega) h34 e8_conjRange_34_35
  have h36 : conjRange .E8 0 36 = true :=
    conjRange_trans (by omega) (by omega) h35 e8_conjRange_35_36
  have h37 : conjRange .E8 0 37 = true :=
    conjRange_trans (by omega) (by omega) h36 e8_conjRange_36_37
  have h38 : conjRange .E8 0 38 = true :=
    conjRange_trans (by omega) (by omega) h37 e8_conjRange_37_38
  have h39 : conjRange .E8 0 39 = true :=
    conjRange_trans (by omega) (by omega) h38 e8_conjRange_38_39
  have h40 : conjRange .E8 0 40 = true :=
    conjRange_trans (by omega) (by omega) h39 e8_conjRange_39_40
  exact h40

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

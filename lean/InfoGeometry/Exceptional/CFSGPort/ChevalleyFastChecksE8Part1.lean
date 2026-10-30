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

theorem e8_conjRange_40_41 : conjRange .E8 40 41 = true := by decide +kernel
theorem e8_conjRange_41_42 : conjRange .E8 41 42 = true := by decide +kernel
theorem e8_conjRange_42_43 : conjRange .E8 42 43 = true := by decide +kernel
theorem e8_conjRange_43_44 : conjRange .E8 43 44 = true := by decide +kernel
theorem e8_conjRange_44_45 : conjRange .E8 44 45 = true := by decide +kernel
theorem e8_conjRange_45_46 : conjRange .E8 45 46 = true := by decide +kernel
theorem e8_conjRange_46_47 : conjRange .E8 46 47 = true := by decide +kernel
theorem e8_conjRange_47_48 : conjRange .E8 47 48 = true := by decide +kernel
theorem e8_conjRange_48_49 : conjRange .E8 48 49 = true := by decide +kernel
theorem e8_conjRange_49_50 : conjRange .E8 49 50 = true := by decide +kernel
theorem e8_conjRange_50_51 : conjRange .E8 50 51 = true := by decide +kernel
theorem e8_conjRange_51_52 : conjRange .E8 51 52 = true := by decide +kernel
theorem e8_conjRange_52_53 : conjRange .E8 52 53 = true := by decide +kernel
theorem e8_conjRange_53_54 : conjRange .E8 53 54 = true := by decide +kernel
theorem e8_conjRange_54_55 : conjRange .E8 54 55 = true := by decide +kernel
theorem e8_conjRange_55_56 : conjRange .E8 55 56 = true := by decide +kernel
theorem e8_conjRange_56_57 : conjRange .E8 56 57 = true := by decide +kernel
theorem e8_conjRange_57_58 : conjRange .E8 57 58 = true := by decide +kernel
theorem e8_conjRange_58_59 : conjRange .E8 58 59 = true := by decide +kernel
theorem e8_conjRange_59_60 : conjRange .E8 59 60 = true := by decide +kernel
theorem e8_conjRange_60_61 : conjRange .E8 60 61 = true := by decide +kernel
theorem e8_conjRange_61_62 : conjRange .E8 61 62 = true := by decide +kernel
theorem e8_conjRange_62_63 : conjRange .E8 62 63 = true := by decide +kernel
theorem e8_conjRange_63_64 : conjRange .E8 63 64 = true := by decide +kernel
theorem e8_conjRange_64_65 : conjRange .E8 64 65 = true := by decide +kernel
theorem e8_conjRange_65_66 : conjRange .E8 65 66 = true := by decide +kernel
theorem e8_conjRange_66_67 : conjRange .E8 66 67 = true := by decide +kernel
theorem e8_conjRange_67_68 : conjRange .E8 67 68 = true := by decide +kernel
theorem e8_conjRange_68_69 : conjRange .E8 68 69 = true := by decide +kernel
theorem e8_conjRange_69_70 : conjRange .E8 69 70 = true := by decide +kernel
theorem e8_conjRange_70_71 : conjRange .E8 70 71 = true := by decide +kernel
theorem e8_conjRange_71_72 : conjRange .E8 71 72 = true := by decide +kernel
theorem e8_conjRange_72_73 : conjRange .E8 72 73 = true := by decide +kernel
theorem e8_conjRange_73_74 : conjRange .E8 73 74 = true := by decide +kernel
theorem e8_conjRange_74_75 : conjRange .E8 74 75 = true := by decide +kernel
theorem e8_conjRange_75_76 : conjRange .E8 75 76 = true := by decide +kernel
theorem e8_conjRange_76_77 : conjRange .E8 76 77 = true := by decide +kernel
theorem e8_conjRange_77_78 : conjRange .E8 77 78 = true := by decide +kernel
theorem e8_conjRange_78_79 : conjRange .E8 78 79 = true := by decide +kernel
theorem e8_conjRange_79_80 : conjRange .E8 79 80 = true := by decide +kernel

/-- E₈ Weyl-conjugation range 40–80, assembled from one-root certificates. -/
theorem conjRange_E8_part1 : conjRange .E8 40 80 = true := by
  have h41 : conjRange .E8 40 41 = true := e8_conjRange_40_41
  have h42 : conjRange .E8 40 42 = true :=
    conjRange_trans (by omega) (by omega) h41 e8_conjRange_41_42
  have h43 : conjRange .E8 40 43 = true :=
    conjRange_trans (by omega) (by omega) h42 e8_conjRange_42_43
  have h44 : conjRange .E8 40 44 = true :=
    conjRange_trans (by omega) (by omega) h43 e8_conjRange_43_44
  have h45 : conjRange .E8 40 45 = true :=
    conjRange_trans (by omega) (by omega) h44 e8_conjRange_44_45
  have h46 : conjRange .E8 40 46 = true :=
    conjRange_trans (by omega) (by omega) h45 e8_conjRange_45_46
  have h47 : conjRange .E8 40 47 = true :=
    conjRange_trans (by omega) (by omega) h46 e8_conjRange_46_47
  have h48 : conjRange .E8 40 48 = true :=
    conjRange_trans (by omega) (by omega) h47 e8_conjRange_47_48
  have h49 : conjRange .E8 40 49 = true :=
    conjRange_trans (by omega) (by omega) h48 e8_conjRange_48_49
  have h50 : conjRange .E8 40 50 = true :=
    conjRange_trans (by omega) (by omega) h49 e8_conjRange_49_50
  have h51 : conjRange .E8 40 51 = true :=
    conjRange_trans (by omega) (by omega) h50 e8_conjRange_50_51
  have h52 : conjRange .E8 40 52 = true :=
    conjRange_trans (by omega) (by omega) h51 e8_conjRange_51_52
  have h53 : conjRange .E8 40 53 = true :=
    conjRange_trans (by omega) (by omega) h52 e8_conjRange_52_53
  have h54 : conjRange .E8 40 54 = true :=
    conjRange_trans (by omega) (by omega) h53 e8_conjRange_53_54
  have h55 : conjRange .E8 40 55 = true :=
    conjRange_trans (by omega) (by omega) h54 e8_conjRange_54_55
  have h56 : conjRange .E8 40 56 = true :=
    conjRange_trans (by omega) (by omega) h55 e8_conjRange_55_56
  have h57 : conjRange .E8 40 57 = true :=
    conjRange_trans (by omega) (by omega) h56 e8_conjRange_56_57
  have h58 : conjRange .E8 40 58 = true :=
    conjRange_trans (by omega) (by omega) h57 e8_conjRange_57_58
  have h59 : conjRange .E8 40 59 = true :=
    conjRange_trans (by omega) (by omega) h58 e8_conjRange_58_59
  have h60 : conjRange .E8 40 60 = true :=
    conjRange_trans (by omega) (by omega) h59 e8_conjRange_59_60
  have h61 : conjRange .E8 40 61 = true :=
    conjRange_trans (by omega) (by omega) h60 e8_conjRange_60_61
  have h62 : conjRange .E8 40 62 = true :=
    conjRange_trans (by omega) (by omega) h61 e8_conjRange_61_62
  have h63 : conjRange .E8 40 63 = true :=
    conjRange_trans (by omega) (by omega) h62 e8_conjRange_62_63
  have h64 : conjRange .E8 40 64 = true :=
    conjRange_trans (by omega) (by omega) h63 e8_conjRange_63_64
  have h65 : conjRange .E8 40 65 = true :=
    conjRange_trans (by omega) (by omega) h64 e8_conjRange_64_65
  have h66 : conjRange .E8 40 66 = true :=
    conjRange_trans (by omega) (by omega) h65 e8_conjRange_65_66
  have h67 : conjRange .E8 40 67 = true :=
    conjRange_trans (by omega) (by omega) h66 e8_conjRange_66_67
  have h68 : conjRange .E8 40 68 = true :=
    conjRange_trans (by omega) (by omega) h67 e8_conjRange_67_68
  have h69 : conjRange .E8 40 69 = true :=
    conjRange_trans (by omega) (by omega) h68 e8_conjRange_68_69
  have h70 : conjRange .E8 40 70 = true :=
    conjRange_trans (by omega) (by omega) h69 e8_conjRange_69_70
  have h71 : conjRange .E8 40 71 = true :=
    conjRange_trans (by omega) (by omega) h70 e8_conjRange_70_71
  have h72 : conjRange .E8 40 72 = true :=
    conjRange_trans (by omega) (by omega) h71 e8_conjRange_71_72
  have h73 : conjRange .E8 40 73 = true :=
    conjRange_trans (by omega) (by omega) h72 e8_conjRange_72_73
  have h74 : conjRange .E8 40 74 = true :=
    conjRange_trans (by omega) (by omega) h73 e8_conjRange_73_74
  have h75 : conjRange .E8 40 75 = true :=
    conjRange_trans (by omega) (by omega) h74 e8_conjRange_74_75
  have h76 : conjRange .E8 40 76 = true :=
    conjRange_trans (by omega) (by omega) h75 e8_conjRange_75_76
  have h77 : conjRange .E8 40 77 = true :=
    conjRange_trans (by omega) (by omega) h76 e8_conjRange_76_77
  have h78 : conjRange .E8 40 78 = true :=
    conjRange_trans (by omega) (by omega) h77 e8_conjRange_77_78
  have h79 : conjRange .E8 40 79 = true :=
    conjRange_trans (by omega) (by omega) h78 e8_conjRange_78_79
  have h80 : conjRange .E8 40 80 = true :=
    conjRange_trans (by omega) (by omega) h79 e8_conjRange_79_80
  exact h80

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

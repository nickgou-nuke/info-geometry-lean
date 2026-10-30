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

theorem e8_conjRange_80_81 : conjRange .E8 80 81 = true := by decide +kernel
theorem e8_conjRange_81_82 : conjRange .E8 81 82 = true := by decide +kernel
theorem e8_conjRange_82_83 : conjRange .E8 82 83 = true := by decide +kernel
theorem e8_conjRange_83_84 : conjRange .E8 83 84 = true := by decide +kernel
theorem e8_conjRange_84_85 : conjRange .E8 84 85 = true := by decide +kernel
theorem e8_conjRange_85_86 : conjRange .E8 85 86 = true := by decide +kernel
theorem e8_conjRange_86_87 : conjRange .E8 86 87 = true := by decide +kernel
theorem e8_conjRange_87_88 : conjRange .E8 87 88 = true := by decide +kernel
theorem e8_conjRange_88_89 : conjRange .E8 88 89 = true := by decide +kernel
theorem e8_conjRange_89_90 : conjRange .E8 89 90 = true := by decide +kernel
theorem e8_conjRange_90_91 : conjRange .E8 90 91 = true := by decide +kernel
theorem e8_conjRange_91_92 : conjRange .E8 91 92 = true := by decide +kernel
theorem e8_conjRange_92_93 : conjRange .E8 92 93 = true := by decide +kernel
theorem e8_conjRange_93_94 : conjRange .E8 93 94 = true := by decide +kernel
theorem e8_conjRange_94_95 : conjRange .E8 94 95 = true := by decide +kernel
theorem e8_conjRange_95_96 : conjRange .E8 95 96 = true := by decide +kernel
theorem e8_conjRange_96_97 : conjRange .E8 96 97 = true := by decide +kernel
theorem e8_conjRange_97_98 : conjRange .E8 97 98 = true := by decide +kernel
theorem e8_conjRange_98_99 : conjRange .E8 98 99 = true := by decide +kernel
theorem e8_conjRange_99_100 : conjRange .E8 99 100 = true := by decide +kernel
theorem e8_conjRange_100_101 : conjRange .E8 100 101 = true := by decide +kernel
theorem e8_conjRange_101_102 : conjRange .E8 101 102 = true := by decide +kernel
theorem e8_conjRange_102_103 : conjRange .E8 102 103 = true := by decide +kernel
theorem e8_conjRange_103_104 : conjRange .E8 103 104 = true := by decide +kernel
theorem e8_conjRange_104_105 : conjRange .E8 104 105 = true := by decide +kernel
theorem e8_conjRange_105_106 : conjRange .E8 105 106 = true := by decide +kernel
theorem e8_conjRange_106_107 : conjRange .E8 106 107 = true := by decide +kernel
theorem e8_conjRange_107_108 : conjRange .E8 107 108 = true := by decide +kernel
theorem e8_conjRange_108_109 : conjRange .E8 108 109 = true := by decide +kernel
theorem e8_conjRange_109_110 : conjRange .E8 109 110 = true := by decide +kernel
theorem e8_conjRange_110_111 : conjRange .E8 110 111 = true := by decide +kernel
theorem e8_conjRange_111_112 : conjRange .E8 111 112 = true := by decide +kernel
theorem e8_conjRange_112_113 : conjRange .E8 112 113 = true := by decide +kernel
theorem e8_conjRange_113_114 : conjRange .E8 113 114 = true := by decide +kernel
theorem e8_conjRange_114_115 : conjRange .E8 114 115 = true := by decide +kernel
theorem e8_conjRange_115_116 : conjRange .E8 115 116 = true := by decide +kernel
theorem e8_conjRange_116_117 : conjRange .E8 116 117 = true := by decide +kernel
theorem e8_conjRange_117_118 : conjRange .E8 117 118 = true := by decide +kernel
theorem e8_conjRange_118_119 : conjRange .E8 118 119 = true := by decide +kernel
theorem e8_conjRange_119_120 : conjRange .E8 119 120 = true := by decide +kernel

/-- E₈ Weyl-conjugation range 80–120, assembled from one-root certificates. -/
theorem conjRange_E8_part2 : conjRange .E8 80 120 = true := by
  have h81 : conjRange .E8 80 81 = true := e8_conjRange_80_81
  have h82 : conjRange .E8 80 82 = true :=
    conjRange_trans (by omega) (by omega) h81 e8_conjRange_81_82
  have h83 : conjRange .E8 80 83 = true :=
    conjRange_trans (by omega) (by omega) h82 e8_conjRange_82_83
  have h84 : conjRange .E8 80 84 = true :=
    conjRange_trans (by omega) (by omega) h83 e8_conjRange_83_84
  have h85 : conjRange .E8 80 85 = true :=
    conjRange_trans (by omega) (by omega) h84 e8_conjRange_84_85
  have h86 : conjRange .E8 80 86 = true :=
    conjRange_trans (by omega) (by omega) h85 e8_conjRange_85_86
  have h87 : conjRange .E8 80 87 = true :=
    conjRange_trans (by omega) (by omega) h86 e8_conjRange_86_87
  have h88 : conjRange .E8 80 88 = true :=
    conjRange_trans (by omega) (by omega) h87 e8_conjRange_87_88
  have h89 : conjRange .E8 80 89 = true :=
    conjRange_trans (by omega) (by omega) h88 e8_conjRange_88_89
  have h90 : conjRange .E8 80 90 = true :=
    conjRange_trans (by omega) (by omega) h89 e8_conjRange_89_90
  have h91 : conjRange .E8 80 91 = true :=
    conjRange_trans (by omega) (by omega) h90 e8_conjRange_90_91
  have h92 : conjRange .E8 80 92 = true :=
    conjRange_trans (by omega) (by omega) h91 e8_conjRange_91_92
  have h93 : conjRange .E8 80 93 = true :=
    conjRange_trans (by omega) (by omega) h92 e8_conjRange_92_93
  have h94 : conjRange .E8 80 94 = true :=
    conjRange_trans (by omega) (by omega) h93 e8_conjRange_93_94
  have h95 : conjRange .E8 80 95 = true :=
    conjRange_trans (by omega) (by omega) h94 e8_conjRange_94_95
  have h96 : conjRange .E8 80 96 = true :=
    conjRange_trans (by omega) (by omega) h95 e8_conjRange_95_96
  have h97 : conjRange .E8 80 97 = true :=
    conjRange_trans (by omega) (by omega) h96 e8_conjRange_96_97
  have h98 : conjRange .E8 80 98 = true :=
    conjRange_trans (by omega) (by omega) h97 e8_conjRange_97_98
  have h99 : conjRange .E8 80 99 = true :=
    conjRange_trans (by omega) (by omega) h98 e8_conjRange_98_99
  have h100 : conjRange .E8 80 100 = true :=
    conjRange_trans (by omega) (by omega) h99 e8_conjRange_99_100
  have h101 : conjRange .E8 80 101 = true :=
    conjRange_trans (by omega) (by omega) h100 e8_conjRange_100_101
  have h102 : conjRange .E8 80 102 = true :=
    conjRange_trans (by omega) (by omega) h101 e8_conjRange_101_102
  have h103 : conjRange .E8 80 103 = true :=
    conjRange_trans (by omega) (by omega) h102 e8_conjRange_102_103
  have h104 : conjRange .E8 80 104 = true :=
    conjRange_trans (by omega) (by omega) h103 e8_conjRange_103_104
  have h105 : conjRange .E8 80 105 = true :=
    conjRange_trans (by omega) (by omega) h104 e8_conjRange_104_105
  have h106 : conjRange .E8 80 106 = true :=
    conjRange_trans (by omega) (by omega) h105 e8_conjRange_105_106
  have h107 : conjRange .E8 80 107 = true :=
    conjRange_trans (by omega) (by omega) h106 e8_conjRange_106_107
  have h108 : conjRange .E8 80 108 = true :=
    conjRange_trans (by omega) (by omega) h107 e8_conjRange_107_108
  have h109 : conjRange .E8 80 109 = true :=
    conjRange_trans (by omega) (by omega) h108 e8_conjRange_108_109
  have h110 : conjRange .E8 80 110 = true :=
    conjRange_trans (by omega) (by omega) h109 e8_conjRange_109_110
  have h111 : conjRange .E8 80 111 = true :=
    conjRange_trans (by omega) (by omega) h110 e8_conjRange_110_111
  have h112 : conjRange .E8 80 112 = true :=
    conjRange_trans (by omega) (by omega) h111 e8_conjRange_111_112
  have h113 : conjRange .E8 80 113 = true :=
    conjRange_trans (by omega) (by omega) h112 e8_conjRange_112_113
  have h114 : conjRange .E8 80 114 = true :=
    conjRange_trans (by omega) (by omega) h113 e8_conjRange_113_114
  have h115 : conjRange .E8 80 115 = true :=
    conjRange_trans (by omega) (by omega) h114 e8_conjRange_114_115
  have h116 : conjRange .E8 80 116 = true :=
    conjRange_trans (by omega) (by omega) h115 e8_conjRange_115_116
  have h117 : conjRange .E8 80 117 = true :=
    conjRange_trans (by omega) (by omega) h116 e8_conjRange_116_117
  have h118 : conjRange .E8 80 118 = true :=
    conjRange_trans (by omega) (by omega) h117 e8_conjRange_117_118
  have h119 : conjRange .E8 80 119 = true :=
    conjRange_trans (by omega) (by omega) h118 e8_conjRange_118_119
  have h120 : conjRange .E8 80 120 = true :=
    conjRange_trans (by omega) (by omega) h119 e8_conjRange_119_120
  exact h120

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

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

theorem e8_conjRange_120_121 : conjRange .E8 120 121 = true := by decide +kernel
theorem e8_conjRange_121_122 : conjRange .E8 121 122 = true := by decide +kernel
theorem e8_conjRange_122_123 : conjRange .E8 122 123 = true := by decide +kernel
theorem e8_conjRange_123_124 : conjRange .E8 123 124 = true := by decide +kernel
theorem e8_conjRange_124_125 : conjRange .E8 124 125 = true := by decide +kernel
theorem e8_conjRange_125_126 : conjRange .E8 125 126 = true := by decide +kernel
theorem e8_conjRange_126_127 : conjRange .E8 126 127 = true := by decide +kernel
theorem e8_conjRange_127_128 : conjRange .E8 127 128 = true := by decide +kernel
theorem e8_conjRange_128_129 : conjRange .E8 128 129 = true := by decide +kernel
theorem e8_conjRange_129_130 : conjRange .E8 129 130 = true := by decide +kernel
theorem e8_conjRange_130_131 : conjRange .E8 130 131 = true := by decide +kernel
theorem e8_conjRange_131_132 : conjRange .E8 131 132 = true := by decide +kernel
theorem e8_conjRange_132_133 : conjRange .E8 132 133 = true := by decide +kernel
theorem e8_conjRange_133_134 : conjRange .E8 133 134 = true := by decide +kernel
theorem e8_conjRange_134_135 : conjRange .E8 134 135 = true := by decide +kernel
theorem e8_conjRange_135_136 : conjRange .E8 135 136 = true := by decide +kernel
theorem e8_conjRange_136_137 : conjRange .E8 136 137 = true := by decide +kernel
theorem e8_conjRange_137_138 : conjRange .E8 137 138 = true := by decide +kernel
theorem e8_conjRange_138_139 : conjRange .E8 138 139 = true := by decide +kernel
theorem e8_conjRange_139_140 : conjRange .E8 139 140 = true := by decide +kernel
theorem e8_conjRange_140_141 : conjRange .E8 140 141 = true := by decide +kernel
theorem e8_conjRange_141_142 : conjRange .E8 141 142 = true := by decide +kernel
theorem e8_conjRange_142_143 : conjRange .E8 142 143 = true := by decide +kernel
theorem e8_conjRange_143_144 : conjRange .E8 143 144 = true := by decide +kernel
theorem e8_conjRange_144_145 : conjRange .E8 144 145 = true := by decide +kernel
theorem e8_conjRange_145_146 : conjRange .E8 145 146 = true := by decide +kernel
theorem e8_conjRange_146_147 : conjRange .E8 146 147 = true := by decide +kernel
theorem e8_conjRange_147_148 : conjRange .E8 147 148 = true := by decide +kernel
theorem e8_conjRange_148_149 : conjRange .E8 148 149 = true := by decide +kernel
theorem e8_conjRange_149_150 : conjRange .E8 149 150 = true := by decide +kernel
theorem e8_conjRange_150_151 : conjRange .E8 150 151 = true := by decide +kernel
theorem e8_conjRange_151_152 : conjRange .E8 151 152 = true := by decide +kernel
theorem e8_conjRange_152_153 : conjRange .E8 152 153 = true := by decide +kernel
theorem e8_conjRange_153_154 : conjRange .E8 153 154 = true := by decide +kernel
theorem e8_conjRange_154_155 : conjRange .E8 154 155 = true := by decide +kernel
theorem e8_conjRange_155_156 : conjRange .E8 155 156 = true := by decide +kernel
theorem e8_conjRange_156_157 : conjRange .E8 156 157 = true := by decide +kernel
theorem e8_conjRange_157_158 : conjRange .E8 157 158 = true := by decide +kernel
theorem e8_conjRange_158_159 : conjRange .E8 158 159 = true := by decide +kernel
theorem e8_conjRange_159_160 : conjRange .E8 159 160 = true := by decide +kernel

/-- E₈ Weyl-conjugation range 120–160, assembled from one-root certificates. -/
theorem conjRange_E8_part3 : conjRange .E8 120 160 = true := by
  have h121 : conjRange .E8 120 121 = true := e8_conjRange_120_121
  have h122 : conjRange .E8 120 122 = true :=
    conjRange_trans (by omega) (by omega) h121 e8_conjRange_121_122
  have h123 : conjRange .E8 120 123 = true :=
    conjRange_trans (by omega) (by omega) h122 e8_conjRange_122_123
  have h124 : conjRange .E8 120 124 = true :=
    conjRange_trans (by omega) (by omega) h123 e8_conjRange_123_124
  have h125 : conjRange .E8 120 125 = true :=
    conjRange_trans (by omega) (by omega) h124 e8_conjRange_124_125
  have h126 : conjRange .E8 120 126 = true :=
    conjRange_trans (by omega) (by omega) h125 e8_conjRange_125_126
  have h127 : conjRange .E8 120 127 = true :=
    conjRange_trans (by omega) (by omega) h126 e8_conjRange_126_127
  have h128 : conjRange .E8 120 128 = true :=
    conjRange_trans (by omega) (by omega) h127 e8_conjRange_127_128
  have h129 : conjRange .E8 120 129 = true :=
    conjRange_trans (by omega) (by omega) h128 e8_conjRange_128_129
  have h130 : conjRange .E8 120 130 = true :=
    conjRange_trans (by omega) (by omega) h129 e8_conjRange_129_130
  have h131 : conjRange .E8 120 131 = true :=
    conjRange_trans (by omega) (by omega) h130 e8_conjRange_130_131
  have h132 : conjRange .E8 120 132 = true :=
    conjRange_trans (by omega) (by omega) h131 e8_conjRange_131_132
  have h133 : conjRange .E8 120 133 = true :=
    conjRange_trans (by omega) (by omega) h132 e8_conjRange_132_133
  have h134 : conjRange .E8 120 134 = true :=
    conjRange_trans (by omega) (by omega) h133 e8_conjRange_133_134
  have h135 : conjRange .E8 120 135 = true :=
    conjRange_trans (by omega) (by omega) h134 e8_conjRange_134_135
  have h136 : conjRange .E8 120 136 = true :=
    conjRange_trans (by omega) (by omega) h135 e8_conjRange_135_136
  have h137 : conjRange .E8 120 137 = true :=
    conjRange_trans (by omega) (by omega) h136 e8_conjRange_136_137
  have h138 : conjRange .E8 120 138 = true :=
    conjRange_trans (by omega) (by omega) h137 e8_conjRange_137_138
  have h139 : conjRange .E8 120 139 = true :=
    conjRange_trans (by omega) (by omega) h138 e8_conjRange_138_139
  have h140 : conjRange .E8 120 140 = true :=
    conjRange_trans (by omega) (by omega) h139 e8_conjRange_139_140
  have h141 : conjRange .E8 120 141 = true :=
    conjRange_trans (by omega) (by omega) h140 e8_conjRange_140_141
  have h142 : conjRange .E8 120 142 = true :=
    conjRange_trans (by omega) (by omega) h141 e8_conjRange_141_142
  have h143 : conjRange .E8 120 143 = true :=
    conjRange_trans (by omega) (by omega) h142 e8_conjRange_142_143
  have h144 : conjRange .E8 120 144 = true :=
    conjRange_trans (by omega) (by omega) h143 e8_conjRange_143_144
  have h145 : conjRange .E8 120 145 = true :=
    conjRange_trans (by omega) (by omega) h144 e8_conjRange_144_145
  have h146 : conjRange .E8 120 146 = true :=
    conjRange_trans (by omega) (by omega) h145 e8_conjRange_145_146
  have h147 : conjRange .E8 120 147 = true :=
    conjRange_trans (by omega) (by omega) h146 e8_conjRange_146_147
  have h148 : conjRange .E8 120 148 = true :=
    conjRange_trans (by omega) (by omega) h147 e8_conjRange_147_148
  have h149 : conjRange .E8 120 149 = true :=
    conjRange_trans (by omega) (by omega) h148 e8_conjRange_148_149
  have h150 : conjRange .E8 120 150 = true :=
    conjRange_trans (by omega) (by omega) h149 e8_conjRange_149_150
  have h151 : conjRange .E8 120 151 = true :=
    conjRange_trans (by omega) (by omega) h150 e8_conjRange_150_151
  have h152 : conjRange .E8 120 152 = true :=
    conjRange_trans (by omega) (by omega) h151 e8_conjRange_151_152
  have h153 : conjRange .E8 120 153 = true :=
    conjRange_trans (by omega) (by omega) h152 e8_conjRange_152_153
  have h154 : conjRange .E8 120 154 = true :=
    conjRange_trans (by omega) (by omega) h153 e8_conjRange_153_154
  have h155 : conjRange .E8 120 155 = true :=
    conjRange_trans (by omega) (by omega) h154 e8_conjRange_154_155
  have h156 : conjRange .E8 120 156 = true :=
    conjRange_trans (by omega) (by omega) h155 e8_conjRange_155_156
  have h157 : conjRange .E8 120 157 = true :=
    conjRange_trans (by omega) (by omega) h156 e8_conjRange_156_157
  have h158 : conjRange .E8 120 158 = true :=
    conjRange_trans (by omega) (by omega) h157 e8_conjRange_157_158
  have h159 : conjRange .E8 120 159 = true :=
    conjRange_trans (by omega) (by omega) h158 e8_conjRange_158_159
  have h160 : conjRange .E8 120 160 = true :=
    conjRange_trans (by omega) (by omega) h159 e8_conjRange_159_160
  exact h160

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

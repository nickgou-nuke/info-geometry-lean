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

theorem e8_conjRange_160_161 : conjRange .E8 160 161 = true := by decide +kernel
theorem e8_conjRange_161_162 : conjRange .E8 161 162 = true := by decide +kernel
theorem e8_conjRange_162_163 : conjRange .E8 162 163 = true := by decide +kernel
theorem e8_conjRange_163_164 : conjRange .E8 163 164 = true := by decide +kernel
theorem e8_conjRange_164_165 : conjRange .E8 164 165 = true := by decide +kernel
theorem e8_conjRange_165_166 : conjRange .E8 165 166 = true := by decide +kernel
theorem e8_conjRange_166_167 : conjRange .E8 166 167 = true := by decide +kernel
theorem e8_conjRange_167_168 : conjRange .E8 167 168 = true := by decide +kernel
theorem e8_conjRange_168_169 : conjRange .E8 168 169 = true := by decide +kernel
theorem e8_conjRange_169_170 : conjRange .E8 169 170 = true := by decide +kernel
theorem e8_conjRange_170_171 : conjRange .E8 170 171 = true := by decide +kernel
theorem e8_conjRange_171_172 : conjRange .E8 171 172 = true := by decide +kernel
theorem e8_conjRange_172_173 : conjRange .E8 172 173 = true := by decide +kernel
theorem e8_conjRange_173_174 : conjRange .E8 173 174 = true := by decide +kernel
theorem e8_conjRange_174_175 : conjRange .E8 174 175 = true := by decide +kernel
theorem e8_conjRange_175_176 : conjRange .E8 175 176 = true := by decide +kernel
theorem e8_conjRange_176_177 : conjRange .E8 176 177 = true := by decide +kernel
theorem e8_conjRange_177_178 : conjRange .E8 177 178 = true := by decide +kernel
theorem e8_conjRange_178_179 : conjRange .E8 178 179 = true := by decide +kernel
theorem e8_conjRange_179_180 : conjRange .E8 179 180 = true := by decide +kernel
theorem e8_conjRange_180_181 : conjRange .E8 180 181 = true := by decide +kernel
theorem e8_conjRange_181_182 : conjRange .E8 181 182 = true := by decide +kernel
theorem e8_conjRange_182_183 : conjRange .E8 182 183 = true := by decide +kernel
theorem e8_conjRange_183_184 : conjRange .E8 183 184 = true := by decide +kernel
theorem e8_conjRange_184_185 : conjRange .E8 184 185 = true := by decide +kernel
theorem e8_conjRange_185_186 : conjRange .E8 185 186 = true := by decide +kernel
theorem e8_conjRange_186_187 : conjRange .E8 186 187 = true := by decide +kernel
theorem e8_conjRange_187_188 : conjRange .E8 187 188 = true := by decide +kernel
theorem e8_conjRange_188_189 : conjRange .E8 188 189 = true := by decide +kernel
theorem e8_conjRange_189_190 : conjRange .E8 189 190 = true := by decide +kernel
theorem e8_conjRange_190_191 : conjRange .E8 190 191 = true := by decide +kernel
theorem e8_conjRange_191_192 : conjRange .E8 191 192 = true := by decide +kernel
theorem e8_conjRange_192_193 : conjRange .E8 192 193 = true := by decide +kernel
theorem e8_conjRange_193_194 : conjRange .E8 193 194 = true := by decide +kernel
theorem e8_conjRange_194_195 : conjRange .E8 194 195 = true := by decide +kernel
theorem e8_conjRange_195_196 : conjRange .E8 195 196 = true := by decide +kernel
theorem e8_conjRange_196_197 : conjRange .E8 196 197 = true := by decide +kernel
theorem e8_conjRange_197_198 : conjRange .E8 197 198 = true := by decide +kernel
theorem e8_conjRange_198_199 : conjRange .E8 198 199 = true := by decide +kernel
theorem e8_conjRange_199_200 : conjRange .E8 199 200 = true := by decide +kernel

/-- E₈ Weyl-conjugation range 160–200, assembled from one-root certificates. -/
theorem conjRange_E8_part4 : conjRange .E8 160 200 = true := by
  have h161 : conjRange .E8 160 161 = true := e8_conjRange_160_161
  have h162 : conjRange .E8 160 162 = true :=
    conjRange_trans (by omega) (by omega) h161 e8_conjRange_161_162
  have h163 : conjRange .E8 160 163 = true :=
    conjRange_trans (by omega) (by omega) h162 e8_conjRange_162_163
  have h164 : conjRange .E8 160 164 = true :=
    conjRange_trans (by omega) (by omega) h163 e8_conjRange_163_164
  have h165 : conjRange .E8 160 165 = true :=
    conjRange_trans (by omega) (by omega) h164 e8_conjRange_164_165
  have h166 : conjRange .E8 160 166 = true :=
    conjRange_trans (by omega) (by omega) h165 e8_conjRange_165_166
  have h167 : conjRange .E8 160 167 = true :=
    conjRange_trans (by omega) (by omega) h166 e8_conjRange_166_167
  have h168 : conjRange .E8 160 168 = true :=
    conjRange_trans (by omega) (by omega) h167 e8_conjRange_167_168
  have h169 : conjRange .E8 160 169 = true :=
    conjRange_trans (by omega) (by omega) h168 e8_conjRange_168_169
  have h170 : conjRange .E8 160 170 = true :=
    conjRange_trans (by omega) (by omega) h169 e8_conjRange_169_170
  have h171 : conjRange .E8 160 171 = true :=
    conjRange_trans (by omega) (by omega) h170 e8_conjRange_170_171
  have h172 : conjRange .E8 160 172 = true :=
    conjRange_trans (by omega) (by omega) h171 e8_conjRange_171_172
  have h173 : conjRange .E8 160 173 = true :=
    conjRange_trans (by omega) (by omega) h172 e8_conjRange_172_173
  have h174 : conjRange .E8 160 174 = true :=
    conjRange_trans (by omega) (by omega) h173 e8_conjRange_173_174
  have h175 : conjRange .E8 160 175 = true :=
    conjRange_trans (by omega) (by omega) h174 e8_conjRange_174_175
  have h176 : conjRange .E8 160 176 = true :=
    conjRange_trans (by omega) (by omega) h175 e8_conjRange_175_176
  have h177 : conjRange .E8 160 177 = true :=
    conjRange_trans (by omega) (by omega) h176 e8_conjRange_176_177
  have h178 : conjRange .E8 160 178 = true :=
    conjRange_trans (by omega) (by omega) h177 e8_conjRange_177_178
  have h179 : conjRange .E8 160 179 = true :=
    conjRange_trans (by omega) (by omega) h178 e8_conjRange_178_179
  have h180 : conjRange .E8 160 180 = true :=
    conjRange_trans (by omega) (by omega) h179 e8_conjRange_179_180
  have h181 : conjRange .E8 160 181 = true :=
    conjRange_trans (by omega) (by omega) h180 e8_conjRange_180_181
  have h182 : conjRange .E8 160 182 = true :=
    conjRange_trans (by omega) (by omega) h181 e8_conjRange_181_182
  have h183 : conjRange .E8 160 183 = true :=
    conjRange_trans (by omega) (by omega) h182 e8_conjRange_182_183
  have h184 : conjRange .E8 160 184 = true :=
    conjRange_trans (by omega) (by omega) h183 e8_conjRange_183_184
  have h185 : conjRange .E8 160 185 = true :=
    conjRange_trans (by omega) (by omega) h184 e8_conjRange_184_185
  have h186 : conjRange .E8 160 186 = true :=
    conjRange_trans (by omega) (by omega) h185 e8_conjRange_185_186
  have h187 : conjRange .E8 160 187 = true :=
    conjRange_trans (by omega) (by omega) h186 e8_conjRange_186_187
  have h188 : conjRange .E8 160 188 = true :=
    conjRange_trans (by omega) (by omega) h187 e8_conjRange_187_188
  have h189 : conjRange .E8 160 189 = true :=
    conjRange_trans (by omega) (by omega) h188 e8_conjRange_188_189
  have h190 : conjRange .E8 160 190 = true :=
    conjRange_trans (by omega) (by omega) h189 e8_conjRange_189_190
  have h191 : conjRange .E8 160 191 = true :=
    conjRange_trans (by omega) (by omega) h190 e8_conjRange_190_191
  have h192 : conjRange .E8 160 192 = true :=
    conjRange_trans (by omega) (by omega) h191 e8_conjRange_191_192
  have h193 : conjRange .E8 160 193 = true :=
    conjRange_trans (by omega) (by omega) h192 e8_conjRange_192_193
  have h194 : conjRange .E8 160 194 = true :=
    conjRange_trans (by omega) (by omega) h193 e8_conjRange_193_194
  have h195 : conjRange .E8 160 195 = true :=
    conjRange_trans (by omega) (by omega) h194 e8_conjRange_194_195
  have h196 : conjRange .E8 160 196 = true :=
    conjRange_trans (by omega) (by omega) h195 e8_conjRange_195_196
  have h197 : conjRange .E8 160 197 = true :=
    conjRange_trans (by omega) (by omega) h196 e8_conjRange_196_197
  have h198 : conjRange .E8 160 198 = true :=
    conjRange_trans (by omega) (by omega) h197 e8_conjRange_197_198
  have h199 : conjRange .E8 160 199 = true :=
    conjRange_trans (by omega) (by omega) h198 e8_conjRange_198_199
  have h200 : conjRange .E8 160 200 = true :=
    conjRange_trans (by omega) (by omega) h199 e8_conjRange_199_200
  exact h200

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

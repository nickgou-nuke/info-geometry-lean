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

theorem e8_conjRange_200_201 : conjRange .E8 200 201 = true := by decide +kernel
theorem e8_conjRange_201_202 : conjRange .E8 201 202 = true := by decide +kernel
theorem e8_conjRange_202_203 : conjRange .E8 202 203 = true := by decide +kernel
theorem e8_conjRange_203_204 : conjRange .E8 203 204 = true := by decide +kernel
theorem e8_conjRange_204_205 : conjRange .E8 204 205 = true := by decide +kernel
theorem e8_conjRange_205_206 : conjRange .E8 205 206 = true := by decide +kernel
theorem e8_conjRange_206_207 : conjRange .E8 206 207 = true := by decide +kernel
theorem e8_conjRange_207_208 : conjRange .E8 207 208 = true := by decide +kernel
theorem e8_conjRange_208_209 : conjRange .E8 208 209 = true := by decide +kernel
theorem e8_conjRange_209_210 : conjRange .E8 209 210 = true := by decide +kernel
theorem e8_conjRange_210_211 : conjRange .E8 210 211 = true := by decide +kernel
theorem e8_conjRange_211_212 : conjRange .E8 211 212 = true := by decide +kernel
theorem e8_conjRange_212_213 : conjRange .E8 212 213 = true := by decide +kernel
theorem e8_conjRange_213_214 : conjRange .E8 213 214 = true := by decide +kernel
theorem e8_conjRange_214_215 : conjRange .E8 214 215 = true := by decide +kernel
theorem e8_conjRange_215_216 : conjRange .E8 215 216 = true := by decide +kernel
theorem e8_conjRange_216_217 : conjRange .E8 216 217 = true := by decide +kernel
theorem e8_conjRange_217_218 : conjRange .E8 217 218 = true := by decide +kernel
theorem e8_conjRange_218_219 : conjRange .E8 218 219 = true := by decide +kernel
theorem e8_conjRange_219_220 : conjRange .E8 219 220 = true := by decide +kernel
theorem e8_conjRange_220_221 : conjRange .E8 220 221 = true := by decide +kernel
theorem e8_conjRange_221_222 : conjRange .E8 221 222 = true := by decide +kernel
theorem e8_conjRange_222_223 : conjRange .E8 222 223 = true := by decide +kernel
theorem e8_conjRange_223_224 : conjRange .E8 223 224 = true := by decide +kernel
theorem e8_conjRange_224_225 : conjRange .E8 224 225 = true := by decide +kernel
theorem e8_conjRange_225_226 : conjRange .E8 225 226 = true := by decide +kernel
theorem e8_conjRange_226_227 : conjRange .E8 226 227 = true := by decide +kernel
theorem e8_conjRange_227_228 : conjRange .E8 227 228 = true := by decide +kernel
theorem e8_conjRange_228_229 : conjRange .E8 228 229 = true := by decide +kernel
theorem e8_conjRange_229_230 : conjRange .E8 229 230 = true := by decide +kernel
theorem e8_conjRange_230_231 : conjRange .E8 230 231 = true := by decide +kernel
theorem e8_conjRange_231_232 : conjRange .E8 231 232 = true := by decide +kernel
theorem e8_conjRange_232_233 : conjRange .E8 232 233 = true := by decide +kernel
theorem e8_conjRange_233_234 : conjRange .E8 233 234 = true := by decide +kernel
theorem e8_conjRange_234_235 : conjRange .E8 234 235 = true := by decide +kernel
theorem e8_conjRange_235_236 : conjRange .E8 235 236 = true := by decide +kernel
theorem e8_conjRange_236_237 : conjRange .E8 236 237 = true := by decide +kernel
theorem e8_conjRange_237_238 : conjRange .E8 237 238 = true := by decide +kernel
theorem e8_conjRange_238_239 : conjRange .E8 238 239 = true := by decide +kernel
theorem e8_conjRange_239_240 : conjRange .E8 239 240 = true := by decide +kernel

/-- E₈ Weyl-conjugation range 200–240, assembled from one-root certificates. -/
theorem conjRange_E8_part5 : conjRange .E8 200 240 = true := by
  have h201 : conjRange .E8 200 201 = true := e8_conjRange_200_201
  have h202 : conjRange .E8 200 202 = true :=
    conjRange_trans (by omega) (by omega) h201 e8_conjRange_201_202
  have h203 : conjRange .E8 200 203 = true :=
    conjRange_trans (by omega) (by omega) h202 e8_conjRange_202_203
  have h204 : conjRange .E8 200 204 = true :=
    conjRange_trans (by omega) (by omega) h203 e8_conjRange_203_204
  have h205 : conjRange .E8 200 205 = true :=
    conjRange_trans (by omega) (by omega) h204 e8_conjRange_204_205
  have h206 : conjRange .E8 200 206 = true :=
    conjRange_trans (by omega) (by omega) h205 e8_conjRange_205_206
  have h207 : conjRange .E8 200 207 = true :=
    conjRange_trans (by omega) (by omega) h206 e8_conjRange_206_207
  have h208 : conjRange .E8 200 208 = true :=
    conjRange_trans (by omega) (by omega) h207 e8_conjRange_207_208
  have h209 : conjRange .E8 200 209 = true :=
    conjRange_trans (by omega) (by omega) h208 e8_conjRange_208_209
  have h210 : conjRange .E8 200 210 = true :=
    conjRange_trans (by omega) (by omega) h209 e8_conjRange_209_210
  have h211 : conjRange .E8 200 211 = true :=
    conjRange_trans (by omega) (by omega) h210 e8_conjRange_210_211
  have h212 : conjRange .E8 200 212 = true :=
    conjRange_trans (by omega) (by omega) h211 e8_conjRange_211_212
  have h213 : conjRange .E8 200 213 = true :=
    conjRange_trans (by omega) (by omega) h212 e8_conjRange_212_213
  have h214 : conjRange .E8 200 214 = true :=
    conjRange_trans (by omega) (by omega) h213 e8_conjRange_213_214
  have h215 : conjRange .E8 200 215 = true :=
    conjRange_trans (by omega) (by omega) h214 e8_conjRange_214_215
  have h216 : conjRange .E8 200 216 = true :=
    conjRange_trans (by omega) (by omega) h215 e8_conjRange_215_216
  have h217 : conjRange .E8 200 217 = true :=
    conjRange_trans (by omega) (by omega) h216 e8_conjRange_216_217
  have h218 : conjRange .E8 200 218 = true :=
    conjRange_trans (by omega) (by omega) h217 e8_conjRange_217_218
  have h219 : conjRange .E8 200 219 = true :=
    conjRange_trans (by omega) (by omega) h218 e8_conjRange_218_219
  have h220 : conjRange .E8 200 220 = true :=
    conjRange_trans (by omega) (by omega) h219 e8_conjRange_219_220
  have h221 : conjRange .E8 200 221 = true :=
    conjRange_trans (by omega) (by omega) h220 e8_conjRange_220_221
  have h222 : conjRange .E8 200 222 = true :=
    conjRange_trans (by omega) (by omega) h221 e8_conjRange_221_222
  have h223 : conjRange .E8 200 223 = true :=
    conjRange_trans (by omega) (by omega) h222 e8_conjRange_222_223
  have h224 : conjRange .E8 200 224 = true :=
    conjRange_trans (by omega) (by omega) h223 e8_conjRange_223_224
  have h225 : conjRange .E8 200 225 = true :=
    conjRange_trans (by omega) (by omega) h224 e8_conjRange_224_225
  have h226 : conjRange .E8 200 226 = true :=
    conjRange_trans (by omega) (by omega) h225 e8_conjRange_225_226
  have h227 : conjRange .E8 200 227 = true :=
    conjRange_trans (by omega) (by omega) h226 e8_conjRange_226_227
  have h228 : conjRange .E8 200 228 = true :=
    conjRange_trans (by omega) (by omega) h227 e8_conjRange_227_228
  have h229 : conjRange .E8 200 229 = true :=
    conjRange_trans (by omega) (by omega) h228 e8_conjRange_228_229
  have h230 : conjRange .E8 200 230 = true :=
    conjRange_trans (by omega) (by omega) h229 e8_conjRange_229_230
  have h231 : conjRange .E8 200 231 = true :=
    conjRange_trans (by omega) (by omega) h230 e8_conjRange_230_231
  have h232 : conjRange .E8 200 232 = true :=
    conjRange_trans (by omega) (by omega) h231 e8_conjRange_231_232
  have h233 : conjRange .E8 200 233 = true :=
    conjRange_trans (by omega) (by omega) h232 e8_conjRange_232_233
  have h234 : conjRange .E8 200 234 = true :=
    conjRange_trans (by omega) (by omega) h233 e8_conjRange_233_234
  have h235 : conjRange .E8 200 235 = true :=
    conjRange_trans (by omega) (by omega) h234 e8_conjRange_234_235
  have h236 : conjRange .E8 200 236 = true :=
    conjRange_trans (by omega) (by omega) h235 e8_conjRange_235_236
  have h237 : conjRange .E8 200 237 = true :=
    conjRange_trans (by omega) (by omega) h236 e8_conjRange_236_237
  have h238 : conjRange .E8 200 238 = true :=
    conjRange_trans (by omega) (by omega) h237 e8_conjRange_237_238
  have h239 : conjRange .E8 200 239 = true :=
    conjRange_trans (by omega) (by omega) h238 e8_conjRange_238_239
  have h240 : conjRange .E8 200 240 = true :=
    conjRange_trans (by omega) (by omega) h239 e8_conjRange_239_240
  exact h240

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

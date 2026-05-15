# Lean Placeholder Trust Audit

Generated: `2026-05-14T19:46:00.998170+00:00`

- Modules scanned: **13**
- Modules with findings: **3**
- Total findings: **11** (hard=0, soft=11, advisory=0)

## `InfoGeometry.Singular.DrazinGreen`
- path: `lean/InfoGeometry/Singular/DrazinGreen.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L35: **SOFT** `skeletal-proof` in `theorem A_mul_Drazin_Green_eq_projector`
  - proof appears to be tactic-automation-only or skeletal
  - `33:     (A D : R) (k : ℕ) (h : IsDrazinInverse A D k) : R :=`
- L135: **SOFT** `skeletal-proof` in `theorem A_mul_drazinGreen_eq_drazinProjector`
  - proof appears to be tactic-automation-only or skeletal
  - `133: noncomputable def drazinResidueProjector (A : Module.End K V) : Module.End K V :=`

## `InfoGeometry.Singular.NaturalGradient`
- path: `lean/InfoGeometry/Singular/NaturalGradient.lean`
- findings: 2 (hard=0, soft=2, advisory=0)

- L32: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `30: `
- L33: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `31: variable {n : ℕ} (J1 : Matrix (Fin 2) (Fin 2) ℝ)`

## `InfoGeometry.Singular.SchurDrazinMoorePenrose`
- path: `lean/InfoGeometry/Singular/SchurDrazinMoorePenrose.lean`
- findings: 7 (hard=0, soft=7, advisory=0)

- L158: **SOFT** `skeletal-proof` in `theorem drazinRegularProjector_idempotent`
  - proof appears to be tactic-automation-only or skeletal
  - `156:     (hD : IsDrazinInverse A D k) : R :=`
- L194: **SOFT** `skeletal-proof` in `theorem drazinRegular_add_drazinNull`
  - proof appears to be tactic-automation-only or skeletal
  - `192:       drazinNullProjector A D k hD := by`
- L239: **SOFT** `skeletal-proof` in `theorem moorePenroseRangeProjector_idempotent`
  - proof appears to be tactic-automation-only or skeletal
  - `237:     (hMP : IsMoorePenroseInverse A B) : R :=`
- L248: **SOFT** `skeletal-proof` in `theorem moorePenroseRangeProjector_self_adjoint`
  - proof appears to be tactic-automation-only or skeletal
  - `246:       moorePenroseRangeProjector A B hMP := by`
- L83: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `81: `
- L330: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `328: `
- L616: **SOFT** `injected-hypothesis-surface` in `variable <file-level>`
  - section variable assumptions detected
  - `614: `


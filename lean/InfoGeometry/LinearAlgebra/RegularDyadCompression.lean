import Mathlib

/-! A normalized rank-one dyad and its compression identities. -/

noncomputable section

namespace InfoGeometry.LinearAlgebra.RegularDyadCompression

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

def normalizedCovector (v : E) (f : Module.Dual 𝕜 E) : Module.Dual 𝕜 E :=
  (f v)⁻¹ • f

@[simp] theorem normalizedCovector_apply (v x : E) (f : Module.Dual 𝕜 E) :
    normalizedCovector v f x = f x / f v := by
  simp only [normalizedCovector, LinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

@[simp] theorem normalizedCovector_self (v : E) (f : Module.Dual 𝕜 E)
    (h : f v ≠ 0) : normalizedCovector v f v = 1 := by
  rw [normalizedCovector_apply, div_self h]

def normalizedDyad (v : E) (f : Module.Dual 𝕜 E) : Module.End 𝕜 E :=
  (normalizedCovector v f).smulRight v

@[simp] theorem normalizedDyad_apply (v x : E) (f : Module.Dual 𝕜 E) :
    normalizedDyad v f x = (f x / f v) • v := by
  change normalizedCovector v f x • v = _
  rw [normalizedCovector_apply]

@[simp] theorem normalizedDyad_self (v : E) (f : Module.Dual 𝕜 E)
    (h : f v ≠ 0) : normalizedDyad v f v = v := by
  rw [normalizedDyad_apply, div_self h, one_smul]

theorem normalizedDyad_idempotent (v : E) (f : Module.Dual 𝕜 E)
    (h : f v ≠ 0) : normalizedDyad v f * normalizedDyad v f = normalizedDyad v f := by
  ext x
  change normalizedCovector v f (normalizedCovector v f x • v) • v = _
  rw [map_smul, normalizedCovector_self v f h]
  simp [smul_eq_mul]

theorem normalizedDyad_compression (v : E) (f : Module.Dual 𝕜 E)
    (A : Module.End 𝕜 E) :
    normalizedDyad v f * A * normalizedDyad v f =
      (f (A v) / f v) • normalizedDyad v f := by
  ext x
  change normalizedCovector v f (A (normalizedCovector v f x • v)) • v = _
  rw [A.map_smul, map_smul, smul_eq_mul,
    normalizedCovector_apply v (A v) f]
  simp only [normalizedDyad, LinearMap.smulRight_apply, LinearMap.smul_apply,
    smul_eq_mul, smul_smul]
  ring

theorem covector_normalizedDyad (v x : E) (f : Module.Dual 𝕜 E)
    (h : f v ≠ 0) : f (normalizedDyad v f x) = f x := by
  rw [normalizedDyad_apply, map_smul, smul_eq_mul, div_mul_cancel₀ _ h]

theorem normalizedDyad_ker (v : E) (f : Module.Dual 𝕜 E)
    (h : f v ≠ 0) : (normalizedDyad v f).ker = f.ker := by
  ext x
  change normalizedDyad v f x = 0 ↔ f x = 0
  constructor
  · intro hx
    rw [← covector_normalizedDyad v x f h, hx, map_zero]
  · intro hx
    simp [normalizedDyad_apply, hx]

end InfoGeometry.LinearAlgebra.RegularDyadCompression

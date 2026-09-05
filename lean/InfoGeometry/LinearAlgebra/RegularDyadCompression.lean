import Mathlib

/-!
# Regular rank-one compression using native linear maps

The construction is `LinearMap.smulRight` after normalizing a covector.
There is no new tensor product, operator multiplication, or boundary-pair
structure. The overlap condition is only the domain of the normalization.
No positivity or self-adjointness is inferred from idempotence.
-/

noncomputable section

namespace InfoGeometry.LinearAlgebra.RegularDyadCompression

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The covector normalized at the selected vector. -/
def normalizedCovector (v : E) (f : Module.Dual 𝕜 E) : Module.Dual 𝕜 E :=
  (f v)⁻¹ • f

@[simp] theorem normalizedCovector_apply (v x : E) (f : Module.Dual 𝕜 E) :
    normalizedCovector v f x = f x / f v := by
  simp only [normalizedCovector, LinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

@[simp] theorem normalizedCovector_self (v : E) (f : Module.Dual 𝕜 E)
    (h : f v ≠ 0) : normalizedCovector v f v = 1 := by
  rw [normalizedCovector_apply, div_self h]

/-- The normalized dyad `x ↦ f(x)/f(v) • v`. -/
def normalizedDyad (v : E) (f : Module.Dual 𝕜 E) : Module.End 𝕜 E :=
  (normalizedCovector v f).smulRight v

@[simp] theorem normalizedDyad_apply (v x : E) (f : Module.Dual 𝕜 E) :
    normalizedDyad v f x = (f x / f v) • v := by
  change normalizedCovector v f x • v = _
  rw [normalizedCovector_apply]

@[simp] theorem normalizedDyad_self (v : E) (f : Module.Dual 𝕜 E)
    (h : f v ≠ 0) : normalizedDyad v f v = v := by
  rw [normalizedDyad_apply, div_self h, one_smul]

/-- The dyad is an idempotent on the regular overlap domain. -/
theorem normalizedDyad_idempotent (v : E) (f : Module.Dual 𝕜 E)
    (h : f v ≠ 0) : normalizedDyad v f * normalizedDyad v f = normalizedDyad v f := by
  ext x
  change normalizedCovector v f (normalizedCovector v f x • v) • v =
    normalizedCovector v f x • v
  rw [map_smul, normalizedCovector_self v f h, smul_eq_mul, mul_one]

/-- Compression of an arbitrary endomorphism onto a regular rank-one dyad. -/
theorem normalizedDyad_compression (v : E) (f : Module.Dual 𝕜 E)
    (A : Module.End 𝕜 E) :
    normalizedDyad v f * A * normalizedDyad v f =
      (f (A v) / f v) • normalizedDyad v f := by
  ext x
  change normalizedCovector v f (A (normalizedCovector v f x • v)) • v =
    (f (A v) / f v) • (normalizedCovector v f x • v)
  rw [A.map_smul, map_smul, smul_eq_mul, smul_smul,
    normalizedCovector_apply v (A v) f]
  rw [mul_comm]

/-- Covector evaluation survives normalized compression. -/
theorem covector_normalizedDyad (v x : E) (f : Module.Dual 𝕜 E)
    (h : f v ≠ 0) : f (normalizedDyad v f x) = f x := by
  rw [normalizedDyad_apply, map_smul, smul_eq_mul, div_mul_cancel₀ _ h]

/-- The dyad's kernel is exactly the covector's kernel. -/
theorem normalizedDyad_ker (v : E) (f : Module.Dual 𝕜 E)
    (h : f v ≠ 0) : (normalizedDyad v f).ker = f.ker := by
  ext x
  change normalizedDyad v f x = 0 ↔ f x = 0
  constructor
  · intro hx
    rw [← covector_normalizedDyad v x f h, hx, map_zero]
  · intro hx
    simp only [normalizedDyad_apply, hx, zero_div, zero_smul]

/-- The regular dyad is the projection onto the line of `v`, along `ker f`. -/
theorem normalizedDyad_range (v : E) (f : Module.Dual 𝕜 E)
    (h : f v ≠ 0) : (normalizedDyad v f).range = Submodule.span 𝕜 {v} := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [normalizedDyad_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro x hx
    have hxv : x = v := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨v, normalizedDyad_self v f h⟩

/-- The scalar quotient is also recovered by one more evaluation of the compression. -/
theorem normalizedDyad_coefficient (v : E) (f : Module.Dual 𝕜 E)
    (h : f v ≠ 0) : f (normalizedDyad v f v) / f v = 1 := by
  rw [normalizedDyad_self v f h, div_self h]

end InfoGeometry.LinearAlgebra.RegularDyadCompression

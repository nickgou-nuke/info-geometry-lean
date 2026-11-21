/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Core.PeirceCompressionDefect

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

/-- The normalized matrix coefficient of an endomorphism, defined without
choosing coordinates on the module. -/
def normalizedReadout {𝕜 E : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (v : E) (f : Module.Dual 𝕜 E)
    (A : Module.End 𝕜 E) : 𝕜 :=
  f (A v) / f v

/-- Evaluating a two-boundary operator sandwich is exactly evaluation of its
successive actions on the selected vector and covector. -/
theorem normalizedReadout_twoBoundaryCompression
    {𝕜 E : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (v : E) (f : Module.Dual 𝕜 E)
    (post observable pre : Module.End 𝕜 E) :
    normalizedReadout v f
        (InfoGeometry.Core.PeirceCompressionDefect.twoBoundaryCompression
          post observable pre) =
      f (post (observable (pre v))) / f v := by
  simp [normalizedReadout,
    InfoGeometry.Core.PeirceCompressionDefect.twoBoundaryCompression,
    Module.End.mul_apply]

/-- The intermediate-idempotent resolution in the operator ring descends
through the coordinate-free normalized module readout. -/
theorem normalizedReadout_twoBoundaryCompression_intermediate
    {𝕜 E : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (v : E) (f : Module.Dual 𝕜 E)
    (post x y pre middle : Module.End 𝕜 E)
    (hmiddle : middle * middle = middle) :
    normalizedReadout v f
        (InfoGeometry.Core.PeirceCompressionDefect.twoBoundaryCompression
          post (x * y) pre) =
      normalizedReadout v f
          (InfoGeometry.Core.PeirceCompressionDefect.twoBoundaryCompression
            post x middle *
            InfoGeometry.Core.PeirceCompressionDefect.twoBoundaryCompression
              middle y pre) +
        normalizedReadout v f
          ((post * x * (1 - middle)) * ((1 - middle) * y * pre)) := by
  rw [InfoGeometry.Core.PeirceCompressionDefect.twoBoundaryCompression_intermediate_decomposition
    post x y pre middle hmiddle]
  simp [normalizedReadout, map_add, add_div]

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

/-- The scalar quotient is also recovered by one more evaluation of the compression. -/
theorem normalizedDyad_coefficient (v : E) (f : Module.Dual 𝕜 E)
    (h : f v ≠ 0) : f (normalizedDyad v f v) / f v = 1 := by
  rw [normalizedDyad_self v f h, div_self h]

end InfoGeometry.LinearAlgebra.RegularDyadCompression

namespace InfoGeometry.LinearAlgebra.RegularDyadCompression

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The ordered product retains the first vector and second covector. -/
theorem normalizedDyad_mul (v w : E) (f g : Module.Dual 𝕜 E) :
    normalizedDyad v f * normalizedDyad w g =
      (f w / (f v * g w)) • g.smulRight v := by
  ext x
  simp only [Module.End.mul_apply, normalizedDyad_apply, map_smul,
    LinearMap.smul_apply, LinearMap.smulRight_apply, smul_smul]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Independent nonzero representative rescalings preserve the actual
endomorphism on the nonincident locus. -/
theorem normalizedDyad_rescale (v : E) (f : Module.Dual 𝕜 E)
    (a b : 𝕜) (ha : a ≠ 0) (hb : b ≠ 0) (h : f v ≠ 0) :
    normalizedDyad (a • v) (b • f) = normalizedDyad v f := by
  ext x
  simp only [normalizedDyad_apply, LinearMap.smul_apply, map_smul,
    smul_eq_mul, smul_smul]
  congr 1
  field_simp [ha, hb, h]

/-- The image is the primal line, with no finite-dimensional assumption. -/
theorem normalizedDyad_range (v : E) (f : Module.Dual 𝕜 E)
    (h : f v ≠ 0) : (normalizedDyad v f).range = 𝕜 ∙ v := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [normalizedDyad_apply]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  · intro hx
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨a • v, ?_⟩
    rw [map_smul, normalizedDyad_self v f h, ha]

end InfoGeometry.LinearAlgebra.RegularDyadCompression

import InfoGeometry.Analysis.BipolarCurveIntegral

/-!
# Admissible loops for the bipolar logarithmic differential

This owner records the exact native boundary currently available for arbitrary
loops: a continuous `Path`, integrability for the Mathlib curve integral, and
pointwise avoidance of the two punctures.  It deliberately does not define a
winding number by reference to the integral.  The global winding-period
factorisation remains a separate topological development frontier.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarAdmissibleLoops

open Complex Set MeasureTheory
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential

/-- The native continuous-linear one-form used by the bipolar curve integral. -/
def dlog01Form (z : ℂ) : ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.mul ℂ ℂ (dlog01 z)

@[simp] theorem dlog01Form_apply (z v : ℂ) : dlog01Form z v = dlog01 z * v := by
  rfl

/-- A loop is analytically admissible when its Mathlib curve integral exists and
its image stays in the twice-punctured plane. -/
structure AdmissibleLoop where
  base : ℂ
  path : Path base base
  integrable : CurveIntegrable dlog01Form path
  avoids_punctures : range path ⊆ punctured01

instance : CoeFun AdmissibleLoop (fun _ => unitInterval → ℂ) :=
  ⟨fun γ => γ.path⟩

@[simp] theorem path_source (γ : AdmissibleLoop) : γ.path 0 = γ.base :=
  γ.path.source

@[simp] theorem path_target (γ : AdmissibleLoop) : γ.path 1 = γ.base :=
  γ.path.target

@[simp] theorem path_integrable (γ : AdmissibleLoop) :
    CurveIntegrable dlog01Form γ.path :=
  γ.integrable

theorem path_mem_punctured (γ : AdmissibleLoop) {t : unitInterval} :
    γ.path t ∈ punctured01 :=
  γ.avoids_punctures ⟨t, rfl⟩

theorem path_range_mem_punctured (γ : AdmissibleLoop) :
    range γ.path ⊆ punctured01 :=
  γ.avoids_punctures

/-- The curve integral carried by an admissible loop. -/
def integral (γ : AdmissibleLoop) : ℂ :=
  curveIntegral dlog01Form γ.path

@[simp] theorem integral_def (γ : AdmissibleLoop) :
    integral γ = curveIntegral dlog01Form γ.path :=
  rfl

/-- Concatenation of admissible loops at their common base point. -/
def concat (γ δ : AdmissibleLoop) (hbase : γ.base = δ.base) : AdmissibleLoop where
  base := γ.base
  path := γ.path.trans (δ.path.cast hbase hbase)
  integrable := γ.integrable.trans (CurveIntegrable.cast hbase hbase δ.integrable)
  avoids_punctures := by
    rw [Path.trans_range]
    intro z hz
    rcases hz with hz | hz
    · exact γ.avoids_punctures hz
    · exact δ.avoids_punctures hz

@[simp] theorem concat_integral (γ δ : AdmissibleLoop) (hbase : γ.base = δ.base) :
    integral (concat γ δ hbase) = integral γ + integral δ := by
  rw [integral, concat]
  simpa [dlog01Form] using
    (curveIntegral_trans γ.integrable
      (CurveIntegrable.cast hbase hbase δ.integrable :
        CurveIntegrable dlog01Form (δ.path.cast hbase hbase)))

/-- Reversal preserves admissibility and reverses the curve integral. -/
def reverse (γ : AdmissibleLoop) : AdmissibleLoop where
  base := γ.base
  path := γ.path.symm
  integrable := γ.integrable.symm
  avoids_punctures := by
    simpa [Path.symm_range] using γ.avoids_punctures

@[simp] theorem reverse_integral (γ : AdmissibleLoop) :
    integral (reverse γ) = -integral γ := by
  change curveIntegral dlog01Form γ.path.symm = -curveIntegral dlog01Form γ.path
  exact curveIntegral_symm dlog01Form γ.path

@[simp] theorem concat_reverse_integral (γ : AdmissibleLoop) :
    integral (concat γ (reverse γ) rfl) = 0 := by
  rw [concat_integral, reverse_integral, add_neg_cancel]

/-- Branch-free scalar holonomy of an admissible loop. -/
def holonomy (γ : AdmissibleLoop) : ℂ := Complex.exp (integral γ)

@[simp] theorem concat_holonomy (γ δ : AdmissibleLoop) (hbase : γ.base = δ.base) :
    holonomy (concat γ δ hbase) = holonomy γ * holonomy δ := by
  change Complex.exp (integral (concat γ δ hbase)) =
    Complex.exp (integral γ) * Complex.exp (integral δ)
  rw [concat_integral, Complex.exp_add]

@[simp] theorem reverse_holonomy (γ : AdmissibleLoop) :
    holonomy (reverse γ) = (holonomy γ)⁻¹ := by
  change Complex.exp (integral (reverse γ)) = (Complex.exp (integral γ))⁻¹
  rw [reverse_integral, Complex.exp_neg]

@[simp] theorem concat_reverse_holonomy (γ : AdmissibleLoop) :
    holonomy (concat γ (reverse γ) rfl) = 1 := by
  rw [concat_holonomy, reverse_holonomy, mul_inv_cancel₀]
  exact Complex.exp_ne_zero _

end InfoGeometry.Analysis.BipolarAdmissibleLoops

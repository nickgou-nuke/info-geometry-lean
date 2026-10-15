import Mathlib.LinearAlgebra.BilinearForm.Properties
import InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT

noncomputable section

namespace InfoGeometry.Canonical.FiniteParaKahler

open InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT

/-!
# Finite nondegenerate para-Kähler lemmas

The existing `ParaKahlerDatum` is the owner for the algebraic metric,
para-complex involution, symmetry, and anti-compatibility laws.  This file
adds direct consequences of a supplied nondegeneracy hypothesis.  It does not
introduce a witness structure, a proxy certificate, a manifold, or a
super-Grassmannian quotient.
-/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The nondegenerate metric identifies a finite-dimensional carrier with its
linear dual through Mathlib's canonical bilinear-form construction. -/
@[simp] theorem metric_toDual_apply
    [FiniteDimensional ℝ V]
    (D : ParaKahlerDatum ℝ V) (hD : D.metric.Nondegenerate)
    (u v : V) :
    D.metric.toDual hD u v = D.metric u v :=
  rfl

/-- The positive para-eigenspace is isotropic for the metric. -/
theorem plus_metric_isotropic
    (D : ParaKahlerDatum ℝ V) {u v : V}
    (hu : D.para.K u = u) (hv : D.para.K v = v) :
    D.metric u v = 0 := by
  have h := D.metric_anti_compat u v
  rw [hu, hv] at h
  linarith

/-- The negative para-eigenspace is isotropic for the metric. -/
theorem minus_metric_isotropic
    (D : ParaKahlerDatum ℝ V) {u v : V}
    (hu : D.para.K u = -u) (hv : D.para.K v = -v) :
    D.metric u v = 0 := by
  have h := D.metric_anti_compat u v
  rw [hu, hv] at h
  rw [D.metric.neg_left, D.metric.neg_right] at h
  linarith

end InfoGeometry.Canonical.FiniteParaKahler

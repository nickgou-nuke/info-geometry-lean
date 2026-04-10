import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.Hom
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.KreinDoubledAtom
import InfoGeometry.Canonical.TomitaTakesaki

/-!
# Quantum Geometric Tensor (Real Doubled Formulation)

This module formalizes the Quantum Geometric Tensor (QGT) as a split pair of
real bilinear forms on the doubled Krein space. This adheres to the Hestenes
geometric formulation where the complex imaginary unit $i$ is replaced by the
internal geometric complex structure $K = J \epsilon$.

The tensor consists of:
1. **Metric ($g$)**: The symmetric part (quantum Fisher / Fubini-Study metric).
2. **Berry Curvature ($\Omega$)**: The alternating part (symplectic form).

The two are unified by the Kähler compatibility condition: $\Omega(u, v) = g(Ku, v)$.
-/

namespace InfoGeometry.Quantum

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.TomitaTakesaki

/--
**Quantum Geometric Tensor (QGT)**:
A split-pair of real bilinear forms on the doubled Krein space.
-/
structure GeometricQuantumTensor (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  /-- The symmetric Riemannian (Fisher/Fubini-Study) component. -/
  metric : LinearMap.BilinForm ℝ (DoubledSpace E)
  /-- The alternating Berry curvature (symplectic) component. -/
  berry  : LinearMap.BilinForm ℝ (DoubledSpace E)
  /-- The metric is symmetric. -/
  metric_symm : metric.IsSymm
  /-- The Berry curvature is alternating. -/
  berry_alt   : berry.IsAlt
  /-- Kähler Compatibility: $\Omega(u, v) = g(K u, v)$. -/
  compat      : ∀ u v, berry u v = metric (modularComplexI u) v

/-- Abbreviation for the Quantum Geometric Tensor. -/
abbrev QGT (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  GeometricQuantumTensor E

namespace GeometricQuantumTensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Accessor for the symmetric metric component. -/
def g (Q : QGT E) : LinearMap.BilinForm ℝ (DoubledSpace E) := Q.metric

/-- Accessor for the antisymmetric Berry component. -/
def Ω (Q : QGT E) : LinearMap.BilinForm ℝ (DoubledSpace E) := Q.berry

/-- Owner-name form of the Kähler compatibility law. -/
@[simp] theorem compat_complex_i
    (Q : QGT E) (u v : DoubledSpace E) :
    Q.berry u v = Q.metric (complex_i (E := E) u) v := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i] using
    Q.compat u v

/--
**ofMajorana**:
Constructor from a symmetric metric satisfying the $K$-skew relation
$g(Ku, v) = -g(u, Kv)$. The Berry form is induced canonically.
-/
noncomputable def ofMajorana
    (metric : LinearMap.BilinForm ℝ (DoubledSpace E))
    (h_symm : metric.IsSymm)
    (h_skew : ∀ u v, metric (modularComplexI u) v = -metric u (modularComplexI v)) : QGT E where
  metric := metric
  berry := metric.compLeft modularComplexI.toLinearMap
  metric_symm := h_symm
  berry_alt := by
    intro u
    have h1 : metric (modularComplexI u) u = - metric u (modularComplexI u) :=
      h_skew u u
    have h2 : metric (modularComplexI u) u = metric u (modularComplexI u) :=
      h_symm.eq (modularComplexI u) u
    rw [h2] at h1
    have hz : metric (modularComplexI u) u = 0 := by
      linarith
    simpa using hz
  compat := by
    intro u v
    simp

/-- Owner-name form of the induced Berry/metric compatibility for `ofMajorana`. -/
@[simp] theorem ofMajorana_compat_complex_i
    (metric : LinearMap.BilinForm ℝ (DoubledSpace E))
    (h_symm : metric.IsSymm)
    (h_skew : ∀ u v, metric (modularComplexI u) v = -metric u (modularComplexI v))
    (u v : DoubledSpace E) :
    (GeometricQuantumTensor.ofMajorana metric h_symm h_skew).berry u v =
      (GeometricQuantumTensor.ofMajorana metric h_symm h_skew).metric (complex_i (E := E) u) v := by
  simpa using
    (GeometricQuantumTensor.ofMajorana metric h_symm h_skew).compat_complex_i u v

end GeometricQuantumTensor

end InfoGeometry.Quantum

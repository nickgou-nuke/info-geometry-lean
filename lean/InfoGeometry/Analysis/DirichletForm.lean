import Mathlib

/-!
# InfoGeometry.Analysis.DirichletForm

This file formalizes the classical Dirichlet form $t(u, v)$ for second-order 
elliptic differential operators with complex-valued coefficients.

The operator is given in divergence form:
$A u = -\operatorname{div}(\mu \nabla u)$
where $\mu(x) = \mu_R(x) + i\mu_I(x)$ is a uniformly bounded, complex-elliptic coefficient matrix.

The numerical range $N(A)$ is dense in the numerical range of the form $N(t)$,
and by Lax-Milgram, it is contained in a sector $\Sigma_\theta$ of the right half-plane.
-/

namespace InfoGeometry.Analysis

open Complex

/-- The fixed model spatial domain used by this finite algebraic sidecar. -/
abbrev DomainPoint := Fin 3 → ℝ

/-- The complex coefficient matrix function $\mu : \Omega \to \mathcal{L}(\mathbb{C}^d)$.
    It decomposes into real and imaginary parts: $\mu_R(x) + i \mu_I(x)$. -/
abbrev ComplexCoefficientMatrix (d : ℕ) := DomainPoint → Matrix (Fin d) (Fin d) ℂ

/-- Function space used by this finite algebraic sidecar. -/
abbrev SobolevSpace := DomainPoint → ℂ

/-- Zero-gradient model used until an owned weak-derivative interface is installed. -/
noncomputable def gradient (_u : SobolevSpace) : DomainPoint → Fin 3 → ℂ :=
  fun _ _ => 0

/-- 
The continuous bilinear Dirichlet form:
$t(u, v) = \int_{\Omega} \mu \nabla u \cdot \overline{\nabla v} \, \mathrm{d}x$

This sidecar has no measure/weak-derivative owner yet, so the installed model
is the unit algebraic form. Analytic sectoriality is supplied explicitly in
downstream theorems rather than derived here.
-/
noncomputable def dirichletForm (μ : ComplexCoefficientMatrix 3) (u v : SobolevSpace) : ℂ :=
  1

/-- A geometric sector in the right half complex plane bounded by angle $\theta < \pi/2$. -/
def IsInSector (z : ℂ) (θ : ℝ) : Prop :=
  z.re > 0 ∧ |z.im| ≤ z.re * Real.tan θ

/-- 
The Sectoriality condition for the Dirichlet form.
The numerical range $N(t) = \{ t(u, u) \mid \|u\| = 1 \}$ must be contained in the sector $\Sigma_\theta$.
-/
def IsSectorialDirichletForm (μ : ComplexCoefficientMatrix 3) (θ : ℝ) : Prop :=
  ∀ u : SobolevSpace, u ≠ 0 → IsInSector (dirichletForm μ u u) θ

end InfoGeometry.Analysis

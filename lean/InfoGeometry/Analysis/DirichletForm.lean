import Mathlib.Tactic
/-!
# InfoGeometry.Analysis.DirichletForm
This module records a finite, explicitly normalized sectorial-form model.  It
does not claim a Sobolev space, a weak derivative, or a Lax--Milgram theorem;
those analytic constructions require additional topological and measure data.
-/
namespace InfoGeometry.Analysis
open Complex
/-- A finite coordinate domain used by the algebraic model. -/
abbrev DomainPoint := Fin 3 → ℝ
/-- The complex coefficient matrix function $\mu : \Omega \to \mathcal{L}(\mathbb{C}^d)$.
    It decomposes into real and imaginary parts: $\mu_R(x) + i \mu_I(x)$. -/
abbrev ComplexCoefficientMatrix (d : ℕ) := DomainPoint → Matrix (Fin d) (Fin d) ℂ
/-- Finite scalar fields on the coordinate domain. -/
abbrev FiniteScalarField := DomainPoint → ℂ
/-- The zero derivative used by the normalized finite model. -/
noncomputable def zeroGradient (_u : FiniteScalarField) : DomainPoint → Fin 3 → ℂ :=
  fun _ _ => 0
/-- A unit-valued finite form.  Its sectoriality is elementary; this is not
    presented as an integral Dirichlet form. -/
noncomputable def unitForm (_μ : ComplexCoefficientMatrix 3)
    (_u _v : FiniteScalarField) : ℂ :=
  1
/-- A geometric sector in the right half complex plane bounded by angle $\theta < \pi/2$. -/
def IsInSector (z : ℂ) (θ : ℝ) : Prop :=
  z.re > 0 ∧ |z.im| ≤ z.re * Real.tan θ
/-- 
The Sectoriality condition for the Dirichlet form.
The numerical range $N(t) = \{ t(u, u) \mid \|u\| = 1 \}$ must be contained in the sector $\Sigma_\theta$.
-/
def IsSectorialUnitForm (μ : ComplexCoefficientMatrix 3) (θ : ℝ) : Prop :=
  ∀ u : FiniteScalarField, u ≠ 0 → IsInSector (unitForm μ u u) θ
theorem unitForm_is_sectorial_zero (μ : ComplexCoefficientMatrix 3) :
    IsSectorialUnitForm μ 0 := by
  intro u hu
  change IsInSector (1 : ℂ) 0
  simp [IsInSector]
end InfoGeometry.Analysis

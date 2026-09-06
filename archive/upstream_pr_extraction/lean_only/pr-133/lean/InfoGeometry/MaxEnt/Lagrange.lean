import InfoGeometry.MaxEnt.Finite
import Mathlib.Analysis.Calculus.LagrangeMultipliers

open scoped BigOperators

/-!
# MaxEnt Stationarity via Lagrange Multipliers

A Mathlib-native stationarity theorem for finite-dimensional Jaynes MaxEnt:
normalization + one moment constraint.
-/

namespace InfoGeometry.MaxEnt

/-- Finite parameter space `(pᵢ)` with `i : Fin n`. -/
abbrev FiniteParamSpace (n : ℕ) := Fin n → ℝ

/-- MaxEnt objective as a function of `p`. -/
noncomputable def entropyObjective (n : ℕ) (K : ℝ) : FiniteParamSpace n → ℝ :=
  fun p => entropy (n := n) p K

/-- Constraint family:
- `k = 0`: normalization `∑ pᵢ`
- `k = 1`: moment `∑ pᵢ fᵢ`. -/
noncomputable def constraintFamily (n : ℕ) (obs : Fin n → ℝ) :
    Fin 2 → FiniteParamSpace n → ℝ
  | k => Fin.cases
      (fun p => ∑ i, p i)
      (fun _ => fun p => ∑ i, p i * obs i) k

/-- Lagrange-multiplier stationarity at an interior local extremum
for finite Jaynes MaxEnt with two equality constraints. -/
theorem maxEnt_stationary
    (n : ℕ)
    (K : ℝ)
    (obs : Fin n → ℝ)
    (p0 : FiniteParamSpace n)
    (phiDeriv : StrongDual ℝ (FiniteParamSpace n))
    (constrDeriv : Fin 2 → StrongDual ℝ (FiniteParamSpace n))
    (hextr : IsLocalExtrOn
      (entropyObjective n K)
      {p | ∀ k : Fin 2, constraintFamily n obs k p = constraintFamily n obs k p0}
      p0)
    (hphi : HasStrictFDerivAt (entropyObjective n K) phiDeriv p0)
    (hconstr : ∀ k : Fin 2, HasStrictFDerivAt (constraintFamily n obs k) (constrDeriv k) p0) :
    ∃ (Λ : Fin 2 → ℝ) (Λ₀ : ℝ), (Λ, Λ₀) ≠ 0 ∧
      (∑ k : Fin 2, Λ k • constrDeriv k) + Λ₀ • phiDeriv = 0 := by
  simpa using hextr.exists_multipliers_of_hasStrictFDerivAt hconstr hphi

end InfoGeometry.MaxEnt

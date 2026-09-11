
import InfoGeometry.KL.Measure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.KL.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# InfoGeometry.KL

Canonical KL umbrella:
- `KL.Measure` gives the measure-theoretic facade `InfoGeometry.KL.kl_div`;
- `KL.Finite` gives the normalized finite/PMF slice;
- the primitive cone/projective state geometry lives in the measure/projective
  foundation and is not redefined here.
-/

namespace InfoGeometry.KL


open scoped BigOperators ENNReal


/-- Empirical/model density ratio `P(x) / Q(x)`. -/
noncomputable def densityRatio
    {α : Type} [Fintype α]
    (N : InfoGeometry.EmpiricalCounts α)
    (Q : InfoGeometry.ProbabilityDist α)
    (x : α) : ℝ :=
  empirical_distribution N x / (Q x).toReal

/-- Rényi moment functional built from the empirical/model density ratio. -/
noncomputable def Phi
    {α : Type} [Fintype α]
    (N_func : InfoGeometry.EmpiricalCounts α)
    (Q : InfoGeometry.ProbabilityDist α)
    (τ : ℝ) : ℝ :=
  ∑ x : α, empirical_distribution N_func x * Real.rpow (densityRatio N_func Q x) τ



/-- `Q` is support-faithful to the empirical distribution:
`Q(x) > 0` wherever `empirical_distribution N_func x ≠ 0`. -/
def PhiSupportFaithful
    {α : Type} [Fintype α]
    (N_func : InfoGeometry.EmpiricalCounts α)
    (Q : InfoGeometry.ProbabilityDist α) : Prop :=
  ∀ x, empirical_distribution N_func x ≠ 0 → 0 < Q x



/-- Helper expressing the shifted Rényi formula `log (Phi s) / s`.

The faithfulness hypothesis is carried explicitly for interface stability. -/
noncomputable def renyiBridge
    {α : Type} [Fintype α]
    (N_func : InfoGeometry.EmpiricalCounts α)
    (Q : InfoGeometry.ProbabilityDist α)
    (s : ℝ)
    (_hQ : PhiSupportFaithful N_func Q) : ℝ :=
  Real.log (Phi N_func Q s) / s


@[simp] lemma renyiBridge_mul
    {α : Type} [Fintype α]
    (N_func : InfoGeometry.EmpiricalCounts α)
    (Q : InfoGeometry.ProbabilityDist α)
    (s : ℝ)
    (hs : s ≠ 0)
    (hQ : PhiSupportFaithful N_func Q) :
    s * renyiBridge N_func Q s hQ = Real.log (Phi N_func Q s) := by
  unfold renyiBridge
  field_simp [hs]

end InfoGeometry.KL

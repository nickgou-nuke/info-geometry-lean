import InfoGeometry.Clifford.ClNN
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Cartan.Involution
import InfoGeometry.Meta.Architecture
import Mathlib.Tactic.NoncommRing

/-!
# InfoGeometry.Clifford.GeneralizedMetricBField

Algebraic generalized-metric and `B`-field surface over the split `Cl(n,n)`
carrier.

This file stays intentionally modest:
- a split generalized-metric seed is a neutral involution `η` together with a
  Cartan involution `S`,
- the derived operator `ηS` is the algebraic generalized metric,
- plus/minus projectors are taken from the Cartan involution,
- a `B`-field datum is recorded only as a skew endomorphism relative to the
  split quadratic polar form.

No projective/recomposition interpretation is imposed here.

Authority note:

- this file remains a split-tower compatibility surface over `ClNN`,
- it is not the corrected phase-space generalized-metric owner,
- the corrected owner-side generalized-metric package lives in
  `PhaseSpaceGeneralizedMetric`.
-/

namespace InfoGeometry.Clifford.GeneralizedMetricBField

open InfoGeometry.Clifford.ClNN
open InfoGeometry.Cartan

noncomputable section

local instance generalizedMetricBFieldInvertibleTwoReal : Invertible (2 : ℝ) :=
  invertibleOfNonzero (by norm_num)

/-- Algebraic generalized-metric seed over the split `Cl(n,n)` carrier. -/
structure SplitGeneralizedMetricSeed (n : ℕ) where
  eta : Module.End ℝ (Carrier (n + 1))
  polarization : Module.End ℝ (Carrier (n + 1))
  eta_sq : eta * eta = 1
  polarization_sq : polarization * polarization = 1
  eta_polarization_anticommute : eta * polarization = -(polarization * eta)

namespace SplitGeneralizedMetricSeed

/-- The derived generalized-metric operator `η ∘ S`. -/
@[rep_depth krein]
noncomputable def metricOperator (G : SplitGeneralizedMetricSeed n) :
    Module.End ℝ (Carrier (n + 1)) :=
  G.eta * G.polarization

/-- The `+1` projector induced by the split generalized-metric polarization. -/
@[rep_depth krein]
noncomputable def plusProjector (G : SplitGeneralizedMetricSeed n) :
    Module.End ℝ (Carrier (n + 1)) :=
  Pplus G.polarization

/-- The `-1` projector induced by the split generalized-metric polarization. -/
@[rep_depth krein]
noncomputable def minusProjector (G : SplitGeneralizedMetricSeed n) :
    Module.End ℝ (Carrier (n + 1)) :=
  Pminus G.polarization

@[rep_depth krein] theorem polarization_is_cartan
    (G : SplitGeneralizedMetricSeed n) :
    IsCartanInvolution G.polarization :=
  G.polarization_sq

@[rep_depth krein] theorem plusProjector_idempotent
    (G : SplitGeneralizedMetricSeed n) :
    G.plusProjector * G.plusProjector = G.plusProjector := by
  exact Pplus_idempotent G.polarization G.polarization_is_cartan

@[rep_depth krein] theorem minusProjector_idempotent
    (G : SplitGeneralizedMetricSeed n) :
    G.minusProjector * G.minusProjector = G.minusProjector := by
  exact Pminus_idempotent G.polarization G.polarization_is_cartan

@[rep_depth krein] theorem plusProjector_add_minusProjector
    (G : SplitGeneralizedMetricSeed n) :
    G.plusProjector + G.minusProjector = 1 := by
  exact Pplus_add_Pminus_eq_id G.polarization

@[rep_depth krein] theorem plusProjector_mul_minusProjector
    (G : SplitGeneralizedMetricSeed n) :
    G.plusProjector * G.minusProjector = 0 := by
  exact Pplus_comp_Pminus G.polarization G.polarization_is_cartan

@[rep_depth krein] theorem minusProjector_mul_plusProjector
    (G : SplitGeneralizedMetricSeed n) :
    G.minusProjector * G.plusProjector = 0 := by
  dsimp [minusProjector, plusProjector, Pminus, Pplus]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h_expand :
      (1 - G.polarization) * (1 + G.polarization) = 1 - G.polarization * G.polarization := by
    rw [sub_mul, one_mul, mul_add, mul_one]
    abel_nf
  rw [h_expand, G.polarization_sq, sub_self, smul_zero]

@[rep_depth krein] theorem polarization_mul_plusProjector
    (G : SplitGeneralizedMetricSeed n) :
    G.polarization * G.plusProjector = G.plusProjector := by
  dsimp [plusProjector, Pplus]
  calc
    G.polarization * ((⅟ (2 : ℝ)) • (1 + G.polarization))
        = (⅟ (2 : ℝ)) • (G.polarization * (1 + G.polarization)) := by
            rw [mul_smul_comm]
    _ = (⅟ (2 : ℝ)) • (G.polarization + G.polarization * G.polarization) := by
          rw [mul_add, mul_one]
    _ = (⅟ (2 : ℝ)) • (1 + G.polarization) := by
          rw [G.polarization_sq]
          simp [add_comm]
    _ = G.plusProjector := by
          rfl

@[rep_depth krein] theorem metric_sq_eq_neg_one
    (G : SplitGeneralizedMetricSeed n) :
    G.metricOperator * G.metricOperator = -1 := by
  apply LinearMap.ext
  intro u
  have hanti :=
    congrArg
      (fun T : Module.End ℝ (Carrier (n + 1)) => T (G.eta (G.polarization u)))
      G.eta_polarization_anticommute
  have heta :=
    congrArg
      (fun T : Module.End ℝ (Carrier (n + 1)) => T (G.polarization u))
      G.eta_sq
  have hpol :=
    congrArg
      (fun T : Module.End ℝ (Carrier (n + 1)) => T u)
      G.polarization_sq
  simp [metricOperator] at hanti heta hpol ⊢
  rw [hanti, heta, hpol]

end SplitGeneralizedMetricSeed

/-- Algebraic `B`-field datum over the split carrier: a skew endomorphism with
respect to the polar form of `Qsplit`. -/
structure SplitBFieldDatum (n : ℕ) where
  twist : Module.End ℝ (Carrier (n + 1))
  skew_polar :
    ∀ u v : Carrier (n + 1),
      QuadraticMap.polar (Quad (n + 1)) (twist u) v
        = -QuadraticMap.polar (Quad (n + 1)) u (twist v)

namespace SplitBFieldDatum

@[rep_depth krein]
noncomputable def zero (n : ℕ) : SplitBFieldDatum n where
  twist := 0
  skew_polar := by
    intro u v
    simp

@[rep_depth krein, simp] theorem zero_twist
    (n : ℕ) :
    (SplitBFieldDatum.zero n).twist = 0 := rfl

end SplitBFieldDatum

end

end InfoGeometry.Clifford.GeneralizedMetricBField

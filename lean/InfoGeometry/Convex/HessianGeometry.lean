import InfoGeometry.Potential.LogPotential
import InfoGeometry.GrandCanonical.Core
import InfoGeometry.Krein.Metric
import Mathlib.Analysis.Convex.Deriv

/-!
# Hessian Geometry Bridges

A minimal bridge layer connecting log-potential Hessian geometry,
grand-canonical thermodynamics, and the scalar neutral Krein form.

`metric` is defined using Lean's totalized `deriv`; when smoothness is not
assumed, this should be read as the totalized second-derivative term.
-/

namespace InfoGeometry.Convex

/-- Minimal 1D Hessian geometry package. -/
structure HessianGeometry1D where
  potential : ℝ → ℝ

namespace HessianGeometry1D

/-- Hessian metric in 1D is the second derivative of the potential. -/
noncomputable def metric (H : HessianGeometry1D) (x : ℝ) : ℝ :=
  deriv (fun t => deriv H.potential t) x

/-- Convexity + differentiability imply nonnegativity of the 1D Hessian metric. -/
lemma metric_nonneg_of_convex
    (H : HessianGeometry1D)
    (hconv : ConvexOn ℝ Set.univ H.potential)
    (hdiff : Differentiable ℝ H.potential)
    (x : ℝ) :
    0 ≤ H.metric x := by
  have hmonoOn : MonotoneOn (deriv H.potential) Set.univ :=
    hconv.monotoneOn_deriv (fun z _hz => hdiff z)
  have hmono : Monotone (deriv H.potential) := by
    intro a b hab
    exact hmonoOn (by simp) (by simp) hab
  unfold metric
  simpa using (Monotone.deriv_nonneg (g := deriv H.potential) (x := x) hmono)

/-- Any 1D `LogPotential` induces a 1D Hessian geometry. -/
noncomputable def ofLogPotential (L : InfoGeometry.LogPotential ℝ) : HessianGeometry1D where
  potential := L.ψ

@[simp]
lemma metric_ofLogPotential
    (L : InfoGeometry.LogPotential ℝ) (x : ℝ) :
    (ofLogPotential L).metric x = deriv (fun t => deriv L.ψ t) x := rfl

end HessianGeometry1D

section GrandCanonicalBridge

open InfoGeometry.GrandCanonical

variable {α : Type _} [Fintype α] [Nonempty α]

/-- The grand-canonical potential viewed as a 1D Hessian geometry. -/
noncomputable def grandCanonicalHessianGeometry
    (params : GrandCanonicalParams α) : HessianGeometry1D where
  potential := potential params

/-- Hessian metric of the grand-canonical potential equals Gibbs variance. -/
lemma grandCanonical_metric_eq_variance
    (params : GrandCanonicalParams α) (β : ℝ) :
    (grandCanonicalHessianGeometry params).metric β = variance params β :=
  potential_second_derivative_eq_variance params β

lemma grandCanonical_metric_nonneg
    (params : GrandCanonicalParams α) (β : ℝ) :
    0 ≤ (grandCanonicalHessianGeometry params).metric β := by
  rw [grandCanonical_metric_eq_variance]
  exact variance_nonneg params β

end GrandCanonicalBridge

section KreinScalarBridge

/-- Scalar neutral-Krein potential on the doubled line. -/
noncomputable def kreinNeutralPotential (v : DoubledSpace ℝ) : ℝ :=
  v.1 * v.2

/-- Bilinear form induced by the scalar neutral potential polarization. -/
def kreinNeutralForm (u v : DoubledSpace ℝ) : ℝ :=
  u.1 * v.2 + v.1 * u.2

@[simp] lemma kreinNeutralForm_primal_primal (a b : ℝ) :
    kreinNeutralForm (a, 0) (b, 0) = 0 := by
  simp [kreinNeutralForm]

@[simp] lemma kreinNeutralForm_dual_dual (a b : ℝ) :
    kreinNeutralForm (0, a) (0, b) = 0 := by
  simp [kreinNeutralForm]

@[simp] lemma kreinNeutralForm_primal_dual (a b : ℝ) :
    kreinNeutralForm (a, 0) (0, b) = a * b := by
  simp [kreinNeutralForm]

@[simp] lemma kreinNeutralForm_dual_primal (a b : ℝ) :
    kreinNeutralForm (0, a) (b, 0) = a * b := by
  simp [kreinNeutralForm, mul_comm]

/-- Polarization identity for the scalar neutral potential. -/
lemma kreinNeutralForm_from_potential
    (u v : DoubledSpace ℝ) :
    kreinNeutralPotential (u + v)
      - kreinNeutralPotential u
      - kreinNeutralPotential v
      = kreinNeutralForm u v := by
  rcases u with ⟨u1, u2⟩
  rcases v with ⟨v1, v2⟩
  simp [kreinNeutralPotential, kreinNeutralForm]
  ring

/-- Scalar bridge to the existing neutral Hessian form. -/
lemma kreinNeutralForm_eq_hessianIndefiniteForm
    (u v : DoubledSpace ℝ) :
    kreinNeutralForm u v = hessianIndefiniteForm (E := ℝ) u v := by
  unfold kreinNeutralForm hessianIndefiniteForm
  simp [mul_comm]

/-- The scalar neutral form is indefinite. -/
lemma kreinNeutralForm_indefinite :
    ∃ u v : DoubledSpace ℝ,
      0 < kreinNeutralForm u u ∧ kreinNeutralForm v v < 0 := by
  refine ⟨(1, 1), (1, -1), ?_, ?_⟩
  · norm_num [kreinNeutralForm]
  · norm_num [kreinNeutralForm]

/-- The existing scalar `hessianIndefiniteForm` is indefinite. -/
lemma hessianIndefiniteForm_scalar_indefinite :
    ∃ u v : DoubledSpace ℝ,
      0 < hessianIndefiniteForm (E := ℝ) u u ∧
        hessianIndefiniteForm (E := ℝ) v v < 0 := by
  rcases kreinNeutralForm_indefinite with ⟨u, v, hu, hv⟩
  refine ⟨u, v, ?_, ?_⟩
  · simpa [kreinNeutralForm_eq_hessianIndefiniteForm] using hu
  · simpa [kreinNeutralForm_eq_hessianIndefiniteForm] using hv

end KreinScalarBridge

end InfoGeometry.Convex

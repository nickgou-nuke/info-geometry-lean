import InfoGeometry.Potential.LogPotential
import InfoGeometry.GrandCanonical.Core
import InfoGeometry.Krein.Metric

/-!
# Hessian Geometry Bridges

A minimal bridge layer connecting log-potential Hessian geometry,
grand-canonical thermodynamics, and the scalar neutral Krein form.
-/

namespace InfoGeometry.Convex

/-- Minimal 1D Hessian geometry package. -/
structure HessianGeometry1D where
  potential : ℝ → ℝ

namespace HessianGeometry1D

/-- Hessian metric in 1D is the second derivative of the potential. -/
noncomputable def metric (H : HessianGeometry1D) (x : ℝ) : ℝ :=
  deriv (fun t => deriv H.potential t) x

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

/-- Hessian metric of `log Z` equals Gibbs variance. -/
lemma grandCanonical_metric_eq_variance
    (params : GrandCanonicalParams α) (β : ℝ) :
    (grandCanonicalHessianGeometry params).metric β = variance params β :=
  potential_second_derivative_eq_variance params β

end GrandCanonicalBridge

section KreinScalarBridge

/-- Scalar neutral-Krein potential on the doubled line. -/
noncomputable def kreinNeutralPotential (v : DoubledSpace ℝ) : ℝ :=
  v.1 * v.2

/-- Bilinear form induced by the scalar neutral potential polarization. -/
def kreinNeutralForm (u v : DoubledSpace ℝ) : ℝ :=
  u.1 * v.2 + v.1 * u.2

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

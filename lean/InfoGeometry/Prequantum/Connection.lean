import InfoGeometry.Prequantum.Bundle
import InfoGeometry.Krein.Metric

section KreinClifford

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace ProjectivePrequantumBundle

/-- Scalar connection observable carried by a projective prequantum bundle point. -/
def connectionObservable (P : ProjectivePrequantumBundle (E := E)) : ℝ :=
  P.data.holonomyScale

/-- Scalar covariant-derivative proxy `F * ℏ`, invariant under Weyl rescaling. -/
def covariantDerivative (P : ProjectivePrequantumBundle (E := E)) : ℝ :=
  P.data.curvatureScale * P.data.hbar

lemma covariantDerivative_eq_omegaScale
    (P : ProjectivePrequantumBundle (E := E)) :
    covariantDerivative (E := E) P = P.data.omegaScale := by
  exact P.data.curvature_mul_hbar_eq_omega

lemma connectionObservable_gauge
    (u : Gauge) (P : ProjectivePrequantumBundle (E := E)) :
    connectionObservable (E := E) (u • P)
      = connectionObservable (E := E) P / (u : ℝ) := by
  rfl

lemma covariantDerivative_gauge_invariant
    (u : Gauge) (P : ProjectivePrequantumBundle (E := E)) :
    covariantDerivative (E := E) (u • P) = covariantDerivative (E := E) P := by
  rw [covariantDerivative_eq_omegaScale (E := E) (P := u • P)]
  rw [covariantDerivative_eq_omegaScale (E := E) (P := P)]
  rfl

end ProjectivePrequantumBundle

/-- Weyl-compatibility predicate: the neutral Hessian form scales conformally by `a²`. -/
def IsWeylCompatibleHessian
    (P : ProjectivePrequantumBundle (E := E)) : Prop :=
  let _ := P
  ∀ (u : Gauge) (v w : DoubledSpace E),
    hessianIndefiniteForm (E := E) (u • v) (u • w)
      = ((u : ℝ) ^ (2 : ℕ)) * hessianIndefiniteForm (E := E) v w

lemma hessianIndefiniteForm_smul_smul_weyl
    (u : Gauge) (v w : DoubledSpace E) :
    hessianIndefiniteForm (E := E) (u • v) (u • w)
      = ((u : ℝ) ^ (2 : ℕ)) * hessianIndefiniteForm (E := E) v w := by
  rcases v with ⟨v1, v2⟩
  rcases w with ⟨w1, w2⟩
  have h1 :
      inner ℝ ((u : ℝ) • v1) ((u : ℝ) • w2)
        = ((u : ℝ) ^ (2 : ℕ)) * inner ℝ v1 w2 := by
    calc
      inner ℝ ((u : ℝ) • v1) ((u : ℝ) • w2)
          = (u : ℝ) * inner ℝ v1 ((u : ℝ) • w2) := by
              simp [inner_smul_left]
      _ = (u : ℝ) * ((u : ℝ) * inner ℝ v1 w2) := by
            simp [inner_smul_right]
      _ = ((u : ℝ) ^ (2 : ℕ)) * inner ℝ v1 w2 := by
            ring
  have h2 :
      inner ℝ ((u : ℝ) • w1) ((u : ℝ) • v2)
        = ((u : ℝ) ^ (2 : ℕ)) * inner ℝ w1 v2 := by
    calc
      inner ℝ ((u : ℝ) • w1) ((u : ℝ) • v2)
          = (u : ℝ) * inner ℝ w1 ((u : ℝ) • v2) := by
              simp [inner_smul_left]
      _ = (u : ℝ) * ((u : ℝ) * inner ℝ w1 v2) := by
            simp [inner_smul_right]
      _ = ((u : ℝ) ^ (2 : ℕ)) * inner ℝ w1 v2 := by
            ring
  change
    inner ℝ ((u : ℝ) • v1) ((u : ℝ) • w2)
      + inner ℝ ((u : ℝ) • w1) ((u : ℝ) • v2)
      =
    ((u : ℝ) ^ (2 : ℕ)) * (inner ℝ v1 w2 + inner ℝ w1 v2)
  rw [h1, h2]
  ring

lemma isWeylCompatibleHessian
    (P : ProjectivePrequantumBundle (E := E)) :
    IsWeylCompatibleHessian (E := E) P := by
  intro u v w
  exact hessianIndefiniteForm_smul_smul_weyl (E := E) u v w

/-- Joint compatibility package: gauge-invariant covariant derivative plus Weyl metric scaling. -/
structure GaugeHessianCompatible
    (P : ProjectivePrequantumBundle (E := E)) : Prop where
  covariant_gauge_invariant :
    ∀ u : Gauge,
      ProjectivePrequantumBundle.covariantDerivative (E := E) (u • P)
        = ProjectivePrequantumBundle.covariantDerivative (E := E) P
  hessian_weyl_compatible :
    IsWeylCompatibleHessian (E := E) P

theorem gaugeHessianCompatible
    (P : ProjectivePrequantumBundle (E := E)) :
    GaugeHessianCompatible (E := E) P := by
  refine ⟨?_, ?_⟩
  · intro u
    exact ProjectivePrequantumBundle.covariantDerivative_gauge_invariant (E := E) u P
  · exact isWeylCompatibleHessian (E := E) P

end KreinClifford

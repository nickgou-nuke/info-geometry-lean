import InfoGeometry.Prequantum.Bundle
import InfoGeometry.Krein.DoubledSpace
import Mathlib.Tactic.Ring

/-!
# InfoGeometry.Prequantum.Connection

Scalarized connection and Weyl-compatibility interfaces for projective prequantum bundles.
-/

namespace InfoGeometry.Prequantum.Connection
end InfoGeometry.Prequantum.Connection

namespace InfoGeometry.Prequantum

open InfoGeometry.Krein

section KreinClifford

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open ProjectivePrequantumBundle

local notation "Hess" => InfoGeometry.Krein.hessian_indefinite_form

private lemma Hess_smul_left (a : ℝ) (v w : InfoGeometry.Krein.DoubledSpace E) :
    Hess (a • v) w = a * Hess v w := by
  simpa [InfoGeometry.Krein.hessian_indefinite_form] using
    (KreinSpace.kreinInner_smul_left (c := a) v w)

private lemma Hess_smul_right (a : ℝ) (v w : InfoGeometry.Krein.DoubledSpace E) :
    Hess v (a • w) = a * Hess v w := by
  simpa [InfoGeometry.Krein.hessian_indefinite_form] using
    (KreinSpace.kreinInner_smul_right (c := a) v w)

private lemma Hess_smul_smul (a : ℝ) (v w : InfoGeometry.Krein.DoubledSpace E) :
    Hess (a • v) (a • w) = a ^ 2 * Hess v w := by
  rw [Hess_smul_left, Hess_smul_right]
  ring

namespace ProjectivePrequantumBundle

/-- Scalar connection observable carried by a projective prequantum bundle point. -/
def connectionObservable (P : ProjectivePrequantumBundle (E := E)) : ℝ :=
  P.data.holonomyScale

/-- Scalar covariant-derivative proxy `F * ℏ`, invariant under Weyl rescaling. -/
def covariantDerivative (P : ProjectivePrequantumBundle (E := E)) : ℝ :=
  P.data.curvatureScale * P.data.hbar

lemma covariantDerivative_eq_omegaScale
    (P : ProjectivePrequantumBundle (E := E)) :
    covariantDerivative P = P.data.omegaScale := by
  exact P.data.curvature_mul_hbar_eq_omega

lemma connectionObservable_gauge
    (u : PrequantumData.Gauge) (P : ProjectivePrequantumBundle (E := E)) :
    connectionObservable (u • P) = connectionObservable P / (u : ℝ) := by
  rfl

lemma covariantDerivative_gauge_invariant
    (u : PrequantumData.Gauge) (P : ProjectivePrequantumBundle (E := E)) :
    covariantDerivative (u • P) = covariantDerivative P := by
  rw [covariantDerivative_eq_omegaScale (P := u • P)]
  rw [covariantDerivative_eq_omegaScale (P := P)]
  rfl

end ProjectivePrequantumBundle

/-- Weyl-compatibility predicate: the neutral Hessian form scales conformally by `a²`. -/
def IsWeylCompatibleHessian
    (P : ProjectivePrequantumBundle (E := E)) : Prop :=
    ∀ (u : PrequantumData.Gauge) (v w : InfoGeometry.Krein.DoubledSpace E),
    Hess (u • v) (u • w) = ((u : ℝ) ^ (2 : ℕ)) * Hess v w

lemma hessian_indefinite_form_smul_smul_weyl
  (u : PrequantumData.Gauge) (v w : InfoGeometry.Krein.DoubledSpace E) :
    Hess (u • v) (u • w) = ((u : ℝ) ^ (2 : ℕ)) * Hess v w := by
  change Hess (((u : ℝ)) • v) (((u : ℝ)) • w) = ((u : ℝ) ^ (2 : ℕ)) * Hess v w
  simpa using Hess_smul_smul ((u : ℝ)) v w

lemma isWeylCompatibleHessian
    (P : ProjectivePrequantumBundle (E := E)) :
    IsWeylCompatibleHessian P := by
  intro u v w
  exact hessian_indefinite_form_smul_smul_weyl u v w

/-- Joint compatibility package: gauge-invariant covariant derivative plus Weyl metric scaling. -/
structure GaugeHessianCompatible
    (P : ProjectivePrequantumBundle (E := E)) : Prop where
  covariant_gauge_invariant :
    ∀ u : PrequantumData.Gauge,
      ProjectivePrequantumBundle.covariantDerivative (u • P) =
        ProjectivePrequantumBundle.covariantDerivative P
  hessian_weyl_compatible :
    IsWeylCompatibleHessian P

theorem gaugeHessianCompatible
    (P : ProjectivePrequantumBundle (E := E)) :
    GaugeHessianCompatible P := by
  refine ⟨?_, ?_⟩
  · intro u
    exact ProjectivePrequantumBundle.covariantDerivative_gauge_invariant u P
  · exact isWeylCompatibleHessian P

end KreinClifford

end InfoGeometry.Prequantum

import InfoGeometry.Prequantum.Bundle
import InfoGeometry.Krein.DoubledSpace
import Mathlib.Tactic.Ring

/-!
# InfoGeometry.Prequantum.Connection

Scalarized connection and Weyl-compatibility interfaces for projective prequantum bundles.
-/

namespace Connection
end Connection

namespace InfoGeometry.Prequantum

open InfoGeometry.Krein

section KreinClifford

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace ProjectivePrequantumBundle

/-- Scalar connection observable carried by a projective prequantum bundle point. -/
def connectionObservable (P : ProjectivePrequantumBundle (E := E)) : ℝ :=
  P.data.connectionScale

/-- Scalar covariant-derivative proxy `F * ℏ`, inherited from the underlying datum. -/
def covariantDerivative (P : ProjectivePrequantumBundle (E := E)) : ℝ :=
  P.data.covariantScale

lemma connectionObservable_gauge
    (u : PrequantumData.Gauge) (P : ProjectivePrequantumBundle (E := E)) :
    connectionObservable (u • P) = connectionObservable P / (u : ℝ) := by
  change PrequantumData.connectionScale (u • P.data) =
      PrequantumData.connectionScale P.data / (u : ℝ)
  exact PrequantumData.connectionScale_smul u P.data

@[simp] lemma covariantDerivative_smul
    (u : PrequantumData.Gauge) (P : ProjectivePrequantumBundle (E := E)) :
    covariantDerivative (u • P) = covariantDerivative P := by
  change PrequantumData.covariantScale (u • P.data) =
      PrequantumData.covariantScale P.data
  exact PrequantumData.covariantScale_smul u P.data

end ProjectivePrequantumBundle

section Complete

variable [CompleteSpace E]

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

lemma hessian_indefinite_form_smul_smul_weyl
  (u : PrequantumData.Gauge) (v w : InfoGeometry.Krein.DoubledSpace E) :
    Hess (u • v) (u • w) = ((u : ℝ) ^ (2 : ℕ)) * Hess v w := by
  change Hess (((u : ℝ)) • v) (((u : ℝ)) • w) = ((u : ℝ) ^ (2 : ℕ)) * Hess v w
  simpa using Hess_smul_smul ((u : ℝ)) v w

end Complete
end KreinClifford

end InfoGeometry.Prequantum

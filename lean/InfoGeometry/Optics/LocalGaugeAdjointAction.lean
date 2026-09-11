import InfoGeometry.Optics.LocalGaugeGroupAction
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Native local gauge action on adjoint differential fields

Adjoint operator fields carry the same local gauge-group action as connections.
The induced derivative of curvature is then defined by transport, and the
adjoint Bianchi equation is proved gauge invariant in both directions.
-/

noncomputable section

namespace InfoGeometry.Optics.LocalGaugeAdjointAction

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.LocalGaugeCovariantDerivative
open InfoGeometry.Optics.LocalGaugeFrameComposition
open InfoGeometry.Optics.LocalGaugeGroupAction
open InfoGeometry.Optics.LocalGaugeQGTCovariance
open InfoGeometry.Optics.OperatorValuedConnection

variable {Point Tangent A : Type*} [Ring A]

omit [Ring A] in
/-- Extensionality for an adjoint differential field. -/
theorem adjointDifferentialField_ext
    {s t : AdjointDifferentialField
      (Point := Point) (Tangent := Tangent) (A := A)}
    (hvalue : s.value = t.value)
    (hderivative : s.derivative = t.derivative) : s = t := by
  cases s
  cases t
  cases hvalue
  cases hderivative
  rfl

/-- Local transformation by a product frame equals successive local
transformation as complete differential fields. -/
theorem localGaugeField_mul
    (H G : RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A))
    (s : AdjointDifferentialField
      (Point := Point) (Tangent := Tangent) (A := A)) :
    localGaugeField (H * G) s = localGaugeField H (localGaugeField G s) := by
  apply adjointDifferentialField_ext
  · funext p
    exact (localGaugeField_compose_value H G s p).symm
  · funext p X
    change
      innerConjugation (H.frame p * G.frame p) (s.derivative p X) +
          associativeCommutator
            (H.theta p X + innerConjugation (H.frame p) (G.theta p X))
            (innerConjugation (H.frame p * G.frame p) (s.value p)) =
        innerConjugation (H.frame p)
            (innerConjugation (G.frame p) (s.derivative p X) +
              associativeCommutator (G.theta p X)
                (innerConjugation (G.frame p) (s.value p))) +
          associativeCommutator (H.theta p X)
            (innerConjugation (H.frame p)
              (innerConjugation (G.frame p) (s.value p)))
    rw [innerConjugation_mul, innerConjugation_mul]
    change _ =
      (innerConjugationRingEquiv (H.frame p))
          (innerConjugation (G.frame p) (s.derivative p X) +
            associativeCommutator (G.theta p X)
              (innerConjugation (G.frame p) (s.value p))) + _
    rw [map_add]
    change _ =
      innerConjugation (H.frame p)
          (innerConjugation (G.frame p) (s.derivative p X)) +
        (innerConjugationRingEquiv (H.frame p))
            (G.theta p X * innerConjugation (G.frame p) (s.value p) -
              innerConjugation (G.frame p) (s.value p) * G.theta p X) + _
    rw [map_sub, map_mul, map_mul]
    simp only [innerConjugationRingEquiv_apply]
    unfold associativeCommutator
    noncomm_ring

/-- The identity local frame fixes a complete adjoint differential field. -/
@[simp] theorem localGaugeField_one
    (s : AdjointDifferentialField
      (Point := Point) (Tangent := Tangent) (A := A)) :
    localGaugeField
        (1 : RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A)) s = s := by
  apply adjointDifferentialField_ext
  · funext p
    change innerConjugation (1 : Aˣ) (s.value p) = s.value p
    exact innerConjugation_one (s.value p)
  · funext p X
    change innerConjugation (1 : Aˣ) (s.derivative p X) +
        associativeCommutator 0 (innerConjugation (1 : Aˣ) (s.value p)) =
      s.derivative p X
    simp [associativeCommutator]

instance : SMul
    (RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A))
    (AdjointDifferentialField (Point := Point) (Tangent := Tangent) (A := A)) where
  smul G s := localGaugeField G s

instance : MulAction
    (RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A))
    (AdjointDifferentialField (Point := Point) (Tangent := Tangent) (A := A)) where
  one_smul := localGaugeField_one
  mul_smul := localGaugeField_mul

/-- Covariance of the adjoint derivative in native action notation. -/
theorem smul_adjointCovariantDerivative
    (G : RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (s : AdjointDifferentialField
      (Point := Point) (Tangent := Tangent) (A := A))
    (p : Point) (X : Tangent) :
    adjointCovariantDerivative (G • C) (G • s) p X =
      innerConjugation (G.frame p) (adjointCovariantDerivative C s p X) :=
  localGaugeField_covariantDerivative G C s p X

/-- Derivative channel of the gauge-transported curvature field. -/
def gaugeCurvatureDerivative
    (G : RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (dF : Point → Tangent → Tangent → Tangent → A) :
    Point → Tangent → Tangent → Tangent → A :=
  fun p X U V =>
    (G • curvatureDifferentialField C dF U V).derivative p X

/-- The curvature field formed after gauge transformation is exactly the
gauge transform of the original curvature differential field. -/
theorem curvatureDifferentialField_smul
    (G : RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (dF : Point → Tangent → Tangent → Tangent → A)
    (U V : Tangent) :
    curvatureDifferentialField (G • C) (gaugeCurvatureDerivative G C dF) U V =
      G • curvatureDifferentialField C dF U V := by
  apply adjointDifferentialField_ext
  · funext p
    exact rightGaugeGroup_smul_curvature G C p U V
  · rfl

/-- Pointwise covariant derivative of the transported curvature is conjugate
to the original covariant derivative. -/
theorem smul_curvature_covariantDerivative
    (G : RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (dF : Point → Tangent → Tangent → Tangent → A)
    (p : Point) (X U V : Tangent) :
    adjointCovariantDerivative (G • C)
        (curvatureDifferentialField (G • C)
          (gaugeCurvatureDerivative G C dF) U V) p X =
      innerConjugation (G.frame p)
        (adjointCovariantDerivative C
          (curvatureDifferentialField C dF U V) p X) := by
  rw [curvatureDifferentialField_smul]
  exact smul_adjointCovariantDerivative G C
    (curvatureDifferentialField C dF U V) p X

/-- The adjoint operator Bianchi equation is invariant and reflected by every
local gauge-group transformation. -/
theorem satisfiesAdjointBianchi_smul_iff
    (G : RightGaugeGroup (Point := Point) (Tangent := Tangent) (A := A))
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (dF : Point → Tangent → Tangent → Tangent → A) :
    SatisfiesAdjointBianchi (G • C) (gaugeCurvatureDerivative G C dF) ↔
      SatisfiesAdjointBianchi C dF := by
  constructor
  · intro h p X U V
    have ht := h p X U V
    rw [smul_curvature_covariantDerivative] at ht
    apply (innerConjugationRingEquiv (G.frame p)).injective
    change innerConjugation (G.frame p)
        (adjointCovariantDerivative C
          (curvatureDifferentialField C dF U V) p X) =
      innerConjugation (G.frame p) 0
    rw [ht]
    exact (map_zero (innerConjugationRingEquiv (G.frame p))).symm
  · intro h p X U V
    rw [smul_curvature_covariantDerivative, h p X U V]
    exact map_zero (innerConjugationRingEquiv (G.frame p))

end InfoGeometry.Optics.LocalGaugeAdjointAction

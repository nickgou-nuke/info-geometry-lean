import InfoGeometry.Canonical.BogoliubovPolarizationBridge
import InfoGeometry.Canonical.SpectralInference

/-!
# Krein Dirac Polarization Bridge

Thin canonical bridge adding the missing spectral middle between the real
Bogoliubov/polarization transport layer and later thermal or modular
interpretations.

This file does not introduce a new bundled thermal ontology. It only packages
existing owners on the same carrier:

- real Bogoliubov transport on a doubled/Krein Majorana carrier,
- the internal square-minus-one axis `K := J ∘ ε`,
- polarization transport,
- Dirac transport on the same carrier,
- and the transported spectral square law.
-/

namespace InfoGeometry.Canonical.KreinDiracPolarizationBridge

open InfoGeometry.Quantum.RealMajorana
open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Canonical.BogoliubovPolarizationBridge
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Krein

section Generic

variable {S : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
variable {M : RealMajoranaDatum (S := S)}

/-- Conjugation transport of an endomorphism by a real Bogoliubov transform. -/
noncomputable def transportEnd
    (T : RealBogoliubovTransform (S := S) M) (A : S →L[ℝ] S) : S →L[ℝ] S :=
  T.B.comp (A.comp T.Binv)

omit [CompleteSpace S] in
@[simp] theorem transportEnd_id
    (T : RealBogoliubovTransform (S := S) M) :
    transportEnd T (ContinuousLinearMap.id ℝ S) = ContinuousLinearMap.id ℝ S := by
  simp [transportEnd, T.right_inv]

/-- Dirac operator transported on the same real doubled/Krein carrier. -/
noncomputable def transportDirac
    (IST : InfoSpectralTriple S) (T : RealBogoliubovTransform (S := S) M) :
    S →L[ℝ] S :=
  transportEnd T IST.D

/-- Metric witness transported on the same real doubled/Krein carrier. -/
noncomputable def transportMetricOp
    (IST : InfoSpectralTriple S) (T : RealBogoliubovTransform (S := S) M) :
    S →L[ℝ] S :=
  transportEnd T (IST.H.metricOp IST.x₀)

/-- Bogoliubov conjugation preserves the Dirac-square witness on the same carrier. -/
theorem transportDirac_sq_eq_transportMetricOp
    (IST : InfoSpectralTriple S) (T : RealBogoliubovTransform (S := S) M) :
    (transportDirac IST T).comp (transportDirac IST T) = transportMetricOp IST T := by
  have hsq : IST.D.comp IST.D = IST.H.metricOp IST.x₀ := by
    ext x
    have hx : (IST.D * IST.D) x = (IST.H.metricOp IST.x₀) x := by
      exact congrArg (fun A : S →L[ℝ] S => A x) IST.dirac_sq_eq_metric
    simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply] using hx
  calc
    (transportDirac IST T).comp (transportDirac IST T)
        = T.B.comp (IST.D.comp ((T.Binv.comp T.B).comp (IST.D.comp T.Binv))) := by
            simp [transportDirac, transportEnd, ContinuousLinearMap.comp_assoc]
    _ = T.B.comp (IST.D.comp ((ContinuousLinearMap.id ℝ S).comp (IST.D.comp T.Binv))) := by
          rw [T.left_inv]
    _ = T.B.comp ((IST.D.comp IST.D).comp T.Binv) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = T.B.comp ((IST.H.metricOp IST.x₀).comp T.Binv) := by
          rw [hsq]
    _ = transportMetricOp IST T := rfl

/-- Strict symmetry morphisms transport the Dirac-square witness on the same carrier. -/
theorem transportDirac_sq_eq_transportMetricOp_of_strictSymmetry
    (IST : InfoSpectralTriple S)
    {X Y : PolarizedMajorana (S := S) M} (h : X ⟶ Y) :
    (transportDirac IST h.toBogoliubovTransform).comp
      (transportDirac IST h.toBogoliubovTransform)
      = transportMetricOp IST h.toBogoliubovTransform := by
  exact transportDirac_sq_eq_transportMetricOp (IST := IST) (T := h.toBogoliubovTransform)

/--
Canonical packaged bridge on a fixed carrier:
strict symmetry transports the internal `K`-axis, the chosen polarization, and
Dirac-square geometry together.
-/
theorem kreinDiracPolarizationBridge_of_strictSymmetry
    (IST : InfoSpectralTriple S)
    {X Y : PolarizedMajorana (S := S) M} (h : X ⟶ Y) :
    (h.toBogoliubovTransform).transportK.comp (h.toBogoliubovTransform).transportK
      = -(ContinuousLinearMap.id ℝ S) ∧
    (h.toBogoliubovTransform).transportP X.polarization = Y.polarization.P ∧
    (transportDirac IST h.toBogoliubovTransform).comp
      (transportDirac IST h.toBogoliubovTransform)
      = transportMetricOp IST h.toBogoliubovTransform := by
  exact ⟨transportK_sq_of_strictSymmetryBogoliubov h,
    transportP_eq_targetPolarization_of_strictSymmetry h,
    transportDirac_sq_eq_transportMetricOp_of_strictSymmetry (IST := IST) h⟩

end Generic

section Doubled

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {M : RealMajoranaDatum (S := DoubledSpace E)}

/--
On doubled space, strict symmetry transports polarization and Dirac geometry,
and the target polarization still yields the canonical projector-super pair.
-/
theorem doubledKreinDiracPolarizationBridge_of_strictSymmetry
    (IST : InfoSpectralTriple (DoubledSpace E))
    {X Y : PolarizedMajorana (S := DoubledSpace E) M} (h : X ⟶ Y) :
    (h.toBogoliubovTransform).transportP X.polarization = Y.polarization.P ∧
    IsProjectorSuperPair
      (KPolarization.splitOfPolarization (M := M) Y.polarization).Pminus
      (KPolarization.splitOfPolarization (M := M) Y.polarization).Pplus ∧
    (transportDirac IST h.toBogoliubovTransform).comp
      (transportDirac IST h.toBogoliubovTransform)
      = transportMetricOp IST h.toBogoliubovTransform := by
  exact ⟨transportP_eq_targetPolarization_of_strictSymmetry h,
    projectorSuperPair_of_targetPolarization (M := M) Y,
    transportDirac_sq_eq_transportMetricOp_of_strictSymmetry (IST := IST) h⟩

end Doubled

end InfoGeometry.Canonical.KreinDiracPolarizationBridge

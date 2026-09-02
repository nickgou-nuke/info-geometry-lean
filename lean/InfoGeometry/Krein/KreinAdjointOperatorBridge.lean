import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Krein.InvolutiveSelfDualCarrier
import InfoGeometry.Krein.KreinModularSpinorBilinearBridge

namespace InfoGeometry.Krein

open scoped InnerProductSpace

variable (X : InvolutiveSelfDualCarrier)

/-- The Krein adjoint induced by the fundamental symmetry `ε`. -/
noncomputable def kreinAdjointOperator
    (C : X.H →L[ℝ] X.H) : X.H →L[ℝ] X.H :=
  X.ε ∘L C.adjoint ∘L X.ε

theorem kreinAdjointOperator_pairing
    (hε : ∀ u v : X.H, ⟪u, X.ε v⟫_ℝ = ⟪X.ε u, v⟫_ℝ)
    (C : X.H →L[ℝ] X.H) (u v : X.H) :
    kreinMetric X u (kreinAdjointOperator X C v) =
      kreinMetric X (C u) v := by
  unfold kreinMetric kreinAdjointOperator
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have he : X.ε (X.ε u) = u := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : X.H →L[ℝ] X.H => T u) X.ε_sq
  have he' (q : X.H) : X.ε (X.ε q) = q := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : X.H →L[ℝ] X.H => T q) X.ε_sq
  rw [he']
  exact ContinuousLinearMap.adjoint_inner_right C u (X.ε v)

theorem kreinSelfAdjointOperator_pairing
    (hε : ∀ u v : X.H, ⟪u, X.ε v⟫_ℝ = ⟪X.ε u, v⟫_ℝ)
    (C : X.H →L[ℝ] X.H)
    (hC : kreinAdjointOperator X C = C) (u v : X.H) :
    kreinMetric X u (C v) = kreinMetric X (C u) v := by
  calc
    kreinMetric X u (C v) =
        kreinMetric X u (kreinAdjointOperator X C v) := by rw [hC]
    _ = kreinMetric X (C u) v :=
      kreinAdjointOperator_pairing X hε C u v

theorem kreinSelfAdjointOperator_eq
    (hε : ∀ u v : X.H, ⟪u, X.ε v⟫_ℝ = ⟪X.ε u, v⟫_ℝ)
    (hmetric : ∀ u v, kreinMetric X u v = X.kreinPairing u v)
    (C : X.H →L[ℝ] X.H)
    (hsym : ∀ u v, kreinMetric X u (C v) = kreinMetric X (C u) v) :
    kreinAdjointOperator X C = C := by
  ext v
  apply X.flat_injective
  ext u
  change X.kreinPairing (kreinAdjointOperator X C v) u =
    X.kreinPairing (C v) u
  calc
    X.kreinPairing (kreinAdjointOperator X C v) u =
        X.kreinPairing u (kreinAdjointOperator X C v) := X.pairing_symm _ _
    _ = kreinMetric X u (kreinAdjointOperator X C v) := by rw [hmetric]
    _ = kreinMetric X (C u) v := kreinAdjointOperator_pairing X hε C u v
    _ = X.kreinPairing (C u) v := by rw [hmetric]
    _ = X.kreinPairing v (C u) := X.pairing_symm _ _
    _ = kreinMetric X v (C u) := (hmetric v (C u)).symm
    _ = kreinMetric X (C v) u := hsym v u
    _ = X.kreinPairing (C v) u := hmetric (C v) u

end InfoGeometry.Krein

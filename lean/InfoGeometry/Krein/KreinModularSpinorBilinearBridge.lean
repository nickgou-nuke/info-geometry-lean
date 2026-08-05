import InfoGeometry.Krein.InvolutiveSelfDualCarrier

namespace InfoGeometry.Krein

open scoped InnerProductSpace

/-!
Structured bilinear readouts for an involutive self-dual carrier.

The Hilbert pairing is only the auxiliary positive pairing.  The split metric
uses `ε`, while `K = Jε` supplies the phase/symplectic axis.  The bridge keeps
the corresponding compatibility hypotheses explicit.
-/

variable (X : InvolutiveSelfDualCarrier)

noncomputable def kreinMetric (u v : X.H) : ℝ :=
  ⟪u, X.ε v⟫_ℝ

noncomputable def modularChargePairing (u v : X.H) : ℝ :=
  kreinMetric X u (X.J v)

noncomputable def phaseSymplecticForm (u v : X.H) : ℝ :=
  ⟪u, X.K v⟫_ℝ

structure BilinearAdjointWitness where
  epsilon_selfAdjoint : ∀ u v, ⟪u, X.ε v⟫_ℝ = ⟪X.ε u, v⟫_ℝ
  phase_skew : ∀ u v, ⟪X.K u, v⟫_ℝ = -⟪u, X.K v⟫_ℝ

theorem kreinMetric_symmetric
    (W : BilinearAdjointWitness X) (u v : X.H) :
    kreinMetric X u v = kreinMetric X v u := by
  unfold kreinMetric
  calc
    ⟪u, X.ε v⟫_ℝ = ⟪X.ε u, v⟫_ℝ := W.epsilon_selfAdjoint u v
    _ = ⟪v, X.ε u⟫_ℝ := by
      simpa using (real_inner_comm (X.ε u) v).symm

theorem phaseSymplecticForm_skew
    (W : BilinearAdjointWitness X) (u v : X.H) :
    phaseSymplecticForm X v u = -phaseSymplecticForm X u v := by
  unfold phaseSymplecticForm
  calc
    ⟪v, X.K u⟫_ℝ = ⟪X.K u, v⟫_ℝ := real_inner_comm _ _
    _ = -⟪u, X.K v⟫_ℝ := W.phase_skew u v

theorem modularChargePairing_eq_neg_phaseSymplecticForm
    (u v : X.H) :
    modularChargePairing X u v = -phaseSymplecticForm X u v := by
  unfold modularChargePairing kreinMetric phaseSymplecticForm
  have hAnti := congrArg (fun T : X.H →L[ℝ] X.H => T v) X.J_ε_anticomm
  have hAnti' : X.J (X.ε v) = -X.ε (X.J v) := by
    simpa [ContinuousLinearMap.comp_apply] using hAnti
  have hEJ : X.ε (X.J v) = -X.K v := by
    calc
      X.ε (X.J v) = -(-X.ε (X.J v)) := by simp
      _ = -(X.J (X.ε v)) := by rw [← hAnti']
      _ = -X.K v := by rfl
  rw [hEJ]
  simp

theorem modularChargePairing_skew
    (W : BilinearAdjointWitness X) (u v : X.H) :
    modularChargePairing X v u = -modularChargePairing X u v := by
  calc
    modularChargePairing X v u = -phaseSymplecticForm X v u :=
      modularChargePairing_eq_neg_phaseSymplecticForm X v u
    _ = -(-phaseSymplecticForm X u v) := by rw [phaseSymplecticForm_skew X W u v]
    _ = -modularChargePairing X u v := by
      rw [modularChargePairing_eq_neg_phaseSymplecticForm X u v]

noncomputable def kreinAdjointBilinear (C : X.H →L[ℝ] X.H) (u v : X.H) : ℝ :=
  kreinMetric X u (C v)

def IsKreinSelfAdjointBilinear (C : X.H →L[ℝ] X.H) : Prop :=
  ∀ u v, kreinAdjointBilinear X C u v = kreinAdjointBilinear X C v u

def IsKreinSkewAdjointBilinear (C : X.H →L[ℝ] X.H) : Prop :=
  ∀ u v, kreinAdjointBilinear X C u v = -kreinAdjointBilinear X C v u

theorem spinorBilinear_symmetric_of_kreinSelfAdjoint
    {C : X.H →L[ℝ] X.H} (hC : IsKreinSelfAdjointBilinear X C) :
    ∀ u v, kreinAdjointBilinear X C u v = kreinAdjointBilinear X C v u := hC

theorem spinorBilinear_skew_of_kreinSkewAdjoint
    {C : X.H →L[ℝ] X.H} (hC : IsKreinSkewAdjointBilinear X C) :
    ∀ u v, kreinAdjointBilinear X C u v = -kreinAdjointBilinear X C v u := hC

end InfoGeometry.Krein

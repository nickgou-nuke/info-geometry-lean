import InfoGeometry.Twistor.PenroseIncidence

/-!
# Algebraic covariance of Penrose incidence under a spinor frame

For an invertible complex `2 × 2` frame `A`, the simultaneous action
`π ↦ Aπ`, `ω ↦ Aω`, and `X ↦ AXA⁻¹` preserves the incidence equation
`ω = iXπ`.  This is the finite local-frame square used by later tetrad or
connection owners; no differential structure is assumed here.
-/

namespace InfoGeometry.Twistor.TwistorFrameCovariance

noncomputable section

open InfoGeometry.Twistor.PenroseIncidence

def frameAction (A : ComplexSpacetime) (X : ComplexSpacetime) : ComplexSpacetime :=
  A * X * A⁻¹

def spinorFrameAction (A : ComplexSpacetime) (π : Spinor2) : Spinor2 :=
  A.mulVec π

def twistorFrameAction (A : ComplexSpacetime) (Z : Twistor4) : Twistor4 :=
  (A.mulVec Z.1, A.mulVec Z.2)

theorem frameAction_det (A X : ComplexSpacetime) (hA : IsUnit A.det) :
    (frameAction A X).det = X.det := by
  unfold frameAction
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv]
  have hne : A.det ≠ 0 := isUnit_iff_ne_zero.mp hA
  have hcancel : A.det * Ring.inverse (A.det) = 1 := by
    simpa only [Ring.inverse_eq_inv] using hA.mul_inv_cancel
  calc
    A.det * X.det * Ring.inverse (A.det) =
        X.det * (A.det * Ring.inverse (A.det)) := by ring
    _ = X.det := by rw [hcancel, mul_one]

theorem frameAction_mulVec_spinorFrameAction
    (A X : ComplexSpacetime) (hA : IsUnit A.det) (π : Spinor2) :
    (frameAction A X).mulVec (spinorFrameAction A π) =
      spinorFrameAction A (X.mulVec π) := by
  unfold frameAction spinorFrameAction
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul A hA]
  simp

theorem incidence_frame_covariant
    (A X : ComplexSpacetime) (hA : IsUnit A.det) (π : Spinor2) :
    incidenceLinearMap (frameAction A X) (spinorFrameAction A π) =
      twistorFrameAction A (incidenceLinearMap X π) := by
  apply Prod.ext
  · simp only [incidenceLinearMap_apply, omegaLinearMap_apply,
      twistorFrameAction, spinorFrameAction]
    change Complex.I •
        (frameAction A X).mulVec (spinorFrameAction A π) =
      A.mulVec (Complex.I • X.mulVec π)
    rw [frameAction_mulVec_spinorFrameAction A X hA π]
    rw [Matrix.mulVec_smul]
    rfl
  · rfl

end

end InfoGeometry.Twistor.TwistorFrameCovariance

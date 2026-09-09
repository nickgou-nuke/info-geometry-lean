import InfoGeometry.Canonical.Cl11SequentialColimitSystemBridge
import InfoGeometry.Clifford.JordanWignerCAR

set_option autoImplicit false

/-!
# Jordan--Wigner generators in the `Cl(1,1)` algebraic direct limit

For a fixed site `k`, the finite Jordan--Wigner generator is represented at
all later stages by `jw_u k d` (and similarly for annihilation).  This file
proves that these representatives have a stage-independent image in the
existing algebraic direct limit, and transports the genuine finite CAR laws
to that image.  No Hilbert-space or C*-completion is asserted.
-/

namespace InfoGeometry.Canonical.Cl11JordanWignerDirectLimit

noncomputable section

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.JordanWignerBridge
open InfoGeometry.Clifford.JordanWignerCAR

abbrev Limit := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

def jwUImage (k d : ℕ) : Limit :=
  ofStage (k + 1 + d) (jw_u k d)

def jwVImage (k d : ℕ) : Limit :=
  ofStage (k + 1 + d) (jw_v k d)

theorem jwUImage_succ (k d : ℕ) :
    jwUImage k (d + 1) = jwUImage k d := by
  rw [jwUImage, jwUImage, ← matStageEmbed_jw_u k d]
  exact ofStage_apply_bond (k + 1 + d) (jw_u k d)

theorem jwVImage_succ (k d : ℕ) :
    jwVImage k (d + 1) = jwVImage k d := by
  rw [jwVImage, jwVImage, ← matStageEmbed_jw_v k d]
  exact ofStage_apply_bond (k + 1 + d) (jw_v k d)

theorem jwUImage_eq_base (k d : ℕ) :
    jwUImage k d = jwUImage k 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [jwUImage_succ, ih]

theorem jwVImage_eq_base (k d : ℕ) :
    jwVImage k d = jwVImage k 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [jwVImage_succ, ih]

theorem jwUImage_sq (k d : ℕ) :
    jwUImage k d * jwUImage k d = 0 := by
  rw [jwUImage_eq_base k d]
  simp only [jwUImage, jw_u, embedToStage]
  rw [← ofStage_mul]
  simpa using congrArg (ofStage (k + 1)) (jw_u_new_sq k)

theorem jwVImage_sq (k d : ℕ) :
    jwVImage k d * jwVImage k d = 0 := by
  rw [jwVImage_eq_base k d]
  simp only [jwVImage, jw_v, embedToStage]
  rw [← ofStage_mul]
  simpa using congrArg (ofStage (k + 1)) (jw_v_new_sq k)

theorem jwUVImage_anticomm (k d : ℕ) :
    jwUImage k d * jwVImage k d + jwVImage k d * jwUImage k d = 1 := by
  rw [jwUImage_eq_base k d, jwVImage_eq_base k d]
  simp only [jwUImage, jwVImage, jw_u, jw_v, embedToStage]
  rw [← ofStage_mul, ← ofStage_mul, ← ofStage_add]
  simpa using congrArg (ofStage (k + 1)) (jw_uv_anticomm_new k)

end

end InfoGeometry.Canonical.Cl11JordanWignerDirectLimit

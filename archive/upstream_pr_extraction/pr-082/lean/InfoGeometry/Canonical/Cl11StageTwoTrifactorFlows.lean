import InfoGeometry.Canonical.Cl11StageTwoMatrixEquivalence
import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# Native stage-two parabolic flow

This owner records the square-zero one-parameter law on the existing stage-two
matrix carrier.  It does not assert membership in a chosen Iwasawa subgroup.
-/

namespace InfoGeometry.Canonical.Cl11StageTwoTrifactorFlows

open InfoGeometry.Canonical.Cl11StageTwoMatrixEquivalence
open InfoGeometry.Clifford.Cl11TensorTowerLimit

abbrev StageTwo := Cl11StageTwoMatrixEquivalence.StageTwo

def parabolicFlow (N : StageTwo) (t : ℝ) : StageTwo :=
  1 + t • N

theorem parabolicFlow_zero (N : StageTwo) :
    parabolicFlow N 0 = 1 := by
  simp [parabolicFlow]

theorem parabolicFlow_add (N : StageTwo) (hN : N * N = 0) (s t : ℝ) :
    parabolicFlow N s * parabolicFlow N t = parabolicFlow N (s + t) := by
  simp only [parabolicFlow, add_mul, mul_add, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, hN, smul_zero, add_zero]
  rw [add_assoc, ← add_smul]

theorem parabolicFlow_inverse (N : StageTwo) (hN : N * N = 0) (t : ℝ) :
    parabolicFlow N t * parabolicFlow N (-t) = 1 := by
  simpa [parabolicFlow] using parabolicFlow_add N hN t (-t)

noncomputable def hyperbolicFlow (H : StageTwo) (t : ℝ) : StageTwo :=
  Real.cosh t • (1 : StageTwo) + Real.sinh t • H

theorem hyperbolicFlow_zero (H : StageTwo) :
    hyperbolicFlow H 0 = 1 := by
  simp [hyperbolicFlow]

theorem hyperbolicFlow_add (H : StageTwo) (hH : H * H = 1) (s t : ℝ) :
    hyperbolicFlow H s * hyperbolicFlow H t = hyperbolicFlow H (s + t) := by
  simp only [hyperbolicFlow, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one, hH]
  rw [Real.cosh_add, Real.sinh_add]
  module

theorem hyperbolicFlow_inverse (H : StageTwo) (hH : H * H = 1) (t : ℝ) :
    hyperbolicFlow H t * hyperbolicFlow H (-t) = 1 := by
  simpa [hyperbolicFlow] using hyperbolicFlow_add H hH t (-t)

noncomputable def ellipticFlow (J : StageTwo) (t : ℝ) : StageTwo :=
  Real.cos t • (1 : StageTwo) + Real.sin t • J

theorem ellipticFlow_zero (J : StageTwo) :
    ellipticFlow J 0 = 1 := by
  simp [ellipticFlow]

theorem ellipticFlow_add (J : StageTwo) (hJ : J * J = -1) (s t : ℝ) :
    ellipticFlow J s * ellipticFlow J t = ellipticFlow J (s + t) := by
  simp only [ellipticFlow, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one, hJ, smul_neg]
  rw [Real.cos_add, Real.sin_add]
  module

theorem ellipticFlow_inverse (J : StageTwo) (hJ : J * J = -1) (t : ℝ) :
    ellipticFlow J t * ellipticFlow J (-t) = 1 := by
  simpa [ellipticFlow] using ellipticFlow_add J hJ t (-t)

theorem ellipticFlow_hyperbolicFlow_commute
    (J H : StageTwo) (hJH : J * H = H * J) (s t : ℝ) :
    ellipticFlow J s * hyperbolicFlow H t =
      hyperbolicFlow H t * ellipticFlow J s := by
  simp only [ellipticFlow, hyperbolicFlow, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hJH]
  module

noncomputable def loxodromicFlow (J H : StageTwo) (theta t : ℝ) : StageTwo :=
  ellipticFlow J theta * hyperbolicFlow H t

theorem loxodromicFlow_zero (J H : StageTwo) :
    loxodromicFlow J H 0 0 = 1 := by
  simp [loxodromicFlow, ellipticFlow_zero, hyperbolicFlow_zero]

theorem loxodromicFlow_add
    (J H : StageTwo) (hJ : J * J = -1) (hH : H * H = 1)
    (hcomm : Commute J H) (theta₁ theta₂ t₁ t₂ : ℝ) :
    loxodromicFlow J H (theta₁ + theta₂) (t₁ + t₂) =
      loxodromicFlow J H theta₁ t₁ * loxodromicFlow J H theta₂ t₂ := by
  unfold loxodromicFlow
  calc
    ellipticFlow J (theta₁ + theta₂) * hyperbolicFlow H (t₁ + t₂) =
        (ellipticFlow J theta₁ * ellipticFlow J theta₂) *
          (hyperbolicFlow H t₁ * hyperbolicFlow H t₂) := by
      rw [ellipticFlow_add J hJ, hyperbolicFlow_add H hH]
    _ = ellipticFlow J theta₁ * hyperbolicFlow H t₁ *
          (ellipticFlow J theta₂ * hyperbolicFlow H t₂) := by
      calc
        (ellipticFlow J theta₁ * ellipticFlow J theta₂) *
            (hyperbolicFlow H t₁ * hyperbolicFlow H t₂) =
            ellipticFlow J theta₁ *
              (ellipticFlow J theta₂ * hyperbolicFlow H t₁) *
                hyperbolicFlow H t₂ := by simp only [mul_assoc]
        _ = ellipticFlow J theta₁ *
              (hyperbolicFlow H t₁ * ellipticFlow J theta₂) *
                hyperbolicFlow H t₂ := by
          exact congrArg
            (fun X => ellipticFlow J theta₁ * X * hyperbolicFlow H t₂)
            (ellipticFlow_hyperbolicFlow_commute J H hcomm.eq theta₂ t₁)
        _ = ellipticFlow J theta₁ * hyperbolicFlow H t₁ *
              (ellipticFlow J theta₂ * hyperbolicFlow H t₂) := by
          simp only [mul_assoc]

theorem loxodromicFlow_inverse
    (J H : StageTwo) (hJ : J * J = -1) (hH : H * H = 1)
    (hcomm : Commute J H) (theta t : ℝ) :
    loxodromicFlow J H (-theta) (-t) *
        loxodromicFlow J H theta t = 1 := by
  rw [← loxodromicFlow_add J H hJ hH hcomm (-theta) theta (-t) t]
  simp [loxodromicFlow_zero]

abbrev Limit := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

noncomputable def limitParabolicFlow (N : StageTwo) (t : ℝ) : Limit :=
  ofStage 2 (parabolicFlow N t)

theorem limitParabolicFlow_add (N : StageTwo) (hN : N * N = 0) (s t : ℝ) :
    limitParabolicFlow N s * limitParabolicFlow N t =
      limitParabolicFlow N (s + t) := by
  change ofStage 2 (parabolicFlow N s) * ofStage 2 (parabolicFlow N t) =
    ofStage 2 (parabolicFlow N (s + t))
  rw [← ofStage_mul]
  exact congrArg (ofStage 2) (parabolicFlow_add N hN s t)

end InfoGeometry.Canonical.Cl11StageTwoTrifactorFlows

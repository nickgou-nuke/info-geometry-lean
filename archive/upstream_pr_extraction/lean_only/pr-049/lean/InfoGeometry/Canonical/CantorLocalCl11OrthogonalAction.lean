import InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Canonical.CantorLocalCl11Universal

/-! The local switch acts by central inversion on the two-generator carrier. -/
noncomputable section
namespace InfoGeometry.Canonical.CantorLocalCl11OrthogonalAction

open InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge
open InfoGeometry.Canonical.CantorLocalCl11Universal
open InfoGeometry.Clifford.Cl11Matrix

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]

def localCl11VectorReadout (P : BinaryWordTiltReadout Op) :
    (ℝ × ℝ) → Op := fun v =>
  v.1 • localCl11Positive P + v.2 • localCl11Negative P

noncomputable def localCl11VectorReadoutLinear
    (P : BinaryWordTiltReadout Op) : (ℝ × ℝ) →ₗ[ℝ] Op :=
    localCl11Generator P

@[simp] theorem localCl11VectorReadoutLinear_apply
    (P : BinaryWordTiltReadout Op) (v : ℝ × ℝ) :
    localCl11VectorReadoutLinear P v = localCl11VectorReadout P v := by
  rfl

def localCl11CentralInversion : (ℝ × ℝ) → (ℝ × ℝ) := fun v => (-v.1, -v.2)

noncomputable def localCl11CentralInversionLinear :
    (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun := localCl11CentralInversion
  map_add' := by
    intro u v
    ext <;> simp [localCl11CentralInversion] <;> ring
  map_smul' := by
    intro a v
    ext <;> simp [localCl11CentralInversion]

@[simp] theorem localCl11CentralInversionLinear_apply (v : ℝ × ℝ) :
    localCl11CentralInversionLinear v = localCl11CentralInversion v := rfl

@[simp] theorem localCl11CentralInversionLinear_involutive (v : ℝ × ℝ) :
    localCl11CentralInversionLinear (localCl11CentralInversionLinear v) = v := by
  ext <;> simp [localCl11CentralInversionLinear, localCl11CentralInversion]

theorem localCl11CentralInversion_q11 (v : ℝ × ℝ) :
    q11 (localCl11CentralInversion v) = q11 v := by
  rcases v with ⟨a, b⟩
  simp [localCl11CentralInversion, q11_apply]

theorem localCl11CentralInversionLinear_q11 (v : ℝ × ℝ) :
    q11 (localCl11CentralInversionLinear v) = q11 v := by
  simpa only [localCl11CentralInversionLinear_apply] using
    localCl11CentralInversion_q11 v

theorem localCl11AlgebraHom_ι_eq_vectorReadout
    (P : BinaryWordTiltReadout Op) (v : ℝ × ℝ) :
    localCl11AlgebraHom P (CliffordAlgebra.ι q11 v) =
      localCl11VectorReadout P v := by
  rw [localCl11AlgebraHom_ι]
  rfl

theorem localCl11Switch_centralInversion
    (P : BinaryWordTiltReadout Op) (v : ℝ × ℝ) :
    P.bitOperator true * localCl11VectorReadout P v * P.bitOperator true =
      localCl11VectorReadout P (localCl11CentralInversion v) := by
  rcases v with ⟨a, b⟩
  dsimp [localCl11VectorReadout, localCl11CentralInversion]
  rw [mul_add, add_mul]
  have hp :
      P.tiltSwitch.S P.word.length * (a • localCl11Positive P) *
          P.tiltSwitch.S P.word.length =
        a • (P.tiltSwitch.S P.word.length * localCl11Positive P *
          P.tiltSwitch.S P.word.length) := by
    simp
  have hn :
      P.tiltSwitch.S P.word.length * (b • localCl11Negative P) *
          P.tiltSwitch.S P.word.length =
        b • (P.tiltSwitch.S P.word.length * localCl11Negative P *
          P.tiltSwitch.S P.word.length) := by
    simp
  have hp' :
      P.tiltSwitch.S P.word.length * localCl11Positive P *
          P.tiltSwitch.S P.word.length = -localCl11Positive P := by
    simpa [BinaryWordTiltReadout.bitOperator] using
      switch_conj_localCl11Positive P
  have hn' :
      P.tiltSwitch.S P.word.length * localCl11Negative P *
          P.tiltSwitch.S P.word.length = -localCl11Negative P := by
    simpa [BinaryWordTiltReadout.bitOperator] using
      switch_conj_localCl11Negative P
  rw [hp, hn, hp', hn']
  simp

theorem localCl11Switch_centralInversion_linear
    (P : BinaryWordTiltReadout Op) (v : ℝ × ℝ) :
    P.bitOperator true * localCl11VectorReadoutLinear P v *
        P.bitOperator true =
      localCl11VectorReadoutLinear P
        (localCl11CentralInversionLinear v) := by
  simpa only [localCl11VectorReadoutLinear_apply,
    localCl11CentralInversionLinear_apply] using
    localCl11Switch_centralInversion P v

end InfoGeometry.Canonical.CantorLocalCl11OrthogonalAction

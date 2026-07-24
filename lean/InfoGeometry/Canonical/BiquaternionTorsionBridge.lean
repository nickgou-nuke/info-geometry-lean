import InfoGeometry.Section8
import InfoGeometry.Section12
import InfoGeometry.Canonical.EmergentGravity
import InfoGeometry.Canonical.BiquaternionSU2

/-
Biquaternion torsion bridge.

This file packages the finite algebraic shadow that the repo actually supports:

* real quaternion torsion is the commutator covariant derivative
  `dq + Ω*q - q*Ω`;
* the same formula makes sense in the complexified quaternion algebra
  `Quaternion ℂ`, which the repository uses as its biquaternion carrier;
* coefficientwise lifting from real quaternions to biquaternions preserves the
  torsion expression;
* the emergent condensate torsion readout is sent to biquaternions by an
  explicit zero-preserving lift and therefore vanishes when the torsion source
  vanishes.

This is a finite operator-shadow result.  It does not claim a continuum
Einstein-Cartan field equation or a full bundle-level torsion theory.
-/

noncomputable section

namespace InfoGeometry.Canonical.BiquaternionTorsionBridge

open Complex

abbrev Biquaternion := InfoGeometry.Canonical.Biquaternions.Biquaternion

/-- Coefficient-wise lift of a real quaternion into the biquaternion channel. -/
def liftQuatToBiquaternion (q : Section8.Quat) : Biquaternion :=
  ⟨(q.r : ℂ), (q.x : ℂ), (q.y : ℂ), (q.z : ℂ)⟩

/-- The biquaternion torsion shadow `T_B = dB + ΩB - BΩ`. -/
def biquaternionTorsion (dB Ω B : Biquaternion) : Biquaternion :=
  dB + (Ω * B - B * Ω)

@[simp] theorem lift_zero :
    liftQuatToBiquaternion (0 : Section8.Quat) = 0 := by
  rfl

@[simp] theorem lift_add (p q : Section8.Quat) :
    liftQuatToBiquaternion (p + q) =
      liftQuatToBiquaternion p + liftQuatToBiquaternion q := by
  ext <;> simp [liftQuatToBiquaternion]

@[simp] theorem lift_quaternionTorsion (dq Ω q : Section8.Quat) :
    liftQuatToBiquaternion (Section12.quaternionTorsion dq Ω q) =
      biquaternionTorsion (liftQuatToBiquaternion dq)
        (liftQuatToBiquaternion Ω)
        (liftQuatToBiquaternion q) := by
  ext <;> simp [liftQuatToBiquaternion, biquaternionTorsion,
    Section12.quaternionTorsion] <;> ring

@[simp] theorem biquaternionTorsion_zero_connection (dB B : Biquaternion) :
    biquaternionTorsion dB 0 B = dB := by
  simp [biquaternionTorsion]

@[simp] theorem biquaternionTorsion_flat (B : Biquaternion) :
    biquaternionTorsion 0 0 B = 0 := by
  simp [biquaternionTorsion]

theorem biquaternionTorsion_zero_of_commuting
    (Ω B : Biquaternion)
    (hcomm : Ω * B = B * Ω) :
    biquaternionTorsion 0 Ω B = 0 := by
  simp [biquaternionTorsion, hcomm]

/-- A zero-preserving lift from a torsion carrier into the biquaternion readout. -/
structure CondensateBiquaternionLift (T : Type*) [AddCommGroup T] [Module ℝ T] where
  toBiquat : T → Biquaternion
  map_zero : toBiquat 0 = 0

/-- The emergent condensate torsion readout lifted to the biquaternion channel. -/
def condensateBiquaternionTorsion
    {V T : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup T] [Module ℝ T]
    (condensate : EmergentGravity.SpinorCondensate V)
    (sigma_phi : V)
    (st : EmergentGravity.SpinorTorsion V T)
    (lift : CondensateBiquaternionLift T) : Biquaternion :=
  lift.toBiquat (EmergentGravity.condensate_torsion condensate sigma_phi st)

/-- If the torsion source is zero, the biquaternion readout vanishes. -/
theorem condensateBiquaternionTorsion_zero
    {V T : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup T] [Module ℝ T]
    (condensate : EmergentGravity.SpinorCondensate V)
    (sigma_phi : V)
    (st : EmergentGravity.SpinorTorsion V T)
    (lift : CondensateBiquaternionLift T)
    (hT : st.torsion_map condensate.bar_phi sigma_phi = 0) :
    condensateBiquaternionTorsion condensate sigma_phi st lift = 0 := by
  simp [condensateBiquaternionTorsion, EmergentGravity.condensate_torsion,
    hT, lift.map_zero]

end InfoGeometry.Canonical.BiquaternionTorsionBridge

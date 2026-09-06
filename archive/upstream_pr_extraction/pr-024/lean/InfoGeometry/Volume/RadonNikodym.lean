import InfoGeometry.Canonical.LogGenerator
import InfoGeometry.Canonical.ProjectiveFoundation
import InfoGeometry.Volume.LogPotential
import InfoGeometry.Meta.Architecture

/-!
# Radon-Nikodym Bridge

Formalizes the connection between algebraic volume characters and scalar
Radon-Nikodym logarithms.  The RN readout is not supplied as a field: it is
defined directly as `log |vol a|`.
-/

namespace InfoGeometry.Volume.RadonNikodym

open InfoGeometry.Canonical
open InfoGeometry.Volume.Base
open InfoGeometry.Volume.LogPotential

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Scalar RN logarithm induced directly by a multiplicative volume character. -/
noncomputable def scalarRN {A : Type*} [Monoid A] (vol : A →* ℝˣ) (a : A) : ℝ :=
  Real.log |((vol a : ℝˣ) : ℝ)|

/--
Any multiplicative volume character yields an exact multiplicative-to-additive
bridge through logarithmic linearization.
-/
noncomputable def exactBridgeOfVolumeCharacter {A : Type*} [Monoid A]
    (vol : A →* ℝˣ) :
    ExactMultiplicativeToAdditiveBridge A ℝˣ ℝ where
  toExactAbelianizingBridge := ⟨vol⟩
  toAdditiveLinearization := logAbsUnitsLinearization

/-- High-level logarithmic generator induced by a scalar RN bridge. -/
noncomputable def logGeneratorOfVolumeCharacter {A : Type*} [Monoid A]
    (vol : A →* ℝˣ) : LogGenerator A ℝ :=
  (ExactDescentLogGenerator.ofBridge (exactBridgeOfVolumeCharacter vol)).toLogGenerator

/-- The RN potential is the additive invariant of the exact bridge. -/
theorem rn_eq_additiveInvariant {A : Type*} [Monoid A]
    (vol : A →* ℝˣ) (a : A) :
    scalarRN vol a = (exactBridgeOfVolumeCharacter vol).additiveInvariant a :=
  rfl

/-- The RN potential is the value of the induced high-level logarithmic generator. -/
theorem rn_eq_logGenerator {A : Type*} [Monoid A]
    (vol : A →* ℝˣ) (a : A) :
    scalarRN vol a = (logGeneratorOfVolumeCharacter vol).logGen a :=
  rn_eq_additiveInvariant vol a

/--
Multiplicative chain rule for the scalar RN bridge.
If the bridge holds, the RN derivative of a composition is the sum of derivatives.
-/
theorem rn_chain_rule {A : Type*} [Monoid A] (vol : A →* ℝˣ) (f g : A) :
    scalarRN vol (f * g) = scalarRN vol f + scalarRN vol g := by
  rw [rn_eq_additiveInvariant]
  rw [rn_eq_additiveInvariant, rn_eq_additiveInvariant]
  exact ExactMultiplicativeToAdditiveBridge.additiveInvariant_mul
    (exactBridgeOfVolumeCharacter vol) f g

/--
Scalar Radon-Nikodym bridge.

Wraps a multiplicative volume character and exposes the induced additive
scalar potential.
-/
@[rep_depth projective]
structure HasScalarRNBridge (A : Type*) [Monoid A] where
  vol : A →* ℝˣ

namespace HasScalarRNBridge

variable {A : Type*} [Monoid A] (B : HasScalarRNBridge A)

/-- The induced scalar RN potential. -/
noncomputable def rn (a : A) : ℝ := scalarRN B.vol a

/-- The RN potential is exactly the log-absolute volume readout. -/
theorem rn_eq_logAbs_vol (a : A) :
    B.rn a = Real.log |((B.vol a : ℝˣ) : ℝ)| :=
  rfl

/-- Compatibility with the induced additive invariant. -/
theorem rn_eq_additiveInvariant (a : A) :
    B.rn a = (exactBridgeOfVolumeCharacter B.vol).additiveInvariant a :=
  rfl

/-- Multiplicative chain rule for the scalar RN bridge. -/
theorem rn_chain_rule (f g : A) :
    B.rn (f * g) = B.rn f + B.rn g :=
  InfoGeometry.Volume.RadonNikodym.rn_chain_rule B.vol f g

end HasScalarRNBridge

/-- The scalar RN potential is an additive monoid homomorphism. -/
noncomputable def rnHom {A : Type*} [Monoid A] (vol : A →* ℝˣ) :
    Additive A →+ ℝ where
  toFun := fun a => scalarRN vol a.toMul
  map_zero' := by
    simp [scalarRN]
  map_add' := by
    intro a b
    exact rn_chain_rule vol a.toMul b.toMul

@[simp] theorem rnHom_apply {A : Type*} [Monoid A] (vol : A →* ℝˣ) (a : A) :
    rnHom vol (Additive.ofMul a) = scalarRN vol a :=
  rfl

/--
An RN bridge can be read as a projective rotor cocycle over the trivial
`PUnit` base action by exponentiating the additive shadow into the additive
wrapper group `Multiplicative ℝ`.
-/
noncomputable def toProjectiveRotorCocycle {A : Type*} [Group A]
    (vol : A →* ℝˣ) :
    InfoGeometry.Canonical.ProjectiveFoundation.ProjectiveRotorCocycle
      A PUnit (Multiplicative ℝ) where
  toFun a _ := Multiplicative.ofAdd (scalarRN vol a)
  map_one := by
    intro x
    simp [scalarRN]
  map_mul := by
    intro a b _
    simpa using congrArg Multiplicative.ofAdd (rn_chain_rule vol a b)

@[simp] theorem toProjectiveRotorCocycle_apply {A : Type*} [Group A]
    (vol : A →* ℝˣ) (a : A) :
    toProjectiveRotorCocycle vol a PUnit.unit = Multiplicative.ofAdd (scalarRN vol a) :=
  rfl

@[simp] theorem toProjectiveRotorCocycle_mul {A : Type*} [Group A]
    (vol : A →* ℝˣ) (a b : A) :
    toProjectiveRotorCocycle vol (a * b) PUnit.unit =
      toProjectiveRotorCocycle vol a PUnit.unit *
        toProjectiveRotorCocycle vol b PUnit.unit := by
  simp [toProjectiveRotorCocycle, rn_chain_rule]

end InfoGeometry.Volume.RadonNikodym

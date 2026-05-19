import InfoGeometry.Canonical.LogGenerator
import InfoGeometry.Volume.LogPotential

/-!
# Radon-Nikodym Bridge

Formalizes the connection between abstract volume changes and the 
Radon-Nikodym derivative. This avoids vacuous existence statements by 
providing a constructive structure interface.
-/

namespace InfoGeometry.Volume.RadonNikodym

open InfoGeometry.Canonical
open InfoGeometry.Volume.Base
open InfoGeometry.Volume.LogPotential

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/--
Structure expressing the bridge between an algebraic volume and a 
scalar Radon-Nikodym derivative.
-/
structure HasScalarRNBridge (A : Type*) [Monoid A] where
  vol : A →* ℝˣ
  rn  : A → ℝ
  rn_eq_logAbs_vol : ∀ a, rn a = Real.log |((vol a : ℝˣ) : ℝ)|

/--
Any scalar Radon-Nikodym bridge yields an exact multiplicative-to-additive
bridge through the volume character and logarithmic linearization.
-/
noncomputable def HasScalarRNBridge.toExactBridge {A : Type*} [Monoid A]
    (B : HasScalarRNBridge A) :
    ExactMultiplicativeToAdditiveBridge A ℝˣ ℝ where
  toExactAbelianizingBridge := ⟨B.vol⟩
  toAdditiveLinearization := logAbsUnitsLinearization

/-- High-level logarithmic generator induced by a scalar RN bridge. -/
noncomputable def HasScalarRNBridge.toLogGenerator {A : Type*} [Monoid A]
    (B : HasScalarRNBridge A) : LogGenerator A ℝ :=
  (ExactDescentLogGenerator.ofBridge B.toExactBridge).toLogGenerator

/-- The RN potential is the additive invariant of the exact bridge. -/
theorem rn_eq_additiveInvariant {A : Type*} [Monoid A]
    (B : HasScalarRNBridge A) (a : A) :
    B.rn a = B.toExactBridge.additiveInvariant a := by
  rw [B.rn_eq_logAbs_vol]
  rfl

/-- The RN potential is the value of the induced high-level logarithmic generator. -/
theorem rn_eq_logGenerator {A : Type*} [Monoid A]
    (B : HasScalarRNBridge A) (a : A) :
    B.rn a = B.toLogGenerator.logGen a := by
  exact rn_eq_additiveInvariant B a

/--
Multiplicative chain rule for the scalar RN bridge.
If the bridge holds, the RN derivative of a composition is the sum of derivatives.
-/
theorem rn_chain_rule {A : Type*} [Monoid A] (B : HasScalarRNBridge A) (f g : A) :
    B.rn (f * g) = B.rn f + B.rn g := by
  rw [rn_eq_additiveInvariant]
  rw [rn_eq_additiveInvariant, rn_eq_additiveInvariant]
  exact ExactMultiplicativeToAdditiveBridge.additiveInvariant_mul B.toExactBridge f g

/-- The scalar RN potential is an additive monoid homomorphism. -/
noncomputable def rnHom {A : Type*} [Monoid A] (B : HasScalarRNBridge A) :
    Additive A →+ ℝ where
  toFun := fun a => B.rn a.toMul
  map_zero' := by
    rw [B.rn_eq_logAbs_vol]
    simp
  map_add' := by
    intro a b
    exact rn_chain_rule B a.toMul b.toMul

@[simp] theorem rnHom_apply {A : Type*} [Monoid A] (B : HasScalarRNBridge A) (a : A) :
    rnHom (B := B) (Additive.ofMul a) = B.rn a :=
  rfl

end InfoGeometry.Volume.RadonNikodym

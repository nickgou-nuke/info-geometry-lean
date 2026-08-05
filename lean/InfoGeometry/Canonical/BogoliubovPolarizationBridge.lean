import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Quantum.RealMajorana
import InfoGeometry.Meta.Architecture

/-!
# Bogoliubov Polarization Bridge

Thin canonical bridge from real Bogoliubov transport on the doubled real carrier
into the polarization and ladder/projector surface used by the Bogoliubov/Fock
layer.

This file does not redefine CAR, `K`, or polarization semantics. It only
packages the existing owners so downstream files can state the thermal reading
cleanly:

- the square-minus-one axis remains internal to the anticommuting involution core,
- Bogoliubov transport moves one polarization to another,
- on doubled space, the transported target polarization yields the canonical
  projector-super pair.
-/

namespace InfoGeometry.Canonical.BogoliubovPolarizationBridge

open InfoGeometry.Quantum.RealMajorana
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Krein

section Generic

variable {S : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
variable {M : RealMajoranaDatum (S := S)}

/-- A strict symmetry morphism transports the source polarization onto the target one. -/
theorem transportP_eq_targetPolarization_of_strictSymmetry
    {X Y : PolarizedMajorana (S := S) M} (h : X ⟶ Y) :
    (h.toBogoliubovTransform).transportP X.polarization = Y.polarization.P := by
  exact h.toBogoliubovTransform_transportP_eq

end Generic

section Doubled

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {M : RealMajoranaDatum (S := DoubledSpace E)}

/-- Any target polarization on doubled space yields the canonical projector-super pair. -/
theorem projectorSuperPair_of_targetPolarization
    (Y : PolarizedMajorana (S := DoubledSpace E) M) :
    IsProjectorSuperPair (E := E)
      (KPolarization.splitOfPolarization (M := M) Y.polarization).Pminus
      (KPolarization.splitOfPolarization (M := M) Y.polarization).Pplus := by
  exact projectorSuperPair_of_ladderOfPolarization (E := E) M Y.polarization

/--
Canonical packaged bridge for the doubled thermal reading:
Bogoliubov transport carries one polarization to another, and the target
polarization induces the projector-super ladder pair used by the Fock layer.
-/
@[rep_depth transport]
theorem bogoliubovPolarizationBridge_of_strictSymmetry
    {X Y : PolarizedMajorana (S := DoubledSpace E) M} (h : X ⟶ Y) :
    (h.toBogoliubovTransform).transportP X.polarization = Y.polarization.P ∧
    IsProjectorSuperPair (E := E)
      (KPolarization.splitOfPolarization (M := M) Y.polarization).Pminus
      (KPolarization.splitOfPolarization (M := M) Y.polarization).Pplus := by
  exact ⟨transportP_eq_targetPolarization_of_strictSymmetry h,
    projectorSuperPair_of_targetPolarization (E := E) Y⟩

end Doubled

end InfoGeometry.Canonical.BogoliubovPolarizationBridge

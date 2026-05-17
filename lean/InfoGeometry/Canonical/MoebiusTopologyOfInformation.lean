import Mathlib
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.PrimeBooleanCube
import InfoGeometry.Geometry.RealMoebiusAction
import SelfReference.Moebius

/-!
# InfoGeometry.Canonical.MoebiusTopologyOfInformation

Canonical Möbius-topology index for the information-geometry lanes.

This file keeps the claim surface strict:

* the cognitive lane is the doubled-space parity-restoration theorem;
* the arithmetic lane is the finite prime Boolean-cube Möbius parity theorem;
* the conformal lane is the real Möbius boundary action theorem.

That is a formal Möbius pattern across three lanes. It is not a theorem that
the universe is physically non-orientable.
-/

noncomputable section

universe u

namespace InfoGeometry.Canonical.MoebiusTopologyOfInformation

open SelfReference
open InfoGeometry.Arithmetic.PrimeBooleanCube
open InfoGeometry.Geometry.RealUpperHalfPlane

/--
Canonical Möbius index for the information-geometry lanes.

This statement packages the existing lane theorems without introducing any
new analytic or metaphysical claim.
-/
@[owner_target_tag]
def MoebiusTopologyOfInformationOwnerTarget : Prop :=
  (∀ {A : Agent.{u}}
      [NormedAddCommGroup A.Output] [InnerProductSpace ℝ A.Output]
      [NormedSpace ℝ A.Output] [CompleteSpace A.Output]
      (o : A.Output),
      WithLp.fst
          (SelfReference.moebiusTwist (A := A)
            (SelfReference.moebiusTwist (A := A)
              (InfoGeometry.Krein.to_doubled o 0))) = -o) ∧
  (∀ (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
      (v : InfoGeometry.Arithmetic.PrimeBooleanCube.Vertex P),
      ArithmeticFunction.moebius
          (InfoGeometry.Arithmetic.PrimeBooleanCube.representedNat v) =
        InfoGeometry.Arithmetic.PrimeBooleanCube.fermionParity v) ∧
  (∀ (g : InfoGeometry.Geometry.SL2R)
      (τ : InfoGeometry.Geometry.RealUpperHalfPlane),
      InfoGeometry.Geometry.RealUpperHalfPlane.toComplex
          (InfoGeometry.Geometry.RealUpperHalfPlane.moebius g τ) =
        g • InfoGeometry.Geometry.RealUpperHalfPlane.toComplex τ)

/-- The canonical Möbius topology index is closed by existing lane theorems. -/
theorem moebiusTopologyOfInformationOwnerTarget :
    MoebiusTopologyOfInformationOwnerTarget := by
  constructor
  · intro A inst₁ inst₂ inst₃ inst₄ o
    exact SelfReference.moebius_parity_restored (o := o)
  · constructor
    · intro P v
      exact
        InfoGeometry.Arithmetic.PrimeBooleanCube.mobius_representedNat_eq_fermionParity P v
    · intro g τ
      exact InfoGeometry.Geometry.RealUpperHalfPlane.toComplex_moebius g τ

end InfoGeometry.Canonical.MoebiusTopologyOfInformation

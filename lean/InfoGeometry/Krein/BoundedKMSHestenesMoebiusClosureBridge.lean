import InfoGeometry.Krein.BoundedKMSHestenesConnesWilsonBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.HestenesMoebiusClosureBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace BigOperators

noncomputable section

/-!
# InfoGeometry.Krein.BoundedKMSHestenesMoebiusClosureBridge

Adapter from the bounded KMS/Hestenes/Connes--Wilson lane to the existing
Möbius closure owner.

This file packages the additional Möbius action witnesses needed to build a
`HestenesMoebiusClosureBridge` from the bounded KMS pipeline.  It does not
derive a Möbius representation theorem.
-/

namespace InfoGeometry.Krein.BoundedKMSHestenesMoebiusClosure

open InfoGeometry.Krein.BoundedKMSHestenesConnesWilson
open InfoGeometry.Krein.HestenesMoebiusClosureBridge
open InfoGeometry.Canonical.HestenesAnalyticity

section Core

variable {E LieAlgebra : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH :=
  inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH :=
  inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH :=
  inferInstance
local instance : CompleteSpace EndH :=
  inferInstance
local instance : SMulCommClass ℝ EndH EndH :=
  inferInstance
local instance : IsScalarTower ℝ EndH EndH :=
  inferInstance

/--
Bounded KMS Hestenes--Möbius closure adapter.

The bounded KMS lane supplies the Connes--Wilson/Ω-volume owner.  The fields in
this structure are exactly the additional Möbius action witnesses required by
`HestenesMoebiusClosureBridge`.
-/
@[rep_depth krein]
structure BoundedKMSHestenesMoebiusClosureBridge
    (Word : Type*) [Fintype Word] [DecidableEq Word] where
  /-- Bounded KMS induced Hestenes--Connes--Wilson owner. -/
  boundedWilson :
    BoundedKMSHestenesConnesWilsonBridge (E := E) (LieAlgebra := LieAlgebra) Word

  /-- Möbius action on vectors in the real doubled carrier. -/
  vectorAction : MoebiusParameter → H₂ → H₂

  /-- The vector action is Krein-isometric. -/
  vectorAction_krein_isometry :
    ∀ (g : MoebiusParameter) (ξ η : H₂),
      KreinSpace.kreinInner (H := H₂) (vectorAction g ξ) (vectorAction g η) =
        KreinSpace.kreinInner (H := H₂) ξ η

  /-- The vacuum apex `Ω` is fixed by the Möbius vector action. -/
  vectorAction_fixes_omega :
    ∀ g : MoebiusParameter,
      vectorAction g
          boundedWilson.toHestenesConnesWilsonBridge.vacuum.omega =
        boundedWilson.toHestenesConnesWilsonBridge.vacuum.omega

  /-- Möbius action on bounded doubled-space operators. -/
  operatorAction : MoebiusParameter → EndH ≃+* EndH

  /-- The Möbius operator action fixes the Hestenes phase axis `K`. -/
  operatorAction_phaseAxis_fixed :
    ∀ g : MoebiusParameter,
      operatorAction g (clockAxis (E := E)) = clockAxis (E := E)

  /-- The Ω-volume state is invariant under the Möbius operator action. -/
  volumeState_operatorAction_invariant :
    ∀ (g : MoebiusParameter) (A : EndH),
      boundedWilson.toHestenesConnesWilsonBridge.volume.volumeState
          (operatorAction g A) =
        boundedWilson.toHestenesConnesWilsonBridge.volume.volumeState A

  /-- Möbius permutation of the finite atom/face layer. -/
  wordAction : MoebiusParameter → Equiv.Perm Word

  /-- Atom weights are invariant under the Möbius face permutation. -/
  atomExpectation_wordAction_invariant :
    ∀ (g : MoebiusParameter) (w : Word),
      boundedWilson.toHestenesConnesWilsonBridge.volume.atomExpectation
          ((wordAction g) w) =
        boundedWilson.toHestenesConnesWilsonBridge.volume.atomExpectation w

  /-- Connes--Wilson holonomy is invariant under Möbius reparameterization. -/
  wilsonHolonomy_wordAction_invariant :
    ∀ (g : MoebiusParameter) (parent child : Word),
      boundedWilson.toHestenesConnesWilsonBridge.wilsonHolonomy
          ((wordAction g) parent) ((wordAction g) child) =
        boundedWilson.toHestenesConnesWilsonBridge.wilsonHolonomy parent child

namespace BoundedKMSHestenesMoebiusClosureBridge

variable {Word : Type*}
variable [Fintype Word] [DecidableEq Word]
variable (B : BoundedKMSHestenesMoebiusClosureBridge
  (E := E) (LieAlgebra := LieAlgebra) Word)

/-- The installed Möbius closure owner induced by the bounded KMS lane. -/
@[rep_depth krein]
def toHestenesMoebiusClosureBridge :
    _root_.InfoGeometry.Krein.HestenesMoebiusClosureBridge.Bridge (E := E) Word where
  wilson := B.boundedWilson.toHestenesConnesWilsonBridge
  vectorAction := B.vectorAction
  vectorAction_krein_isometry := B.vectorAction_krein_isometry
  vectorAction_fixes_omega := B.vectorAction_fixes_omega
  operatorAction := B.operatorAction
  operatorAction_phaseAxis_fixed := B.operatorAction_phaseAxis_fixed
  volumeState_operatorAction_invariant := B.volumeState_operatorAction_invariant
  wordAction := B.wordAction
  atomExpectation_wordAction_invariant := B.atomExpectation_wordAction_invariant
  wilsonHolonomy_wordAction_invariant := B.wilsonHolonomy_wordAction_invariant


/-- The bounded KMS Möbius action preserves the Hestenes natural cone shadow. -/
@[rep_depth krein]
theorem moebius_preserves_naturalCone
    (g : MoebiusParameter) {ξ : H₂}
    (hξ :
      ξ ∈
        B.boundedWilson.toHestenesConnesWilsonBridge.kmsPacket.HestenesNaturalCone) :
    B.vectorAction g ξ ∈
      B.boundedWilson.toHestenesConnesWilsonBridge.kmsPacket.HestenesNaturalCone :=
  B.toHestenesMoebiusClosureBridge.moebius_preserves_naturalCone g hξ

/-- The bounded KMS Möbius action preserves the Krein null cone. -/
@[rep_depth krein]
theorem moebius_preserves_nullCone
    (g : MoebiusParameter) {ξ : H₂}
    (hξ :
      ξ ∈ HestenesNullCone
        B.boundedWilson.toHestenesConnesWilsonBridge.kmsPacket) :
    B.vectorAction g ξ ∈
      HestenesNullCone
        B.boundedWilson.toHestenesConnesWilsonBridge.kmsPacket :=
  B.toHestenesMoebiusClosureBridge.moebius_preserves_nullCone g hξ


end BoundedKMSHestenesMoebiusClosureBridge

end Core

end InfoGeometry.Krein.BoundedKMSHestenesMoebiusClosure

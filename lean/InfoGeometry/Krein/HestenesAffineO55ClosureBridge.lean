import InfoGeometry.Krein.HestenesCPTONNDualityBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace BigOperators

noncomputable section

/-!
# InfoGeometry.Krein.HestenesAffineO55ClosureBridge

Affine `O(5,5)` / `Cl(5,5)` closure interface for the Hestenes--Krein arithmetic
lane.

This file is a post-seal backend interface.  It does not construct a split
Clifford algebra `Cl(5,5)`, prove a universal affine D4 closure theorem, or
derive `O(5,5)` T-duality from first principles.  Those facts belong to a
concrete Clifford/lattice/string backend.

The local purpose is theorem-safe:

* record the affine null-root and central-extension directions as supplied
  bounded operators;
* record the `Cl(5,5)`, affine-extension, and `O(5,5)` backend fields directly;
* inherit Drazin affine-null-root readbacks and nilpotence from the already
  compiled `D4HurwitzArithmeticBridge`;
* preserve Ω-volume and the 24 Hurwitz/D4 root atom readouts under the supplied
  `O(5,5)` action.
-/

namespace InfoGeometry.Krein.HestenesAffineO55ClosureBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.HestenesMoebiusClosureBridge
open InfoGeometry.Krein.HestenesD4HurwitzBridge
open InfoGeometry.Krein.HestenesCPTONNDualityBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance affineO55NormedRing : NormedRing EndH := inferInstance
noncomputable local instance affineO55NormedAlgebra : NormedAlgebra ℝ EndH :=
  inferInstance
noncomputable local instance affineO55NormedAlgebraRat : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance affineO55TopologicalRing : IsTopologicalRing EndH := inferInstance
local instance affineO55CompleteSpace : CompleteSpace EndH := inferInstance
local instance affineO55SMulCommClass : SMulCommClass ℝ EndH EndH := inferInstance
local instance affineO55IsScalarTower : IsScalarTower ℝ EndH EndH := inferInstance

/--
Affine `O(5,5)` closure bridge over the installed CPT / D4-Hurwitz backend.

The fields are explicit backend data. A concrete backend supplies the
actual `Cl(5,5)` substrate and `O(5,5)` isometry law; this bridge proves only
the local consequences that follow from those fields and from already-owned
Hestenes--Krein, Drazin, and Ω-volume APIs.
-/
@[rep_depth krein]
structure Bridge where
  /-- CPT / `O(N,N)` duality layer over the D4/Hurwitz backend. -/
  duality : _root_.InfoGeometry.Krein.HestenesCPTONNDualityBridge.Bridge (E := E)

  /-- Supplied bounded representative of the dynamic `Cl(5,5)` substrate. -/
  clifford55Substrate : EndH

  /-- Supplied affine null-root direction. -/
  affineNullRoot : EndH

  /-- Supplied central-extension direction. -/
  centralExtension : EndH

  /-- Supplied vector-side `O(5,5)` action on the doubled carrier. -/
  o55VectorAction : EndH

  /-- The supplied `O(5,5)` vector action is Krein-isometric. -/
  o55VectorAction_krein_isometry :
    KreinSpace.IsKreinIsometry (H := H₂) o55VectorAction

  /-- Supplied operator-side `O(5,5)` automorphism. -/
  o55OperatorAction : EndH ≃+* EndH

  /-- The supplied `O(5,5)` action preserves the Ω-volume state. -/
  o55_volumeState_invariant :
    ∀ A : EndH,
      duality.arithmetic.moebius.wilson.volume.volumeState (o55OperatorAction A) =
        duality.arithmetic.moebius.wilson.volume.volumeState A

  /-- Root permutation induced by the supplied `O(5,5)` action. -/
  o55RootAction : Equiv.Perm (Fin 24)

  /-- The supplied `O(5,5)` action permutes the 24 D4/Hurwitz root operators. -/
  o55_maps_hurwitzRoots :
    ∀ i : Fin 24,
      o55OperatorAction (duality.arithmetic.hurwitzRoot i) =
        duality.arithmetic.hurwitzRoot (o55RootAction i)


namespace Bridge

variable (B : Bridge (E := E))

/-- Predicate readback for `O(5,5)` invariance via Ω-volume. -/
@[rep_depth projective]
def IsO55Invariant : Prop :=
  ∀ A : EndH,
    B.duality.arithmetic.moebius.wilson.volume.volumeState (B.o55OperatorAction A) =
      B.duality.arithmetic.moebius.wilson.volume.volumeState A

/-- The supplied `O(5,5)` vector action preserves the Hestenes natural cone shadow. -/
@[rep_depth krein]
theorem o55_preserves_naturalCone {ξ : H₂}
    (hξ : ξ ∈ B.duality.arithmetic.moebius.wilson.kmsPacket.HestenesNaturalCone) :
    B.o55VectorAction ξ ∈
      B.duality.arithmetic.moebius.wilson.kmsPacket.HestenesNaturalCone := by
  change 0 ≤ KreinSpace.kreinInner (H := H₂) ξ ξ at hξ
  change 0 ≤ KreinSpace.kreinInner (H := H₂)
    (B.o55VectorAction ξ) (B.o55VectorAction ξ)
  rw [B.o55VectorAction_krein_isometry]
  simpa using hξ

/-! The supplied vector action now has an explicit operator-level Krein
adjoint law.  This is the honest compatibility interface for the generic
`kreinConjugation` calculus; it does not identify the supplied operator-side
automorphism with conjugation by this vector action. -/

@[rep_depth krein]
theorem o55VectorAction_kreinAdjoint_comp_self :
    (KreinSpace.kreinAdjoint (H := H₂) B.o55VectorAction).comp
        B.o55VectorAction = ContinuousLinearMap.id ℝ H₂ :=
  (KreinSpace.isKreinIsometry_iff_star_comp_self
    (H := H₂) B.o55VectorAction).mp B.o55VectorAction_krein_isometry

/-- The supplied `O(5,5)` vector action preserves the Krein null cone. -/
@[rep_depth krein]
theorem o55_preserves_nullCone {ξ : H₂}
    (hξ : ξ ∈ HestenesNullCone B.duality.arithmetic.moebius.wilson.kmsPacket) :
    B.o55VectorAction ξ ∈
      HestenesNullCone B.duality.arithmetic.moebius.wilson.kmsPacket := by
  change KreinSpace.kreinInner (H := H₂) ξ ξ = 0 at hξ
  change KreinSpace.kreinInner (H := H₂)
    (B.o55VectorAction ξ) (B.o55VectorAction ξ) = 0
  rw [B.o55VectorAction_krein_isometry]
  simpa using hξ

/-- The supplied `O(5,5)` action preserves the Ω-volume readout. -/
@[rep_depth operator]
theorem volumeState_o55_invariant (A : EndH) :
    B.duality.arithmetic.moebius.wilson.volume.volumeState (B.o55OperatorAction A) =
      B.duality.arithmetic.moebius.wilson.volume.volumeState A :=
  B.o55_volumeState_invariant A

/-- The supplied `O(5,5)` action permutes D4/Hurwitz roots. -/
@[rep_depth operator]
theorem o55_hurwitzRoot_covariant (i : Fin 24) :
    B.o55OperatorAction (B.duality.arithmetic.hurwitzRoot i) =
      B.duality.arithmetic.hurwitzRoot (B.o55RootAction i) :=
  B.o55_maps_hurwitzRoots i

/-- The Ω-weight of D4/Hurwitz roots is invariant under the supplied `O(5,5)` action. -/
@[rep_depth operator]
theorem hurwitzRoot_expectation_o55_invariant (i : Fin 24) :
    B.duality.arithmetic.moebius.wilson.volume.volumeState
        (B.duality.arithmetic.hurwitzRoot (B.o55RootAction i)) =
      B.duality.arithmetic.moebius.wilson.volume.volumeState
        (B.duality.arithmetic.hurwitzRoot i) := by
  rw [← B.o55_hurwitzRoot_covariant i]
  exact B.volumeState_o55_invariant (B.duality.arithmetic.hurwitzRoot i)

/-- Total D4/Hurwitz Ω-volume remains normalized in the affine `O(5,5)` layer. -/
@[rep_depth operator]
theorem total_hurwitz_root_expectation_is_unity :
    (∑ i : Fin 24,
      B.duality.arithmetic.moebius.wilson.volume.volumeState
        (B.duality.arithmetic.hurwitzRoot i)) = 1 :=
  B.duality.arithmetic.total_hurwitz_root_expectation_is_unity

/-- Total D4/Hurwitz Ω-volume is invariant under the supplied `O(5,5)` action. -/
@[rep_depth operator]
theorem total_hurwitz_root_expectation_o55_invariant :
    (∑ i : Fin 24,
      B.duality.arithmetic.moebius.wilson.volume.volumeState
        (B.duality.arithmetic.hurwitzRoot (B.o55RootAction i))) = 1 := by
  calc
    (∑ i : Fin 24,
      B.duality.arithmetic.moebius.wilson.volume.volumeState
        (B.duality.arithmetic.hurwitzRoot (B.o55RootAction i)))
        = ∑ i : Fin 24,
            B.duality.arithmetic.moebius.wilson.volume.volumeState
              (B.duality.arithmetic.hurwitzRoot i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact B.hurwitzRoot_expectation_o55_invariant i
    _ = 1 := B.total_hurwitz_root_expectation_is_unity

/-- Same-arrow nilpotence for the positive affine null root. -/
@[rep_depth operator]
theorem affineNullRootPlus_same_arrow_nilpotent (A C : EndH) :
    B.duality.arithmetic.affineNullRootPlus A *
        B.duality.arithmetic.affineNullRootPlus C = 0 :=
  B.duality.arithmetic.affineNullRootPlus_mul_affineNullRootPlus_eq_zero A C

/-- Same-arrow nilpotence for the negative affine null root. -/
@[rep_depth operator]
theorem affineNullRootMinus_same_arrow_nilpotent (A C : EndH) :
    B.duality.arithmetic.affineNullRootMinus A *
        B.duality.arithmetic.affineNullRootMinus C = 0 :=
  B.duality.arithmetic.affineNullRootMinus_mul_affineNullRootMinus_eq_zero A C

end Bridge

end Core

end InfoGeometry.Krein.HestenesAffineO55ClosureBridge

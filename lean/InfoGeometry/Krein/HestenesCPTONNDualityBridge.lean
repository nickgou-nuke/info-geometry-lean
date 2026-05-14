import InfoGeometry.Krein.HestenesD4HurwitzBridge
import InfoGeometry.Canonical.HestenesRealStructures
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace BigOperators

noncomputable section

set_option linter.dupNamespace false

/-!
# InfoGeometry.Krein.HestenesCPTONNDualityBridge

Witness-gated CPT / `O(N,N)` duality socket for the Hestenes--Krein arithmetic
closure lane.

This file deliberately does **not** construct the full continuous `O(N,N)` group,
prove T-duality, or derive a CPT theorem for arbitrary Type-III nets.  Those are
backend theorems.  The purpose here is narrower and theorem-safe:

* package a supplied CPT/Tomita reflection `θ` on the real doubled carrier;
* record that `θ` is Krein-isometric, involutive, fixes the vacuum `Ω`, and
  flips the Hestenes phase axis `K` by conjugation;
* package a supplied `O(N,N)`-style arithmetic duality action on the operator
  algebra and on the 24 D4/Hurwitz root atoms;
* prove the local consequences used by the already sealed Hestenes--Krein,
  Connes--Wilson, Möbius, and D4/Hurwitz pipelines.

Thus `θ` and `O(N,N)` are installed as calibrated symmetry sockets, not as new
unproved primitives contaminating the core DAG.
-/

namespace InfoGeometry.Krein.HestenesCPTONNDualityBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.HestenesModularKMSBridge
open InfoGeometry.Krein.HestenesMoebiusClosureBridge
open InfoGeometry.Krein.HestenesD4HurwitzBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance cptONNNormedRing : NormedRing EndH := inferInstance
noncomputable local instance cptONNNormedAlgebra : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance cptONNNormedAlgebraRat : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance cptONNTopologicalRing : IsTopologicalRing EndH := inferInstance
local instance cptONNCompleteSpace : CompleteSpace EndH := inferInstance
local instance cptONNSMulCommClass : SMulCommClass ℝ EndH EndH := inferInstance
local instance cptONNIsScalarTower : IsScalarTower ℝ EndH EndH := inferInstance

/--
CPT and `O(N,N)` duality bridge over the already installed D4/Hurwitz arithmetic
backend.

`θ` is the supplied real CPT/Tomita reflection.  `onnDualityAction` is a supplied
operator-algebra automorphism standing for the selected `O(N,N)` or
`O(N,N,ℤ)` duality move in the concrete backend.
-/
@[rep_depth krein]
structure HestenesCPTONNDualityBridge where
  /-- The arithmetic D4/Hurwitz backend already tied to Möbius and Ω-volume. -/
  arithmetic : D4HurwitzArithmeticBridge (E := E)

  /-- CPT/Tomita reflection on the real doubled carrier. -/
  theta : EndH

  /-- CPT is involutive at the real doubled-carrier level. -/
  theta_involutive : theta * theta = (1 : EndH)

  /-- CPT preserves the Krein bilinear metric. -/
  theta_krein_isometry : KreinSpace.IsKreinIsometry (H := H₂) theta

  /-- CPT fixes the vacuum apex `Ω`. -/
  theta_fixes_omega :
    theta arithmetic.moebius.wilson.vacuum.omega =
      arithmetic.moebius.wilson.vacuum.omega

  /-- CPT flips the Hestenes phase axis by conjugation: `θ K θ = -K`. -/
  theta_phaseAxis_flip :
    theta * clockAxis (E := E) * theta = -(clockAxis (E := E))

  /-- The Ω-volume state is invariant under CPT conjugation. -/
  theta_volumeState_invariant :
    ∀ A : EndH,
      arithmetic.moebius.wilson.volume.volumeState (theta * A * theta) =
        arithmetic.moebius.wilson.volume.volumeState A

  /-- CPT permutation of the 24 D4/Hurwitz root atoms. -/
  thetaRootAction : Equiv.Perm (Fin 24)

  /-- CPT conjugation permutes the supplied D4/Hurwitz root operators. -/
  theta_maps_hurwitzRoots :
    ∀ i : Fin 24,
      theta * arithmetic.hurwitzRoot i * theta =
        arithmetic.hurwitzRoot (thetaRootAction i)

  /-- Selected `O(N,N)`/T-duality operator-algebra automorphism. -/
  onnDualityAction : EndH ≃+* EndH

  /-- The selected duality action preserves the Ω-volume state. -/
  onn_volumeState_invariant :
    ∀ A : EndH,
      arithmetic.moebius.wilson.volume.volumeState (onnDualityAction A) =
        arithmetic.moebius.wilson.volume.volumeState A

  /-- Root permutation induced by the selected `O(N,N)`/T-duality action. -/
  onnRootAction : Equiv.Perm (Fin 24)

  /-- The selected duality action permutes the D4/Hurwitz root operators. -/
  onn_maps_hurwitzRoots :
    ∀ i : Fin 24,
      onnDualityAction (arithmetic.hurwitzRoot i) =
        arithmetic.hurwitzRoot (onnRootAction i)

  /-- Backend certificate that `onnDualityAction` is the intended `O(N,N)` move. -/
  onn_duality_certificate : Prop

  /-- Evidence for the `O(N,N)` backend certificate. -/
  onn_duality_holds : onn_duality_certificate

  /-- Backend certificate that `theta` realizes the intended CPT/Tomita symmetry. -/
  cpt_certificate : Prop

  /-- Evidence for the CPT/Tomita certificate. -/
  cpt_holds : cpt_certificate

namespace HestenesCPTONNDualityBridge

variable (B : HestenesCPTONNDualityBridge (E := E))

/-- CPT conjugation on bounded doubled-space operators. -/
@[rep_depth operator]
def thetaConjugate (A : EndH) : EndH :=
  B.theta * A * B.theta

/-- Readback: CPT is an involution. -/
@[rep_depth krein]
theorem theta_sq_eq_one :
    B.theta * B.theta = (1 : EndH) :=
  B.theta_involutive

/-- Readback: CPT fixes the vacuum vector. -/
@[rep_depth krein]
theorem theta_omega_eq_omega :
    B.theta B.arithmetic.moebius.wilson.vacuum.omega =
      B.arithmetic.moebius.wilson.vacuum.omega :=
  B.theta_fixes_omega

/-- CPT preserves the Hestenes natural cone shadow. -/
@[rep_depth krein]
theorem theta_preserves_naturalCone {ξ : H₂}
    (hξ : ξ ∈ B.arithmetic.moebius.wilson.kmsPacket.HestenesNaturalCone) :
    B.theta ξ ∈ B.arithmetic.moebius.wilson.kmsPacket.HestenesNaturalCone := by
  change 0 ≤ KreinSpace.kreinInner (H := H₂) ξ ξ at hξ
  change 0 ≤ KreinSpace.kreinInner (H := H₂) (B.theta ξ) (B.theta ξ)
  rw [B.theta_krein_isometry]
  exact hξ

/-- CPT preserves the Krein null cone. -/
@[rep_depth krein]
theorem theta_preserves_nullCone {ξ : H₂}
    (hξ : ξ ∈ HestenesNullCone B.arithmetic.moebius.wilson.kmsPacket) :
    B.theta ξ ∈ HestenesNullCone B.arithmetic.moebius.wilson.kmsPacket := by
  change KreinSpace.kreinInner (H := H₂) ξ ξ = 0 at hξ
  change KreinSpace.kreinInner (H := H₂) (B.theta ξ) (B.theta ξ) = 0
  rw [B.theta_krein_isometry]
  exact hξ

/-- CPT keeps the vacuum normalized. -/
@[rep_depth krein]
theorem theta_vacuum_norm_invariant :
    KreinSpace.kreinInner (H := H₂)
        (B.theta B.arithmetic.moebius.wilson.vacuum.omega)
        (B.theta B.arithmetic.moebius.wilson.vacuum.omega) = 1 := by
  rw [B.theta_krein_isometry]
  exact B.arithmetic.moebius.wilson.vacuum.omega_normalized

/-- CPT flips the Hestenes phase axis `K` by conjugation. -/
@[rep_depth krein]
theorem theta_phaseAxis_conjugation :
    B.thetaConjugate (clockAxis (E := E)) = -(clockAxis (E := E)) := by
  exact B.theta_phaseAxis_flip

/-- The Ω-volume readout is CPT invariant. -/
@[rep_depth operator]
theorem volumeState_theta_invariant (A : EndH) :
    B.arithmetic.moebius.wilson.volume.volumeState (B.thetaConjugate A) =
      B.arithmetic.moebius.wilson.volume.volumeState A :=
  B.theta_volumeState_invariant A

/-- CPT conjugation permutes D4/Hurwitz roots. -/
@[rep_depth operator]
theorem theta_hurwitzRoot_covariant (i : Fin 24) :
    B.thetaConjugate (B.arithmetic.hurwitzRoot i) =
      B.arithmetic.hurwitzRoot (B.thetaRootAction i) :=
  B.theta_maps_hurwitzRoots i

/-- The Ω-weight of D4/Hurwitz roots is CPT invariant. -/
@[rep_depth operator]
theorem hurwitzRoot_expectation_theta_invariant (i : Fin 24) :
    B.arithmetic.moebius.wilson.volume.volumeState
        (B.arithmetic.hurwitzRoot (B.thetaRootAction i)) =
      B.arithmetic.moebius.wilson.volume.volumeState (B.arithmetic.hurwitzRoot i) := by
  rw [← B.theta_hurwitzRoot_covariant i]
  exact B.volumeState_theta_invariant (B.arithmetic.hurwitzRoot i)

/-- Readback of the selected `O(N,N)`/T-duality certificate. -/
@[rep_depth krein]
theorem onn_duality_readback :
    B.onn_duality_certificate :=
  B.onn_duality_holds

/-- Readback of the selected CPT/Tomita certificate. -/
@[rep_depth krein]
theorem cpt_readback :
    B.cpt_certificate :=
  B.cpt_holds

/-- The selected `O(N,N)`/T-duality action preserves the Ω-volume readout. -/
@[rep_depth operator]
theorem volumeState_onn_invariant (A : EndH) :
    B.arithmetic.moebius.wilson.volume.volumeState (B.onnDualityAction A) =
      B.arithmetic.moebius.wilson.volume.volumeState A :=
  B.onn_volumeState_invariant A

/-- The selected `O(N,N)`/T-duality action permutes D4/Hurwitz roots. -/
@[rep_depth operator]
theorem onn_hurwitzRoot_covariant (i : Fin 24) :
    B.onnDualityAction (B.arithmetic.hurwitzRoot i) =
      B.arithmetic.hurwitzRoot (B.onnRootAction i) :=
  B.onn_maps_hurwitzRoots i

/-- The Ω-weight of D4/Hurwitz roots is invariant under the selected duality move. -/
@[rep_depth operator]
theorem hurwitzRoot_expectation_onn_invariant (i : Fin 24) :
    B.arithmetic.moebius.wilson.volume.volumeState
        (B.arithmetic.hurwitzRoot (B.onnRootAction i)) =
      B.arithmetic.moebius.wilson.volume.volumeState (B.arithmetic.hurwitzRoot i) := by
  rw [← B.onn_hurwitzRoot_covariant i]
  exact B.volumeState_onn_invariant (B.arithmetic.hurwitzRoot i)

/-- Total D4/Hurwitz Ω-volume is invariant under CPT. -/
@[rep_depth operator]
theorem total_hurwitz_root_expectation_theta_invariant :
    (∑ i : Fin 24,
      B.arithmetic.moebius.wilson.volume.volumeState
        (B.arithmetic.hurwitzRoot (B.thetaRootAction i))) = 1 := by
  calc
    (∑ i : Fin 24,
      B.arithmetic.moebius.wilson.volume.volumeState
        (B.arithmetic.hurwitzRoot (B.thetaRootAction i)))
        = ∑ i : Fin 24,
            B.arithmetic.moebius.wilson.volume.volumeState
              (B.arithmetic.hurwitzRoot i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact B.hurwitzRoot_expectation_theta_invariant i
    _ = 1 := B.arithmetic.total_hurwitz_root_expectation_is_unity

/-- Total D4/Hurwitz Ω-volume is invariant under the selected `O(N,N)` move. -/
@[rep_depth operator]
theorem total_hurwitz_root_expectation_onn_invariant :
    (∑ i : Fin 24,
      B.arithmetic.moebius.wilson.volume.volumeState
        (B.arithmetic.hurwitzRoot (B.onnRootAction i))) = 1 := by
  calc
    (∑ i : Fin 24,
      B.arithmetic.moebius.wilson.volume.volumeState
        (B.arithmetic.hurwitzRoot (B.onnRootAction i)))
        = ∑ i : Fin 24,
            B.arithmetic.moebius.wilson.volume.volumeState
              (B.arithmetic.hurwitzRoot i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact B.hurwitzRoot_expectation_onn_invariant i
    _ = 1 := B.arithmetic.total_hurwitz_root_expectation_is_unity

end HestenesCPTONNDualityBridge

end Core

end InfoGeometry.Krein.HestenesCPTONNDualityBridge

end

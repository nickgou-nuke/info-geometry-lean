import InfoGeometry.Krein.KreinSpace
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Krein.HestenesKreinNaturalConeBridge

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.OperatorThermodynamics

section Core

variable {H NormalPositive Op : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H]

/--
Standard-form natural-cone socket over a Hestenes/Krein carrier.

The axioms enforce that:
1. The eval readout equals the Krein inner product of the acted cone vector.
2. Cone vectors belong to the natural cone.
3. The natural cone is fixed by the Krein/Tomita reflection.
4. The natural cone is self-dual.
-/
@[rep_depth krein]
structure HestenesKreinNaturalConeBridge where
  naturalCone : Set H
  coneVector : NormalPositive → H
  act : Op → H → H
  eval : NormalPositive → Op → ℝ
  eval_eq_krein_vector_readout :
    ∀ (ω : NormalPositive) (A : Op),
      eval ω A =
        KreinSpace.kreinInner (H := H) (act A (coneVector ω)) (coneVector ω)
  coneVector_mem : ∀ (ω : NormalPositive), coneVector ω ∈ naturalCone
  J_fixes_cone :
    ∀ (ξ : H), ξ ∈ naturalCone → KreinSpace.jCLM (H := H) ξ = ξ
  naturalCone_self_dual :
    naturalCone = {ξ | ∀ η ∈ naturalCone, ⟪ξ, η⟫_ℝ ≥ 0}

namespace HestenesKreinNaturalConeBridge

variable (B : HestenesKreinNaturalConeBridge (H := H) (NormalPositive := NormalPositive)
  (Op := Op))

@[rep_depth krein]
theorem eval_eq_krein_vector_readout_thm
    (ω : NormalPositive) (A : Op) :
    B.eval ω A =
      KreinSpace.kreinInner (H := H) (B.act A (B.coneVector ω)) (B.coneVector ω) :=
  B.eval_eq_krein_vector_readout ω A

@[rep_depth krein]
theorem coneVector_mem_thm
    (ω : NormalPositive) :
    B.coneVector ω ∈ B.naturalCone :=
  B.coneVector_mem ω

@[rep_depth krein]
theorem J_fixes_cone_thm
    (ξ : H)
    (hξ : ξ ∈ B.naturalCone) :
    KreinSpace.jCLM (H := H) ξ = ξ :=
  B.J_fixes_cone ξ hξ

@[rep_depth krein]
theorem naturalCone_self_dual_thm :
    B.naturalCone = {ξ | ∀ η ∈ B.naturalCone, ⟪ξ, η⟫_ℝ ≥ 0} :=
  B.naturalCone_self_dual

end HestenesKreinNaturalConeBridge

/--
Distinguished vacuum/state representative inside the supplied standard-form
natural cone.
-/
@[rep_depth krein]
structure HestenesKreinNaturalConeVacuum where
  natural :
    HestenesKreinNaturalConeBridge (H := H) (NormalPositive := NormalPositive) (Op := Op)
  Omega : H
  Omega_mem_naturalCone : Omega ∈ natural.naturalCone
  Omega_fixed_by_J : KreinSpace.jCLM (H := H) Omega = Omega
  Omega_normalized : KreinSpace.kreinInner (H := H) Omega Omega = 1

namespace HestenesKreinNaturalConeVacuum

variable (V : HestenesKreinNaturalConeVacuum (H := H)
  (NormalPositive := NormalPositive) (Op := Op))

@[rep_depth krein]
theorem Omega_mem_naturalCone_thm :
    V.Omega ∈ V.natural.naturalCone :=
  V.Omega_mem_naturalCone

@[rep_depth krein]
theorem Omega_fixed_by_J_thm :
    KreinSpace.jCLM (H := H) V.Omega = V.Omega :=
  V.Omega_fixed_by_J

@[rep_depth krein]
theorem Omega_normalized_thm :
    KreinSpace.kreinInner (H := H) V.Omega V.Omega = 1 :=
  V.Omega_normalized

end HestenesKreinNaturalConeVacuum

section KMS

variable [Mul Op]

/--
KMS adapter for a Hestenes/Krein natural-cone readout.
-/
@[rep_depth krein]
structure HestenesKreinNaturalConeKMSBridge where
  vacuum :
    HestenesKreinNaturalConeVacuum (H := H)
      (NormalPositive := NormalPositive) (Op := Op)
  omegaState : NormalPositive
  flow : OperatorFlow Op
  beta : ℝ
  kms : KMSState Op flow beta
  coneVector_eq_Omega :
    vacuum.natural.coneVector omegaState = vacuum.Omega
  complexEval_eq_realConeEval :
    ∀ (A : Op), kms.state.eval A = (vacuum.natural.eval omegaState A : ℂ)

namespace HestenesKreinNaturalConeKMSBridge

variable (B : HestenesKreinNaturalConeKMSBridge (H := H)
  (NormalPositive := NormalPositive) (Op := Op))

@[rep_depth krein]
theorem coneVector_eq_Omega_thm :
    B.vacuum.natural.coneVector B.omegaState = B.vacuum.Omega :=
  B.coneVector_eq_Omega

@[rep_depth krein]
theorem complexEval_eq_realConeEval_thm
    (A : Op) :
    B.kms.state.eval A = (B.vacuum.natural.eval B.omegaState A : ℂ) :=
  B.complexEval_eq_realConeEval A

@[rep_depth krein]
theorem complexEval_eq_vacuum_readout_thm
    (A : Op) :
    B.kms.state.eval A =
      (KreinSpace.kreinInner (H := H) (B.vacuum.natural.act A B.vacuum.Omega)
        B.vacuum.Omega : ℂ) := by
  calc
    B.kms.state.eval A = (B.vacuum.natural.eval B.omegaState A : ℂ) :=
      B.complexEval_eq_realConeEval A
    _ =
        (KreinSpace.kreinInner (H := H)
          (B.vacuum.natural.act A (B.vacuum.natural.coneVector B.omegaState))
          (B.vacuum.natural.coneVector B.omegaState) : ℂ) := by
          rw [B.vacuum.natural.eval_eq_krein_vector_readout B.omegaState A]
    _ =
        (KreinSpace.kreinInner (H := H) (B.vacuum.natural.act A B.vacuum.Omega)
          B.vacuum.Omega : ℂ) := by
          rw [B.coneVector_eq_Omega]

@[rep_depth krein]
theorem kms_flow_invariant_thm
    (t : ℝ) (A : Op) :
    B.kms.state.eval (B.flow.flow t A) = B.kms.state.eval A :=
  B.kms.invariant t A

@[rep_depth krein]
theorem kms_boundary_holds_thm :
    B.kms.kms_boundary_condition :=
  B.kms.kms_boundary_holds

end HestenesKreinNaturalConeKMSBridge

end KMS

/--
Vector-side flow carrier with a supplied Krein-isometry law.
-/
@[rep_depth krein]
structure KreinIsometricVectorFlow where
  vectorFlow : ℝ → H →L[ℝ] H
  vectorFlow_kreinIsometry :
    ∀ t : ℝ, KreinSpace.IsKreinIsometry (H := H) (vectorFlow t)

namespace KreinIsometricVectorFlow

variable (F : KreinIsometricVectorFlow (H := H))

@[rep_depth krein]
theorem vectorFlow_preserves_krein_null_thm
    (t : ℝ) (ξ : H)
    (hξ : KreinSpace.kreinInner (H := H) ξ ξ = 0) :
    KreinSpace.kreinInner (H := H) (F.vectorFlow t ξ) (F.vectorFlow t ξ) = 0 := by
  rw [F.vectorFlow_kreinIsometry t ξ ξ, hξ]

end KreinIsometricVectorFlow

end Core

end InfoGeometry.Krein.HestenesKreinNaturalConeBridge

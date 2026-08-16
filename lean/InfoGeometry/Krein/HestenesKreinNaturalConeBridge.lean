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

The `naturalCone` field is not defined as the Krein nonnegative/light cone.
It is supplied as the candidate standard-form natural positive cone.  The
analytic/operator-algebraic theorem `M_*^+ ≃ P` is not represented by proof
fields.  Its cone-vector, readout, and Tomita-fixpoint laws are theorem-owner
debt below.
-/
@[rep_depth krein]
structure Bridge where
  /-- Candidate standard-form natural positive cone. -/
  naturalCone : Set H

  /-- Cone vector representative of a normal positive functional. -/
  coneVector : NormalPositive → H

  /-- Operator action on the Hestenes/Krein carrier. -/
  act : Op → H → H

  /-- Real state/readout evaluation. -/
  eval : NormalPositive → Op → ℝ

  /-- The supplied cone-vector readout law. -/
  eval_eq_krein_vector_readout_law :
    ∀ (ω : NormalPositive) (A : Op),
      eval ω A =
        KreinSpace.kreinInner (H := H) (act A (coneVector ω)) (coneVector ω)

  /-- The supplied cone membership law. -/
  coneVector_mem_law :
    ∀ (ω : NormalPositive), coneVector ω ∈ naturalCone

  /-- The supplied Tomita/Krein fixpoint law. -/
  J_fixes_cone_law :
    ∀ (ξ : H), ξ ∈ naturalCone → KreinSpace.jCLM (H := H) ξ = ξ

  /-- The natural cone is self-dual for the real Hilbert pairing.
  Takesaki (2003), Theory of Operator Algebras II, §IX.1. -/
  naturalCone_self_dual_holds : naturalCone = {ξ | ∀ η ∈ naturalCone, ⟪ξ, η⟫_ℝ ≥ 0}

namespace Bridge

variable (B : Bridge (H := H) (NormalPositive := NormalPositive)
  (Op := Op))


/-- Theorem owner: the natural cone is fixed pointwise by the Krein/Tomita reflection. -/
@[rep_depth krein]
theorem J_fixes_cone
    (ξ : H)
    (hξ : ξ ∈ B.naturalCone) :
    KreinSpace.jCLM (H := H) ξ = ξ :=
  B.J_fixes_cone_law ξ hξ

/-- Cone representatives are fixed by the Krein/Tomita reflection. -/
@[rep_depth krein]
theorem J_fixes_coneVector
    (ω : NormalPositive) :
    KreinSpace.jCLM (H := H) (B.coneVector ω) = B.coneVector ω :=
  B.J_fixes_cone_law (B.coneVector ω) (B.coneVector_mem_law ω)

/-- The supplied natural cone is self-dual for the real Hilbert pairing. -/
@[rep_depth krein]
theorem naturalCone_self_dual :
    B.naturalCone = {ξ | ∀ η ∈ B.naturalCone, ⟪ξ, η⟫_ℝ ≥ 0} :=
  B.naturalCone_self_dual_holds

end Bridge

/--
Distinguished vacuum/state representative inside the supplied standard-form
natural cone.

`Omega` is not called an apex: the cone apex is `0`; `Omega` is a selected
state/weight representative.
-/
@[rep_depth krein]
abbrev HestenesKreinNaturalConeVacuum :=
  { data :
      Bridge (H := H) (NormalPositive := NormalPositive) (Op := Op) × H //
    data.2 ∈ data.1.naturalCone ∧
    KreinSpace.jCLM (H := H) data.2 = data.2 ∧
    KreinSpace.kreinInner (H := H) data.2 data.2 = 1 }

namespace HestenesKreinNaturalConeVacuum

abbrev natural
    (V : HestenesKreinNaturalConeVacuum (H := H)
      (NormalPositive := NormalPositive) (Op := Op)) :
    Bridge (H := H) (NormalPositive := NormalPositive) (Op := Op) := V.1.1

abbrev Omega
    (V : HestenesKreinNaturalConeVacuum (H := H)
      (NormalPositive := NormalPositive) (Op := Op)) : H := V.1.2

abbrev omega_in_cone
    (V : HestenesKreinNaturalConeVacuum (H := H)
      (NormalPositive := NormalPositive) (Op := Op)) :
    V.Omega ∈ V.natural.naturalCone := V.2.1

abbrev J_fixes_omega
    (V : HestenesKreinNaturalConeVacuum (H := H)
      (NormalPositive := NormalPositive) (Op := Op)) :
    KreinSpace.jCLM (H := H) V.Omega = V.Omega := V.2.2.1

abbrev omega_normalized
    (V : HestenesKreinNaturalConeVacuum (H := H)
      (NormalPositive := NormalPositive) (Op := Op)) :
    KreinSpace.kreinInner (H := H) V.Omega V.Omega = 1 := V.2.2.2

end HestenesKreinNaturalConeVacuum

section KMS

variable [AddMonoid Op] [Monoid Op]

/--
KMS adapter for a Hestenes/Krein natural-cone readout.

The geometric real readout and the complex KMS state are connected by an
explicit theorem owner below.  The analytic strip condition remains the
existing `OperatorThermodynamics.KMSState` property.
-/
@[rep_depth krein]
structure HestenesKreinNaturalConeKMSBridge where
  /-- Natural-cone vacuum carrier. -/
  vacuum :
    HestenesKreinNaturalConeVacuum (H := H)
      (NormalPositive := NormalPositive) (Op := Op)

  /-- Selected normal-positive functional represented by the vacuum. -/
  omegaState : NormalPositive

  /-- Operator flow used by the existing KMS API. -/
  flow : OperatorFlow Op

  /-- Inverse temperature. -/
  beta : ℝ

  /-- Existing complex KMS state/property. -/
  kms : KMSState Op flow beta

  /-- The selected state is calibrated to the vacuum vector `Ω`. -/
  coneVector_eq_Omega_law :
    vacuum.natural.coneVector omegaState = vacuum.Omega

  /-- The complex KMS readout equals the real cone readout. -/
  complexEval_eq_realConeEval_law :
    ∀ (A : Op), kms.state.eval A = (vacuum.natural.eval omegaState A : ℂ)

namespace HestenesKreinNaturalConeKMSBridge

variable (B : HestenesKreinNaturalConeKMSBridge (H := H)
  (NormalPositive := NormalPositive) (Op := Op))

/-- The complex KMS readout is represented by the vacuum vector, after calibration. -/
@[rep_depth krein]
theorem complexEval_eq_vacuum_readout
    (A : Op) :
    B.kms.state.eval A =
      (KreinSpace.kreinInner (H := H) (B.vacuum.natural.act A B.vacuum.Omega)
        B.vacuum.Omega : ℂ) := by
  calc
    B.kms.state.eval A = (B.vacuum.natural.eval B.omegaState A : ℂ) :=
      B.complexEval_eq_realConeEval_law A
    _ =
        (KreinSpace.kreinInner (H := H)
          (B.vacuum.natural.act A (B.vacuum.natural.coneVector B.omegaState))
          (B.vacuum.natural.coneVector B.omegaState) : ℂ) := by
          rw [B.vacuum.natural.eval_eq_krein_vector_readout_law B.omegaState A]
    _ =
        (KreinSpace.kreinInner (H := H) (B.vacuum.natural.act A B.vacuum.Omega)
          B.vacuum.Omega : ℂ) := by
          rw [B.coneVector_eq_Omega_law]


end HestenesKreinNaturalConeKMSBridge

end KMS

/--
Vector-side flow carrier with a supplied Krein-isometry law.

This is the correct property surface for null-cone preservation; it is not
derived from an operator flow or from `K² = -1`.
-/
@[rep_depth krein]
structure KreinIsometricVectorFlow where
  /-- Vector-side flow. -/
  vectorFlow : ℝ → H →L[ℝ] H

  /-- Each time slice preserves the Krein form. -/
  vectorFlow_kreinIsometry :
    ∀ t : ℝ, KreinSpace.IsKreinIsometry (H := H) (vectorFlow t)

namespace KreinIsometricVectorFlow

variable (F : KreinIsometricVectorFlow (H := H))

/-- A Krein-isometric vector flow preserves the Krein null cone. -/
@[rep_depth krein]
theorem vectorFlow_preserves_krein_null
    (t : ℝ) (ξ : H)
    (hξ : KreinSpace.kreinInner (H := H) ξ ξ = 0) :
    KreinSpace.kreinInner (H := H) (F.vectorFlow t ξ) (F.vectorFlow t ξ) = 0 := by
  rw [F.vectorFlow_kreinIsometry t ξ ξ, hξ]

end KreinIsometricVectorFlow

end Core

end InfoGeometry.Krein.HestenesKreinNaturalConeBridge

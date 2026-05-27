import InfoGeometry.Canonical.StandardFormNaturalConeBridge
import InfoGeometry.Krein.HestenesKreinNaturalConeBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Krein.HestenesStandardFormNaturalConeAdapter

open InfoGeometry.Canonical.StandardFormNaturalConeBridge
open InfoGeometry.Krein.HestenesKreinNaturalConeBridge

section Core

variable {H NormalPositive Op : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H]

/--
Adapter from the Hestenes/Krein natural-cone socket to the canonical
standard-form natural-cone interface.

This is a specialization adapter only.  It does not prove the analytic
standard-form theorem `M_*^+ ≃ P`; it records that the canonical interface is
realized by the supplied Hestenes/Krein carrier with:

* `KreinSpace.kreinInner` as the real readout;
* `KreinSpace.jCLM` as the Tomita/Krein reflection;
* the supplied Hestenes/Krein natural cone as the canonical cone.
-/
@[rep_depth krein]
structure HestenesStandardFormNaturalConeAdapter where
  /-- Hestenes/Krein natural-cone carrier. -/
  hestenes :
    HestenesKreinNaturalConeBridge (H := H) (NormalPositive := NormalPositive)
      (Op := Op)

namespace HestenesStandardFormNaturalConeAdapter

variable (A : HestenesStandardFormNaturalConeAdapter (H := H)
  (NormalPositive := NormalPositive) (Op := Op))

/--
Canonical standard-form interface induced by the Hestenes/Krein carrier.

All states in `NormalPositive` are treated as already selected normal-positive
readouts because the Hestenes/Krein carrier itself is the supplied positive
state socket.
-/
@[rep_depth krein]
def toCanonical :
    NaturalConeStandardFormInterface Op H NormalPositive where
  act := A.hestenes.act
  J := KreinSpace.jCLM (H := H)
  cone := A.hestenes.naturalCone
  isNormalPositive := fun ω => A.hestenes.coneVector ω ∈ A.hestenes.naturalCone
  coneVector := A.hestenes.coneVector
  eval := A.hestenes.eval
  innerReadout := KreinSpace.kreinInner (H := H)
  coneVector_mem := fun ω hω => hω
  eval_eq_vector_readout := fun ω B _ => A.hestenes.eval_eq_krein_vector_readout ω B
  J_fixes_cone := A.hestenes.J_fixes_cone
  cone_self_dual := A.hestenes.naturalCone_self_dual
  cone_self_dual_holds := A.hestenes.naturalCone_self_dual_holds

/-- Readback: the induced canonical cone is the supplied Hestenes/Krein cone. -/
@[rep_depth krein]
theorem toCanonical_cone :
    (A.toCanonical).cone = A.hestenes.naturalCone :=
  rfl

/-- Readback: the induced canonical reflection is `KreinSpace.jCLM`. -/
@[rep_depth krein]
theorem toCanonical_J
    (ξ : H) :
    (A.toCanonical).J ξ = KreinSpace.jCLM (H := H) ξ :=
  rfl

/-- Readback: the induced canonical inner readout is `KreinSpace.kreinInner`. -/
@[rep_depth krein]
theorem toCanonical_innerReadout
    (ξ η : H) :
    (A.toCanonical).innerReadout ξ η = KreinSpace.kreinInner (H := H) ξ η :=
  rfl

/-- Readback: canonical evaluation is the Hestenes/Krein evaluation. -/
@[rep_depth krein]
theorem toCanonical_eval
    (ω : NormalPositive) (B : Op) :
    (A.toCanonical).eval ω B = A.hestenes.eval ω B :=
  rfl

/-- Readback: canonical cone vectors are the Hestenes/Krein cone vectors. -/
@[rep_depth krein]
theorem toCanonical_coneVector
    (ω : NormalPositive) :
    (A.toCanonical).coneVector ω = A.hestenes.coneVector ω :=
  rfl

/-- Readback: every supplied Hestenes/Krein readout is normal-positive in the adapter. -/
@[rep_depth krein]
theorem toCanonical_isNormalPositive
    (ω : NormalPositive) :
    (A.toCanonical).isNormalPositive ω :=
  A.hestenes.coneVector_mem ω

/--
Readback: the canonical standard-form vector expectation is the Krein vector
readout supplied by the Hestenes/Krein carrier.
-/
@[rep_depth krein]
theorem toCanonical_eval_eq_krein_readout
    (ω : NormalPositive) (B : Op) :
    (A.toCanonical).eval ω B =
      KreinSpace.kreinInner (H := H)
        (A.hestenes.act B (A.hestenes.coneVector ω))
        (A.hestenes.coneVector ω) :=
  A.hestenes.eval_eq_krein_vector_readout ω B

/-- Readback: canonical cone vectors are fixed by `KreinSpace.jCLM`. -/
@[rep_depth krein]
theorem toCanonical_J_fixes_coneVector
    (ω : NormalPositive) :
    (A.toCanonical).J ((A.toCanonical).coneVector ω) =
      (A.toCanonical).coneVector ω :=
  NaturalConeStandardFormInterface.J_fixes_coneVector
    A.toCanonical ω (A.toCanonical_isNormalPositive ω)

/-- Readback: the canonical self-duality certificate is exactly the supplied Krein one. -/
@[rep_depth krein]
theorem toCanonical_cone_self_dual :
    (A.toCanonical).cone_self_dual :=
  A.hestenes.naturalCone_self_dual_holds

end HestenesStandardFormNaturalConeAdapter

/--
Compatibility witness for an already supplied canonical interface and an
already supplied Hestenes/Krein carrier.

Use this when the canonical socket was constructed elsewhere and must be
recorded as realized by a Hestenes/Krein model without replacing it by
`toCanonical`.
-/
@[rep_depth krein]
structure CanonicalRealizedByHestenesKrein
    (S : NaturalConeStandardFormInterface Op H NormalPositive)
    (B : HestenesKreinNaturalConeBridge (H := H) (NormalPositive := NormalPositive)
      (Op := Op)) where
  /-- The canonical action agrees pointwise with the Hestenes/Krein action. -/
  act_eq :
    ∀ (A : Op) (ξ : H), S.act A ξ = B.act A ξ

  /-- The canonical reflection is the Krein/Tomita reflection. -/
  J_eq :
    ∀ ξ : H, S.J ξ = KreinSpace.jCLM (H := H) ξ

  /-- The canonical cone is the supplied Hestenes/Krein natural cone. -/
  cone_iff :
    ∀ ξ : H, ξ ∈ S.cone ↔ ξ ∈ B.naturalCone

  /-- Canonical cone vectors agree with Hestenes/Krein cone vectors. -/
  coneVector_eq :
    ∀ ω : NormalPositive, S.coneVector ω = B.coneVector ω

  /-- Canonical evaluation agrees with Hestenes/Krein evaluation. -/
  eval_eq :
    ∀ (ω : NormalPositive) (A : Op), S.eval ω A = B.eval ω A

  /-- Canonical readout agrees with the Krein inner product. -/
  innerReadout_eq :
    ∀ ξ η : H, S.innerReadout ξ η = KreinSpace.kreinInner (H := H) ξ η

namespace CanonicalRealizedByHestenesKrein

variable {S : NaturalConeStandardFormInterface Op H NormalPositive}
variable {B : HestenesKreinNaturalConeBridge (H := H) (NormalPositive := NormalPositive)
  (Op := Op)}

/-- Readback: canonical evaluation is realized by the Hestenes/Krein evaluation. -/
@[rep_depth krein]
theorem eval_realized
    (R : CanonicalRealizedByHestenesKrein (H := H)
      (NormalPositive := NormalPositive) (Op := Op) S B)
    (ω : NormalPositive) (A : Op) :
    S.eval ω A = B.eval ω A :=
  CanonicalRealizedByHestenesKrein.eval_eq R ω A

/-- Readback: canonical evaluation is the Hestenes/Krein Krein-vector readout. -/
@[rep_depth krein]
theorem eval_eq_krein_readout
    (R : CanonicalRealizedByHestenesKrein (H := H)
      (NormalPositive := NormalPositive) (Op := Op) S B)
    (ω : NormalPositive) (A : Op) :
    S.eval ω A =
      KreinSpace.kreinInner (H := H) (B.act A (B.coneVector ω)) (B.coneVector ω) := by
  rw [CanonicalRealizedByHestenesKrein.eval_eq R ω A]
  exact B.eval_eq_krein_vector_readout ω A

/-- Readback: canonical cone membership matches Hestenes/Krein cone membership. -/
@[rep_depth krein]
theorem cone_mem_iff
    (R : CanonicalRealizedByHestenesKrein (H := H)
      (NormalPositive := NormalPositive) (Op := Op) S B)
    (ξ : H) :
    ξ ∈ S.cone ↔ ξ ∈ B.naturalCone :=
  CanonicalRealizedByHestenesKrein.cone_iff R ξ

/-- Readback: canonical reflection is the Krein/Tomita reflection. -/
@[rep_depth krein]
theorem J_eq_jCLM
    (R : CanonicalRealizedByHestenesKrein (H := H)
      (NormalPositive := NormalPositive) (Op := Op) S B)
    (ξ : H) :
    S.J ξ = KreinSpace.jCLM (H := H) ξ :=
  CanonicalRealizedByHestenesKrein.J_eq R ξ

end CanonicalRealizedByHestenesKrein

end Core

end InfoGeometry.Krein.HestenesStandardFormNaturalConeAdapter

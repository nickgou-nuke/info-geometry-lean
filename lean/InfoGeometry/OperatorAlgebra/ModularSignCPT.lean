/-
InfoGeometry/OperatorAlgebra/ModularSignCPT.lean

Modular sign, CPT reflection, and emergent Hestenes complex structure.

The primitive relation is

  J eps = - eps J

where `eps` is the sign of the modular Hamiltonian and `J` is modular
conjugation/CPT reflection.

The product

  Kmod = J eps

is the real Hestenes phase axis / complex structure on the active modular
support.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ModularWeightTrace
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ModularSignCPT

/-! ## 0. Bounded real operator notation -/

/-- Real bounded endomorphisms. -/
abbrev EndR
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  H →L[ℝ] H

/-! ## 1. Full/gapped modular sign-CPT datum -/

/--
Primitive full/gapped modular sign-CPT relations.

This is the constructible algebraic input: two involutions `eps` and `J` that
anticommute.  The modular phase axis is then forced to be `J ∘ eps`, and its
square law is proved below rather than stored as a free certificate.
-/
structure ModularSignCPTRelations
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- Modular sign/parity. -/
  eps : EndR H

  /-- Modular conjugation/CPT reflection. -/
  J : EndR H

  /-- `eps² = 1`. -/
  eps_square :
    eps.comp eps = 1

  /-- `J² = 1`. -/
  J_square :
    J.comp J = 1

  /-- Clifford anticommutation relation: `J eps = - eps J`. -/
  J_eps_anticomm :
    J.comp eps = -(eps.comp J)

namespace ModularSignCPTRelations

variable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (R : ModularSignCPTRelations H)

/-- The generated Hestenes phase axis `J ε`. -/
def Kmod : EndR H :=
  R.J.comp R.eps

/-- Definitional equation for the generated phase axis. -/
theorem Kmod_eq :
    R.Kmod = R.J.comp R.eps :=
  rfl

/-- The opposite Clifford anticommutation relation follows from `J ε = - ε J`. -/
theorem eps_J_anticomm :
    R.eps.comp R.J = -(R.J.comp R.eps) := by
  rw [R.J_eps_anticomm]
  simp

/-- The generated phase axis squares to `-1`. -/
theorem Kmod_square :
    R.Kmod.comp R.Kmod = -(1 : EndR H) := by
  dsimp [Kmod]
  calc
    (R.J.comp R.eps).comp (R.J.comp R.eps)
        = R.J.comp ((R.eps.comp R.J).comp R.eps) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = R.J.comp ((-(R.J.comp R.eps)).comp R.eps) := by
          rw [R.eps_J_anticomm]
    _ = -(R.J.comp ((R.J.comp R.eps).comp R.eps)) := by
          ext v
          simp [ContinuousLinearMap.comp_apply]
    _ = -(((R.J.comp R.J).comp R.eps).comp R.eps) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = -((1 : EndR H).comp R.eps).comp R.eps := by
          rw [R.J_square]
    _ = -(R.eps.comp R.eps) := by
          ext v
          simp [ContinuousLinearMap.comp_apply]
    _ = -(1 : EndR H) := by
          rw [R.eps_square]

end ModularSignCPTRelations

/--
Full, gapped modular sign/CPT datum.

This is the clean case where the modular Hamiltonian has no zero-mode sector,
so the sign operator satisfies `eps² = 1`.

The field `Kmod` is required to be `J ∘ eps`; the complex-structure law is
stored as a proof-carrying field at this socket layer.
-/
structure ModularSignCPTDatum
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- Modular sign/parity: `eps = sign(log Delta)`. -/
  eps : EndR H

  /-- Modular conjugation/CPT reflection, represented real-linearly. -/
  J : EndR H

  /-- Emergent Hestenes complex structure, intended as `J ∘ eps`. -/
  Kmod : EndR H

  /-- `eps² = 1` on the active modular sector. -/
  eps_square :
    eps.comp eps = 1

  /-- `J² = 1`. -/
  J_square :
    J.comp J = 1

  /-- Clifford anticommutation relation: `J eps = - eps J`. -/
  J_eps_anticomm :
    J.comp eps = -(eps.comp J)

  /-- The modular complex structure is `J eps`. -/
  Kmod_eq :
    Kmod = J.comp eps

  /-- Complex-structure law: `Kmod² = -1`. -/
  Kmod_square :
    Kmod.comp Kmod = -1

namespace ModularSignCPTRelations

variable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (R : ModularSignCPTRelations H)

/-- Construct the full datum from the primitive relations. -/
def toDatum : ModularSignCPTDatum H where
  eps := R.eps
  J := R.J
  Kmod := R.Kmod
  eps_square := R.eps_square
  J_square := R.J_square
  J_eps_anticomm := R.J_eps_anticomm
  Kmod_eq := R.Kmod_eq
  Kmod_square := R.Kmod_square

end ModularSignCPTRelations

namespace ModularSignCPTDatum

variable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (M : ModularSignCPTDatum H)

/-- The opposite anticommutation relation follows from `J eps = - eps J`. -/
theorem eps_J_anticomm :
    M.eps.comp M.J = -(M.J.comp M.eps) := by
  rw [M.J_eps_anticomm]
  simp

/-- The modular sign is the supergrading/parity operator. -/
def parity : EndR H :=
  M.eps

/-- The modular CPT/reflection operator. -/
def cpt : EndR H :=
  M.J

/-- The dynamically generated Hestenes phase axis. -/
def complexStructure : EndR H :=
  M.Kmod

/-- `Kmod` is the product `J eps`. -/
theorem Kmod_eq_J_eps :
    M.Kmod = M.J.comp M.eps :=
  M.Kmod_eq

/--
The dynamically generated modular phase axis squares to `-1`.

This is the real Clifford calculation:

At this abstract socket layer this is re-exported from the datum. A concrete
functional-calculus layer can later prove the witness from `eps_square`,
`J_square`, and `J_eps_anticomm`.
-/
theorem Kmod_square_apply :
    M.Kmod.comp M.Kmod = -(1 : EndR H) := by
  simpa using M.Kmod_square

/-- The defining square law for the dynamically generated complex structure. -/
theorem complexStructure_square :
    M.complexStructure.comp M.complexStructure = -(1 : EndR H) := by
  simpa [complexStructure] using M.Kmod_square_apply

/--
An operator is even with respect to the modular sign when it commutes with
`eps`.
-/
def IsEvenOperator
    (T : EndR H) : Prop :=
  M.eps.comp T = T.comp M.eps

/--
An operator is odd with respect to the modular sign when it anticommutes with
`eps`.
-/
def IsOddOperator
    (T : EndR H) : Prop :=
  M.eps.comp T = -(T.comp M.eps)

/--
The primitive four-dimensional real Clifford/CPT span.

Mathematically this is the real span of

`{1, eps, J, Jeps}`,

with `eps² = 1`, `J² = 1`, and `Jeps = -epsJ`.
-/
structure CliffordCPTBasis where
  scalarUnit : EndR H := 1
  modularParity : EndR H := M.eps
  modularReflection : EndR H := M.J
  hestenesPhase : EndR H := M.Kmod

/--
The primitive four-dimensional real Clifford/CPT span generated by
`{1, eps, J, J eps}`.
-/
def cliffordCPTSpan : Submodule ℝ (EndR H) :=
  Submodule.span ℝ ({1, M.eps, M.J, M.Kmod} : Set (EndR H))

end ModularSignCPTDatum

/-! ## 2. Partial/zero-mode modular sign-CPT datum -/

/--
Primitive partial/zero-mode modular sign-CPT relations.

Here `eps²` is the active support projection rather than the identity.  The
partial phase axis is still `J ∘ eps`; its square and support laws are proved
from the primitive relations below.
-/
structure PartialModularSignCPTRelations
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- Active modular support. -/
  support : EndR H

  /-- Modular sign/parity on the active support. -/
  eps : EndR H

  /-- Modular conjugation/CPT reflection. -/
  J : EndR H

  /-- The support is idempotent. -/
  support_idempotent :
    support.comp support = support

  /-- `eps² = support`. -/
  eps_square :
    eps.comp eps = support

  /-- The support acts as identity on `eps` from the left. -/
  support_eps :
    support.comp eps = eps

  /-- The support acts as identity on `eps` from the right. -/
  eps_support :
    eps.comp support = eps

  /-- `J² = 1`. -/
  J_square :
    J.comp J = 1

  /-- Clifford anticommutation relation on the active sector. -/
  J_eps_anticomm :
    J.comp eps = -(eps.comp J)

  /-- The active support is preserved by modular reflection. -/
  J_support_comm :
    J.comp support = support.comp J

namespace PartialModularSignCPTRelations

variable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (R : PartialModularSignCPTRelations H)

/-- The opposite Clifford anticommutation relation follows from `J ε = - ε J`. -/
theorem eps_J_anticomm :
    R.eps.comp R.J = -(R.J.comp R.eps) := by
  rw [R.J_eps_anticomm]
  simp

/-- The partial modular phase axis `J ε`. -/
def Kmod : EndR H :=
  R.J.comp R.eps

/-- Definitional equation for the partial phase axis. -/
theorem Kmod_eq :
    R.Kmod = R.J.comp R.eps :=
  rfl

/-- The partial generated phase axis squares to `-support`. -/
theorem Kmod_square :
    R.Kmod.comp R.Kmod = -R.support := by
  dsimp [Kmod]
  calc
    (R.J.comp R.eps).comp (R.J.comp R.eps)
        = R.J.comp ((R.eps.comp R.J).comp R.eps) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = R.J.comp ((-(R.J.comp R.eps)).comp R.eps) := by
          rw [R.eps_J_anticomm]
    _ = -(R.J.comp ((R.J.comp R.eps).comp R.eps)) := by
          ext v
          simp [ContinuousLinearMap.comp_apply]
    _ = -(((R.J.comp R.J).comp R.eps).comp R.eps) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = -((1 : EndR H).comp R.eps).comp R.eps := by
          rw [R.J_square]
    _ = -(R.eps.comp R.eps) := by
          ext v
          simp [ContinuousLinearMap.comp_apply]
    _ = -R.support := by
          rw [R.eps_square]

/-- The support acts as identity on the generated phase axis from the left. -/
theorem support_Kmod :
    R.support.comp R.Kmod = R.Kmod := by
  dsimp [Kmod]
  calc
    R.support.comp (R.J.comp R.eps)
        = (R.support.comp R.J).comp R.eps := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (R.J.comp R.support).comp R.eps := by
          rw [← R.J_support_comm]
    _ = R.J.comp (R.support.comp R.eps) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = R.J.comp R.eps := by
          rw [R.support_eps]

/-- The generated phase axis is supported on the right. -/
theorem Kmod_support :
    R.Kmod.comp R.support = R.Kmod := by
  dsimp [Kmod]
  calc
    (R.J.comp R.eps).comp R.support
        = R.J.comp (R.eps.comp R.support) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = R.J.comp R.eps := by
          rw [R.eps_support]

end PartialModularSignCPTRelations

/--
Partial modular sign/CPT datum.

This is the correct version when `0` lies in the spectrum of the modular
Hamiltonian. Then `eps²` is a support projection rather than the identity.

The field `support` should be read as the active modular support, usually
`1 - Pker(log Delta)`.
-/
structure PartialModularSignCPTDatum
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- Active support projection, usually `1 - Pker(log Delta)`. -/
  support : EndR H

  /-- Modular sign/parity on the active support. -/
  eps : EndR H

  /-- Modular conjugation/CPT reflection. -/
  J : EndR H

  /-- Partial Hestenes complex structure, intended as `J ∘ eps`. -/
  Kmod : EndR H

  /-- The active support is idempotent. -/
  support_idempotent :
    support.comp support = support

  /-- `eps² = support`. -/
  eps_square :
    eps.comp eps = support

  /-- The support acts as identity on `eps` from the left. -/
  support_eps :
    support.comp eps = eps

  /-- The support acts as identity on `eps` from the right. -/
  eps_support :
    eps.comp support = eps

  /-- `J² = 1`. -/
  J_square :
    J.comp J = 1

  /-- Clifford anticommutation relation on the active sector. -/
  J_eps_anticomm :
    J.comp eps = -(eps.comp J)

  /-- Opposite orientation of the Clifford anticommutation relation. -/
  eps_J_anticomm :
    eps.comp J = -(J.comp eps)

  /--
  The active support is preserved by modular reflection.

  This models the functional-calculus fact that the zero-mode sector is sent
  to itself by `J`.
  -/
  J_support_comm :
    J.comp support = support.comp J

  /-- The partial modular complex structure is `J eps`. -/
  Kmod_eq :
    Kmod = J.comp eps

  /-- Partial complex-structure law: `Kmod² = -support`. -/
  Kmod_square :
    Kmod.comp Kmod = -support

  /-- The support acts as identity on the partial complex structure from the left. -/
  support_Kmod :
    support.comp Kmod = Kmod

  /-- The partial complex structure is supported on the right. -/
  Kmod_support :
    Kmod.comp support = Kmod

namespace PartialModularSignCPTRelations

variable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (R : PartialModularSignCPTRelations H)

/-- Construct the partial datum from primitive zero-mode-aware relations. -/
def toDatum : PartialModularSignCPTDatum H where
  support := R.support
  eps := R.eps
  J := R.J
  Kmod := R.Kmod
  support_idempotent := R.support_idempotent
  eps_square := R.eps_square
  support_eps := R.support_eps
  eps_support := R.eps_support
  J_square := R.J_square
  J_eps_anticomm := R.J_eps_anticomm
  eps_J_anticomm := R.eps_J_anticomm
  J_support_comm := R.J_support_comm
  Kmod_eq := R.Kmod_eq
  Kmod_square := R.Kmod_square
  support_Kmod := R.support_Kmod
  Kmod_support := R.Kmod_support

end PartialModularSignCPTRelations

namespace PartialModularSignCPTDatum

variable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (M : PartialModularSignCPTDatum H)

/-- Re-export the opposite anticommutation relation. -/
theorem eps_J_anticomm_apply :
    M.eps.comp M.J = -(M.J.comp M.eps) := by
  exact M.eps_J_anticomm

/-- The partial modular phase axis. -/
def partialComplexStructure : EndR H :=
  M.Kmod

/-- The partial Hestenes phase is `J eps`. -/
theorem Kmod_eq_J_eps :
    M.Kmod = M.J.comp M.eps :=
  M.Kmod_eq

/--
The partial modular phase axis squares to `-support`.

This is the zero-mode-corrected Clifford calculation:

At this abstract layer this is re-exported from the datum; concrete modular
functional calculus should prove the witness.
-/
theorem Kmod_square_apply :
    M.Kmod.comp M.Kmod = -M.support := by
  simpa using M.Kmod_square

/-- The partial square law on the active modular support. -/
theorem partialComplexStructure_square :
    M.partialComplexStructure.comp M.partialComplexStructure = -M.support := by
  simpa [partialComplexStructure] using M.Kmod_square_apply

/-- The support projection is a projector/idempotent. -/
theorem support_isProjector :
    M.support.comp M.support = M.support :=
  M.support_idempotent

/-- The active support is the identity on the sign operator from both sides. -/
theorem support_absorbs_eps :
    M.support.comp M.eps = M.eps ∧ M.eps.comp M.support = M.eps :=
  ⟨M.support_eps, M.eps_support⟩

/-- The active support is the identity on the partial complex structure from both sides. -/
theorem support_absorbs_Kmod :
    M.support.comp M.Kmod = M.Kmod ∧ M.Kmod.comp M.support = M.Kmod :=
  ⟨M.support_Kmod, M.Kmod_support⟩

/-- An operator is supported on the active modular sector from the left. -/
def IsLeftActiveSupported
    (T : EndR H) : Prop :=
  M.support.comp T = T

/-- An operator is supported on the active modular sector from both sides. -/
def IsActiveSupported
    (T : EndR H) : Prop :=
  M.support.comp T = T ∧ T.comp M.support = T

end PartialModularSignCPTDatum

/-! ## 3. Dynamic modular CPT algebra -/

/--
Dynamic modular CPT algebra.

This packages the Clifford sign/CPT algebra together with the modular flow.
The analytic statement that `eps` is actually `sign(log Delta)` remains a
proof-carrying field.
-/
structure DynamicModularCPTAlgebra
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- Full/gapped modular sign-CPT algebra. -/
  signCPT :
    ModularSignCPTDatum H

  /-- Modular flow on represented observables/operators. -/
  modularFlow : ℝ → EndR H → EndR H

  flow_zero :
    ∀ T : EndR H, modularFlow 0 T = T

  flow_add :
    ∀ s t T,
      modularFlow (s + t) T = modularFlow s (modularFlow t T)

  /-- Multiplicativity of the modular flow on represented operators. -/
  flow_mul :
    ∀ t A B,
      modularFlow t (A.comp B) = (modularFlow t A).comp (modularFlow t B)

  /--
  Optional link to the type-III modular integration backend.

  This is optional because one may want to study the sign/CPT algebra before a
  concrete weight has been chosen.
  -/
  modularWeightBackend :
    Option (InfoGeometry.OperatorAlgebra.ModularWeightDatum (EndR H))

  /--
  Certificate that `eps` is the sign of the modular Hamiltonian generating the
  flow.
  -/
  eps_is_sign_of_modular_hamiltonian : Prop

  /-- Certificate that `J` reverses modular time/CPT orientation. -/
  J_reverses_modular_flow : Prop

  /--
  Certificate that the generated algebra is the intended split Clifford/CPT
  superalgebra.
  -/
  split_clifford_cpt_superalgebra : Prop

namespace DynamicModularCPTAlgebra

variable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (M : DynamicModularCPTAlgebra H)

/-- Re-export of the modular flow identity law. -/
@[simp]
theorem modularFlow_zero_apply
    (T : EndR H) :
    M.modularFlow 0 T = T :=
  M.flow_zero T

/-- Re-export of the modular flow additive law. -/
theorem modularFlow_add_apply
    (s t : ℝ)
    (T : EndR H) :
    M.modularFlow (s + t) T =
      M.modularFlow s (M.modularFlow t T) :=
  M.flow_add s t T

/-- Multiplicativity of the modular flow. -/
theorem modularFlow_mul_apply
    (t : ℝ)
    (A B : EndR H) :
    M.modularFlow t (A.comp B) = (M.modularFlow t A).comp (M.modularFlow t B) :=
  M.flow_mul t A B

/-- The dynamically generated phase axis squares to `-1`. -/
theorem complexStructure_square :
    M.signCPT.Kmod.comp M.signCPT.Kmod = -(1 : EndR H) :=
  M.signCPT.Kmod_square_apply

end DynamicModularCPTAlgebra

/-! ## 4. Owner targets -/

/--
Compatibility predicate for constructing a modular sign/CPT datum from
Tomita-Takesaki data.

The compatibility content is the primitive Clifford pair: two involutions
`eps` and `J` satisfying `J ε = - ε J`.  From these relations the phase-axis
square law is proved by `ModularSignCPTRelations.Kmod_square`.
-/
def ModularSignCPTCompatibility
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] : Type _ :=
  ModularSignCPTRelations H

/--
The full/gapped datum is constructed from primitive Clifford relations.

This remains intentionally compatibility-gated: abstract normed real Hilbert
data alone do not construct the modular sign and conjugation witnesses.
-/
theorem modularSignCPTDatumOwnerTarget :
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    ModularSignCPTCompatibility H →
      ∃ R : ModularSignCPTRelations H,
        R.eps.comp R.eps = 1 ∧
          R.J.comp R.J = 1 ∧
          R.J.comp R.eps = -(R.eps.comp R.J) ∧
          R.Kmod = R.J.comp R.eps ∧
          R.Kmod.comp R.Kmod = -(1 : EndR H) := by
  intro H _ _ h
  let R : ModularSignCPTRelations H := h
  exact ⟨R, R.eps_square, R.J_square, R.J_eps_anticomm, R.Kmod_eq, R.Kmod_square⟩

/-- Packet readout for the datum constructed from full modular sign-CPT relations. -/
theorem modularSignCPTDatum_packet
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (R : ModularSignCPTRelations H) :
    R.Kmod = R.J.comp R.eps ∧
      R.Kmod.comp R.Kmod = -(1 : EndR H) :=
  ⟨R.Kmod_eq, R.Kmod_square⟩

/-- Compatibility predicate for constructing the partial zero-mode-aware datum. -/
def PartialModularSignCPTCompatibility
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] : Type _ :=
  PartialModularSignCPTRelations H

/-- The partial datum is constructed from primitive zero-mode-aware relations. -/
theorem partialModularSignCPTDatumOwnerTarget :
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    PartialModularSignCPTCompatibility H →
      ∃ R : PartialModularSignCPTRelations H,
        R.support.comp R.support = R.support ∧
          R.eps.comp R.eps = R.support ∧
          R.J.comp R.J = 1 ∧
          R.J.comp R.eps = -(R.eps.comp R.J) ∧
          R.Kmod = R.J.comp R.eps ∧
          R.Kmod.comp R.Kmod = -R.support ∧
          R.support.comp R.Kmod = R.Kmod ∧
          R.Kmod.comp R.support = R.Kmod := by
  intro H _ _ h
  let R : PartialModularSignCPTRelations H := h
  exact ⟨R, R.support_idempotent, R.eps_square, R.J_square,
    R.J_eps_anticomm, R.Kmod_eq, R.Kmod_square, R.support_Kmod,
    R.Kmod_support⟩

/-- Packet readout for the datum constructed from partial modular sign-CPT relations. -/
theorem partialModularSignCPTDatum_packet
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (R : PartialModularSignCPTRelations H) :
    R.Kmod = R.J.comp R.eps ∧
      R.Kmod.comp R.Kmod = -R.support ∧
      R.support.comp R.Kmod = R.Kmod ∧
      R.Kmod.comp R.support = R.Kmod :=
  ⟨R.Kmod_eq, R.Kmod_square, R.support_Kmod, R.Kmod_support⟩

/--
Read back the full/gapped modular sign-CPT algebra once the datum is supplied.

This is intentionally witness-gated: the sign operator, modular conjugation,
and anticommutation relation are analytic input.
-/
theorem modularSignCPTOwnerTarget :
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    ∀ M : ModularSignCPTDatum H,
      M.Kmod = M.J.comp M.eps ∧
        M.Kmod.comp M.Kmod = -(1 : EndR H) ∧
        M.J.comp M.eps = -(M.eps.comp M.J) := by
  intro H _ _ M
  exact ⟨M.Kmod_eq, M.Kmod_square, M.J_eps_anticomm⟩

/-- Read back the partial/zero-mode modular sign-CPT algebra once the datum is supplied. -/
theorem partialModularSignCPTOwnerTarget :
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    ∀ M : PartialModularSignCPTDatum H,
      M.Kmod = M.J.comp M.eps ∧
        M.Kmod.comp M.Kmod = -M.support ∧
        M.support.comp M.Kmod = M.Kmod ∧
        M.Kmod.comp M.support = M.Kmod := by
  intro H _ _ M
  exact ⟨M.Kmod_eq, M.Kmod_square, M.support_Kmod, M.Kmod_support⟩

end InfoGeometry.OperatorAlgebra.ModularSignCPT

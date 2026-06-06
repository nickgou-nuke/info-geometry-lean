import InfoGeometry.Projective.SelfDualCone
import InfoGeometry.Projective.Orthant
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Canonical.SelfDualNormalConeBridge

set_option linter.dupNamespace false

open InfoGeometry.Projective

/-

BUCKET 1: CLOSED FINITE THEOREMS

[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]

BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

[Theorems that compile from explicitly named theorem parameters or imported verified premises.]

BUCKET 3: OPEN CLOSURE DEBT

[Exact theorem statements that remain unproved. No wrappers, sockets, fields, witnesses, certificates, or renamed placeholders.]
-/

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

@[rep_depth operator]
def inwardConeOrthogonal (P : Set E) (ξ : E) : Set E :=
{η | η ∈ P ∧ ⟪η, ξ⟫_ℝ = 0}

@[rep_depth operator]
def outwardConeOrthogonal (P : Set E) (ξ : E) : Set E :=
{η | -η ∈ P ∧ ⟪η, ξ⟫_ℝ = 0}

@[rep_depth operator]
def convexOutwardNormalCone (P : Set E) (ξ : E) : Set E :=
{η | ∀ ζ : E, ζ ∈ P → ⟪η, ζ - ξ⟫_ℝ ≤ 0}

@[rep_depth operator]
def convexInwardNormalCone (P : Set E) (ξ : E) : Set E :=
{η | ∀ ζ : E, ζ ∈ P → 0 ≤ ⟪η, ζ - ξ⟫_ℝ}

@[rep_depth operator]
structure StandardFormNormalConeLite
(Functional : Type*) where
J : E → E
naturalCone : Set E
coneVector : Functional → E
coneVector_mem : ∀ ω : Functional, coneVector ω ∈ naturalCone
J_involutive : ∀ ξ : E, J (J ξ) = ξ
J_fixes_naturalCone : ∀ ⦃ξ : E⦄, ξ ∈ naturalCone → J ξ = ξ

namespace StandardFormNormalConeLite

variable {E Functional : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (S : StandardFormNormalConeLite (E := E) Functional)

@[rep_depth operator]
theorem coneVector_mem_naturalCone (ω : Functional) :
S.coneVector ω ∈ S.naturalCone :=
S.coneVector_mem ω

@[rep_depth operator]
theorem J_fixes_coneVector (ω : Functional) :
S.J (S.coneVector ω) = S.coneVector ω :=
S.J_fixes_naturalCone (S.coneVector_mem ω)

@[rep_depth operator]
theorem outward_normal_cone
(ξ : E)
(hnormal :
∀ η : E,
η ∈ convexOutwardNormalCone S.naturalCone ξ ↔
η ∈ outwardConeOrthogonal S.naturalCone ξ) :
convexOutwardNormalCone S.naturalCone ξ = outwardConeOrthogonal S.naturalCone ξ := by
ext η
exact hnormal η

@[rep_depth operator]
theorem inward_normal_cone
(ξ : E)
(hnormal :
∀ η : E,
η ∈ convexInwardNormalCone S.naturalCone ξ ↔
η ∈ inwardConeOrthogonal S.naturalCone ξ) :
convexInwardNormalCone S.naturalCone ξ = inwardConeOrthogonal S.naturalCone ξ := by
ext η
exact hnormal η

@[rep_depth operator]
theorem outwardNormalCone_coneVector
(ω : Functional)
(hnormal :
∀ η : E,
η ∈ convexOutwardNormalCone S.naturalCone (S.coneVector ω) ↔
η ∈ outwardConeOrthogonal S.naturalCone (S.coneVector ω)) :
convexOutwardNormalCone S.naturalCone (S.coneVector ω) =
outwardConeOrthogonal S.naturalCone (S.coneVector ω) :=
S.outward_normal_cone (S.coneVector ω) hnormal

@[rep_depth operator]
theorem inwardNormalCone_coneVector
(ω : Functional)
(hnormal :
∀ η : E,
η ∈ convexInwardNormalCone S.naturalCone (S.coneVector ω) ↔
η ∈ inwardConeOrthogonal S.naturalCone (S.coneVector ω)) :
convexInwardNormalCone S.naturalCone (S.coneVector ω) =
inwardConeOrthogonal S.naturalCone (S.coneVector ω) :=
S.inward_normal_cone (S.coneVector ω) hnormal

end StandardFormNormalConeLite

@[rep_depth operator]
structure SelfDualNormalConeBridge
(Functional : Type*) where
selfDualCone : SelfDualCone E
standardForm :
StandardFormNormalConeLite (E := E) Functional
naturalCone_eq_selfDualCone :
standardForm.naturalCone = selfDualCone.cone

namespace SelfDualNormalConeBridge

variable {E Functional : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (B : SelfDualNormalConeBridge (E := E) (Functional := Functional))

@[rep_depth operator]
theorem coneVector_mem_selfDualCone (ω : Functional) :
B.standardForm.coneVector ω ∈ B.selfDualCone.cone := by
simpa [B.naturalCone_eq_selfDualCone] using
B.standardForm.coneVector_mem_naturalCone ω

@[rep_depth operator]
theorem J_fixes_coneVector (ω : Functional) :
B.standardForm.J (B.standardForm.coneVector ω) = B.standardForm.coneVector ω :=
B.standardForm.J_fixes_coneVector ω

@[rep_depth operator]
theorem outwardNormalCone_coneVector
(ω : Functional)
(hnormal :
∀ η : E,
η ∈ convexOutwardNormalCone B.selfDualCone.cone (B.standardForm.coneVector ω) ↔
η ∈ outwardConeOrthogonal B.selfDualCone.cone (B.standardForm.coneVector ω)) :
convexOutwardNormalCone B.selfDualCone.cone (B.standardForm.coneVector ω) =
outwardConeOrthogonal B.selfDualCone.cone (B.standardForm.coneVector ω) := by
ext η
exact hnormal η

@[rep_depth operator]
theorem inwardNormalCone_coneVector
(ω : Functional)
(hnormal :
∀ η : E,
η ∈ convexInwardNormalCone B.selfDualCone.cone (B.standardForm.coneVector ω) ↔
η ∈ inwardConeOrthogonal B.selfDualCone.cone (B.standardForm.coneVector ω)) :
convexInwardNormalCone B.selfDualCone.cone (B.standardForm.coneVector ω) =
inwardConeOrthogonal B.selfDualCone.cone (B.standardForm.coneVector ω) := by
ext η
exact hnormal η

@[rep_depth operator]
def positiveOrthant_selfDual
{α : Type*} [Fintype α] [Nonempty α] :
SelfDualCone (EuclideanSpace ℝ α) :=
positiveOrthant (α := α)

end SelfDualNormalConeBridge

end Core

end InfoGeometry.Canonical.SelfDualNormalConeBridge
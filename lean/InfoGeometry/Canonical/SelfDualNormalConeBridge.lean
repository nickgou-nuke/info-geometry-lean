import InfoGeometry.Projective.SelfDualCone
import InfoGeometry.Projective.Orthant
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SelfDualNormalConeBridge

Self-dual cone and standard-form normal cone readout.

This file packages the cone-theoretic language the user asked for:

* a self-dual proper cone;
* a standard-form natural positive cone;
* a calibration identifying the two cones;
* normal-cone readback at the cone vector;
* positivity readback at the projective/state level.

It does not construct a von Neumann algebra from scratch.  The operator-algebra
content is carried by the local standard-form normal cone interface below.
-/

noncomputable section

namespace InfoGeometry.Canonical.SelfDualNormalConeBridge

set_option linter.dupNamespace false

open InfoGeometry.Projective

/-
Local normal-cone formulas.
These are defined directly here so the bridge does not depend on the broken
modular-cartan source lane.
-/

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Positive cone vectors orthogonal to `ξ`. This is the inward normal convention. -/
@[rep_depth operator]
def inwardConeOrthogonal (P : Set E) (ξ : E) : Set E :=
  {η | η ∈ P ∧ ⟪η, ξ⟫_ℝ = 0}

/-- Negative cone vectors orthogonal to `ξ`. This is the outward normal convention. -/
@[rep_depth operator]
def outwardConeOrthogonal (P : Set E) (ξ : E) : Set E :=
  {η | -η ∈ P ∧ ⟪η, ξ⟫_ℝ = 0}

/-- Convex-analytic outward normal cone to `P` at `ξ`. -/
@[rep_depth operator]
def convexOutwardNormalCone (P : Set E) (ξ : E) : Set E :=
  {η | ∀ ζ : E, ζ ∈ P → ⟪η, ζ - ξ⟫_ℝ ≤ 0}

/-- Convex-analytic inward normal cone to `P` at `ξ`. -/
@[rep_depth operator]
def convexInwardNormalCone (P : Set E) (ξ : E) : Set E :=
  {η | ∀ ζ : E, ζ ∈ P → 0 ≤ ⟪η, ζ - ξ⟫_ℝ}

/-- Minimal standard-form normal cone interface. -/
@[rep_depth operator]
structure StandardFormNormalConeLite
    (Functional : Type*) where
  /-- Tomita modular conjugation / real reflection. -/
  J : E → E

  /-- Natural positive cone `P`. -/
  naturalCone : Set E

  /-- Standard-form cone vector representing a normal positive functional. -/
  coneVector : Functional → E

  /-- Every supplied normal positive functional has a cone vector. -/
  coneVector_mem : ∀ ω : Functional, coneVector ω ∈ naturalCone

  /-- `J² = 1`. -/
  J_involutive : ∀ ξ : E, J (J ξ) = ξ

  /-- `J` fixes natural-cone vectors pointwise. -/
  J_fixes_naturalCone : ∀ ⦃ξ : E⦄, ξ ∈ naturalCone → J ξ = ξ

  /-- Outward normal cone formula `N_P(ξ) = -P ∩ ξᗮ`. -/
  outward_normal_cone_law :
    ∀ ξ : E, ξ ∈ naturalCone →
      convexOutwardNormalCone naturalCone ξ = outwardConeOrthogonal naturalCone ξ

  /-- Inward normal cone formula `N_P^in(ξ) = P ∩ ξᗮ`. -/
  inward_normal_cone_law :
    ∀ ξ : E, ξ ∈ naturalCone →
      convexInwardNormalCone naturalCone ξ = inwardConeOrthogonal naturalCone ξ

namespace StandardFormNormalConeLite

variable {E Functional : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (S : StandardFormNormalConeLite (E := E) Functional)

/-- Readback: normal positive functionals are represented by natural-cone vectors. -/
@[rep_depth operator]
theorem coneVector_mem_naturalCone (ω : Functional) :
    S.coneVector ω ∈ S.naturalCone :=
  S.coneVector_mem ω

/-- Readback: `J` fixes the cone vector of a normal positive functional. -/
@[rep_depth operator]
theorem J_fixes_coneVector (ω : Functional) :
    S.J (S.coneVector ω) = S.coneVector ω :=
  S.J_fixes_naturalCone (S.coneVector_mem ω)

/-- Outward normal cone at a cone vector. -/
@[rep_depth operator]
theorem outwardNormalCone_coneVector (ω : Functional) :
    convexOutwardNormalCone S.naturalCone (S.coneVector ω) =
      outwardConeOrthogonal S.naturalCone (S.coneVector ω) :=
  S.outward_normal_cone_law (S.coneVector ω) (S.coneVector_mem ω)

/-- Inward normal cone at a cone vector. -/
@[rep_depth operator]
theorem inwardNormalCone_coneVector (ω : Functional) :
    convexInwardNormalCone S.naturalCone (S.coneVector ω) =
      inwardConeOrthogonal S.naturalCone (S.coneVector ω) :=
  S.inward_normal_cone_law (S.coneVector ω) (S.coneVector_mem ω)

end StandardFormNormalConeLite

/-- Self-dual cone and normal positive cone packaged together. -/
@[rep_depth operator]
structure SelfDualNormalConeBridge
    (Functional : Type*) where
  /-- Ambient self-dual cone. -/
  selfDualCone : SelfDualCone E

  /-- Standard-form normal cone for normal positive functionals. -/
  standardForm :
    StandardFormNormalConeLite (E := E) Functional

  /-- Calibration: the natural cone is the underlying self-dual proper cone. -/
  naturalCone_eq_selfDualCone :
    standardForm.naturalCone = selfDualCone.cone

namespace SelfDualNormalConeBridge

variable {E Functional : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (B : SelfDualNormalConeBridge (E := E) (Functional := Functional))

/-- Normal positive functionals are represented by vectors in the self-dual cone. -/
@[rep_depth operator]
theorem coneVector_mem_selfDualCone (ω : Functional) :
    B.standardForm.coneVector ω ∈ B.selfDualCone.cone := by
  simpa [B.naturalCone_eq_selfDualCone] using
    B.standardForm.coneVector_mem_naturalCone ω

/-- The Tomita/Krein reflection fixes the cone vector of a normal positive functional. -/
@[rep_depth operator]
theorem J_fixes_coneVector (ω : Functional) :
    B.standardForm.J (B.standardForm.coneVector ω) = B.standardForm.coneVector ω :=
  B.standardForm.J_fixes_coneVector ω

/-- Outward normal cone at a cone vector, written in self-dual form. -/
@[rep_depth operator]
theorem outwardNormalCone_coneVector (ω : Functional) :
    convexOutwardNormalCone B.selfDualCone.cone (B.standardForm.coneVector ω) =
      outwardConeOrthogonal B.selfDualCone.cone (B.standardForm.coneVector ω) := by
  simpa [B.naturalCone_eq_selfDualCone] using
    B.standardForm.outwardNormalCone_coneVector ω

/-- Inward normal cone at a cone vector, written in self-dual form. -/
@[rep_depth operator]
theorem inwardNormalCone_coneVector (ω : Functional) :
    convexInwardNormalCone B.selfDualCone.cone (B.standardForm.coneVector ω) =
      inwardConeOrthogonal B.selfDualCone.cone (B.standardForm.coneVector ω) := by
  simpa [B.naturalCone_eq_selfDualCone] using
    B.standardForm.inwardNormalCone_coneVector ω

/-- The positive orthant is a concrete self-dual cone instance. -/
@[rep_depth operator]
def positiveOrthant_selfDual
    {α : Type*} [Fintype α] [Nonempty α] :
    SelfDualCone (EuclideanSpace ℝ α) :=
  positiveOrthant (α := α)

end SelfDualNormalConeBridge

end Core

end InfoGeometry.Canonical.SelfDualNormalConeBridge

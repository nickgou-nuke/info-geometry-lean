/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.KleinBottleOrbitQuotient
import InfoGeometry.Canonical.DiscreteDiracHodgeChiral
import InfoGeometry.Canonical.KleinBottleTomitaCrosscapBridge
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Star

/-! Real linear operators on the existing glide quotient. Descent requires
preservation of glide-invariant fields; no spectral or dynamical hypothesis
is inferred from the quotient construction. -/

noncomputable section

namespace InfoGeometry.Topology.KleinRealOperatorDescent

open KleinBrillouinBase KleinBottleOrbitQuotient
open InfoGeometry.Canonical.KleinBottleTomitaCrosscap
open InfoGeometry.Algebra.DeWittPeirceSuperalgebra

variable {M : Type*} [Ring M] [StarRing M] [TopologicalSpace M] [IsTopologicalRing M]

/-- Operator fields on the glide cover whose values satisfy the Tomita
crosscap fixed equation and which are constant on the Klein deck orbits.
This is a subring of the actual function algebra, with no scalarization of the
operator values. -/
def crosscapInvariantContinuousSubring (D : CrosscapDatum M) :
    Subring C(BrillouinTorus, M) where
  carrier := {field | (∀ point, field point ∈ crosscapFixedSubring D) ∧
    ∀ point, field (torusGlide point) = field point}
  zero_mem' := by
    constructor
    · intro point
      change (0 : M) ∈ crosscapFixedSubring D
      exact (crosscapFixedSubring D).zero_mem
    · intro point
      rfl
  one_mem' := by
    constructor
    · intro point
      change (1 : M) ∈ crosscapFixedSubring D
      exact (crosscapFixedSubring D).one_mem
    · intro point
      rfl
  add_mem' := by
    intro f g hf hg
    constructor
    · intro point
      change f point + g point ∈ crosscapFixedSubring D
      exact (crosscapFixedSubring D).add_mem (hf.1 point) (hg.1 point)
    · intro point
      change f (torusGlide point) + g (torusGlide point) = f point + g point
      rw [hf.2 point, hg.2 point]
  neg_mem' := by
    intro f hf
    constructor
    · intro point
      change -f point ∈ crosscapFixedSubring D
      exact (crosscapFixedSubring D).neg_mem (hf.1 point)
    · intro point
      change -f (torusGlide point) = -f point
      rw [hf.2 point]
  mul_mem' := by
    intro f g hf hg
    constructor
    · intro point
      change f point * g point ∈ crosscapFixedSubring D
      exact (crosscapFixedSubring D).mul_mem (hf.1 point) (hg.1 point)
    · intro point
      change f (torusGlide point) * g (torusGlide point) = f point * g point
      rw [hf.2 point, hg.2 point]

/-- Continuous operator fields on the Klein quotient whose values satisfy the
Tomita crosscap fixed equation. -/
def crosscapQuotientContinuousSubring (D : CrosscapDatum M) :
    Subring C(KleinBrillouinQuotient, M) where
  carrier := {field | ∀ point, field point ∈ crosscapFixedSubring D}
  zero_mem' := by
    intro point
    change (0 : M) ∈ crosscapFixedSubring D
    exact (crosscapFixedSubring D).zero_mem
  one_mem' := by
    intro point
    change (1 : M) ∈ crosscapFixedSubring D
    exact (crosscapFixedSubring D).one_mem
  add_mem' := by
    intro f g hf hg point
    change f point + g point ∈ crosscapFixedSubring D
    exact (crosscapFixedSubring D).add_mem (hf point) (hg point)
  neg_mem' := by
    intro f hf point
    change -f point ∈ crosscapFixedSubring D
    exact (crosscapFixedSubring D).neg_mem (hf point)
  mul_mem' := by
    intro f g hf hg point
    change f point * g point ∈ crosscapFixedSubring D
    exact (crosscapFixedSubring D).mul_mem (hf point) (hg point)

/-- Pullback along the Klein quotient preserves continuous operator fields and
lands in the crosscap fixed subring. -/
def pullbackCrosscapContinuousRingHom (D : CrosscapDatum M) :
    crosscapQuotientContinuousSubring D →+*
      crosscapInvariantContinuousSubring D where
  toFun field := ⟨field.1.comp ⟨quotientMap, quotientMap_continuous⟩, by
    constructor
    · intro point
      exact field.property (quotientMap point)
    · intro point
      exact congrArg (fun quotientPoint => (field.1 quotientPoint : M))
        (quotientMap_glide point)⟩
  map_one' := by
    ext point
    rfl
  map_mul' := by
    intro first second
    ext point
    rfl
  map_zero' := by
    ext point
    rfl
  map_add' := by
    intro first second
    ext point
    rfl

private theorem crosscapInvariant_respects_quotient (D : CrosscapDatum M)
    (field : crosscapInvariantContinuousSubring D) (first second : BrillouinTorus)
    (related : KleinBottleOrbitQuotient.glideSetoid.r first second) :
    field.1 first = field.1 second := by
  rcases related with rfl | related
  · rfl
  · rw [related, field.property.2 first]

/-- The unique continuous quotient field descended from a glide-invariant
continuous operator field. -/
def descendCrosscapContinuousMap (D : CrosscapDatum M)
    (field : crosscapInvariantContinuousSubring D) :
    crosscapQuotientContinuousSubring D :=
  ⟨⟨Quotient.lift (field.1 : BrillouinTorus → M)
        (crosscapInvariant_respects_quotient D field),
      Continuous.quotient_lift
        field.1.continuous_toFun
        (crosscapInvariant_respects_quotient D field)⟩, by
      intro quotientPoint
      refine Quotient.inductionOn quotientPoint ?_
      intro point
      exact field.property.1 point⟩

/-- Continuous fields on the Klein quotient are exactly glide-invariant
continuous fields whose values satisfy the Tomita crosscap equation. -/
def crosscapContinuousRingEquiv (D : CrosscapDatum M) :
    crosscapQuotientContinuousSubring D ≃+*
      crosscapInvariantContinuousSubring D where
  toFun := pullbackCrosscapContinuousRingHom D
  invFun := descendCrosscapContinuousMap D
  left_inv := by
    intro field
    ext quotientPoint
    refine Quotient.inductionOn quotientPoint ?_
    intro point
    rfl
  right_inv := by
    intro field
    ext point
    rfl
  map_mul' := by
    intro first second
    ext point
    rfl
  map_add' := by
    intro first second
    ext point
    rfl

section StarStructure

variable [ContinuousStar M]

/-- The cover-side crosscap subring inherits the coefficient involution when
the Klein glide commutes with it.  The two defining conditions are preserved
separately: crosscap fixedness by the ring-general closure theorem, and orbit
invariance by applying `star` to the existing glide equation. -/
def crosscapInvariantContinuousSubringStar (D : CrosscapDatum M)
    (hGlideStar : ∀ A : M, D.glide (star A) = star (D.glide A)) :
    Star (crosscapInvariantContinuousSubring D) :=
  { star := fun field => ⟨star field.1, by
      constructor
      · intro point
        exact star_mem_crosscap D hGlideStar (field.1 point) (field.2.1 point)
      · intro point
        change star (field.1 (torusGlide point)) = star (field.1 point)
        rw [field.2.2 point]⟩ }

/-- The quotient-side crosscap subring inherits the coefficient involution. -/
def crosscapQuotientContinuousSubringStar (D : CrosscapDatum M)
    (hGlideStar : ∀ A : M, D.glide (star A) = star (D.glide A)) :
    Star (crosscapQuotientContinuousSubring D) :=
  { star := fun field => ⟨star field.1, by
      intro point
      exact star_mem_crosscap D hGlideStar (field.1 point) (field.2 point)⟩ }

def crosscapInvariantContinuousSubringStarRing (D : CrosscapDatum M)
    (hGlideStar : ∀ A : M, D.glide (star A) = star (D.glide A)) :
    StarRing (crosscapInvariantContinuousSubring D) := by
  letI : Star (crosscapInvariantContinuousSubring D) :=
    crosscapInvariantContinuousSubringStar D hGlideStar
  exact {
    star_add field₁ field₂ := by
      apply Subtype.ext
      ext point
      change star ((field₁.1 + field₂.1) point) =
        star (field₁.1 point) + star (field₂.1 point)
      rw [ContinuousMap.add_apply, star_add]
    star_involutive field := by
      apply Subtype.ext
      ext point
      change star (star (field.1 point)) = field.1 point
      exact star_star _
    star_mul field₁ field₂ := by
      apply Subtype.ext
      ext point
      change star ((field₁.1 * field₂.1) point) =
        star (field₂.1 point) * star (field₁.1 point)
      rw [ContinuousMap.mul_apply, star_mul] }

def crosscapQuotientContinuousSubringStarRing (D : CrosscapDatum M)
    (hGlideStar : ∀ A : M, D.glide (star A) = star (D.glide A)) :
    StarRing (crosscapQuotientContinuousSubring D) := by
  letI : Star (crosscapQuotientContinuousSubring D) :=
    crosscapQuotientContinuousSubringStar D hGlideStar
  exact {
    star_add field₁ field₂ := by
      apply Subtype.ext
      ext point
      change star ((field₁.1 + field₂.1) point) =
        star (field₁.1 point) + star (field₂.1 point)
      rw [ContinuousMap.add_apply, star_add]
    star_involutive field := by
      apply Subtype.ext
      ext point
      change star (star (field.1 point)) = field.1 point
      exact star_star _
    star_mul field₁ field₂ := by
      apply Subtype.ext
      ext point
      change star ((field₁.1 * field₂.1) point) =
        star (field₂.1 point) * star (field₁.1 point)
      rw [ContinuousMap.mul_apply, star_mul] }

/-- Pullback along the Klein quotient is a star-ring equivalence whenever the
operator glide respects the coefficient involution. -/
def crosscapContinuousStarRingEquiv (D : CrosscapDatum M)
    (hGlideStar : ∀ A : M, D.glide (star A) = star (D.glide A)) :
    @StarRingEquiv (crosscapQuotientContinuousSubring D)
      (crosscapInvariantContinuousSubring D) _ _ _ _
      (crosscapQuotientContinuousSubringStar D hGlideStar)
      (crosscapInvariantContinuousSubringStar D hGlideStar) :=
  @StarRingEquiv.mk (crosscapQuotientContinuousSubring D)
    (crosscapInvariantContinuousSubring D) _ _ _ _
    (crosscapQuotientContinuousSubringStar D hGlideStar)
    (crosscapInvariantContinuousSubringStar D hGlideStar)
    (crosscapContinuousRingEquiv D) (by
      intro field
      apply Subtype.ext
      ext point
      rfl)

end StarStructure

section PeirceSections

variable [S : ChiralPeirceSystem M]

/-- Apply the existing DeWitt body projection pointwise to a continuous field
on the Klein quotient.  The crosscap corner theorem proves that every value
remains in the fixed subring. -/
def crosscapQuotientBodyMap (D : CrosscapDatum M)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL) :
    crosscapQuotientContinuousSubring D →
      crosscapQuotientContinuousSubring D := fun field =>
  ⟨{ toFun := fun point => body (field.1 point)
     continuous_toFun := continuous_body.comp field.1.continuous_toFun },
    fun point => (crosscap_splits_body_and_soul D hstarPL hstarPR
      hJPL hJPR hΩPL hΩPR (field.1 point) (field.2 point)).1⟩

/-- Apply the existing DeWitt soul projection pointwise to a continuous field
on the Klein quotient.  This retains both off-diagonal Peirce corners in the
original operator ring. -/
def crosscapQuotientSoulMap (D : CrosscapDatum M)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL) :
    crosscapQuotientContinuousSubring D →
      crosscapQuotientContinuousSubring D := fun field =>
  ⟨{ toFun := fun point => soul (field.1 point)
     continuous_toFun := continuous_soul.comp field.1.continuous_toFun },
    fun point => (crosscap_splits_body_and_soul D hstarPL hstarPR
      hJPL hJPR hΩPL hΩPR (field.1 point) (field.2 point)).2⟩

/-- The Peirce body projection on glide-invariant cover fields. -/
def crosscapInvariantBodyMap (D : CrosscapDatum M)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL) :
    crosscapInvariantContinuousSubring D → crosscapInvariantContinuousSubring D :=
  fun field =>
    ⟨{ toFun := fun point => body (field.1 point)
       continuous_toFun := continuous_body.comp field.1.continuous_toFun }, by
      constructor
      · intro point
        exact (crosscap_splits_body_and_soul D hstarPL hstarPR hJPL hJPR
          hΩPL hΩPR (field.1 point) (field.2.1 point)).1
      · intro point
        exact congrArg body (field.2.2 point)⟩

/-- The DeWitt soul projection on glide-invariant cover fields. -/
def crosscapInvariantSoulMap (D : CrosscapDatum M)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL) :
    crosscapInvariantContinuousSubring D → crosscapInvariantContinuousSubring D :=
  fun field =>
    ⟨{ toFun := fun point => soul (field.1 point)
       continuous_toFun := continuous_soul.comp field.1.continuous_toFun }, by
      constructor
      · intro point
        exact (crosscap_splits_body_and_soul D hstarPL hstarPR hJPL hJPR
          hΩPL hΩPR (field.1 point) (field.2.1 point)).2
      · intro point
        exact congrArg soul (field.2.2 point)⟩

/-- Pullback from the Klein quotient commutes with the existing Peirce body
projection; both sides evaluate to the same operator at every cover point. -/
theorem crosscapContinuousRingEquiv_body (D : CrosscapDatum M)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL)
    (field : crosscapQuotientContinuousSubring D) :
    crosscapContinuousRingEquiv D
        (crosscapQuotientBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR field) =
      crosscapInvariantBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR
        (crosscapContinuousRingEquiv D field) := by
  apply Subtype.ext
  ext point
  rfl

/-- Pullback from the Klein quotient commutes with the existing Peirce soul
projection. -/
theorem crosscapContinuousRingEquiv_soul (D : CrosscapDatum M)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL)
    (field : crosscapQuotientContinuousSubring D) :
    crosscapContinuousRingEquiv D
        (crosscapQuotientSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR field) =
      crosscapInvariantSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR
        (crosscapContinuousRingEquiv D field) := by
  apply Subtype.ext
  ext point
  rfl

/-- The Peirce body and soul projections reconstruct every continuous
crosscap field on the quotient, pointwise in the original coefficient ring. -/
theorem crosscapQuotient_body_soul_decomposition (D : CrosscapDatum M)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL)
    (field : crosscapQuotientContinuousSubring D) :
    crosscapQuotientBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR field +
      crosscapQuotientSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR field = field := by
  apply Subtype.ext
  ext point
  exact (dewitt_split (field.1 point)).symm

/-- On the quotient crosscap carrier, body and soul remain complementary
idempotent projections. -/
theorem crosscapQuotient_body_soul_projection_laws (D : CrosscapDatum M)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL)
    (field : crosscapQuotientContinuousSubring D) :
    crosscapQuotientBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR
      (crosscapQuotientBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR field) =
        crosscapQuotientBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR field ∧
    crosscapQuotientSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR
      (crosscapQuotientSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR field) =
        crosscapQuotientSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR field ∧
    crosscapQuotientBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR
      (crosscapQuotientSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR field) = 0 ∧
    crosscapQuotientSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR
      (crosscapQuotientBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR field) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    ext point
    exact body_is_idempotent (field.1 point)
  · apply Subtype.ext
    ext point
    exact soul_is_idempotent (field.1 point)
  · apply Subtype.ext
    ext point
    exact (body_soul_orthogonal (field.1 point)).1
  · apply Subtype.ext
    ext point
    exact (body_soul_orthogonal (field.1 point)).2

end PeirceSections

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def invariantFields : Submodule ℝ (BrillouinTorus → V) where
  carrier := {field | ∀ point, field (torusGlide point) = field point}
  zero_mem' := fun _ => rfl
  add_mem' := by
    intro first second first_fixed second_fixed point
    exact congrArg₂ (· + ·) (first_fixed point) (second_fixed point)
  smul_mem' := by
    intro scalar field fixed point
    exact congrArg (scalar • ·) (fixed point)

def fieldEquiv : (KleinBrillouinQuotient → V) ≃ₗ[ℝ] invariantFields (V := V) where
  toFun field := ⟨fun point => field (quotientMap point), fun point =>
    congrArg field (quotientMap_glide point)⟩
  invFun field := Quotient.lift (field : BrillouinTorus → V) (by
    intro first second related
    rcases related with rfl | related
    · rfl
    · rw [related, field.property first])
  left_inv := by
    intro field
    funext point
    obtain ⟨representative, rfl⟩ := quotientMap_surjective point
    rfl
  right_inv := by
    intro field
    apply Subtype.ext
    rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem fieldEquiv_apply (field : KleinBrillouinQuotient → V)
    (point : BrillouinTorus) :
    (fieldEquiv (V := V) field).1 point = field (quotientMap point) := rfl

@[simp] theorem fieldEquiv_symm_apply (field : invariantFields (V := V))
    (point : BrillouinTorus) :
    ((fieldEquiv (V := V)).symm field) (quotientMap point) = field.1 point := rfl

def glidePullback : Module.End ℝ (BrillouinTorus → V) where
  toFun field point := field (torusGlide point)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem commuting_preserves_invariants
    (operator : Module.End ℝ (BrillouinTorus → V))
    (commutes : Commute operator glidePullback)
    (field : invariantFields (V := V)) :
    operator field ∈ invariantFields := by
  intro point
  have fixed : glidePullback (field : BrillouinTorus → V) = field :=
    funext field.property
  have transported := congrFun (LinearMap.congr_fun commutes.eq
    (field : BrillouinTorus → V)) point
  change operator (glidePullback field) point =
    operator field (torusGlide point) at transported
  rw [fixed] at transported
  exact transported.symm

def restrictOperator (operator : Module.End ℝ (BrillouinTorus → V))
    (preserves : ∀ field : invariantFields (V := V),
      operator field ∈ invariantFields) : Module.End ℝ (invariantFields (V := V)) :=
  operator.restrict (fun field fixed => preserves ⟨field, fixed⟩)

def quotientOperator (operator : Module.End ℝ (BrillouinTorus → V))
    (preserves : ∀ field : invariantFields (V := V),
      operator field ∈ invariantFields) : Module.End ℝ (KleinBrillouinQuotient → V) :=
  (fieldEquiv (V := V)).symm.conjAlgEquiv ℝ (restrictOperator operator preserves)

@[simp] theorem quotientOperator_apply
    (operator : Module.End ℝ (BrillouinTorus → V))
    (preserves : ∀ field : invariantFields (V := V),
      operator field ∈ invariantFields)
    (field : KleinBrillouinQuotient → V) (point : BrillouinTorus) :
    quotientOperator operator preserves field (quotientMap point) =
      operator (fun representative => field (quotientMap representative)) point := rfl

theorem quotientOperator_unique
    (operator : Module.End ℝ (BrillouinTorus → V))
    (preserves : ∀ field : invariantFields (V := V),
      operator field ∈ invariantFields)
    (candidate : Module.End ℝ (KleinBrillouinQuotient → V))
    (evaluation : ∀ field point, candidate field (quotientMap point) =
      operator (fun representative => field (quotientMap representative)) point) :
    candidate = quotientOperator operator preserves := by
  ext field point
  obtain ⟨representative, rfl⟩ := quotientMap_surjective point
  exact evaluation field representative

theorem restrictOperator_sq_zero
    (operator : Module.End ℝ (BrillouinTorus → V))
    (preserves : ∀ field : invariantFields (V := V),
      operator field ∈ invariantFields) (square : operator * operator = 0) :
    restrictOperator operator preserves * restrictOperator operator preserves = 0 := by
  apply LinearMap.ext
  intro field
  apply Subtype.ext
  exact LinearMap.congr_fun square (field : BrillouinTorus → V)

theorem quotientOperator_sq_zero
    (operator : Module.End ℝ (BrillouinTorus → V))
    (preserves : ∀ field : invariantFields (V := V),
      operator field ∈ invariantFields) (square : operator * operator = 0) :
    quotientOperator operator preserves * quotientOperator operator preserves = 0 := by
  unfold quotientOperator
  rw [← map_mul, restrictOperator_sq_zero operator preserves square, map_zero]

theorem quotient_dirac_square
    (differential codifferential : Module.End ℝ (BrillouinTorus → V))
    (differential_preserves : ∀ field : invariantFields (V := V),
      differential field ∈ invariantFields)
    (codifferential_preserves : ∀ field : invariantFields (V := V),
      codifferential field ∈ invariantFields)
    (differential_square : differential * differential = 0)
    (codifferential_square : codifferential * codifferential = 0) :
    let descendedD := quotientOperator differential differential_preserves
    let descendedCod := quotientOperator codifferential codifferential_preserves
    Canonical.DiscreteDiracHodgeChiral.diracHodge descendedD descendedCod *
        Canonical.DiscreteDiracHodgeChiral.diracHodge descendedD descendedCod =
      Canonical.DiscreteDiracHodgeChiral.hodgeLaplacian descendedD descendedCod := by
  exact Canonical.DiscreteDiracHodgeChiral.diracHodge_sq_eq_hodgeLaplacian _ _
    (quotientOperator_sq_zero differential differential_preserves differential_square)
    (quotientOperator_sq_zero codifferential codifferential_preserves codifferential_square)

end InfoGeometry.Topology.KleinRealOperatorDescent

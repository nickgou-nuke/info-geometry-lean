/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.KleinBottleOrbitQuotient
import InfoGeometry.Canonical.DiscreteDiracHodgeChiral
import InfoGeometry.Canonical.KleinBottleTomitaCrosscapBridge
import InfoGeometry.Clifford.OperatorKleinTomitaCPTBridge
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
import InfoGeometry.Physics.ModularTimeEvolutionAutomorphism
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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
open scoped Matrix

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

/-! ### Modular time evolution on the quotient crosscap algebra

The quotient field algebra above is an actual ring of continuous, operator-valued
sections.  A modular time slice acts on this algebra when it is continuous on
the coefficient ring and commutes with both defining maps of the crosscap
equalizer.  These compatibility conditions are stated explicitly; they are
not consequences of the abstract ring-level flow laws. -/

section ModularTimeEvolution

open InfoGeometry.Physics

omit [TopologicalSpace M] [IsTopologicalRing M] in
/-- Tomita--Klein monodromy gives the time-reversal law for the multiplicative
CPT map on a modular flow, provided the flow commutes with the ring star.
The involutive anti-automorphism is applied twice in the monodromy identity;
its involutivity cancels one occurrence, leaving the required CPT action at
negative time. -/
theorem modularTimeEvolution_tomitaCPT_reverses_time
    (D : CrosscapDatum M) (F : ModularTimeEvolutionData M)
    (hStarFlow : ∀ (t : ℝ) (x : M),
      star (F.sigma t x) = F.sigma t (star x))
    (hKlein : InfoGeometry.Clifford.OperatorKleinTomitaCPT.IsTomitaKleinModular
      D.J F.toModularFlowData)
    (t : ℝ) (x : M) :
    tomitaCPT D (F.sigma t x) = F.sigma (-t) (tomitaCPT D x) := by
  change D.J.toFun (star (F.sigma t x)) = F.sigma (-t) (D.J.toFun (star x))
  rw [hStarFlow]
  have h := hKlein t (D.J.toFun (star x))
  change D.J.toFun
      (F.sigma t (D.J.toFun (D.J.toFun (star x)))) =
    F.sigma (-t) (D.J.toFun (star x)) at h
  rw [D.J.inv] at h
  exact h

omit [StarRing M] [TopologicalSpace M] [IsTopologicalRing M] in
/-- If a modular time slice fixes the two Peirce idempotents, it commutes with
the existing DeWitt body and soul projections on the operator ring. This keeps
the even/odd decomposition compatible with the time evolution without replacing
the operator carrier by scalar data. -/
theorem modularTimeEvolution_commutes_with_peirce_projections
    (F : ModularTimeEvolutionData M) [S : ChiralPeirceSystem M]
    (t : ℝ) (hPL : F.sigma t S.PL = S.PL)
    (x : M) :
    F.sigma t (body x) = body (F.sigma t x) ∧
    F.sigma t (soul x) = soul (F.sigma t x) := by
  have hPR : F.sigma t S.PR = S.PR := by
    rw [InfoGeometry.Algebra.DeWittPeirceChiralBridge.right_is_complement]
    let σ := modularTimeEvolutionRingHom F t
    change σ (1 - S.PL) = 1 - S.PL
    have hPL' : σ S.PL = S.PL := hPL
    rw [map_sub σ, map_one σ, hPL']
  constructor <;> simp [body, soul, soul_LR, soul_RL,
    F.sigma_additive, F.sigma_multiplicative, hPL, hPR]

omit [TopologicalSpace M] [IsTopologicalRing M] in
/-- The multiplicative glide and the multiplicative Tomita-CPT composite
preserve a crosscap fixed point under a time slice when both transport it by
the same reparameterization. -/
theorem modularTimeEvolution_preserves_crosscap
    (D : CrosscapDatum M) (F : ModularTimeEvolutionData M)
    (timeTransform : ℝ → ℝ)
    (hGlide : ∀ (t : ℝ) (x : M),
      D.glide (F.sigma t x) = F.sigma (timeTransform t) (D.glide x))
    (hCPT : ∀ (t : ℝ) (x : M),
      tomitaCPT D (F.sigma t x) = F.sigma (timeTransform t) (tomitaCPT D x))
    (t : ℝ) (x : M) (hx : InCrosscapSubalgebra D x) :
    InCrosscapSubalgebra D (F.sigma t x) := by
  change D.glide (F.sigma t x) = tomitaCPT D (F.sigma t x)
  rw [hGlide, hx, hCPT]

omit [TopologicalSpace M] [IsTopologicalRing M] in
/-- Klein monodromy and star-equivariance supply the CPT part of the crosscap
flow condition.  Thus preservation follows from the single remaining
compatibility: the glide transports time to its inverse. -/
theorem modularTimeEvolution_preserves_crosscap_of_tomitaKlein
    (D : CrosscapDatum M) (F : ModularTimeEvolutionData M)
    (hGlide : ∀ (t : ℝ) (x : M),
      D.glide (F.sigma t x) = F.sigma (-t) (D.glide x))
    (hStarFlow : ∀ (t : ℝ) (x : M),
      star (F.sigma t x) = F.sigma t (star x))
    (hKlein : InfoGeometry.Clifford.OperatorKleinTomitaCPT.IsTomitaKleinModular
      D.J F.toModularFlowData)
    (t : ℝ) (x : M) (hx : InCrosscapSubalgebra D x) :
    InCrosscapSubalgebra D (F.sigma t x) := by
  change D.glide (F.sigma t x) = tomitaCPT D (F.sigma t x)
  rw [hGlide t x, hx,
    modularTimeEvolution_tomitaCPT_reverses_time D F hStarFlow hKlein t x]

/-- Restrict a Tomita--Klein compatible modular time evolution to continuous
crosscap fields on the Klein quotient.  The glide and multiplicative CPT map
both transport time to its inverse; the latter compatibility is derived from
the ring-star equivariance and Tomita--Klein monodromy. -/
def crosscapQuotientModularTimeEvolution
    (D : CrosscapDatum M) (F : ModularTimeEvolutionData M)
    (hContinuous : ∀ t : ℝ, Continuous (F.sigma t))
    (hGlide : ∀ (t : ℝ) (x : M),
      D.glide (F.sigma t x) = F.sigma (-t) (D.glide x))
    (hStarFlow : ∀ (t : ℝ) (x : M),
      star (F.sigma t x) = F.sigma t (star x))
    (hKlein : InfoGeometry.Clifford.OperatorKleinTomitaCPT.IsTomitaKleinModular
      D.J F.toModularFlowData) :
    ModularTimeEvolutionData (crosscapQuotientContinuousSubring D) where
  sigma t field :=
    ⟨⟨fun point => F.sigma t (field.1 point),
      (hContinuous t).comp field.1.continuous_toFun⟩,
      fun point => modularTimeEvolution_preserves_crosscap_of_tomitaKlein D F hGlide
        hStarFlow hKlein t (field.1 point) (field.2 point)⟩
  sigma_zero field := by
    apply Subtype.ext
    ext point
    exact F.sigma_zero (field.1 point)
  sigma_add t s field := by
    apply Subtype.ext
    ext point
    exact F.sigma_add t s (field.1 point)
  sigma_neg_left t field := by
    apply Subtype.ext
    ext point
    exact F.sigma_neg_left t (field.1 point)
  sigma_neg_right t field := by
    apply Subtype.ext
    ext point
    exact F.sigma_neg_right t (field.1 point)
  sigma_zero_add t := by
    apply Subtype.ext
    ext point
    exact F.sigma_zero_add t
  sigma_additive t first second := by
    apply Subtype.ext
    ext point
    exact F.sigma_additive t (first.1 point) (second.1 point)
  sigma_one t := by
    apply Subtype.ext
    ext point
    exact F.sigma_one t
  sigma_multiplicative t first second := by
    apply Subtype.ext
    ext point
    exact F.sigma_multiplicative t (first.1 point) (second.1 point)

/-! ### Existing finite matrix crosscap with a concrete quotient flow

The following instance uses the `M₂(ℝ)` crosscap owner from
`KleinBottleTomitaCrosscapBridge`. Its glide and Tomita maps retain their
existing sheet convention. The rotation flow is inner conjugation by the real
rotation matrix, and its intertwining equations instantiate the quotient
construction above. -/

private def crosscapRotation2 (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]

private theorem crosscapRotation2_mul (t s : ℝ) :
    crosscapRotation2 (t + s) = crosscapRotation2 t * crosscapRotation2 s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crosscapRotation2, Matrix.mul_apply, Fin.sum_univ_two,
      Real.cos_add, Real.sin_add] <;> ring

private theorem crosscapRotation2_transpose (t : ℝ) :
    (crosscapRotation2 t)ᵀ = crosscapRotation2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crosscapRotation2, Real.cos_neg, Real.sin_neg]

private theorem crosscapRotation2_orthogonal (t : ℝ) :
    (crosscapRotation2 t)ᵀ * crosscapRotation2 t = 1 := by
  rw [crosscapRotation2_transpose]
  calc crosscapRotation2 (-t) * crosscapRotation2 t =
      crosscapRotation2 ((-t) + t) := by rw [crosscapRotation2_mul]
    _ = crosscapRotation2 0 := by
      congr 1
      ring
    _ = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [crosscapRotation2, Real.cos_zero, Real.sin_zero]

private theorem crosscapRotation2_orthogonal_right (t : ℝ) :
    crosscapRotation2 t * (crosscapRotation2 t)ᵀ = 1 := by
  rw [crosscapRotation2_transpose]
  calc crosscapRotation2 t * crosscapRotation2 (-t) =
      crosscapRotation2 (t + -t) := by rw [crosscapRotation2_mul]
    _ = crosscapRotation2 0 := by
      congr 1
      ring
    _ = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [crosscapRotation2, Real.cos_zero, Real.sin_zero]

private def mat2CrosscapFlowSlice (t : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  crosscapRotation2 t * A * (crosscapRotation2 t)ᵀ

private theorem mat2CrosscapFlowSlice_add (t s : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    mat2CrosscapFlowSlice (t + s) A =
      mat2CrosscapFlowSlice t (mat2CrosscapFlowSlice s A) := by
  simp only [mat2CrosscapFlowSlice]
  rw [crosscapRotation2_mul, Matrix.transpose_mul]
  noncomm_ring

private theorem mat2CrosscapFlowSlice_zero (A : Matrix (Fin 2) (Fin 2) ℝ) :
    mat2CrosscapFlowSlice 0 A = A := by
  simp only [mat2CrosscapFlowSlice]
  have h0 : crosscapRotation2 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [crosscapRotation2, Real.cos_zero, Real.sin_zero]
  simp [h0]

private theorem mat2CrosscapFlowSlice_neg_left (t : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    mat2CrosscapFlowSlice (-t) (mat2CrosscapFlowSlice t A) = A := by
  calc mat2CrosscapFlowSlice (-t) (mat2CrosscapFlowSlice t A) =
      mat2CrosscapFlowSlice ((-t) + t) A :=
        (mat2CrosscapFlowSlice_add (-t) t A).symm
    _ = mat2CrosscapFlowSlice 0 A := by
      congr 1
      abel
    _ = A := mat2CrosscapFlowSlice_zero A

private theorem mat2CrosscapFlowSlice_neg_right (t : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    mat2CrosscapFlowSlice t (mat2CrosscapFlowSlice (-t) A) = A := by
  calc mat2CrosscapFlowSlice t (mat2CrosscapFlowSlice (-t) A) =
      mat2CrosscapFlowSlice (t + -t) A :=
        (mat2CrosscapFlowSlice_add t (-t) A).symm
    _ = mat2CrosscapFlowSlice 0 A := by
      congr 1
      abel
    _ = A := mat2CrosscapFlowSlice_zero A

private noncomputable def mat2CrosscapModularFlow :
    ModularTimeEvolutionData (Matrix (Fin 2) (Fin 2) ℝ) where
  sigma := mat2CrosscapFlowSlice
  sigma_zero := mat2CrosscapFlowSlice_zero
  sigma_add := mat2CrosscapFlowSlice_add
  sigma_neg_left := mat2CrosscapFlowSlice_neg_left
  sigma_neg_right := mat2CrosscapFlowSlice_neg_right
  sigma_zero_add t := by simp [mat2CrosscapFlowSlice]
  sigma_additive t A B := by
    simp only [mat2CrosscapFlowSlice, Matrix.mul_add, add_mul]
  sigma_one t := by
    simp only [mat2CrosscapFlowSlice, Matrix.mul_one]
    exact crosscapRotation2_orthogonal_right t
  sigma_multiplicative t A B := by
    simp only [mat2CrosscapFlowSlice]
    calc crosscapRotation2 t * (A * B) * (crosscapRotation2 t)ᵀ =
        crosscapRotation2 t * A * ((crosscapRotation2 t)ᵀ *
          crosscapRotation2 t) * B * (crosscapRotation2 t)ᵀ := by
            rw [crosscapRotation2_orthogonal]
            noncomm_ring
      _ = (crosscapRotation2 t * A * (crosscapRotation2 t)ᵀ) *
          (crosscapRotation2 t * B * (crosscapRotation2 t)ᵀ) := by noncomm_ring

private theorem mat2CrosscapFlowSlice_continuous (t : ℝ) :
    Continuous (mat2CrosscapFlowSlice t) := by
  change Continuous (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
    crosscapRotation2 t * A * (crosscapRotation2 t)ᵀ)
  exact (continuous_const.mul continuous_id).mul continuous_const

private theorem mat2CrosscapFlowSlice_star (t : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    star (mat2CrosscapFlowSlice t A) = mat2CrosscapFlowSlice t (star A) := by
  simp only [mat2CrosscapFlowSlice, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  noncomm_ring

private theorem mat2SheetGlideRotation_conjugation (t : ℝ) :
    (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) *
        crosscapRotation2 t * !![1, 0; 0, -1] = crosscapRotation2 (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crosscapRotation2, Matrix.mul_apply, Fin.sum_univ_two,
      Real.cos_neg, Real.sin_neg]

private theorem mat2CrosscapFlow_glide_intertwines (t : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    InfoGeometry.Canonical.KleinBottleTomitaCrosscap.mat2SheetPreservingCrosscapDatum.glide
        (mat2CrosscapFlowSlice t A) =
      mat2CrosscapFlowSlice (-t)
        (InfoGeometry.Canonical.KleinBottleTomitaCrosscap.mat2SheetPreservingCrosscapDatum.glide A) := by
  let g : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
  change g * (crosscapRotation2 t * A * (crosscapRotation2 t)ᵀ) * g =
    crosscapRotation2 (-t) * (g * A * g) * (crosscapRotation2 (-t))ᵀ
  have hg2 : g * g = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [g, Matrix.mul_apply, Fin.sum_univ_two]
  have hG := mat2SheetGlideRotation_conjugation t
  have hGT : g * (crosscapRotation2 t)ᵀ * g = (crosscapRotation2 (-t))ᵀ := by
    rw [crosscapRotation2_transpose t, mat2SheetGlideRotation_conjugation (-t),
      neg_neg, crosscapRotation2_transpose (-t)]
    simp only [neg_neg]
  calc
    _ = g * crosscapRotation2 t * (g * g) * A * (g * g) *
          (crosscapRotation2 t)ᵀ * g := by
            rw [hg2]
            noncomm_ring
    _ = (g * crosscapRotation2 t * g) * (g * A * g) *
          (g * (crosscapRotation2 t)ᵀ * g) := by
            noncomm_ring
    _ = crosscapRotation2 (-t) * (g * A * g) *
          (crosscapRotation2 (-t))ᵀ := by
          rw [show g = !![1, 0; 0, -1] by rfl, hG, hGT]

private theorem mat2CrosscapFlow_tomitaKlein :
    InfoGeometry.Clifford.OperatorKleinTomitaCPT.IsTomitaKleinModular
      InfoGeometry.Canonical.KleinBottleTomitaCrosscap.mat2SheetPreservingCrosscapDatum.J
        mat2CrosscapModularFlow.toModularFlowData := by
  intro t A
  change (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
      star (mat2CrosscapFlowSlice t
        ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * star A *
          !![0, 1; 1, 0])) * !![0, 1; 1, 0] =
      mat2CrosscapFlowSlice (-t) A
  rw [mat2CrosscapFlowSlice_star]
  change (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
      (crosscapRotation2 t *
        star ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * star A *
          !![0, 1; 1, 0]) * (crosscapRotation2 t)ᵀ) * !![0, 1; 1, 0] = _
  have hX : ∀ s : ℝ,
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * crosscapRotation2 s *
        !![0, 1; 1, 0] = crosscapRotation2 (-s) := by
    intro s
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [crosscapRotation2, Matrix.mul_apply, Fin.sum_univ_two,
        Real.cos_neg, Real.sin_neg]
  have hXT :
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
        (crosscapRotation2 t)ᵀ * !![0, 1; 1, 0] =
        (crosscapRotation2 (-t))ᵀ := by
    rw [crosscapRotation2_transpose t, hX (-t), neg_neg,
      crosscapRotation2_transpose (-t)]
    rw [neg_neg]
  have hJstar :
      star ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * star A *
        !![0, 1; 1, 0]) =
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * A * !![0, 1; 1, 0] := by
    change ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * Aᵀ *
      !![0, 1; 1, 0])ᵀ =
      !![0, 1; 1, 0] * A * !![0, 1; 1, 0]
    have hXt : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ =
        !![0, 1; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hXt]
    noncomm_ring
  rw [hJstar, mat2CrosscapFlowSlice]
  calc
    _ = ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
        crosscapRotation2 t * !![0, 1; 1, 0]) * A *
        ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
          (crosscapRotation2 t)ᵀ * !![0, 1; 1, 0]) := by noncomm_ring
    _ = mat2CrosscapFlowSlice (-t) A := by
          rw [hX, hXT]
          rfl

private def mat2CrosscapQuotientFlow :
    ModularTimeEvolutionData
      (crosscapQuotientContinuousSubring
        InfoGeometry.Canonical.KleinBottleTomitaCrosscap.mat2SheetPreservingCrosscapDatum) :=
  crosscapQuotientModularTimeEvolution
    InfoGeometry.Canonical.KleinBottleTomitaCrosscap.mat2SheetPreservingCrosscapDatum
    mat2CrosscapModularFlow
    mat2CrosscapFlowSlice_continuous
    mat2CrosscapFlow_glide_intertwines
    mat2CrosscapFlowSlice_star
    mat2CrosscapFlow_tomitaKlein

/-- The existing paired-soul element `U - V` in the sheet-preserving
`M₂(ℝ)` crosscap is fixed by the concrete rotation modular flow.  This
identifies the surviving crosscap channel dynamically, while the two pure
Peirce corners remain excluded by
`mat2_crosscap_paired_soul_fixed_locus`. -/
theorem mat2CrosscapSoulMatrix_flow_fixed :
    ∀ t : ℝ, mat2CrosscapFlowSlice t
      (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
        (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mat2CrosscapFlowSlice, crosscapRotation2, Matrix.mul_apply,
      Fin.sum_univ_two] <;> nlinarith [Real.sin_sq_add_cos_sq t]

/-- The square of the commutator with the left sheet, evaluated pointwise on
a continuous Klein-quotient crosscap field.  Ring-general crosscap closure
places this induced second-grade operator field back in the same quotient
subring; its continuity comes from the existing continuous-map ring. -/
def crosscapQuotientPeirceObstructionSquare
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hJPL : D.J.toFun S.PL = S.PR)
    (hΩPL : D.glide S.PL = S.PR)
    (field : crosscapQuotientContinuousSubring D) :
    crosscapQuotientContinuousSubring D := by
  refine ⟨⟨fun point =>
      InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL (field.1 point) *
        InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL (field.1 point), ?_⟩, ?_⟩
  · have hComm : Continuous (fun point : KleinBrillouinQuotient =>
        InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL (field.1 point)) := by
      change Continuous (fun point => S.PL * field.1 point - field.1 point * S.PL)
      exact (continuous_const.mul field.1.continuous_toFun).sub
        (field.1.continuous_toFun.mul continuous_const)
    exact hComm.mul hComm
  · intro point
    exact (crosscap_fixed_peirce_obstruction_generates_body_grade D
      hstarPL hJPL hΩPL (field.1 point) (field.2 point)).2.1

omit [StarRing M] [TopologicalSpace M] [IsTopologicalRing M] in
/-- A modular time slice fixing the left Peirce idempotent transports the
noncommutativity commutator square covariantly.  This is the operator-level
step that makes the obstruction-generated body grade compatible with the
induced quotient flow. -/
theorem modularTimeEvolution_transports_peirce_obstruction_square
    (F : ModularTimeEvolutionData M) [S : ChiralPeirceSystem M]
    (t : ℝ) (hPL : F.sigma t S.PL = S.PL) (x : M) :
    F.sigma t
        (InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL x *
          InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL x) =
      InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL (F.sigma t x) *
        InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL (F.sigma t x) := by
  let σ := modularTimeEvolutionRingHom F t
  have hPL' : σ S.PL = S.PL := hPL
  have hComm : σ (InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL x) =
      InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL (σ x) := by
    change σ (S.PL * x - x * S.PL) = S.PL * σ x - σ x * S.PL
    rw [map_sub σ, map_mul σ, map_mul σ, hPL']
  change σ (InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL x *
    InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL x) =
      InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL (σ x) *
        InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL (σ x)
  rw [map_mul σ, hComm]

@[simp] theorem crosscapQuotientModularTimeEvolution_transports_peirce_obstruction_square
    (D : CrosscapDatum M) (F : ModularTimeEvolutionData M)
    (hContinuous : ∀ t : ℝ, Continuous (F.sigma t))
    (hGlide : ∀ (t : ℝ) (x : M),
      D.glide (F.sigma t x) = F.sigma (-t) (D.glide x))
    (hStarFlow : ∀ (t : ℝ) (x : M),
      star (F.sigma t x) = F.sigma t (star x))
    (hKlein : InfoGeometry.Clifford.OperatorKleinTomitaCPT.IsTomitaKleinModular
      D.J F.toModularFlowData)
    [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hJPL : D.J.toFun S.PL = S.PR)
    (hΩPL : D.glide S.PL = S.PR)
    (t : ℝ) (hPL : F.sigma t S.PL = S.PL)
    (field : crosscapQuotientContinuousSubring D) :
    (crosscapQuotientModularTimeEvolution D F hContinuous hGlide hStarFlow hKlein).sigma t
      (crosscapQuotientPeirceObstructionSquare D hstarPL hJPL hΩPL field) =
    crosscapQuotientPeirceObstructionSquare D hstarPL hJPL hΩPL
      ((crosscapQuotientModularTimeEvolution D F hContinuous hGlide hStarFlow hKlein).sigma t
        field) ∧
    (∀ point : KleinBrillouinQuotient,
      body ((crosscapQuotientPeirceObstructionSquare D hstarPL hJPL hΩPL field).1 point) =
        (crosscapQuotientPeirceObstructionSquare D hstarPL hJPL hΩPL field).1 point ∧
      InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL
        ((crosscapQuotientPeirceObstructionSquare D hstarPL hJPL hΩPL field).1 point) = 0) := by
  constructor
  · apply Subtype.ext
    ext point
    change F.sigma t
        (InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL (field.1 point) *
          InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL (field.1 point)) =
      InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL (F.sigma t (field.1 point)) *
        InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL (F.sigma t (field.1 point))
    exact modularTimeEvolution_transports_peirce_obstruction_square F t hPL (field.1 point)
  · intro point
    exact ⟨
      (crosscap_fixed_peirce_obstruction_generates_body_grade D hstarPL hJPL hΩPL
        (field.1 point) (field.2 point)).2.2.1,
      (crosscap_fixed_peirce_obstruction_generates_body_grade D hstarPL hJPL hΩPL
        (field.1 point) (field.2 point)).2.2.2⟩

end ModularTimeEvolution

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

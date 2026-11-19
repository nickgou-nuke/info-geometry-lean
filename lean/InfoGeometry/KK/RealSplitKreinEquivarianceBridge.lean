/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.KK.RealSplitKreinKasparovCycle
import InfoGeometry.KK.DiracFredholmIndex
import InfoGeometry.KK.ClNNFredholmBridge
import InfoGeometry.KK.Examples
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
import InfoGeometry.Canonical.Erlangen20Unification
import InfoGeometry.OperatorAlgebra.SymmetryInvariants
import InfoGeometry.Erlangen.InvariantGeometry
import InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation
import InfoGeometry.Clifford.CoordinateLessCliffordInvariance
import InfoGeometry.Categorical.CantorDoubleCylinderColimitAlgebra
import InfoGeometry.Krein.DoubledSpace
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Equivariance interface for the primitive real split-Krein cycle

This owner records the exact algebraic hypotheses needed to call a bounded
real split-Krein cycle equivariant.  It deliberately does not assert an
analytic `KK^G` class, a group integration, or a Kasparov product.  Those are
separate layers.  The present interface only transports a Lie-algebra action
through the bounded phase, grading, and represented algebra actions.
-/

noncomputable section

namespace InfoGeometry.KK.RealSplitKreinEquivarianceBridge

open InfoGeometry.KK
open InfoGeometry.Krein

/-- Scoped `LieRing` on `EndH H` inherited from associative operator composition.
Opening `InfoGeometry.KK.RealSplitKreinEquivarianceBridge` (or `open scoped ...`) brings this
instance into scope without leaking globally or colliding with `DoubleCylinderColimit` /
`ClTower` / `ℝ`. -/
scoped instance (priority := 100) instLieRingEndH
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] :
    LieRing (EndH H) :=
  LieRing.ofAssociativeRing

/-- Scoped `LieAlgebra ℝ` on `EndH H` inherited from associative operator composition. -/
scoped instance (priority := 100) instLieAlgebraEndH
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] :
    LieAlgebra ℝ (EndH H) :=
  LieAlgebra.ofAssociativeAlgebra

variable {A B H 𝔤 : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]
variable [LieRing 𝔤] [LieAlgebra ℝ 𝔤]

/-- A proof-carrying Lie-algebra action on the primitive bounded cycle.

The fields are intentionally operator-level.  In particular, `action` is a
Lie homomorphism into bounded endomorphisms, while the three commutation
fields are the exact equivariance conditions used below.
-/
structure EquivariantDatum
    (X : RealSplitKreinKasparovCycle A B H) where
  action : 𝔤 →ₗ⁅ℝ⁆ EndH H
  commutes_phase : ∀ D, action D * X.F = X.F * action D
  commutes_grade : ∀ D,
    action D * KreinGradedModule.gradeCLM (H := H) =
      KreinGradedModule.gradeCLM (H := H) * action D
  commutes_left_rep : ∀ D a, action D * X.π a = X.π a * action D
  commutes_right_rep : ∀ D b, action D * X.ρ b = X.ρ b * action D

/-- Zero-instance smart constructor for `EquivariantDatum` from an ℝ-linear map
`act : 𝔤 →ₗ[ℝ] EndH H` and an explicit commutator compatibility law. Callers do not need
`open InfoGeometry.KK.RealSplitKreinEquivarianceBridge` or a `LieRing (EndH H)` instance in
scope. -/
def EquivariantDatum.ofLinearMap
    {A B H 𝔤 : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    {X : RealSplitKreinKasparovCycle A B H}
    (act : 𝔤 →ₗ[ℝ] EndH H)
    (map_lie : ∀ x y : 𝔤, act ⁅x, y⁆ = act x * act y - act y * act x)
    (commutes_phase : ∀ D, act D * X.F = X.F * act D)
    (commutes_grade : ∀ D,
      act D * KreinGradedModule.gradeCLM (H := H) =
        KreinGradedModule.gradeCLM (H := H) * act D)
    (commutes_left_rep : ∀ D a, act D * X.π a = X.π a * act D)
    (commutes_right_rep : ∀ D b, act D * X.ρ b = X.ρ b * act D) :
    EquivariantDatum (𝔤 := 𝔤) X where
  action :=
    letI : LieRing (EndH H) := LieRing.ofAssociativeRing
    letI : LieAlgebra ℝ (EndH H) := LieAlgebra.ofAssociativeAlgebra
    { toLinearMap := act
      map_lie' := fun {x y} => map_lie x y }
  commutes_phase := commutes_phase
  commutes_grade := commutes_grade
  commutes_left_rep := commutes_left_rep
  commutes_right_rep := commutes_right_rep

@[simp] theorem EquivariantDatum.ofLinearMap_apply
    {A B H 𝔤 : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    {X : RealSplitKreinKasparovCycle A B H}
    (act : 𝔤 →ₗ[ℝ] EndH H)
    (map_lie : ∀ x y : 𝔤, act ⁅x, y⁆ = act x * act y - act y * act x)
    (commutes_phase : ∀ D, act D * X.F = X.F * act D)
    (commutes_grade : ∀ D,
      act D * KreinGradedModule.gradeCLM (H := H) =
        KreinGradedModule.gradeCLM (H := H) * act D)
    (commutes_left_rep : ∀ D a, act D * X.π a = X.π a * act D)
    (commutes_right_rep : ∀ D b, act D * X.ρ b = X.ρ b * act D)
    (D : 𝔤) :
    (EquivariantDatum.ofLinearMap act map_lie commutes_phase commutes_grade
      commutes_left_rep commutes_right_rep).action D = act D :=
  rfl

variable {X : RealSplitKreinKasparovCycle A B H}

theorem action_commutes_phase_commutator
    (E : EquivariantDatum X) (D : 𝔤) (a : A) :
    E.action D * (X.F * X.π a - X.π a * X.F) =
      (X.F * X.π a - X.π a * X.F) * E.action D := by
  calc
    E.action D * (X.F * X.π a - X.π a * X.F) =
        (E.action D * X.F) * X.π a -
          (E.action D * X.π a) * X.F := by
            simp only [mul_sub, mul_assoc]
    _ = (X.F * E.action D) * X.π a -
          (X.π a * E.action D) * X.F := by
            rw [E.commutes_phase D, E.commutes_left_rep D a]
    _ = X.F * (E.action D * X.π a) -
          X.π a * (E.action D * X.F) := by
            simp only [mul_assoc]
    _ = X.F * (X.π a * E.action D) -
          X.π a * (X.F * E.action D) := by
            rw [E.commutes_left_rep D a, E.commutes_phase D]
    _ = (X.F * X.π a - X.π a * X.F) * E.action D := by
            simp only [sub_mul, mul_assoc]

theorem action_commutes_phase_square_defect
    (E : EquivariantDatum X) (D : 𝔤) :
    E.action D * (X.F * X.F - (1 : EndH H)) =
      (X.F * X.F - (1 : EndH H)) * E.action D := by
  calc
    E.action D * (X.F * X.F - (1 : EndH H)) =
        (E.action D * X.F) * X.F - E.action D := by
          simp only [mul_sub, mul_one, mul_assoc]
    _ = (X.F * E.action D) * X.F - E.action D := by
          rw [E.commutes_phase D]
    _ = X.F * (E.action D * X.F) - E.action D := by
          simp only [mul_assoc]
    _ = X.F * (X.F * E.action D) - E.action D := by
          rw [E.commutes_phase D]
    _ = (X.F * X.F - (1 : EndH H)) * E.action D := by
          simp only [sub_mul, one_mul, mul_assoc]

theorem action_preserves_compact_phase_defects
    (E : EquivariantDatum X) (D : 𝔤) (a : A) :
    E.action D * (X.F * X.F - (1 : EndH H)) =
        (X.F * X.F - (1 : EndH H)) * E.action D ∧
      E.action D * (X.F * X.π a - X.π a * X.F) =
        (X.F * X.π a - X.π a * X.F) * E.action D := by
  exact ⟨action_commutes_phase_square_defect E D,
    action_commutes_phase_commutator E D a⟩

theorem action_commutes_right_rep
    (E : EquivariantDatum X) (D : 𝔤) (b : B) :
    E.action D * X.ρ b = X.ρ b * E.action D :=
  E.commutes_right_rep D b

theorem action_preserves_phase_and_representations
    (E : EquivariantDatum X) (D : 𝔤) :
    E.action D * X.F = X.F * E.action D ∧
      (∀ a : A, E.action D * X.π a = X.π a * E.action D) ∧
      (∀ b : B, E.action D * X.ρ b = X.ρ b * E.action D) := by
  exact ⟨E.commutes_phase D, E.commutes_left_rep D, E.commutes_right_rep D⟩

theorem action_preserves_grading
    (E : EquivariantDatum X) (D : 𝔤) :
    E.action D * KreinGradedModule.gradeCLM (H := H) =
      KreinGradedModule.gradeCLM (H := H) * E.action D :=
  E.commutes_grade D

/-! ## Erlangen 2.0 & Chiral Fredholm Invariance Bridges (F2.4 / M3.5) -/

section Erlangen20AndChiralInvariance

open InfoGeometry.OperatorAlgebra
open InfoGeometry.Erlangen.InvariantGeometry
open InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
open InfoGeometry.Canonical.Erlangen20Unification

local instance (priority := 100) instLocalLieRingModuleEnd
    {V : Type*} [AddCommGroup V] [Module ℝ V] :
    LieRing (Module.End ℝ V) :=
  LieRing.ofAssociativeRing

local instance (priority := 100) instLocalLieAlgebraModuleEnd
    {V : Type*} [AddCommGroup V] [Module ℝ V] :
    LieAlgebra ℝ (Module.End ℝ V) :=
  LieAlgebra.ofAssociativeAlgebra

/-- Symmetry-adapted operator family extracted from a real split-Krein cycle `X`. -/
structure EquivariantSymmetryData
    {A B H : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    (X : RealSplitKreinKasparovCycle A B H) where
  phase : EndH H := X.F
  grading : EndH H := KreinGradedModule.gradeCLM (H := H)
  leftRep : A →ₐ[ℝ] EndH H := X.π
  rightRep : B →ₐ[ℝ] EndH H := X.ρ

/-- Chiral-kernel and defect invariants extracted from a real split-Krein cycle `X`. -/
structure EquivariantInvariantData
    {A B H : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    (X : RealSplitKreinKasparovCycle A B H) where
  chiralPlus : Submodule ℝ H := X.chiralKernelSlicePlus
  chiralMinus : Submodule ℝ H := X.chiralKernelSliceMinus
  phaseSquareDefect : EndH H := X.F * X.F - (1 : EndH H)

/-- The Lie-algebra representation `𝔤 →ₗ⁅ℝ⁆ Module.End ℝ H` induced by `EquivariantDatum X`. -/
def EquivariantDatum.endLieHom (E : EquivariantDatum (𝔤 := 𝔤) X) :
    𝔤 →ₗ⁅ℝ⁆ Module.End ℝ H :=
  (clmToEndAlgHom H).toLieHom.comp E.action

/-- Associative operator subalgebra of `Module.End ℝ H` generated by `E.action`. -/
def EquivariantDatum.operatorAlgebra (E : EquivariantDatum (𝔤 := 𝔤) X) :
    Subalgebra ℝ (Module.End ℝ H) :=
  Algebra.adjoin ℝ (Set.range fun D : 𝔤 => clmToEndAlgHom H (E.action D))

/-- Direct Erlangen 2.0 datum induced by `E : EquivariantDatum X` over `𝔤`. -/
def EquivariantDatum.toErlangen20Datum (E : EquivariantDatum (𝔤 := 𝔤) X) :
    Erlangen20Datum ℝ H 𝔤 (EquivariantSymmetryData X) (EquivariantInvariantData X) where
  operatorAlgebra := E.operatorAlgebra
  representation := E.endLieHom
  representation_mem D := Algebra.subset_adjoin (Set.mem_range_self D)
  symmetryData := {}
  invariantData := {}

@[simp] theorem EquivariantDatum.toErlangen20Datum_representation
    (E : EquivariantDatum (𝔤 := 𝔤) X) (D : 𝔤) :
    E.toErlangen20Datum.representation D = (E.action D).toLinearMap :=
  rfl

/-- `E.action D` preserves `X.chiralKernelSlicePlus`. -/
theorem action_maps_chiralKernelSlicePlus
    (E : EquivariantDatum (𝔤 := 𝔤) X) (D : 𝔤) {v : H} (hv : v ∈ X.chiralKernelSlicePlus) :
    E.action D v ∈ X.chiralKernelSlicePlus := by
  rcases hv with ⟨hvKer, ⟨w, rfl⟩⟩
  refine ⟨?_, ⟨E.action D w, ?_⟩⟩
  · change X.F (E.action D (KreinGradedModule.gradeProjPlus (H := H) w)) = 0
    have hF := congrArg (fun T : EndH H => T (KreinGradedModule.gradeProjPlus (H := H) w))
      (E.commutes_phase D)
    change E.action D (X.F (KreinGradedModule.gradeProjPlus (H := H) w)) =
      X.F (E.action D (KreinGradedModule.gradeProjPlus (H := H) w)) at hF
    rw [← hF]
    change E.action D (X.diracOperator (X.chiralProjectorPlus w)) = 0
    have hKer : X.diracOperator (X.chiralProjectorPlus w) = 0 := hvKer
    rw [hKer, map_zero]
  · change X.chiralProjectorPlus (E.action D w) = E.action D (X.chiralProjectorPlus w)
    have hG := congrArg (fun T : EndH H => T w) (E.commutes_grade D)
    change E.action D (KreinGradedModule.gradeCLM (H := H) w) =
      KreinGradedModule.gradeCLM (H := H) (E.action D w) at hG
    change (2 : ℝ)⁻¹ • (E.action D w + KreinGradedModule.gradeCLM (H := H) (E.action D w)) =
      E.action D ((2 : ℝ)⁻¹ • (w + KreinGradedModule.gradeCLM (H := H) w))
    rw [map_smul, map_add, hG]

/-- `E.action D` preserves `X.chiralKernelSliceMinus`. -/
theorem action_maps_chiralKernelSliceMinus
    (E : EquivariantDatum (𝔤 := 𝔤) X) (D : 𝔤) {v : H} (hv : v ∈ X.chiralKernelSliceMinus) :
    E.action D v ∈ X.chiralKernelSliceMinus := by
  rcases hv with ⟨hvKer, ⟨w, rfl⟩⟩
  refine ⟨?_, ⟨E.action D w, ?_⟩⟩
  · change X.F (E.action D (KreinGradedModule.gradeProjMinus (H := H) w)) = 0
    have hF := congrArg (fun T : EndH H => T (KreinGradedModule.gradeProjMinus (H := H) w))
      (E.commutes_phase D)
    change E.action D (X.F (KreinGradedModule.gradeProjMinus (H := H) w)) =
      X.F (E.action D (KreinGradedModule.gradeProjMinus (H := H) w)) at hF
    rw [← hF]
    change E.action D (X.diracOperator (X.chiralProjectorMinus w)) = 0
    have hKer : X.diracOperator (X.chiralProjectorMinus w) = 0 := hvKer
    rw [hKer, map_zero]
  · change X.chiralProjectorMinus (E.action D w) = E.action D (X.chiralProjectorMinus w)
    have hG := congrArg (fun T : EndH H => T w) (E.commutes_grade D)
    change E.action D (KreinGradedModule.gradeCLM (H := H) w) =
      KreinGradedModule.gradeCLM (H := H) (E.action D w) at hG
    change (2 : ℝ)⁻¹ • (E.action D w - KreinGradedModule.gradeCLM (H := H) (E.action D w)) =
      E.action D ((2 : ℝ)⁻¹ • (w - KreinGradedModule.gradeCLM (H := H) w))
    rw [map_smul, map_sub, hG]

/-- Bundled cross-pillar record pairing `EquivariantDatum X` with its induced
`Erlangen20Datum` and chiral kernel slice invariance. -/
structure EquivariantErlangenKasparov
    (A B H 𝔤 : Type*)
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (X : RealSplitKreinKasparovCycle A B H) where
  equivariant : EquivariantDatum (𝔤 := 𝔤) X
  erlangen : Erlangen20Datum ℝ H 𝔤 (EquivariantSymmetryData X) (EquivariantInvariantData X)
  erlangen_eq : erlangen = equivariant.toErlangen20Datum
  chiralPlus_invariant :
    ∀ D v, v ∈ X.chiralKernelSlicePlus → equivariant.action D v ∈ X.chiralKernelSlicePlus
  chiralMinus_invariant :
    ∀ D v, v ∈ X.chiralKernelSliceMinus → equivariant.action D v ∈ X.chiralKernelSliceMinus
  compact_defects_invariant :
    ∀ D a,
      equivariant.action D * (X.F * X.F - (1 : EndH H)) =
          (X.F * X.F - (1 : EndH H)) * equivariant.action D ∧
        equivariant.action D * (X.F * X.π a - X.π a * X.F) =
          (X.F * X.π a - X.π a * X.F) * equivariant.action D

/-- Canonical construction of `EquivariantErlangenKasparov` from `EquivariantDatum X`. -/
def EquivariantDatum.toEquivariantErlangenKasparov (E : EquivariantDatum (𝔤 := 𝔤) X) :
    EquivariantErlangenKasparov A B H 𝔤 X where
  equivariant := E
  erlangen := E.toErlangen20Datum
  erlangen_eq := rfl
  chiralPlus_invariant D _ hv := action_maps_chiralKernelSlicePlus E D hv
  chiralMinus_invariant D _ hv := action_maps_chiralKernelSliceMinus E D hv
  compact_defects_invariant D a := action_preserves_compact_phase_defects E D a

/-- Any grading- and phase-intertwining linear equivalence `e : H ≃ₗ[ℝ] H'` transports
`X.chiralKernelSlicePlus` linearly onto `Y.chiralKernelSlicePlus`. -/
def chiralKernelSlicePlusEquivOfIntertwiner
    {A' B' H' : Type*}
    [NormedRing A'] [NormedRing B']
    [NormedAlgebra ℝ A'] [NormedAlgebra ℝ B']
    [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H']
    [KreinSpace H'] [KreinGradedModule H']
    {Y : RealSplitKreinKasparovCycle A' B' H'}
    (e : H ≃ₗ[ℝ] H')
    (he_F : ∀ v : H, Y.F (e v) = e (X.F v))
    (he_grade : ∀ v : H,
      KreinGradedModule.gradeCLM (H := H') (e v) =
        e (KreinGradedModule.gradeCLM (H := H) v)) :
    X.chiralKernelSlicePlus ≃ₗ[ℝ] Y.chiralKernelSlicePlus where
  toFun v :=
    ⟨e v.1, by
      rcases v.2 with ⟨hvKer, ⟨w, hw⟩⟩
      refine ⟨?_, ⟨e w, ?_⟩⟩
      · change Y.F (e v.1) = 0
        rw [he_F]
        have h0 : X.F v.1 = 0 := hvKer
        rw [h0, map_zero]
      · change KreinGradedModule.gradeProjPlus (H := H') (e w) = e v.1
        rw [← hw]
        change (2 : ℝ)⁻¹ • (e w + KreinGradedModule.gradeCLM (H := H') (e w)) =
          e ((2 : ℝ)⁻¹ • (w + KreinGradedModule.gradeCLM (H := H) w))
        rw [he_grade, map_smul, map_add]⟩
  invFun u :=
    ⟨e.symm u.1, by
      rcases u.2 with ⟨huKer, ⟨w, hw⟩⟩
      refine ⟨?_, ⟨e.symm w, ?_⟩⟩
      · change X.F (e.symm u.1) = 0
        apply e.injective
        rw [← he_F, e.apply_symm_apply, map_zero]
        exact huKer
      · change KreinGradedModule.gradeProjPlus (H := H) (e.symm w) = e.symm u.1
        apply e.injective
        rw [e.apply_symm_apply, ← hw]
        change e ((2 : ℝ)⁻¹ • (e.symm w + KreinGradedModule.gradeCLM (H := H) (e.symm w))) =
          (2 : ℝ)⁻¹ • (w + KreinGradedModule.gradeCLM (H := H') w)
        rw [map_smul, map_add, e.apply_symm_apply, ← he_grade, e.apply_symm_apply]⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.1)
  right_inv u := Subtype.ext (e.apply_symm_apply u.1)
  map_add' v₁ v₂ := Subtype.ext (e.map_add v₁.1 v₂.1)
  map_smul' r v := Subtype.ext (e.map_smul r v.1)

/-- Any grading- and phase-intertwining linear equivalence `e : H ≃ₗ[ℝ] H'` transports
`X.chiralKernelSliceMinus` linearly onto `Y.chiralKernelSliceMinus`. -/
def chiralKernelSliceMinusEquivOfIntertwiner
    {A' B' H' : Type*}
    [NormedRing A'] [NormedRing B']
    [NormedAlgebra ℝ A'] [NormedAlgebra ℝ B']
    [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H']
    [KreinSpace H'] [KreinGradedModule H']
    {Y : RealSplitKreinKasparovCycle A' B' H'}
    (e : H ≃ₗ[ℝ] H')
    (he_F : ∀ v : H, Y.F (e v) = e (X.F v))
    (he_grade : ∀ v : H,
      KreinGradedModule.gradeCLM (H := H') (e v) =
        e (KreinGradedModule.gradeCLM (H := H) v)) :
    X.chiralKernelSliceMinus ≃ₗ[ℝ] Y.chiralKernelSliceMinus where
  toFun v :=
    ⟨e v.1, by
      rcases v.2 with ⟨hvKer, ⟨w, hw⟩⟩
      refine ⟨?_, ⟨e w, ?_⟩⟩
      · change Y.F (e v.1) = 0
        rw [he_F]
        have h0 : X.F v.1 = 0 := hvKer
        rw [h0, map_zero]
      · change KreinGradedModule.gradeProjMinus (H := H') (e w) = e v.1
        rw [← hw]
        change (2 : ℝ)⁻¹ • (e w - KreinGradedModule.gradeCLM (H := H') (e w)) =
          e ((2 : ℝ)⁻¹ • (w - KreinGradedModule.gradeCLM (H := H) w))
        rw [he_grade, map_smul, map_sub]⟩
  invFun u :=
    ⟨e.symm u.1, by
      rcases u.2 with ⟨huKer, ⟨w, hw⟩⟩
      refine ⟨?_, ⟨e.symm w, ?_⟩⟩
      · change X.F (e.symm u.1) = 0
        apply e.injective
        rw [← he_F, e.apply_symm_apply, map_zero]
        exact huKer
      · change KreinGradedModule.gradeProjMinus (H := H) (e.symm w) = e.symm u.1
        apply e.injective
        rw [e.apply_symm_apply, ← hw]
        change e ((2 : ℝ)⁻¹ • (e.symm w - KreinGradedModule.gradeCLM (H := H) (e.symm w))) =
          (2 : ℝ)⁻¹ • (w - KreinGradedModule.gradeCLM (H := H') w)
        rw [map_smul, map_sub, e.apply_symm_apply, ← he_grade, e.apply_symm_apply]⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.1)
  right_inv u := Subtype.ext (e.apply_symm_apply u.1)
  map_add' v₁ v₂ := Subtype.ext (e.map_add v₁.1 v₂.1)
  map_smul' r v := Subtype.ext (e.map_smul r v.1)

/-- Grading- and phase-intertwining equivalence preserves `ChiralFredholmSurface` and
`analyticalIndex`. -/
theorem analyticalIndex_eq_of_intertwiner
    {A' B' H' : Type*}
    [NormedRing A'] [NormedRing B']
    [NormedAlgebra ℝ A'] [NormedAlgebra ℝ B']
    [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H']
    [KreinSpace H'] [KreinGradedModule H']
    {Y : RealSplitKreinKasparovCycle A' B' H'}
    (e : H ≃ₗ[ℝ] H')
    (he_F : ∀ v : H, Y.F (e v) = e (X.F v))
    (he_grade : ∀ v : H,
      KreinGradedModule.gradeCLM (H := H') (e v) =
        e (KreinGradedModule.gradeCLM (H := H) v))
    (hX : X.ChiralFredholmSurface) :
    Y.ChiralFredholmSurface ∧
      ∀ (hY : Y.ChiralFredholmSurface), X.analyticalIndex hX = Y.analyticalIndex hY := by
  let ePlus := chiralKernelSlicePlusEquivOfIntertwiner (X := X) (Y := Y) e he_F he_grade
  let eMinus := chiralKernelSliceMinusEquivOfIntertwiner (X := X) (Y := Y) e he_F he_grade
  have hY : Y.ChiralFredholmSurface := by
    rcases hX with ⟨hXp, hXm⟩
    exact ⟨ePlus.finiteDimensional, eMinus.finiteDimensional⟩
  refine ⟨hY, fun hY' => ?_⟩
  rcases hX with ⟨hXp, hXm⟩
  rcases hY' with ⟨hYp, hYm⟩
  simp only [RealSplitKreinKasparovCycle.analyticalIndex]
  rw [ePlus.finrank_eq, eMinus.finrank_eq]

/-- In particular, transporting a cycle along a Krein- and grading-preserving linear isometry
equivalence `eH : H ≃ₗᵢ[ℝ] H'` preserves `ChiralFredholmSurface` and `analyticalIndex`. -/
theorem analyticalIndex_transportOfLinearIsometryEquiv
    {H' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H']
    [KreinSpace H'] [KreinGradedModule H']
    (eH : H ≃ₗᵢ[ℝ] H')
    (he_inner : ∀ u v : H, KreinSpace.kreinInner (eH u) (eH v) = KreinSpace.kreinInner u v)
    (he_grade : ∀ x : H, KreinGradedModule.grade (eH x) = eH (KreinGradedModule.grade x))
    (hX : X.ChiralFredholmSurface) :
    let Y := ClNNFredholmBridge.RealSplitKreinKasparovCycle.transportOfLinearIsometryEquiv
      eH he_inner he_grade X
    Y.ChiralFredholmSurface ∧
      ∀ (hY : Y.ChiralFredholmSurface), X.analyticalIndex hX = Y.analyticalIndex hY := by
  apply analyticalIndex_eq_of_intertwiner (X := X) eH.toLinearEquiv
  · intro v
    change eH (X.F (eH.symm (eH v))) = eH (X.F v)
    rw [eH.symm_apply_apply]
  · intro v
    exact he_grade v

/-- Group-level `SymmetryAction G (EndH H)` invariance for a real split-Krein cycle `X`:
if `g • F = F`, `g • Γ = Γ`, `g • J = J`, `g • π(a) = π(a)`, then the compact phase defect
`F² - 1`, `[F, π(a)]`, and chiral projectors `gradeProjPlus` / `gradeProjMinus` lie in
`invariantSubring α`. -/
theorem symmetryAction_preserves_cycle_invariants
    {G : Type*} [Group G]
    (α : SymmetryAction G (EndH H))
    (hF : ∀ g : G, α.act g X.F = X.F)
    (hGrade : ∀ g : G, α.act g (KreinGradedModule.gradeCLM (H := H)) =
      KreinGradedModule.gradeCLM (H := H))
    (hJ : ∀ g : G, α.act g X.cl11.J = X.cl11.J)
    (hπ : ∀ (g : G) (a : A), α.act g (X.π a) = X.π a) :
    (X.F * X.F - (1 : EndH H) ∈ invariantSubring α) ∧
      (∀ a : A, X.F * X.π a - X.π a * X.F ∈ invariantSubring α) ∧
      (∀ g : G, α.act g X.cl11.J = X.cl11.J) ∧
      (∀ g : G, α.act g (KreinGradedModule.gradeCLM (H := H)) =
        KreinGradedModule.gradeCLM (H := H)) := by
  refine ⟨?_, ?_, hJ, hGrade⟩
  · intro g
    simp [hF g]
  · intro a g
    simp [hF g, hπ g a]

/-- Group representation `G →* (EndH H)ˣ` preserving the bounded phase, grading, split atom
`cl11`, and both algebra representations of `X`. -/
structure EquivariantCycleGroupAction
    (G : Type*) [Group G]
    (X : RealSplitKreinKasparovCycle A B H) where
  unitAction : G →* (EndH H)ˣ
  commutes_phase : ∀ g : G, (unitAction g : EndH H) * X.F = X.F * (unitAction g : EndH H)
  commutes_grade : ∀ g : G,
    (unitAction g : EndH H) * KreinGradedModule.gradeCLM (H := H) =
      KreinGradedModule.gradeCLM (H := H) * (unitAction g : EndH H)
  commutes_J : ∀ g : G,
    (unitAction g : EndH H) * X.cl11.J = X.cl11.J * (unitAction g : EndH H)
  commutes_eps : ∀ g : G,
    (unitAction g : EndH H) * X.cl11.eps = X.cl11.eps * (unitAction g : EndH H)
  commutes_left_rep : ∀ (g : G) (a : A),
    (unitAction g : EndH H) * X.π a = X.π a * (unitAction g : EndH H)
  commutes_right_rep : ∀ (g : G) (b : B),
    (unitAction g : EndH H) * X.ρ b = X.ρ b * (unitAction g : EndH H)

/-- Conjugate `EndH H` by `U.unitAction g`, producing `SymmetryAction G (EndH H)`. -/
def EquivariantCycleGroupAction.toSymmetryAction
    {G : Type*} [Group G]
    (U : EquivariantCycleGroupAction G X) :
    SymmetryAction G (EndH H) where
  act g :=
    { toFun := fun T => (U.unitAction g : EndH H) * T * (↑(U.unitAction g)⁻¹ : EndH H)
      invFun := fun T => (↑(U.unitAction g)⁻¹ : EndH H) * T * (U.unitAction g : EndH H)
      left_inv := fun T => by simp [mul_assoc]
      right_inv := fun T => by simp [mul_assoc]
      map_mul' := fun S T => by simp [mul_assoc]
      map_add' := fun S T => by rw [mul_add, add_mul] }
  act_one T := by
    change (U.unitAction 1 : EndH H) * T * (↑(U.unitAction 1)⁻¹ : EndH H) = T
    simp
  act_mul g h T := by
    change (U.unitAction (g * h) : EndH H) * T * (↑(U.unitAction (g * h))⁻¹ : EndH H) =
      (U.unitAction g : EndH H) *
        ((U.unitAction h : EndH H) * T * (↑(U.unitAction h)⁻¹ : EndH H)) *
        (↑(U.unitAction g)⁻¹ : EndH H)
    rw [map_mul, _root_.mul_inv_rev]
    simp only [Units.val_mul, mul_assoc]

/-- The `G`-invariant chiral slice predicates (`IsGeometricInvariant`) and cycle invariants
induced by `U : EquivariantCycleGroupAction G X`. -/
theorem EquivariantCycleGroupAction.chiralSlices_isGeometricInvariant_and_invariants
    {G : Type*} [Group G]
    (U : EquivariantCycleGroupAction G X) :
    let _instMul : MulAction G H :=
      { smul := fun g v => (U.unitAction g : EndH H) v
        one_smul := fun v => by
          change (U.unitAction 1 : EndH H) v = v
          simp
        mul_smul := fun g h v => by
          change (U.unitAction (g * h) : EndH H) v =
            (U.unitAction g : EndH H) ((U.unitAction h : EndH H) v)
          rw [map_mul]
          rfl }
    @IsGeometricInvariant G H _ _instMul (fun v => v ∈ X.chiralKernelSlicePlus) ∧
      @IsGeometricInvariant G H _ _instMul (fun v => v ∈ X.chiralKernelSliceMinus) ∧
      (X.F * X.F - (1 : EndH H) ∈ invariantSubring U.toSymmetryAction) ∧
      (∀ a : A, X.F * X.π a - X.π a * X.F ∈ invariantSubring U.toSymmetryAction) := by
  let instMul : MulAction G H :=
    { smul := fun g v => (U.unitAction g : EndH H) v
      one_smul := fun v => by
        change (U.unitAction 1 : EndH H) v = v
        simp
      mul_smul := fun g h v => by
        change (U.unitAction (g * h) : EndH H) v =
          (U.unitAction g : EndH H) ((U.unitAction h : EndH H) v)
        rw [map_mul]
        rfl }
  have hMapPlus : ∀ (g : G) {v : H}, v ∈ X.chiralKernelSlicePlus →
      (U.unitAction g : EndH H) v ∈ X.chiralKernelSlicePlus := by
    intro g v ⟨hvKer, ⟨w, hw⟩⟩
    refine ⟨?_, ⟨(U.unitAction g : EndH H) w, ?_⟩⟩
    · change X.F ((U.unitAction g : EndH H) v) = 0
      have hF := congrArg (fun T : EndH H => T v) (U.commutes_phase g)
      change (U.unitAction g : EndH H) (X.F v) = X.F ((U.unitAction g : EndH H) v) at hF
      rw [← hF]
      have hv0 : X.F v = 0 := hvKer
      rw [hv0, map_zero]
    · change X.chiralProjectorPlus ((U.unitAction g : EndH H) w) = (U.unitAction g : EndH H) v
      rw [← hw]
      have hG := congrArg (fun T : EndH H => T w) (U.commutes_grade g)
      change (U.unitAction g : EndH H) (KreinGradedModule.gradeCLM (H := H) w) =
        KreinGradedModule.gradeCLM (H := H) ((U.unitAction g : EndH H) w) at hG
      change (2 : ℝ)⁻¹ • ((U.unitAction g : EndH H) w +
          KreinGradedModule.gradeCLM (H := H) ((U.unitAction g : EndH H) w)) =
        (U.unitAction g : EndH H) ((2 : ℝ)⁻¹ • (w + KreinGradedModule.gradeCLM (H := H) w))
      rw [map_smul, map_add, hG]
  have hMapMinus : ∀ (g : G) {v : H}, v ∈ X.chiralKernelSliceMinus →
      (U.unitAction g : EndH H) v ∈ X.chiralKernelSliceMinus := by
    intro g v ⟨hvKer, ⟨w, hw⟩⟩
    refine ⟨?_, ⟨(U.unitAction g : EndH H) w, ?_⟩⟩
    · change X.F ((U.unitAction g : EndH H) v) = 0
      have hF := congrArg (fun T : EndH H => T v) (U.commutes_phase g)
      change (U.unitAction g : EndH H) (X.F v) = X.F ((U.unitAction g : EndH H) v) at hF
      rw [← hF]
      have hv0 : X.F v = 0 := hvKer
      rw [hv0, map_zero]
    · change X.chiralProjectorMinus ((U.unitAction g : EndH H) w) = (U.unitAction g : EndH H) v
      rw [← hw]
      have hG := congrArg (fun T : EndH H => T w) (U.commutes_grade g)
      change (U.unitAction g : EndH H) (KreinGradedModule.gradeCLM (H := H) w) =
        KreinGradedModule.gradeCLM (H := H) ((U.unitAction g : EndH H) w) at hG
      change (2 : ℝ)⁻¹ • ((U.unitAction g : EndH H) w -
          KreinGradedModule.gradeCLM (H := H) ((U.unitAction g : EndH H) w)) =
        (U.unitAction g : EndH H) ((2 : ℝ)⁻¹ • (w - KreinGradedModule.gradeCLM (H := H) w))
      rw [map_smul, map_sub, hG]
  have hInv :
      (X.F * X.F - (1 : EndH H) ∈ invariantSubring U.toSymmetryAction) ∧
        (∀ a : A, X.F * X.π a - X.π a * X.F ∈ invariantSubring U.toSymmetryAction) := by
    have hSym := symmetryAction_preserves_cycle_invariants (X := X) U.toSymmetryAction
      (fun g => by
        change (U.unitAction g : EndH H) * X.F * (↑(U.unitAction g)⁻¹ : EndH H) = X.F
        rw [U.commutes_phase g, mul_assoc, Units.mul_inv, mul_one])
      (fun g => by
        change (U.unitAction g : EndH H) * KreinGradedModule.gradeCLM (H := H) *
            (↑(U.unitAction g)⁻¹ : EndH H) = KreinGradedModule.gradeCLM (H := H)
        rw [U.commutes_grade g, mul_assoc, Units.mul_inv, mul_one])
      (fun g => by
        change (U.unitAction g : EndH H) * X.cl11.J * (↑(U.unitAction g)⁻¹ : EndH H) = X.cl11.J
        rw [U.commutes_J g, mul_assoc, Units.mul_inv, mul_one])
      (fun g a => by
        change (U.unitAction g : EndH H) * X.π a * (↑(U.unitAction g)⁻¹ : EndH H) = X.π a
        rw [U.commutes_left_rep g a, mul_assoc, Units.mul_inv, mul_one])
    exact ⟨hSym.1, hSym.2.1⟩
  refine ⟨?_, ?_, hInv.1, hInv.2⟩
  · intro g v
    constructor
    · intro hv
      have hback := hMapPlus g⁻¹ hv
      have hmul : (U.unitAction g⁻¹ : EndH H) * (U.unitAction g : EndH H) = 1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      have hid : (U.unitAction g⁻¹ : EndH H) ((U.unitAction g : EndH H) v) = v := by
        change ((U.unitAction g⁻¹ : EndH H) * (U.unitAction g : EndH H)) v = v
        rw [hmul]
        rfl
      change (U.unitAction g⁻¹ : EndH H) ((U.unitAction g : EndH H) v) ∈
        X.chiralKernelSlicePlus at hback
      rwa [hid] at hback
    · exact hMapPlus g
  · intro g v
    constructor
    · intro hv
      have hback := hMapMinus g⁻¹ hv
      have hmul : (U.unitAction g⁻¹ : EndH H) * (U.unitAction g : EndH H) = 1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      have hid : (U.unitAction g⁻¹ : EndH H) ((U.unitAction g : EndH H) v) = v := by
        change ((U.unitAction g⁻¹ : EndH H) * (U.unitAction g : EndH H)) v = v
        rw [hmul]
        rfl
      change (U.unitAction g⁻¹ : EndH H) ((U.unitAction g : EndH H) v) ∈
        X.chiralKernelSliceMinus at hback
      rwa [hid] at hback
    · exact hMapMinus g

/-- `EquivariantCycleGroupAction` embeds into `Erlangen20Unification.erlangen20EndSymmetryAction`
on `Module.End ℝ H` whenever `U` acts inside `E.operatorAlgebra`. -/
theorem EquivariantCycleGroupAction.to_erlangen20EndSymmetryAction_apply
    {G : Type*} [Group G]
    (E : EquivariantDatum (𝔤 := 𝔤) X)
    (U : EquivariantCycleGroupAction G X)
    (hmem : ∀ g : G, (clmToEndAlgHom H (U.unitAction g : EndH H)) ∈ E.operatorAlgebra)
    (g : G) (T : EndH H) :
    let ρ : G →* E.toErlangen20Datum.operatorAlgebraˣ :=
      { toFun := fun k =>
          { val := ⟨clmToEndAlgHom H (U.unitAction k : EndH H), hmem k⟩
            inv := ⟨clmToEndAlgHom H (U.unitAction k⁻¹ : EndH H), hmem k⁻¹⟩
            val_inv := by
              apply Subtype.ext
              change clmToEndAlgHom H (U.unitAction k : EndH H) *
                  clmToEndAlgHom H (U.unitAction k⁻¹ : EndH H) = 1
              rw [← map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
                Units.val_one, map_one]
            inv_val := by
              apply Subtype.ext
              change clmToEndAlgHom H (U.unitAction k⁻¹ : EndH H) *
                  clmToEndAlgHom H (U.unitAction k : EndH H) = 1
              rw [← map_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
                Units.val_one, map_one] }
        map_one' := by
          apply Units.ext; apply Subtype.ext
          change clmToEndAlgHom H (U.unitAction 1 : EndH H) = 1
          simp
        map_mul' := fun k₁ k₂ => by
          apply Units.ext; apply Subtype.ext
          change clmToEndAlgHom H (U.unitAction (k₁ * k₂) : EndH H) =
            clmToEndAlgHom H (U.unitAction k₁ : EndH H) *
              clmToEndAlgHom H (U.unitAction k₂ : EndH H)
          rw [map_mul, Units.val_mul, map_mul] }
    (erlangen20EndSymmetryAction E.toErlangen20Datum ρ).act g (clmToEndAlgHom H T) =
      clmToEndAlgHom H (U.toSymmetryAction.act g T) := by
  simp only [erlangen20EndSymmetryAction, erlangen20EndConjAlgEquiv,
    EquivariantCycleGroupAction.toSymmetryAction]
  change (clmToEndAlgHom H (U.unitAction g : EndH H)) * clmToEndAlgHom H T *
      (clmToEndAlgHom H (U.unitAction g⁻¹ : EndH H)) =
    clmToEndAlgHom H ((U.unitAction g : EndH H) * T * (↑(U.unitAction g)⁻¹ : EndH H))
  rw [← map_mul, ← map_mul, map_inv]

end Erlangen20AndChiralInvariance

/-! ## M2 `Cl(1,1)` / `V₄` & Cantor Double-Cylinder Equivariance -/

section Cl11AndCantorEquivariance

open InfoGeometry.OperatorAlgebra
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.CoordinateLessCliffordInvariance
open InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation
open InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
open InfoGeometry.Canonical.Erlangen20Unification
open InfoGeometry.Categorical.CantorDoubleCylinderColimitAlgebra
open InfoGeometry.OperatorAlgebra.ErlangenDoubleCylinderSymmetryInvariants

local instance (priority := 100) instLocalLieRingCliffordQ11 :
    LieRing (CliffordAlgebra q11) :=
  LieRing.ofAssociativeRing

local instance (priority := 100) instLocalLieAlgebraCliffordQ11 :
    LieAlgebra ℝ (CliffordAlgebra q11) :=
  LieAlgebra.ofAssociativeAlgebra

/-- Coordinate-less `V₄` symmetry action on `CliffordAlgebra q11` via M2's
`v4ToQ11IsometryHom` and `cliffordSymmetryAction q11`, intertwined with `localCl11RootMap`
on `M₂(ℝ)` and matching `Erlangen20Datum` on `CliffordAlgebra q11`. -/
theorem cl11V4_coordinateLess_erlangen20_intertwining
    (g : InfoGeometry.Topology.V4RootSystem.V4Group)
    (a : CliffordAlgebra q11) :
    cl11EquivMat
        ((cliffordSymmetryAction q11).act (v4ToQ11IsometryHom g) a) =
      localCl11RootMap g (cl11EquivMat a) ∧
      (erlangen20DatumOfSymmetryAction ℝ
          (cliffordSymmetryAction q11)
          (LinearMap.id : CliffordAlgebra q11 →ₗ[ℝ] CliffordAlgebra q11)
          (fun x y => Ring.lie_def x y)).symmetryData =
        cliffordSymmetryAction q11 :=
  ⟨cl11EquivMat_v4_equivOfIsometry g a, rfl⟩

/-- `cantorDoubleCylinderErlangen20Datum` (`DoubleCylinderColimit ℝ` on `H_lp ℝ`) carries
`G_swap` symmetry action `erlangenDoubleCylinderSymmetryAction ℝ` together with `J_lp_clm`
sewing invariance and zero chiral anomaly. -/
theorem cantorDoubleCylinder_erlangen20_sewn_equivariance
    (X : InfoGeometry.OperatorAlgebra.CantorDoubleCylinderFractalColimit.DoubleCylinderColimit ℝ)
    (v : InfoGeometry.Canonical.ConcreteHilbertCommutation.H_lp ℝ) :
    ((InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ)).toLinearMap *
        (cantorDoubleCylinderErlangen20Datum.representation X) *
        (InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly.J_lp_clm (E := ℝ)).toLinearMap) v =
      (cantorDoubleCylinderErlangen20Datum.representation X) v ∧
      inner ℝ InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly.canonicalCantorSewnState
        (((InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly.epsilon_lp_clm (E := ℝ)).comp
          (colimitRepresentationCLM X))
          InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly.canonicalCantorSewnState) = 0 :=
  ⟨cantorDoubleCylinder_sewn_fixes_operatorAlgebra X v,
    doubleCylinderColimit_canonicalVacuum_chiral_zero X⟩

end Cl11AndCantorEquivariance

/-! ## Noncommutativity (`T1-F2.4-5`) & `DoubledSpace` (`T3-20`) Witnesses -/

section NoncommutativeAndDoubledSpaceWitnesses

open InfoGeometry.KK.ClNNFredholmBridge
open InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
open InfoGeometry.Canonical.Erlangen20Unification

/-- Noncommutativity witness (`T1-F2.4-5`): `EquivariantDatum` and `EquivariantErlangenKasparov`
operate over arbitrary noncommutative `[NormedRing A]` (never `[CommRing A]`), witnessed
concretely by `M₂(ℝ)` elementary matrices `E₊ * E₋ ≠ E₋ * E₊` together with `EquivariantDatum`
preservation of `[X.F, X.π a]`. -/
theorem equivariantDatum_mat2_noncommutative_witness
    {A B H 𝔤 : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (X : RealSplitKreinKasparovCycle A B H) (E : EquivariantDatum (𝔤 := 𝔤) X) :
    let e01 : Matrix (Fin 2) (Fin 2) ℝ := !![(0 : ℝ), 1; 0, 0]
    let e10 : Matrix (Fin 2) (Fin 2) ℝ := !![(0 : ℝ), 0; 1, 0]
    e01 * e10 ≠ e10 * e01 ∧
      ∀ D : 𝔤, ∀ a : A,
        E.action D * (X.F * X.π a - X.π a * X.F) =
          (X.F * X.π a - X.π a * X.F) * E.action D := by
  intro e01 e10
  refine ⟨?_, fun D a => action_commutes_phase_commutator E D a⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  simp [e01, e10, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Scalar Lie-character equivariant datum on `nontrivialSplitKasparovCycle` over any
`[LieRing L] [LieAlgebra ℝ L]` equipped with an abelian Lie character `χ : L →ₗ[ℝ] ℝ`. -/
def doubledSpaceSplitEquivariantDatum
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (χ : L →ₗ[ℝ] ℝ) (hχ : ∀ x y : L, χ ⁅x, y⁆ = 0) :
    EquivariantDatum (𝔤 := L) nontrivialSplitKasparovCycle where
  action :=
    { toFun := fun D => χ D • (1 : EndH (SplitDoubledSpace (FinModelE 2)))
      map_add' := fun x y => by
        apply ContinuousLinearMap.ext
        intro v
        simp [map_add, add_smul]
      map_smul' := fun r x => by
        apply ContinuousLinearMap.ext
        intro v
        simp [map_smul, mul_smul]
      map_lie' := fun {x y} => by
        apply ContinuousLinearMap.ext
        intro v
        have hxy : χ ⁅x, y⁆ = 0 := hχ x y
        change (χ ⁅x, y⁆ • (1 : EndH (SplitDoubledSpace (FinModelE 2)))) v =
          ((χ x • (1 : EndH (SplitDoubledSpace (FinModelE 2)))) *
            (χ y • (1 : EndH (SplitDoubledSpace (FinModelE 2)))) -
            (χ y • (1 : EndH (SplitDoubledSpace (FinModelE 2)))) *
              (χ x • (1 : EndH (SplitDoubledSpace (FinModelE 2))))) v
        rw [hxy]
        simp only [zero_smul, zero_apply, sub_apply, ContinuousLinearMap.mul_def,
          ContinuousLinearMap.comp_apply, smul_apply, one_apply_eq_self]
        rw [smul_comm (χ x) (χ y) v, sub_self] }
  commutes_phase := fun D => by
    apply ContinuousLinearMap.ext
    intro v
    simp [ContinuousLinearMap.mul_def]
  commutes_grade := fun D => by
    apply ContinuousLinearMap.ext
    intro v
    simp [ContinuousLinearMap.mul_def]
  commutes_left_rep := fun D a => by
    apply ContinuousLinearMap.ext
    intro v
    simp [ContinuousLinearMap.mul_def]
  commutes_right_rep := fun D b => by
    apply ContinuousLinearMap.ext
    intro v
    simp [ContinuousLinearMap.mul_def]

/-- Concrete `DoubledSpace` witness (`T3-20`): `nontrivialSplitKasparovCycle` on
`SplitDoubledSpace (FinModelE 2) ≃ₗᵢ[ℝ] DoubledSpace (FinModelE 2)` (extending
`DoubledSpace ℝ`) satisfies `F ≠ 0`, `F² = 1`, `[F, π proj0E2] ≠ 0`, and induces an
`EquivariantDatum` / `Erlangen20Datum` preserving both chiral kernel slices. -/
theorem doubledSpace_kasparov_erlangen20_witness :
    let _instLieRing : LieRing ℝ := LieRing.ofAssociativeRing
    let _instLieAlg : LieAlgebra ℝ ℝ := LieAlgebra.ofAssociativeAlgebra
    let eLIE : SplitDoubledSpace (FinModelE 2) ≃ₗᵢ[ℝ] DoubledSpace (FinModelE 2) :=
      SplitDoubledSpace.toDoubledLIE (E := FinModelE 2)
    let eReal : SplitDoubledSpace ℝ ≃ₗᵢ[ℝ] DoubledSpace ℝ :=
      SplitDoubledSpace.toDoubledLIE (E := ℝ)
    let E := doubledSpaceSplitEquivariantDatum (L := ℝ) LinearMap.id
      (fun x y => by change x * y - y * x = 0; ring)
    let E20 : Erlangen20Datum ℝ (SplitDoubledSpace (FinModelE 2)) ℝ
        (EquivariantSymmetryData nontrivialSplitKasparovCycle)
        (EquivariantInvariantData nontrivialSplitKasparovCycle) :=
      E.toErlangen20Datum
    nontrivialSplitKasparovCycle.F ≠ 0 ∧
      E20.representation (1 : ℝ) = LinearMap.id ∧
      (∀ u : SplitDoubledSpace ℝ,
        KreinSpace.J (eReal u) = eReal (KreinSpace.J u)) ∧
      (∀ u : SplitDoubledSpace (FinModelE 2),
        KreinSpace.J (eLIE u) = eLIE (KreinSpace.J u)) := by
  let _instLieRing : LieRing ℝ := LieRing.ofAssociativeRing
  let _instLieAlg : LieAlgebra ℝ ℝ := LieAlgebra.ofAssociativeAlgebra
  refine ⟨nontrivialSplitKasparovCycle_F_ne_zero, ?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro v
    simp [doubledSpaceSplitEquivariantDatum]
  · exact splitDoubled_toDoubledLIE_intertwines_J (E := ℝ)
  · exact splitDoubled_toDoubledLIE_intertwines_J (E := FinModelE 2)

/-- Zero-instance helper building a scalar Lie-character `EquivariantDatum` on
`nontrivialSplitKasparovCycle` from any `[LieRing L] [LieAlgebra ℝ L]` and abelian character
`χ : L →ₗ[ℝ] ℝ` via `EquivariantDatum.ofLinearMap`. -/
def doubledSpaceSplitEquivariantDatum_ofLinearMap
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (χ : L →ₗ[ℝ] ℝ) (hχ : ∀ x y : L, χ ⁅x, y⁆ = 0) :
    EquivariantDatum (𝔤 := L) nontrivialSplitKasparovCycle :=
  EquivariantDatum.ofLinearMap
    (χ.smulRight (1 : EndH (SplitDoubledSpace (FinModelE 2))))
    (fun x y => by
      apply ContinuousLinearMap.ext
      intro v
      have hxy : χ ⁅x, y⁆ = 0 := hχ x y
      simp only [LinearMap.smulRight_apply, hxy, zero_smul, zero_apply,
        sub_apply, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply, smul_apply,
        one_apply_eq_self]
      rw [smul_comm (χ x) (χ y) v, sub_self])
    (fun D => by apply ContinuousLinearMap.ext; intro v; simp [ContinuousLinearMap.mul_def])
    (fun D => by apply ContinuousLinearMap.ext; intro v; simp [ContinuousLinearMap.mul_def])
    (fun D a => by apply ContinuousLinearMap.ext; intro v; simp [ContinuousLinearMap.mul_def])
    (fun D b => by apply ContinuousLinearMap.ext; intro v; simp [ContinuousLinearMap.mul_def])

/-- Concrete 1D real abelian `EquivariantDatum` on `nontrivialSplitKasparovCycle` over
`InfoGeometry.Erlangen.SmoothCartanGeometry.HomothetyH`, requiring no `LieRing ℝ` or
`local instance` at external call sites. -/
def doubledSpaceSplitEquivariantDatum_homothety :
    EquivariantDatum (𝔤 := InfoGeometry.Erlangen.SmoothCartanGeometry.HomothetyH)
      nontrivialSplitKasparovCycle :=
  doubledSpaceSplitEquivariantDatum_ofLinearMap
    { toFun := fun x => x.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (fun _ _ => rfl)

/-- External-callable `DoubledSpace` witness requiring zero `local instance`s or `LieRing ℝ`
workarounds at call sites (using `doubledSpaceSplitEquivariantDatum_homothety`). -/
theorem doubledSpace_kasparov_erlangen20_homothety_witness :
    let eLIE : SplitDoubledSpace (FinModelE 2) ≃ₗᵢ[ℝ] DoubledSpace (FinModelE 2) :=
      SplitDoubledSpace.toDoubledLIE (E := FinModelE 2)
    let eReal : SplitDoubledSpace ℝ ≃ₗᵢ[ℝ] DoubledSpace ℝ :=
      SplitDoubledSpace.toDoubledLIE (E := ℝ)
    let E20 := doubledSpaceSplitEquivariantDatum_homothety.toErlangen20Datum
    nontrivialSplitKasparovCycle.F ≠ 0 ∧
      E20.representation ⟨1⟩ = LinearMap.id ∧
      (∀ u : SplitDoubledSpace ℝ,
        KreinSpace.J (eReal u) = eReal (KreinSpace.J u)) ∧
      (∀ u : SplitDoubledSpace (FinModelE 2),
        KreinSpace.J (eLIE u) = eLIE (KreinSpace.J u)) := by
  refine ⟨nontrivialSplitKasparovCycle_F_ne_zero, ?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro v
    change ((1 : ℝ) • (1 : EndH (SplitDoubledSpace (FinModelE 2)))) v = v
    simp
  · exact splitDoubled_toDoubledLIE_intertwines_J (E := ℝ)
  · exact splitDoubled_toDoubledLIE_intertwines_J (E := FinModelE 2)

end NoncommutativeAndDoubledSpaceWitnesses

end InfoGeometry.KK.RealSplitKreinEquivarianceBridge

namespace InfoGeometry.KK.RealSplitKreinEquivarianceBridge

/-- Closed `M₂(ℝ)` noncommutativity witness in the `RealSplitKreinEquivarianceBridge`
namespace (`E₀₁ * E₁₀ ≠ E₁₀ * E₀₁`). -/
theorem mat2_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨!![(0 : ℝ), 1; 0, 0], !![(0 : ℝ), 0; 1, 0], ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

end InfoGeometry.KK.RealSplitKreinEquivarianceBridge

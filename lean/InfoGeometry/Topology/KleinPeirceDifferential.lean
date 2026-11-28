/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.KleinRealKreinPeirceSections
import InfoGeometry.OperatorAlgebra.PeirceTwistedComplex

/-!
# A continuous twisted differential on real Klein--Krein sections

The existing section grading and the existing twisted inner action define a
continuous real-linear operator on the full algebra of equivariant sections.
Its square is the inner action of the odd generator's square. In particular,
the concrete mirror section has square one and induces a nonzero square-zero
differential. Its explicit continuous contraction makes its cycles exactly
its boundaries. This is an algebraic differential, not a derivative along
the base torus or an assertion about physical supersymmetry.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinPeirceDifferential

open InfoGeometry.OperatorAlgebra.LieJordan
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open KleinRealKreinPeirceSections
open KleinBrillouinBase KleinBottleOrbitQuotient

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable local instance operatorNormedRing : NormedRing (Operator (E := E)) :=
  ContinuousLinearMap.toNormedRing

local instance operatorTopologicalRing : IsTopologicalRing (Operator (E := E)) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance sectionsRing : Ring (Sections (E := E)) :=
  (sectionAlgebra (E := E)).toRing

local instance sectionsAlgebra : Algebra ℝ (Sections (E := E)) :=
  (sectionAlgebra (E := E)).algebra

local instance sectionsAddCommMonoid : AddCommMonoid (Sections (E := E)) :=
  (sectionAlgebra (E := E)).toSubmodule.addCommMonoid

local instance sectionsModule : Module ℝ (Sections (E := E)) :=
  (sectionAlgebra (E := E)).toSubmodule.module

/-- The existing twisted inner linear map, with continuity on actual sections. -/
def differential (q : Sections (E := E)) :
    Sections (E := E) →L[ℝ] Sections (E := E) where
  toLinearMap := twistedInner ℝ (sectionGradingEquiv (E := E)).toAlgEquiv.toAlgHom q
  cont := by
    change Continuous (fun a : Sections (E := E) =>
      q * a - sectionGradingEquiv a * q)
    exact (continuous_const.mul continuous_id).sub
      ((sectionGradingEquiv (E := E)).continuous_toFun.mul continuous_const)

theorem differential_toLinearMap (q : Sections (E := E)) :
    (differential q).toLinearMap =
      twistedInner ℝ (sectionGradingEquiv (E := E)).toAlgEquiv.toAlgHom q := rfl

@[simp] theorem differential_apply (q a : Sections (E := E)) :
    differential q a = q * a - sectionGrading a * q := rfl

/-- Every value uses the full noncommutative operator fibre. -/
theorem differential_apply_at (q a : Sections (E := E)) (x : BrillouinTorus) :
    (differential q a).1 x =
      q.1 x * a.1 x - (gamma5 * a.1 x * gamma5) * q.1 x := by
  change q.1 x * a.1 x - (sectionGrading a).1 x * q.1 x = _
  rw [sectionGrading_apply]

/-- The differential takes values in the same twisted section algebra. -/
theorem differential_deck_equivariance (q a : Sections (E := E))
    (d : KleinGlideCovering.Deck2) (x : BrillouinTorus) :
    (differential q a).1 (d +ᵥ x) =
      if d.val = 0 then (differential q a).1 x
      else mirror ((differential q a).1 x) :=
  section_deck_equivariance (differential q a) d x

/-- The native section grading supplies the sign on the left factor. -/
theorem differential_leibniz (q a b : Sections (E := E)) :
    differential q (a * b) =
      differential q a * b + sectionGrading a * differential q b :=
  twistedInner_leibniz ℝ _ q a b

theorem differential_reverses_parity {q : Sections (E := E)}
    (hq : sectionGrading q = -q) (a : Sections (E := E)) :
    sectionGrading (differential q a) = -differential q (sectionGrading a) :=
  twistedInner_reverses_parity ℝ
    (sectionGradingEquiv (E := E)).toAlgEquiv.toAlgHom hq a

/-- Oddness forces an inner square; centrality is a separate hypothesis. -/
theorem differential_square {q : Sections (E := E)}
    (hq : sectionGrading q = -q) (a : Sections (E := E)) :
    differential q (differential q a) = (q * q) * a - a * (q * q) := by
  exact congrArg (fun f : Module.End ℝ (Sections (E := E)) => f a)
    (twistedInner_square ℝ (sectionGradingEquiv (E := E)).toAlgEquiv.toAlgHom
      (sectionGrading_involutive (E := E)) hq)

/-- A central square suffices; the odd section itself need not be nilpotent. -/
theorem differential_square_zero_of_central {q : Sections (E := E)}
    (hq : sectionGrading q = -q)
    (hcentral : ∀ a : Sections (E := E), Commute (q * q) a) :
    (differential q).comp (differential q) = 0 := by
  apply ContinuousLinearMap.ext
  intro a
  change differential q (differential q a) = 0
  rw [differential_square hq, (hcentral a).eq, sub_self]

/-- The concrete cross-sheet mirror supplies a globally defined odd charge. -/
def mirrorDifferential : Sections (E := E) →L[ℝ] Sections (E := E) :=
  differential (mirrorSection (E := E))

theorem mirrorDifferential_square_zero :
    (mirrorDifferential (E := E)).comp mirrorDifferential = 0 := by
  apply differential_square_zero_of_central (sectionGrading_mirrorSection (E := E))
  intro a
  rw [mirrorSection_sq]
  exact Commute.one_left a

@[simp] theorem mirrorDifferential_apply_twice (a : Sections (E := E)) :
    mirrorDifferential (mirrorDifferential a) = 0 :=
  congrArg (fun f : Sections (E := E) →L[ℝ] Sections (E := E) => f a)
    (mirrorDifferential_square_zero (E := E))

/-- A nonzero value distinguishes this differential from the zero operator. -/
theorem mirrorDifferential_mirrorSection :
    mirrorDifferential (mirrorSection (E := E)) = (2 : ℝ) • (1 : Sections (E := E)) := by
  change mirrorSection (E := E) * mirrorSection -
    sectionGrading (mirrorSection (E := E)) * mirrorSection = _
  rw [sectionGrading_mirrorSection (E := E),
    neg_mul (mirrorSection (E := E)) (mirrorSection (E := E)),
    mirrorSection_sq (E := E), sub_neg_eq_add,
    two_smul ℝ (1 : Sections (E := E))]

theorem mirrorDifferential_ne_zero [Nontrivial E] :
    mirrorDifferential (E := E) ≠ 0 := by
  intro h
  have htwo : (2 : ℝ) • (1 : Sections (E := E)) = 0 := by
    rw [← mirrorDifferential_mirrorSection (E := E), h]
    rfl
  exact (smul_ne_zero (R := ℝ) (M := Sections (E := E)) (by norm_num : (2 : ℝ) ≠ 0)
    (section_one_ne_zero (E := E))) htwo

/-- The concrete differential satisfies a contracting identity on all sections. -/
theorem mirrorDifferential_mirror_mul_add (a : Sections (E := E)) :
    mirrorDifferential (mirrorSection * a) + mirrorSection * mirrorDifferential a =
      (2 : ℝ) • a := by
  change differential (mirrorSection (E := E)) (mirrorSection * a) +
    mirrorSection * differential (mirrorSection (E := E)) a = _
  rw [differential_leibniz, sectionGrading_mirrorSection (E := E)]
  change mirrorDifferential (mirrorSection (E := E)) * a +
    -mirrorSection * mirrorDifferential a + mirrorSection * mirrorDifferential a = _
  rw [mirrorDifferential_mirrorSection (E := E)]
  rw [smul_mul_assoc (2 : ℝ) (1 : Sections (E := E)) a, one_mul a,
    neg_mul (mirrorSection (E := E)) (mirrorDifferential a)]
  abel

private def halfLeftLinear {A : Type*} [Ring A] [Algebra ℝ A] (q : A) : A →ₗ[ℝ] A :=
  (1 / 2 : ℝ) • LinearMap.mulLeft ℝ q

/-- Continuous contraction by one half of left multiplication by the mirror. -/
def mirrorHomotopy : Sections (E := E) →L[ℝ] Sections (E := E) where
  toLinearMap := halfLeftLinear (mirrorSection (E := E))
  cont := by
    change Continuous (fun a : Sections (E := E) =>
      (1 / 2 : ℝ) • (mirrorSection (E := E) * a))
    exact (continuous_const.mul continuous_id).const_smul (1 / 2 : ℝ)

@[simp] theorem mirrorHomotopy_apply (a : Sections (E := E)) :
    mirrorHomotopy a = (1 / 2 : ℝ) • (mirrorSection * a) := rfl

private theorem half_add_of_eq_two_smul {A : Type*}
    [AddCommMonoid A] [Module ℝ A] (x y a : A) (h : x + y = (2 : ℝ) • a) :
    (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y = a := by
  rw [← smul_add, h, smul_smul]
  norm_num

/-- A native continuous contracting homotopy, with both compositions explicit. -/
theorem mirrorDifferential_contracting :
    (mirrorDifferential (E := E)).comp (mirrorHomotopy (E := E)) +
      (mirrorHomotopy (E := E)).comp mirrorDifferential =
        ContinuousLinearMap.id ℝ (Sections (E := E)) := by
  apply ContinuousLinearMap.ext
  intro a
  change mirrorDifferential ((1 / 2 : ℝ) • (mirrorSection * a)) +
    (1 / 2 : ℝ) • (mirrorSection * mirrorDifferential a) = a
  rw [map_smul (mirrorDifferential (E := E)) (1 / 2 : ℝ) (mirrorSection * a)]
  exact half_add_of_eq_two_smul
    (mirrorDifferential (mirrorSection * a)) (mirrorSection * mirrorDifferential a) a
    (mirrorDifferential_mirror_mul_add a)

theorem mirrorDifferential_range_le_ker :
    LinearMap.range (mirrorDifferential (E := E)).toLinearMap ≤
      LinearMap.ker (mirrorDifferential (E := E)).toLinearMap := by
  rintro a ⟨b, rfl⟩
  change mirrorDifferential (mirrorDifferential b) = 0
  exact mirrorDifferential_apply_twice b

/-- Every cycle has the explicit boundary preimage supplied by the contraction. -/
theorem mirrorDifferential_range_eq_ker :
    LinearMap.range (mirrorDifferential (E := E)).toLinearMap =
      LinearMap.ker (mirrorDifferential (E := E)).toLinearMap := by
  apply le_antisymm (mirrorDifferential_range_le_ker (E := E))
  intro a ha
  refine ⟨mirrorHomotopy a, ?_⟩
  have h := congrArg (fun f : Sections (E := E) →L[ℝ] Sections (E := E) => f a)
    (mirrorDifferential_contracting (E := E))
  change mirrorDifferential (mirrorHomotopy a) +
    mirrorHomotopy (mirrorDifferential a) = a at h
  have hcycle : mirrorDifferential a = 0 := ha
  rw [hcycle, (mirrorHomotopy (E := E)).map_zero,
    add_zero (mirrorDifferential (mirrorHomotopy a))] at h
  exact h

/-- The actual differential defines a native Mathlib short complex. -/
def mirrorShortComplex : CategoryTheory.ShortComplex (ModuleCat ℝ) :=
  CategoryTheory.ShortComplex.mk
    (ModuleCat.ofHom (mirrorDifferential (E := E)).toLinearMap)
    (ModuleCat.ofHom (mirrorDifferential (E := E)).toLinearMap) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact mirrorDifferential_apply_twice a)

end InfoGeometry.Topology.KleinPeirceDifferential

end

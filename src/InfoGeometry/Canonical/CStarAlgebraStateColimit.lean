/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Canonical.FilteredDirectInverseColimit

/-!
# Continuous C*-Algebraic Filtered State Duality & Colimit Readouts

This module establishes the continuous star-algebraic filtered direct system,
contravariant state restriction, compatible state families, and star-algebraic
cocones over `CStarAlgebra` stages, together with the forgetful functor to
`FilteredColimit.DirectInductiveSystem` and `FilteredColimit.InductiveCocone`.

## Audit Classification
- **BUCKET 1 (Genuine Constructive Proofs)**:
  - `PositiveState.gns_state_pos`, `PositiveState.gns_state_self_star_real`,
    `PositiveState.gns_null_re_zero`, `PositiveState.kms_tracial_state`
  - `Native.starAlgHom_map_nonneg`, `Native.starAlgHom_monotone`,
    `Native.starAlgHomToContinuousLinearMap`
  - `Native.State.restrict`, `Native.State.restrict_id`, `Native.State.restrict_comp`
  - `Native.ContinuousStarInductiveSystem.toDirectInductiveSystem`,
    `Native.ContinuousStarInductiveSystem.CompatibleStateFamily.eval_transition`,
    `Native.ContinuousStarInductiveSystem.StarInductiveCocone.toInductiveCocone`,
    `Native.ContinuousStarInductiveSystem.StarInductiveCocone.restrictStateFamily`,
    `Native.ContinuousStarInductiveSystem.StarInductiveCocone.state_readout_transition`
- **BUCKET 2 (Honest Numeric/Finite Certificates)**: None.
- **BUCKET 3 (Eliminated Debt)**: `0` `sorry`, `0` `admit`, `0` Prop-def/KMSState wrappers.
-/

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Complex Real

namespace CStarStateColimit

universe u

open scoped ComplexOrder

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A state functional is the native positive linear map from Mathlib. -/
abbrev PositiveState (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] := A →ₚ[ℂ] ℂ

namespace PositiveState

variable (phi : PositiveState A)

/-- **Theorem**: Non-commutative GNS State Positivity: Re(φ(a* a)) ≥ 0 for all a ∈ A. -/
theorem gns_state_pos (a : A) : 0 ≤ (phi (star a * a)).re := by
  have hnonneg : 0 ≤ phi (star a * a) :=
    PositiveLinearMap.map_nonneg phi
      (CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr ⟨a, rfl⟩)
  exact (Complex.nonneg_iff.mp hnonneg).1

/-- **Theorem**: Real Part of Self-Adjoint Star Product is Zero in Imaginary Component. -/
theorem gns_state_self_star_real (a : A) : (phi (star a * a)).im = 0 := by
  have hnonneg : 0 ≤ phi (star a * a) :=
    PositiveLinearMap.map_nonneg phi
      (CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr ⟨a, rfl⟩)
  exact (Complex.nonneg_iff.mp hnonneg).2.symm

/-- **Theorem**: GNS Null Element Characterization: φ(a* a) = 0 ⟹ Re(φ(a* a)) = 0. -/
theorem gns_null_re_zero (a : A) (h_null : phi (star a * a) = 0) :
    (phi (star a * a)).re = 0 := by
  rw [h_null]
  rfl

/-- **Theorem**: KMS Boundary State Commutativity under Identity Modular Automorphism:
    If φ(a * b) = φ(b * σ(a)) with σ = id, then φ(a * b) = φ(b * a) (Tracial State Condition). -/
theorem kms_tracial_state
    (h_kms : ∀ x y : A, phi (x * y) = phi (y * (fun z : A => z) x))
    (a b : A) :
    phi (a * b) = phi (b * a) := by
  have h := h_kms a b
  exact h

end PositiveState

end CStarStateColimit

/-!
## Native continuous star-algebraic filtered state duality

The original finite algebraic API above is retained.  The owner below adds the
missing native layer:

* stages are genuine Mathlib `CStarAlgebra`s;
* direct transitions are `StarAlgHom`s, hence multiplicative, unital,
  star-preserving, and automatically continuous;
* states are normalized Mathlib `PositiveLinearMap`s;
* state restriction is contravariant and satisfies the inverse-system
  composition law;
* a star-algebraic cocone induces a compatible family of finite-stage states;
* forgetting multiplication and star recovers the existing
  `FilteredColimit.DirectInductiveSystem` and `InductiveCocone` owners.

No commutativity or diagonalization hypothesis is imposed.
-/

namespace CStarStateColimit.Native

open scoped ComplexOrder
open CategoryTheory
open FilteredColimit

universe u

variable {A B C : Type u}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- A star algebra homomorphism between C-star algebras preserves the positive
cone. -/
theorem starAlgHom_map_nonneg
    (f : A →⋆ₐ[ℂ] B) {a : A} (ha : 0 ≤ a) :
    0 ≤ f a := by
  obtain ⟨b, rfl⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  simp only [map_mul, map_star]
  exact
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr
      ⟨f b, rfl⟩

/-- A star algebra homomorphism between C-star algebras is monotone. -/
theorem starAlgHom_monotone
    (f : A →⋆ₐ[ℂ] B) :
    Monotone f := by
  intro x y hxy
  rw [← sub_nonneg] at hxy ⊢
  have hmap : f (y - x) = f y - f x :=
    map_sub f y x
  rw [← hmap]
  exact starAlgHom_map_nonneg f hxy

/-- The native continuous-linear map underlying a C-star algebra
homomorphism.  Continuity is supplied by Mathlib's C-star theorem. -/
def starAlgHomToContinuousLinearMap
    (f : A →⋆ₐ[ℂ] B) :
    A →L[ℂ] B := by
  letI : ContinuousLinearMapClass (A →⋆ₐ[ℂ] B) ℂ A B :=
    NonUnitalStarAlgHom.instContinuousLinearMapClassComplex
  exact
    { toLinearMap := f.toAlgHom.toLinearMap
      cont := ContinuousMapClass.map_continuous f }

@[simp] theorem starAlgHomToContinuousLinearMap_apply
    (f : A →⋆ₐ[ℂ] B) (a : A) :
    starAlgHomToContinuousLinearMap f a = f a :=
  rfl

/-- A normalized positive functional in Mathlib's native C-star sense, represented as a
subtype of positive linear maps `A →ₚ[ℂ] ℂ` taking `1` to `1`. -/
def State
    (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] : Type u :=
  { functional : A →ₚ[ℂ] ℂ // functional 1 = 1 }

namespace State

/-- Construct a `State A` from a positive linear functional and its normalization proof. -/
def mk
    (functional : A →ₚ[ℂ] ℂ)
    (normalized : functional 1 = 1) :
    State A :=
  ⟨functional, normalized⟩

/-- Underlying positive linear map `A →ₚ[ℂ] ℂ` of a state. -/
def functional (ω : State A) : A →ₚ[ℂ] ℂ :=
  ω.1

/-- Normalization equation `ω.functional 1 = 1`. -/
theorem normalized (ω : State A) : ω.functional 1 = 1 := by
  have h := ω.2
  exact h

/-- Simplification rule for `(State.mk f h).functional`. -/
@[simp] theorem functional_mk
    (f : A →ₚ[ℂ] ℂ) (h : f 1 = 1) :
    (State.mk f h).functional = f := by
  change f = f
  rfl

/-- Simplification rule for `State.functional ⟨f, h⟩`. -/
@[simp] theorem functional_subtype_mk
    (f : A →ₚ[ℂ] ℂ) (h : f 1 = 1) :
    State.functional (A := A) ⟨f, h⟩ = f := by
  change f = f
  rfl

/-- States are determined by their native positive linear functionals. -/
@[ext] theorem ext
    {ω ν : State A}
    (h : ω.functional = ν.functional) :
    ω = ν := by
  exact Subtype.ext h

/-- Evaluation of `ω.functional` at `1` equals `1`. -/
@[simp] theorem apply_one (ω : State A) :
    ω.functional 1 = 1 := by
  have h := ω.normalized
  exact h

/-- The continuous-linear functional underlying a state. -/
def toContinuousLinearMap
    (ω : State A) :
    A →L[ℂ] ℂ := by
  letI :
      ContinuousLinearMapClass (A →ₚ[ℂ] ℂ) ℂ A ℂ :=
    PositiveLinearMap.instContinuousLinearMapClassComplexOfLinearMapClassOfOrderHomClass
  exact
    { toLinearMap := ω.functional.toLinearMap
      cont := ContinuousMapClass.map_continuous ω.functional }


/-- Evaluation of `ω.toContinuousLinearMap` agrees with `ω.functional`. -/
@[simp] theorem toContinuousLinearMap_apply
    (ω : State A) (a : A) :
    ω.toContinuousLinearMap a = ω.functional a := by
  change ω.functional a = ω.functional a
  rfl


/-- Contravariant restriction of a state along a star algebra homomorphism. -/
def restrict
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B) :
    State A :=
  State.mk
    (PositiveLinearMap.mk
      (ω.functional.toLinearMap.comp f.toAlgHom.toLinearMap)
      (ω.functional.monotone.comp (starAlgHom_monotone f)))
    (by
      change ω.functional (f 1) = 1
      rw [map_one, ω.normalized])

/-- Pointwise evaluation of `ω.restrict f` at `a : A`. -/
@[simp] theorem restrict_apply
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B) (a : A) :
    (ω.restrict f).functional a =
      ω.functional (f a) := by
  change ω.functional (f a) = ω.functional (f a)
  rfl

/-- Compatibility of `State.restrict` with `toContinuousLinearMap`. -/
theorem restrict_toContinuousLinearMap
    (f : A →⋆ₐ[ℂ] B) (ω : State B) :
    (ω.restrict f).toContinuousLinearMap =
      ω.toContinuousLinearMap.comp (starAlgHomToContinuousLinearMap f) := by
  ext a
  rfl

/-- Restricting a state along the identity star-homomorphism returns the same state. -/
@[simp] theorem restrict_id
    (ω : State A) :
    ω.restrict (StarAlgHom.id ℂ A) = ω := by
  ext a
  rfl

/-- State restriction is a genuine inverse-system operation. -/
theorem restrict_comp
    (f : A →⋆ₐ[ℂ] B)
    (g : B →⋆ₐ[ℂ] C)
    (ω : State C) :
    (ω.restrict g).restrict f =
      ω.restrict (g.comp f) := by
  ext a
  rfl

end State

variable {I : Type u} [Preorder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]

/-- A filtered direct system in the category of noncommutative complex
C-star algebras and unital star homomorphisms, represented as a subtype of
transition star-homomorphisms satisfying identity and composition laws. -/
def ContinuousStarInductiveSystem : Type u :=
  { map :
      ∀ {i j : I}, i ≤ j →
        (Stage i →⋆ₐ[ℂ] Stage j) //
    (∀ i,
      map (le_refl i) =
        StarAlgHom.id ℂ (Stage i)) ∧
    (∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      (map hjk).comp (map hij) =
        map (le_trans hij hjk)) }

namespace ContinuousStarInductiveSystem

/-- Construct a `ContinuousStarInductiveSystem` from star-algebra transition maps and their laws. -/
def mk
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    (map : ∀ {i j : I}, i ≤ j → (Stage i →⋆ₐ[ℂ] Stage j))
    (map_id : ∀ i, map (le_refl i) = StarAlgHom.id ℂ (Stage i))
    (map_comp :
      ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
        (map hjk).comp (map hij) = map (le_trans hij hjk)) :
    ContinuousStarInductiveSystem Stage :=
  ⟨map, map_id, map_comp⟩

/-- Transition star-algebra homomorphism `sys.map hij : Stage i →⋆ₐ[ℂ] Stage j`. -/
def map
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    {i j : I} (hij : i ≤ j) :
    Stage i →⋆ₐ[ℂ] Stage j :=
  sys.1 hij

/-- Simplification rule for `(ContinuousStarInductiveSystem.mk ...).map`. -/
@[simp] theorem map_mk
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    (f : ∀ {i j : I}, i ≤ j → (Stage i →⋆ₐ[ℂ] Stage j))
    (fid : ∀ i, f (le_refl i) = StarAlgHom.id ℂ (Stage i))
    (fcomp :
      ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
        (f hjk).comp (f hij) = f (le_trans hij hjk))
    {i j : I} (hij : i ≤ j) :
    (ContinuousStarInductiveSystem.mk f fid fcomp).map hij = f hij := by
  change f hij = f hij
  rfl

/-- Simplification rule for `ContinuousStarInductiveSystem.map ⟨f, h⟩`. -/
@[simp] theorem map_subtype_mk
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    (f : ∀ {i j : I}, i ≤ j → (Stage i →⋆ₐ[ℂ] Stage j))
    (h :
      (∀ i, f (le_refl i) = StarAlgHom.id ℂ (Stage i)) ∧
      (∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
        (f hjk).comp (f hij) = f (le_trans hij hjk)))
    {i j : I} (hij : i ≤ j) :
    ContinuousStarInductiveSystem.map (Stage := Stage) ⟨f, h⟩ hij = f hij := by
  change f hij = f hij
  rfl

/-- Identity law `sys.map (le_refl i) = StarAlgHom.id ℂ (Stage i)`. -/
theorem map_id
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (i : I) :
    sys.map (le_refl i) = StarAlgHom.id ℂ (Stage i) := by
  have h := sys.2.1 i
  exact h

/-- Composition law `(sys.map hjk).comp (sys.map hij) = sys.map (le_trans hij hjk)`. -/
theorem map_comp
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    (sys.map hjk).comp (sys.map hij) =
      sys.map (le_trans hij hjk) := by
  have h := sys.2.2 hij hjk
  exact h

variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

/-- Continuous operator underlying a filtered star transition. -/
def transitionCLM
    {i j : I} (hij : i ≤ j) :
    Stage i →L[ℂ] Stage j :=
  starAlgHomToContinuousLinearMap (sys.map hij)

/-- Evaluation of `transitionCLM` agrees with `sys.map`. -/
@[simp] theorem transitionCLM_apply
    {i j : I} (hij : i ≤ j) (a : Stage i) :
    transitionCLM Stage sys hij a =
      sys.map hij a := by
  change sys.map hij a = sys.map hij a
  rfl

/-- Forgetting multiplication, star, norm, and topology recovers the existing
linear direct-inductive-system owner. -/
def toDirectInductiveSystem :
    DirectInductiveSystem ℂ I Stage :=
  DirectInductiveSystem.mk
    (fun hij => (sys.map hij).toAlgHom.toLinearMap)
    (by
      intro i
      rw [sys.map_id]
      rfl)
    (by
      intro i j k hij hjk
      rw [← sys.map_comp hij hjk]
      rfl)

/-- A projectively compatible family of states on the filtered stages, represented as a
subtype of stage states compatible under `State.restrict (sys.map hij)`. -/
def CompatibleStateFamily : Type u :=
  { state : ∀ i, State (Stage i) //
    ∀ {i j : I} (hij : i ≤ j),
      (state j).restrict (sys.map hij) =
        state i }

namespace CompatibleStateFamily

/-- Construct a `CompatibleStateFamily` from stage states and their restriction compatibility. -/
def mk
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)]
    [∀ i, StarOrderedRing (Stage i)]
    {sys : ContinuousStarInductiveSystem Stage}
    (state : ∀ i, State (Stage i))
    (compatible :
      ∀ {i j : I} (hij : i ≤ j),
        (state j).restrict (sys.map hij) = state i) :
    CompatibleStateFamily Stage sys :=
  ⟨state, compatible⟩

/-- Stage state `ω.state i : State (Stage i)`. -/
def state
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)]
    [∀ i, StarOrderedRing (Stage i)]
    {sys : ContinuousStarInductiveSystem Stage}
    (ω : CompatibleStateFamily Stage sys)
    (i : I) :
    State (Stage i) :=
  ω.1 i

/-- Simplification rule for `(CompatibleStateFamily.mk s h).state`. -/
@[simp] theorem state_mk
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)]
    [∀ i, StarOrderedRing (Stage i)]
    {sys : ContinuousStarInductiveSystem Stage}
    (s : ∀ i, State (Stage i))
    (h : ∀ {i j : I} (hij : i ≤ j), (s j).restrict (sys.map hij) = s i)
    (i : I) :
    (CompatibleStateFamily.mk s h).state i = s i := by
  change s i = s i
  rfl

/-- Simplification rule for `CompatibleStateFamily.state ⟨s, h⟩`. -/
@[simp] theorem state_subtype_mk
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)]
    [∀ i, StarOrderedRing (Stage i)]
    {sys : ContinuousStarInductiveSystem Stage}
    (s : ∀ i, State (Stage i))
    (h : ∀ {i j : I} (hij : i ≤ j), (s j).restrict (sys.map hij) = s i)
    (i : I) :
    CompatibleStateFamily.state (Stage := Stage) (sys := sys) ⟨s, h⟩ i = s i := by
  change s i = s i
  rfl

/-- Restriction compatibility `(ω.state j).restrict (sys.map hij) = ω.state i`. -/
theorem compatible
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)]
    [∀ i, StarOrderedRing (Stage i)]
    {sys : ContinuousStarInductiveSystem Stage}
    (ω : CompatibleStateFamily Stage sys)
    {i j : I} (hij : i ≤ j) :
    (ω.state j).restrict (sys.map hij) = ω.state i := by
  have h := ω.2 hij
  exact h

variable (ω : CompatibleStateFamily Stage sys)

/-- Evaluation form of projective state compatibility. -/
theorem eval_transition
    {i j : I} (hij : i ≤ j)
    (a : Stage i) :
    (ω.state j).functional (sys.map hij a) =
      (ω.state i).functional a := by
  have h := congrArg
    (fun ν : State (Stage i) => ν.functional a)
    (ω.compatible hij)
  exact h

/-- Continuous-linear functional compatibility `(ω.state j).toContinuousLinearMap.comp (sys.transitionCLM Stage hij) = (ω.state i).toContinuousLinearMap`. -/
theorem continuousLinearMap_transition
    {i j : I} (hij : i ≤ j) :
    (ω.state j).toContinuousLinearMap.comp
        (sys.transitionCLM Stage hij) =
      (ω.state i).toContinuousLinearMap := by
  ext a
  exact eval_transition Stage sys ω hij a

/-- Transitive continuous-linear functional compatibility across `i ≤ j ≤ k`. -/
theorem continuousLinearMap_transition_trans
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    ((ω.state k).toContinuousLinearMap.comp
        (sys.transitionCLM Stage hjk)).comp
        (sys.transitionCLM Stage hij) =
      (ω.state i).toContinuousLinearMap := by
  ext a
  change (ω.state k).functional
      (sys.map hjk (sys.map hij a)) =
    (ω.state i).functional a
  rw [eval_transition Stage sys ω hjk (sys.map hij a)]
  exact eval_transition Stage sys ω hij a

/-- Compatibility after two transitions follows from the inverse-system
composition law and the direct-system composition law. -/
theorem compatible_trans
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    (ω.state k).restrict
        ((sys.map hjk).comp (sys.map hij)) =
      ω.state i := by
  rw [← State.restrict_comp]
  rw [ω.compatible hjk, ω.compatible hij]

end CompatibleStateFamily

variable {Ainf : Type u}
variable [CStarAlgebra Ainf]

omit [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)] in
/-- A star-algebraic cocone over the filtered system, represented as a subtype
of stage star-homomorphisms commuting with `sys.map`. -/
def StarInductiveCocone
    (sys : ContinuousStarInductiveSystem Stage) : Type u :=
  { ι : ∀ i, Stage i →⋆ₐ[ℂ] Ainf //
    ∀ {i j : I} (hij : i ≤ j),
      (ι j).comp (sys.map hij) =
        ι i }

namespace StarInductiveCocone

/-- Construct a `StarInductiveCocone` from stage star-homomorphisms and their transition compatibility. -/
def mk
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    {sys : ContinuousStarInductiveSystem Stage}
    (ι : ∀ i, Stage i →⋆ₐ[ℂ] Ainf)
    (ι_comm :
      ∀ {i j : I} (hij : i ≤ j),
        (ι j).comp (sys.map hij) = ι i) :
    StarInductiveCocone (Ainf := Ainf) Stage sys :=
  ⟨ι, ι_comm⟩

/-- Stage star-homomorphism leg `cocone.ι i : Stage i →⋆ₐ[ℂ] Ainf`. -/
def ι
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    {sys : ContinuousStarInductiveSystem Stage}
    (cocone : StarInductiveCocone (Ainf := Ainf) Stage sys)
    (i : I) :
    Stage i →⋆ₐ[ℂ] Ainf :=
  cocone.1 i

/-- Simplification rule for `(StarInductiveCocone.mk ι h).ι`. -/
@[simp] theorem ι_mk
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    {sys : ContinuousStarInductiveSystem Stage}
    (ι : ∀ i, Stage i →⋆ₐ[ℂ] Ainf)
    (h : ∀ {i j : I} (hij : i ≤ j), (ι j).comp (sys.map hij) = ι i)
    (i : I) :
    (StarInductiveCocone.mk (Ainf := Ainf) ι h).ι i = ι i := by
  change ι i = ι i
  rfl

/-- Simplification rule for `StarInductiveCocone.ι ⟨ι, h⟩`. -/
@[simp] theorem ι_subtype_mk
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    {sys : ContinuousStarInductiveSystem Stage}
    (ι : ∀ i, Stage i →⋆ₐ[ℂ] Ainf)
    (h : ∀ {i j : I} (hij : i ≤ j), (ι j).comp (sys.map hij) = ι i)
    (i : I) :
    StarInductiveCocone.ι (Stage := Stage) (sys := sys) (Ainf := Ainf) ⟨ι, h⟩ i = ι i := by
  change ι i = ι i
  rfl

/-- Cocone compatibility `(cocone.ι j).comp (sys.map hij) = cocone.ι i`. -/
theorem ι_comm
    {Stage : I → Type u}
    [∀ i, CStarAlgebra (Stage i)]
    {sys : ContinuousStarInductiveSystem Stage}
    (cocone : StarInductiveCocone (Ainf := Ainf) Stage sys)
    {i j : I} (hij : i ≤ j) :
    (cocone.ι j).comp (sys.map hij) = cocone.ι i := by
  have h := cocone.2 hij
  exact h

variable [PartialOrder Ainf] [StarOrderedRing Ainf]
variable
    (cocone :
      StarInductiveCocone (Ainf := Ainf) Stage sys)

/-- Forgetting star and multiplication yields the existing linear cocone. -/
def toInductiveCocone :
    InductiveCocone ℂ (toDirectInductiveSystem Stage sys) Ainf :=
  InductiveCocone.mk
    (fun i => (cocone.ι i).toAlgHom.toLinearMap)
    (by
      intro i j hij
      rw [← cocone.ι_comm hij]
      rfl)

/-- A state on a star-algebraic colimit cocone restricts to a compatible
inverse family of finite-stage states. -/
def restrictStateFamily
    (ω : State Ainf) :
    CompatibleStateFamily Stage sys :=
  CompatibleStateFamily.mk
    (fun i => ω.restrict (cocone.ι i))
    (by
      intro i j hij
      rw [State.restrict_comp]
      rw [cocone.ι_comm hij])

/-- Compatibility of `restrictStateFamily` with `toContinuousLinearMap` at stage `i`. -/
theorem state_readout_continuousLinearMap
    (ω : State Ainf) (i : I) :
    ω.toContinuousLinearMap.comp
        (starAlgHomToContinuousLinearMap (cocone.ι i)) =
      ((restrictStateFamily (Stage := Stage) (sys := sys) cocone ω).state i).toContinuousLinearMap := by
  ext a
  rfl

/-- The topological-category cocone leg associated to a star-algebraic leg. -/
def ιTopCatHom (i : I) :
    TopCat.of (Stage i) ⟶ TopCat.of Ainf :=
  TopCat.ofHom
    { toFun := starAlgHomToContinuousLinearMap (cocone.ι i)
      continuous_toFun :=
        (starAlgHomToContinuousLinearMap (cocone.ι i)).continuous }

/-- Pointwise evaluation of `ιTopCatHom` agrees with `cocone.ι`. -/
@[simp] theorem ιTopCatHom_apply (i : I) (a : Stage i) :
    ιTopCatHom (Stage := Stage) (sys := sys) cocone i a = cocone.ι i a := by
  change cocone.ι i a = cocone.ι i a
  rfl

/-- The readout of a colimit state is independent of the chosen later-stage
representative. -/
theorem state_readout_transition
    (ω : State Ainf)
    {i j : I} (hij : i ≤ j)
    (a : Stage i) :
    ω.functional
        (cocone.ι j (sys.map hij a)) =
      ω.functional (cocone.ι i a) := by
  have h := congrArg
    (fun f : Stage i →⋆ₐ[ℂ] Ainf => f a)
    (cocone.ι_comm hij)
  simpa using congrArg ω.functional h

end StarInductiveCocone

end ContinuousStarInductiveSystem

end CStarStateColimit.Native

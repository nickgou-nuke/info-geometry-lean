import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Canonical.FilteredDirectInverseColimit

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
theorem gns_state_pos (a : A) : 0 ≤ (phi (star a * a)).re :=
  (Complex.nonneg_iff.mp
    (PositiveLinearMap.map_nonneg phi
      (CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr ⟨a, rfl⟩))).1

/-- **Theorem**: Real Part of Self-Adjoint Star Product is Zero in Imaginary Component. -/
theorem gns_state_self_star_real (a : A) : (phi (star a * a)).im = 0 := by
  exact (Complex.nonneg_iff.mp
    (PositiveLinearMap.map_nonneg phi
      (CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr ⟨a, rfl⟩))).2.symm

/-- GNS Null Space N_φ = { a ∈ A | φ(a* a) = 0 }. -/
def gnsNullSpace (a : A) : Prop :=
  phi (star a * a) = 0

/-- **Theorem**: GNS Null Element Characterization: a ∈ N_φ ⟹ Re(φ(a* a)) = 0. -/
theorem gns_null_re_zero (a : A) (h_null : phi.gnsNullSpace a) :
    (phi (star a * a)).re = 0 := by
  dsimp [gnsNullSpace] at h_null
  rw [h_null]
  rfl

/-- KMS Thermal Equilibrium Condition for modular time flow σ_t on C*-algebra A:
    φ(a * b) = φ(b * σ_iβ(a)). -/
structure KMSState (sigma_i_beta : A → A) where
  state : PositiveState A
  kms_condition : ∀ a b : A, state (a * b) = state (b * sigma_i_beta a)

/-- **Theorem**: KMS Boundary State Commutativity under Identity Modular Automorphism:
    If σ_iβ = Id, then φ(a * b) = φ(b * a) (Tracial State Condition). -/
theorem kms_tracial_state (kms : KMSState (fun x => x)) (a b : A) :
    kms.state (a * b) = kms.state (b * a) :=
  kms.kms_condition a b

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

No commutativity or diagonalization property is imposed.
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

/-- A normalized positive functional in Mathlib's native C-star sense. -/
structure State
    (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] where
  functional : A →ₚ[ℂ] ℂ
  normalized : functional 1 = 1

namespace State

/-- States are determined by their native positive linear functionals. -/
@[ext] theorem ext
    {ω ν : State A}
    (h : ω.functional = ν.functional) :
    ω = ν := by
  cases ω
  cases ν
  simp_all

@[simp] theorem apply_one (ω : State A) :
    ω.functional 1 = 1 :=
  ω.normalized

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


@[simp] theorem toContinuousLinearMap_apply
    (ω : State A) (a : A) :
    ω.toContinuousLinearMap a = ω.functional a :=
  rfl


/-- Contravariant restriction of a state along a star algebra homomorphism. -/
def restrict
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B) :
    State A where
  functional :=
    PositiveLinearMap.mk
      (ω.functional.toLinearMap.comp f.toAlgHom.toLinearMap)
      (ω.functional.monotone.comp (starAlgHom_monotone f))
  normalized := by
    change ω.functional (f 1) = 1
    rw [map_one, ω.normalized]

@[simp] theorem restrict_apply
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B) (a : A) :
    (ω.restrict f).functional a =
      ω.functional (f a) :=
  rfl

theorem restrict_toContinuousLinearMap
    (f : A →⋆ₐ[ℂ] B) (ω : State B) :
    (ω.restrict f).toContinuousLinearMap =
      ω.toContinuousLinearMap.comp (starAlgHomToContinuousLinearMap f) := by
  ext a
  rfl

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
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]

/-- A filtered direct system in the category of noncommutative complex
C-star algebras and unital star homomorphisms. -/
structure ContinuousStarInductiveSystem where
  map :
    ∀ {i j : I}, i ≤ j →
      (Stage i →⋆ₐ[ℂ] Stage j)
  map_id :
    ∀ i,
      map (le_refl i) =
        StarAlgHom.id ℂ (Stage i)
  map_comp :
    ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      (map hjk).comp (map hij) =
        map (le_trans hij hjk)

namespace ContinuousStarInductiveSystem

variable (sys : ContinuousStarInductiveSystem Stage)

/-- Continuous operator underlying a filtered star transition. -/
def transitionCLM
    {i j : I} (hij : i ≤ j) :
    Stage i →L[ℂ] Stage j :=
  starAlgHomToContinuousLinearMap (sys.map hij)

@[simp] theorem transitionCLM_apply
    {i j : I} (hij : i ≤ j) (a : Stage i) :
    transitionCLM Stage sys hij a =
      sys.map hij a :=
  rfl

/-- Forgetting multiplication, star, norm, and topology recovers the existing
linear direct-inductive-system owner. -/
def toDirectInductiveSystem :
    DirectInductiveSystem ℂ I Stage where
  f := fun hij =>
    (sys.map hij).toAlgHom.toLinearMap
  f_id := by
    intro i
    rw [sys.map_id]
    rfl
  f_comp := by
    intro i j k hij hjk
    rw [← sys.map_comp hij hjk]
    rfl

/-- A projectively compatible family of states on the filtered stages. -/
structure CompatibleStateFamily where
  state : ∀ i, State (Stage i)
  compatible :
    ∀ {i j : I} (hij : i ≤ j),
      (state j).restrict (sys.map hij) =
        state i

namespace CompatibleStateFamily

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

theorem continuousLinearMap_transition
    {i j : I} (hij : i ≤ j) :
    (ω.state j).toContinuousLinearMap.comp
        (sys.transitionCLM Stage hij) =
      (ω.state i).toContinuousLinearMap := by
  ext a
  exact eval_transition Stage sys ω hij a

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
variable [CStarAlgebra Ainf] [PartialOrder Ainf] [StarOrderedRing Ainf]

/-- A star-algebraic cocone over the filtered system. -/
abbrev StarInductiveCocone
    (sys : ContinuousStarInductiveSystem Stage) : Type _ :=
  {ι : ∀ i, Stage i →⋆ₐ[ℂ] Ainf //
    ∀ {i j : I} (hij : i ≤ j),
      (ι j).comp (sys.map hij) =
        ι i}

namespace StarInductiveCocone

variable
    (cocone :
      StarInductiveCocone (Ainf := Ainf) Stage sys)

def leg (cocone : StarInductiveCocone (Ainf := Ainf) Stage sys)
    (i : I) : Stage i →⋆ₐ[ℂ] Ainf := cocone.1 i

theorem compatibility (cocone : StarInductiveCocone (Ainf := Ainf) Stage sys)
    {i j : I} (hij : i ≤ j) :
    (leg (Stage := Stage) (sys := sys) cocone j).comp (sys.map hij) =
      leg (Stage := Stage) (sys := sys) cocone i :=
  cocone.2 hij

/-- Forgetting star and multiplication yields the existing linear cocone. -/
def toInductiveCocone :
    InductiveCocone ℂ sys.toDirectInductiveSystem Ainf :=
  ⟨(fun i => (leg (Stage := Stage) (sys := sys) cocone i).toAlgHom.toLinearMap), by
    intro i j hij
    change
      ((leg (Stage := Stage) (sys := sys) cocone j).toAlgHom.toLinearMap).comp
          ((sys.map hij).toAlgHom.toLinearMap) =
        (leg (Stage := Stage) (sys := sys) cocone i).toAlgHom.toLinearMap
    rw [← compatibility (Stage := Stage) (sys := sys) cocone hij]
    rfl⟩

/-- A state on a star-algebraic colimit cocone restricts to a compatible
inverse family of finite-stage states. -/
def restrictStateFamily
    (ω : State Ainf) :
    CompatibleStateFamily Stage sys where
  state := fun i =>
    ω.restrict (leg (Stage := Stage) (sys := sys) cocone i)
  compatible := by
    intro i j hij
    rw [State.restrict_comp]
    rw [compatibility (Stage := Stage) (sys := sys) cocone hij]

theorem state_readout_continuousLinearMap
    (ω : State Ainf) (i : I) :
    ω.toContinuousLinearMap.comp
        (starAlgHomToContinuousLinearMap
          (leg (Stage := Stage) (sys := sys) cocone i)) =
      ((restrictStateFamily (Stage := Stage) (sys := sys) cocone ω).state i).toContinuousLinearMap := by
  ext a
  rfl

/-- The topological-category cocone leg associated to a star-algebraic leg. -/
def ιTopCatHom (i : I) :
    TopCat.of (Stage i) ⟶ TopCat.of Ainf :=
  TopCat.ofHom
    { toFun := starAlgHomToContinuousLinearMap
        (leg (Stage := Stage) (sys := sys) cocone i)
      continuous_toFun :=
        (starAlgHomToContinuousLinearMap
          (leg (Stage := Stage) (sys := sys) cocone i)).continuous }

@[simp] theorem ιTopCatHom_apply (i : I) (a : Stage i) :
    ιTopCatHom (Stage := Stage) (sys := sys) cocone i a =
      leg (Stage := Stage) (sys := sys) cocone i a :=
  rfl

/-- The readout of a colimit state is independent of the chosen later-stage
representative. -/
theorem state_readout_transition
    (ω : State Ainf)
    {i j : I} (hij : i ≤ j)
    (a : Stage i) :
    ω.functional
        (leg (Stage := Stage) (sys := sys) cocone j (sys.map hij a)) =
      ω.functional (leg (Stage := Stage) (sys := sys) cocone i a) := by
  have h := congrArg
    (fun f : Stage i →⋆ₐ[ℂ] Ainf => f a)
    (compatibility (Stage := Stage) (sys := sys) cocone hij)
  simpa using congrArg ω.functional h

end StarInductiveCocone

end ContinuousStarInductiveSystem

end CStarStateColimit.Native

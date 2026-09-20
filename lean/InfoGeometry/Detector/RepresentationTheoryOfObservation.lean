import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace DetectorGeometry.RepresentationTheoryOfObservation

/-! The formal content extracted from the stream is algebraic. Statements about
physical systems are represented by explicit structures or hypotheses; no
physical identification is introduced as an axiom. -/

section Representations

structure Representation (G V : Type*) where
  act : G → V → V

def IsInvariant {G V Y : Type*} (representation : Representation G V)
    (observable : V → Y) : Prop :=
  ∀ g v, observable (representation.act g v) = observable v

theorem invariant_comp {G V Y Z : Type*} (representation : Representation G V)
    (observable : V → Y) (postprocess : Y → Z)
    (hinv : IsInvariant representation observable) :
    IsInvariant representation (postprocess ∘ observable) := by
  intro g v
  simp [Function.comp, hinv g v]

end Representations

section RankConstraint

def singleCount (ε : ℝ) : ℝ := ε

def coincidenceCount (k ε : ℝ) : ℝ := k * ε ^ 2

theorem coincidenceCount_eq_coefficient_mul_singleCount_sq (k ε : ℝ) :
    coincidenceCount k ε = k * (singleCount ε) ^ 2 := by
  rfl

theorem rank_two_is_quadratic (k ε : ℝ) :
    coincidenceCount k ε = coincidenceCount k (-ε) := by
  simp [coincidenceCount]

end RankConstraint

section PoissonMetric

noncomputable def poissonMetric (N dN : ℝ) : ℝ := dN ^ 2 / N

noncomputable def rootCoordinate (N : ℝ) : ℝ := Real.sqrt N

theorem rootCoordinate_sq (N : ℝ) (hN : 0 ≤ N) :
    rootCoordinate N ^ 2 = N := by
  simp [rootCoordinate, Real.sq_sqrt hN]

theorem poissonMetric_rootCoordinate (x dx : ℝ) (hx : 0 < x) :
    poissonMetric (x ^ 2) (2 * x * dx) = 4 * dx ^ 2 := by
  dsimp [poissonMetric]
  have hxne : x ≠ 0 := ne_of_gt hx
  field_simp
  ring

end PoissonMetric

section BoundaryConstraint

def boundedCapacity (x : ℝ) : ℝ := x * (1 - x)

def complement (x : ℝ) : ℝ := 1 - x

theorem boundedCapacity_complement (x : ℝ) :
    boundedCapacity (complement x) = boundedCapacity x := by
  simp [boundedCapacity, complement]
  ring

theorem complement_fixed_iff (x : ℝ) : complement x = x ↔ x = 1 / 2 := by
  simp only [complement]
  constructor
  · intro h
    linarith
  · intro h
    rw [h]
    norm_num

theorem boundedCapacity_nonnegative {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    0 ≤ boundedCapacity x := by
  exact mul_nonneg hx₀ (sub_nonneg.mpr hx₁)

end BoundaryConstraint

section CanonicalPeriod

noncomputable def normalizedPrimitive (x : ℝ) : ℝ := x ^ 2 / 2 - x ^ 3 / 3

theorem normalizedPeriod :
    normalizedPrimitive 1 - normalizedPrimitive 0 = 1 / 6 := by
  norm_num [normalizedPrimitive]

end CanonicalPeriod

section CausalPoset

inductive Archetype
  | rankRepresentation
  | poissonFlattening
  | boundaryReflection
  | selfDualMidpoint
  | canonicalPeriod
  | observationSynthesis
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .rankRepresentation => 180
  | .poissonFlattening => 181
  | .boundaryReflection => 182
  | .selfDualMidpoint => 183
  | .canonicalPeriod => 184
  | .observationSynthesis => 185

def causallyPrecedes (a b : Archetype) : Prop := rank a ≤ rank b

theorem causal_refl (a : Archetype) : causallyPrecedes a a := le_rfl

theorem causal_trans {a b c : Archetype} :
    causallyPrecedes a b → causallyPrecedes b c → causallyPrecedes a c := by
  exact Nat.le_trans

theorem causal_antisymm {a b : Archetype} :
    causallyPrecedes a b → causallyPrecedes b a → a = b := by
  intro hab hba
  cases a <;> cases b <;> simp [causallyPrecedes, rank] at hab hba ⊢

theorem canonical_chain :
    causallyPrecedes .rankRepresentation .poissonFlattening ∧
    causallyPrecedes .poissonFlattening .boundaryReflection ∧
    causallyPrecedes .boundaryReflection .selfDualMidpoint ∧
    causallyPrecedes .selfDualMidpoint .canonicalPeriod ∧
    causallyPrecedes .canonicalPeriod .observationSynthesis := by
  norm_num [causallyPrecedes, rank]

end CausalPoset

end DetectorGeometry.RepresentationTheoryOfObservation

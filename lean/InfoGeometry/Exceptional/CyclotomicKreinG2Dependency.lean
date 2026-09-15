import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace InfoGeometry.Exceptional.CyclotomicKreinG2.ProofDependency

inductive Archetype
  | cyclotomicPolynomial
  | unitArithmetic
  | galoisGroup
  | integerClock
  | exactPeriod
  | rootDecomposition
  | neutralPairing
  | paraAntiIsometry
  | traceDiscriminant
  | ellipticCounterexample
  | primitiveRoot
  | rotationRepresentation
  | rotationPeriod
  | ellipticRotation
  | rotationQuartic
  | rotationHalfPeriod
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | cyclotomicPolynomial => {cyclotomicPolynomial}
  | unitArithmetic => {unitArithmetic}
  | galoisGroup => {unitArithmetic, galoisGroup}
  | integerClock => {cyclotomicPolynomial, integerClock}
  | exactPeriod => {cyclotomicPolynomial, integerClock, exactPeriod}
  | rootDecomposition => {rootDecomposition}
  | neutralPairing => {neutralPairing}
  | paraAntiIsometry => {neutralPairing, paraAntiIsometry}
  | traceDiscriminant => {traceDiscriminant}
  | ellipticCounterexample => {traceDiscriminant, ellipticCounterexample}
  | primitiveRoot => {primitiveRoot}
  | rotationRepresentation => {primitiveRoot, rotationRepresentation}
  | rotationPeriod => {primitiveRoot, rotationRepresentation, rotationPeriod}
  | ellipticRotation =>
      {primitiveRoot, rotationRepresentation, traceDiscriminant, ellipticRotation}
  | rotationQuartic =>
      {cyclotomicPolynomial, primitiveRoot, rotationRepresentation, rotationQuartic}
  | rotationHalfPeriod =>
      {cyclotomicPolynomial, primitiveRoot, rotationRepresentation,
        rotationQuartic, rotationHalfPeriod}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

instance : DecidableLE Archetype := fun earlier later =>
  inferInstanceAs (Decidable (prerequisites earlier ⊆ prerequisites later))

theorem dependency_branches :
    cyclotomicPolynomial < integerClock ∧ integerClock < exactPeriod ∧
    unitArithmetic < galoisGroup ∧ neutralPairing < paraAntiIsometry ∧
    traceDiscriminant < ellipticCounterexample := by
  simp only [lt_iff_le_not_ge]
  decide

theorem arithmetic_and_roots_incomparable :
    ¬ galoisGroup ≤ rootDecomposition ∧ ¬ rootDecomposition ≤ galoisGroup ∧
    ¬ exactPeriod ≤ rootDecomposition ∧ ¬ rootDecomposition ≤ exactPeriod := by
  decide

theorem neutral_and_spectral_branches_incomparable :
    ¬ paraAntiIsometry ≤ traceDiscriminant ∧
    ¬ traceDiscriminant ≤ paraAntiIsometry := by
  decide

theorem no_cycle {earlier later : Archetype} (forward : earlier < later) :
    ¬ later < earlier := lt_asymm forward

theorem rotation_dependencies :
    primitiveRoot < rotationRepresentation ∧ rotationRepresentation < rotationPeriod ∧
    rotationRepresentation < ellipticRotation ∧ traceDiscriminant < ellipticRotation ∧
    cyclotomicPolynomial < rotationQuartic ∧ rotationRepresentation < rotationQuartic ∧
    rotationQuartic < rotationHalfPeriod := by
  simp only [lt_iff_le_not_ge]
  decide

theorem periodicity_and_ellipticity_incomparable :
    ¬ rotationPeriod ≤ ellipticRotation ∧ ¬ ellipticRotation ≤ rotationPeriod := by
  decide

end InfoGeometry.Exceptional.CyclotomicKreinG2.ProofDependency

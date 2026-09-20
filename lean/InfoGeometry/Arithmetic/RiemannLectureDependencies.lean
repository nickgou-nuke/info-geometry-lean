import Mathlib.Data.Finset.Order
import Mathlib.Tactic

namespace InfoGeometry.Arithmetic.RiemannLectureDependencies

inductive Archetype
  | eulerProduct
  | dirichletSeries
  | sumProductIdentification
  | functionalEquation
  | schwarzSymmetry
  | zeroReflection
  | uniqueZeroInInvariantRegion
  | localCriticalLineCertificate
  deriving DecidableEq, Fintype

def prerequisites : Archetype → Finset ℕ
  | .eulerProduct => {0}
  | .dirichletSeries => {1}
  | .sumProductIdentification => {0, 1, 2}
  | .functionalEquation => {3}
  | .schwarzSymmetry => {4}
  | .zeroReflection => {3, 4, 5}
  | .uniqueZeroInInvariantRegion => {6}
  | .localCriticalLineCertificate => {3, 4, 5, 6, 7}

theorem prerequisites_injective : Function.Injective prerequisites := by decide

instance : PartialOrder Archetype :=
  PartialOrder.lift prerequisites prerequisites_injective

instance : DecidableRel (α := Archetype) (· ≤ ·) :=
  fun left right => inferInstanceAs (Decidable (prerequisites left ⊆ prerequisites right))

theorem arithmetic_branch :
    Archetype.eulerProduct ≤ Archetype.sumProductIdentification ∧
      Archetype.dirichletSeries ≤ Archetype.sumProductIdentification := by decide

theorem symmetry_branch :
    Archetype.functionalEquation ≤ Archetype.zeroReflection ∧
      Archetype.schwarzSymmetry ≤ Archetype.zeroReflection := by decide

theorem local_certificate_branch :
    Archetype.zeroReflection ≤ Archetype.localCriticalLineCertificate ∧
      Archetype.uniqueZeroInInvariantRegion ≤ Archetype.localCriticalLineCertificate := by
  decide

theorem arithmetic_and_local_certificate_incomparable :
    ¬ Archetype.sumProductIdentification ≤ Archetype.localCriticalLineCertificate ∧
      ¬ Archetype.localCriticalLineCertificate ≤ Archetype.sumProductIdentification := by
  decide

theorem symmetry_does_not_supply_uniqueness :
    ¬ Archetype.uniqueZeroInInvariantRegion ≤ Archetype.zeroReflection := by decide

theorem no_cycle (left right : Archetype) (forward : left ≤ right)
    (backward : right ≤ left) : left = right :=
  le_antisymm forward backward

end InfoGeometry.Arithmetic.RiemannLectureDependencies

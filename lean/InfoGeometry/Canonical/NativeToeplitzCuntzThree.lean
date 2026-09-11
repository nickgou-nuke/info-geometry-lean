import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Native three-generator Toeplitz--Cuntz carrier

This is the owner-level API for the three-generator algebraic quotient.  It
uses the noncommutative `CuntzToeplitzAlg 3` carrier directly; no structure of
generator fields and no commutative or diagonal replacement is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.NativeToeplitzCuntzThree

open InfoGeometry.Algebra.CuntzTensorQuotient

abbrev Carrier := CuntzToeplitzAlg 3

def generator (i : Fin 3) : Carrier := toeplitzS 3 i

def rangeProjection (i : Fin 3) : Carrier :=
  generator i * star (generator i)

def vacuumDefect : Carrier :=
  1 + (-rangeProjection 0) + (-rangeProjection 1) + (-rangeProjection 2)

def excitation : Carrier :=
  rangeProjection 0 + rangeProjection 1 + rangeProjection 2

theorem initialRelation (i j : Fin 3) :
    star (generator i) * generator j = if i = j then 1 else 0 := by
  rw [generator, star_toeplitzS]
  exact toeplitz_orthogonality 3 i j

theorem rangeProjection_idempotent (i : Fin 3) :
    rangeProjection i * rangeProjection i = rangeProjection i := by
  dsimp [rangeProjection]
  have h : generator i * star (generator i) *
      (generator i * star (generator i)) =
      generator i * (star (generator i) * generator i) *
        star (generator i) := by noncomm_ring
  rw [h, initialRelation i i]
  simp

theorem rangeProjection_orthogonal {i j : Fin 3} (hij : i ≠ j) :
    rangeProjection i * rangeProjection j = 0 := by
  dsimp [rangeProjection]
  have h : generator i * star (generator i) *
      (generator j * star (generator j)) =
      generator i * (star (generator i) * generator j) *
        star (generator j) := by noncomm_ring
  rw [h, initialRelation i j]
  simp [hij]

theorem resolution :
    excitation + vacuumDefect = (1 : Carrier) := by
  dsimp [excitation, vacuumDefect]
  abel

theorem vacuumDefect_selfAdjoint :
    star vacuumDefect = vacuumDefect := by
  simp [vacuumDefect, rangeProjection, generator, star_toeplitzS,
    star_toeplitzSdag]

end InfoGeometry.Canonical.NativeToeplitzCuntzThree

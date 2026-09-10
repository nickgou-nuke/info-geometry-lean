import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Matrix Complex

noncomputable section

/-!
# Cyclic Cocycle Maps Across Twisted K-Theory Sectors

This module keeps the twisted-sector cocycle lane finite and noncommutative:
all operators are explicit `2 × 2` complex matrices, multiplication is matrix
multiplication, and the closed theorems are trace/commutator consequences.

No global axioms are introduced.
-/

namespace InfoGeometry.Canonical.CyclicCocycleTwistedSectors

abbrev Mat2 := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-! ## Matrix commutators and cyclic cochains -/

/-- The matrix commutator `[D, A] = D * A - A * D`. -/
def commutator (D A : Mat2) : Mat2 :=
  D * A - A * D

/-- The cyclic 0-cochain `A ↦ Tr(tilt * A)`. -/
def cocycle0 (tilt A : Mat2) : ℂ :=
  Matrix.trace (tilt * A)

/-- The cyclic 1-cochain `(A₀,A₁) ↦ Tr(tilt * A₀ * [D,A₁])`. -/
def cocycle1 (tilt D A₀ A₁ : Mat2) : ℂ :=
  Matrix.trace (tilt * A₀ * commutator D A₁)

/-- The commutator vanishes exactly when the two matrices commute. -/
theorem commutator_eq_zero_of_commutes
    (D A : Mat2)
    (hcomm : D * A = A * D) :
    commutator D A = 0 := by
  unfold commutator
  rw [hcomm, sub_self]

/-- The cyclic 1-cochain vanishes when the second argument commutes with `D`. -/
theorem cocycle1_vanishes_when_commutes
    (tilt D A₀ A₁ : Mat2)
    (hcomm : D * A₁ = A₁ * D) :
    cocycle1 tilt D A₀ A₁ = 0 := by
  unfold cocycle1
  rw [commutator_eq_zero_of_commutes D A₁ hcomm]
  simp

/-- Leibniz rule for the noncommutative matrix commutator. -/
theorem commutator_mul (D A B : Mat2) :
    commutator D (A * B) = commutator D A * B + A * commutator D B := by
  unfold commutator
  noncomm_ring

/-- Three-term cyclic trace rotation for matrix products. -/
theorem trace_rot (A B C : Mat2) :
    Matrix.trace (A * B * C) = Matrix.trace (C * A * B) := by
  calc
    Matrix.trace (A * B * C) = Matrix.trace ((A * B) * C) := by rw [mul_assoc]
    _ = Matrix.trace (C * (A * B)) := Matrix.trace_mul_comm (A * B) C
    _ = Matrix.trace (C * A * B) := by rw [mul_assoc]

/-! ## Pairing with the Connes cocycle derivative -/

/-- Pair the cyclic 1-cochain with a Connes cocycle derivative `H`. -/
def pairingWithConnesCocycle
    (tilt D H A : Mat2) : ℂ :=
  cocycle1 tilt D H A

/--
At a flat boundary projection commuting with `D`, the 1-cocycle pairing
with the Connes cocycle derivative vanishes.
-/
theorem pairing_vanishes_at_flat_boundary
    (tilt D H proj : Mat2)
    (hcomm : D * proj = proj * D) :
    pairingWithConnesCocycle tilt D H proj = 0 :=
  cocycle1_vanishes_when_commutes tilt D H proj hcomm

/-! ## Twisted sector index -/

/-- The twisted-sector index pairing `Tr(tilt * P₀ * [D,P₁])`. -/
def twistedSectorIndex
    (tilt D P₀ P₁ : Mat2) : ℂ :=
  cocycle1 tilt D P₀ P₁

/-- At a flat boundary, a `D`-commuting sector has zero twisted-sector index. -/
theorem twistedSectorIndex_vanishes_at_flat_boundary
    (tilt D P₀ P₁ : Mat2)
    (hcomm : D * P₁ = P₁ * D) :
    twistedSectorIndex tilt D P₀ P₁ = 0 :=
  cocycle1_vanishes_when_commutes tilt D P₀ P₁ hcomm

/--
If both sector projections commute with the Dirac matrix, both orientations
of the twisted-sector index vanish and hence agree up to sign.
-/
theorem twistedSectorIndex_antisymm_at_flat_boundary
    (tilt D P₀ P₁ : Mat2)
    (hcomm₀ : D * P₀ = P₀ * D)
    (hcomm₁ : D * P₁ = P₁ * D) :
    twistedSectorIndex tilt D P₁ P₀ = -twistedSectorIndex tilt D P₀ P₁ := by
  rw [twistedSectorIndex_vanishes_at_flat_boundary tilt D P₁ P₀ hcomm₀]
  rw [twistedSectorIndex_vanishes_at_flat_boundary tilt D P₀ P₁ hcomm₁]
  simp

end InfoGeometry.Canonical.CyclicCocycleTwistedSectors

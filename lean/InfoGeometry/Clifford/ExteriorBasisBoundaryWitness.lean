import InfoGeometry.Clifford.Cl55ExteriorSpinorCoordinateReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.LinearAlgebra.RegularDyadCompression
import Mathlib.Tactic

/-!
# An exact two-boundary separation witness on the existing exterior spinor

The basis is the repository's actual exterior basis, indexed by subsets of
`Fin 5`. Empty, singleton and full subsets are not arbitrary replacements for
the spinor carrier. The transition below is the native rank-one map from the
empty basis state to the full basis state.

The file does not assert that this rank-one map is already identified with
the separately normalized `Cl55` creation word. That representation
calibration, and any dynamical current interpretation, remain separate.
-/

noncomputable section

namespace InfoGeometry.Clifford.ExteriorBasisBoundaryWitness

open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.SplitClifford55ExteriorDegrees
open InfoGeometry.LinearAlgebra.RegularDyadCompression

abbrev OccupationIndex := Finset (Fin 5)

/-- The already constructed exterior basis state. -/
abbrev basisState (I : OccupationIndex) : Spinor := exteriorAlgebraBasisFinset I

/-- A coordinate covector from that same native basis. -/
def coordinate (I : OccupationIndex) : Module.Dual ℝ Spinor :=
  (LinearMap.proj I).comp exteriorAlgebraBasisFinset.equivFun.toLinearMap

@[simp] theorem coordinate_basisState (I J : OccupationIndex) :
    coordinate I (basisState J) = if J = I then 1 else 0 := by
  change exteriorAlgebraBasisFinset.equivFun (exteriorAlgebraBasisFinset J) I = _
  exact exteriorAlgebraBasisFinset.equivFun_self J I

abbrev emptyState : Spinor := basisState ∅
abbrev fullState : Spinor := basisState Finset.univ

/-- The source's two-boundary covector, expressed in the actual exterior basis. -/
def boundaryCovector : Module.Dual ℝ Spinor := coordinate ∅ + coordinate Finset.univ

@[simp] theorem overlap_empty : boundaryCovector emptyState = 1 := by
  have hne : (∅ : Finset (Fin 5)) ≠ Finset.univ := by
    intro h
    have hz : (0 : Fin 5) ∈ (∅ : Finset (Fin 5)) := h ▸ Finset.mem_univ _
    simpa using hz
  simp [boundaryCovector, emptyState, coordinate_basisState, hne]

@[simp] theorem overlap_full : boundaryCovector fullState = 1 := by
  have hne : Finset.univ ≠ (∅ : Finset (Fin 5)) := by
    intro h
    have hz : (0 : Fin 5) ∈ (∅ : Finset (Fin 5)) := h ▸ Finset.mem_univ _
    simpa using hz
  simp [boundaryCovector, fullState, coordinate_basisState, hne]

/-- Projection onto the one-mode basis line. -/
def singletonProjection : SpinorEnd :=
  (coordinate {0}).smulRight (basisState {0})

/-- Rank-one transition from the empty state to the full state. -/
def emptyToFull : SpinorEnd :=
  (coordinate ∅).smulRight fullState

@[simp] theorem singletonProjection_empty : singletonProjection emptyState = 0 := by
  simp [singletonProjection, emptyState, basisState, coordinate_basisState]

@[simp] theorem emptyToFull_empty : emptyToFull emptyState = fullState := by
  simp [emptyToFull, emptyState, basisState, coordinate_basisState]

theorem singletonProjection_idempotent :
    singletonProjection * singletonProjection = singletonProjection := by
  ext x
  simp [singletonProjection, coordinate_basisState,
    map_smul, smul_eq_mul, mul_assoc]

theorem emptyToFull_square_zero : emptyToFull * emptyToFull = 0 := by
  ext x
  have hne : Finset.univ ≠ (∅ : Finset (Fin 5)) := by
    intro h
    have hz : (0 : Fin 5) ∈ (∅ : Finset (Fin 5)) := h ▸ Finset.mem_univ _
    simpa using hz
  simp [emptyToFull, coordinate_basisState,
    map_smul, smul_eq_mul, mul_assoc, hne]

/-- The regular quotient, evaluated without imposing a positive-state axiom. -/
def boundaryReadout (A : SpinorEnd) : ℝ :=
  boundaryCovector (A emptyState) / boundaryCovector emptyState

@[simp] theorem boundaryReadout_zero : boundaryReadout 0 = 0 := by
  simp [boundaryReadout]

@[simp] theorem boundaryReadout_one : boundaryReadout 1 = 1 := by
  simp [boundaryReadout]

@[simp] theorem boundaryReadout_singleton : boundaryReadout singletonProjection = 0 := by
  simp [boundaryReadout]

@[simp] theorem boundaryReadout_transition : boundaryReadout emptyToFull = 1 := by
  simp [boundaryReadout]

/-- This static separation is not an algebra character or a probability state. -/
theorem boundaryReadout_not_multiplicative :
    boundaryReadout (emptyToFull * emptyToFull) ≠
      boundaryReadout emptyToFull * boundaryReadout emptyToFull := by
  rw [emptyToFull_square_zero, boundaryReadout_zero, boundaryReadout_transition]
  norm_num

/-- The regular dyad on the literal real exterior spinor. -/
def boundaryProjection : SpinorEnd := normalizedDyad emptyState boundaryCovector

theorem boundaryProjection_idempotent :
    boundaryProjection * boundaryProjection = boundaryProjection := by
  apply normalizedDyad_idempotent
  rw [overlap_empty]
  norm_num

theorem boundaryProjection_compression (A : SpinorEnd) :
    boundaryProjection * A * boundaryProjection = boundaryReadout A • boundaryProjection :=
  normalizedDyad_compression emptyState boundaryCovector A

/-- Spinor dimension and operator dimension are different ledger entries. -/
theorem spinor_operator_dimension :
    Module.finrank ℝ Spinor = 32 ∧ Module.finrank ℝ SpinorEnd = 1024 := by
  letI : FiniteDimensional ℝ Spinor := spinor_finiteDimensional
  constructor
  · exact spinor_finrank
  · change Module.finrank ℝ (Spinor →ₗ[ℝ] Spinor) = 1024
    rw [Module.finrank_linearMap, spinor_finrank]

end InfoGeometry.Clifford.ExteriorBasisBoundaryWitness

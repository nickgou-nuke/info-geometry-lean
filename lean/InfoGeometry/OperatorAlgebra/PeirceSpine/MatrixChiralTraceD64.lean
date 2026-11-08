/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixPeirceOperatorGeometryD62
import InfoGeometry.OperatorAlgebra.MatrixTraceGeometry
import InfoGeometry.Meta.ArchetypePipeline

/-!
# D₆₄: Matrix realization of the cyclic chiral-trace identity

This module specializes the Peirce cyclic-trace theorem to the native matrix
trace. The matrix carrier and star projection are arbitrary; no diagonal form
or commutativity assumption is introduced.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open Matrix
open InfoGeometry.Core.IdempotentCartan
open InfoGeometry.MetaCompiler

/-! ## The D₆₄ causal archetypes -/

inductive MatrixD64Stage where
  | peirceDiracIdentity
  | cyclicTraceIdentity
  | matrixTraceSpecialization
  deriving DecidableEq, Repr

def MatrixD64Stage.rank : MatrixD64Stage → ℕ
  | .peirceDiracIdentity => 0
  | .cyclicTraceIdentity => 1
  | .matrixTraceSpecialization => 2

def MatrixD64Stage.edge : MatrixD64Stage → MatrixD64Stage → Prop
  | .peirceDiracIdentity, .cyclicTraceIdentity => True
  | .cyclicTraceIdentity, .matrixTraceSpecialization => True
  | _, _ => False

def MatrixD64Stage.causalLE : MatrixD64Stage → MatrixD64Stage → Prop
  | .peirceDiracIdentity, _ => True
  | .cyclicTraceIdentity, .cyclicTraceIdentity => True
  | .cyclicTraceIdentity, .matrixTraceSpecialization => True
  | .matrixTraceSpecialization, .matrixTraceSpecialization => True
  | _, _ => False

theorem MatrixD64Stage.causalLE_refl (a : MatrixD64Stage) : a.causalLE a := by
  cases a <;> simp [causalLE]

theorem MatrixD64Stage.causalLE_trans {a b c : MatrixD64Stage}
    (hab : a.causalLE b) (hbc : b.causalLE c) : a.causalLE c := by
  cases a <;> cases b <;> cases c <;> simp_all [causalLE]

theorem MatrixD64Stage.causalLE_antisymm {a b : MatrixD64Stage}
    (hab : a.causalLE b) (hba : b.causalLE a) : a = b := by
  cases a <;> cases b <;> simp_all [causalLE]

theorem MatrixD64Stage.edge_causal {a b : MatrixD64Stage} (h : a.edge b) :
    a.causalLE b := by
  cases a <;> cases b <;> simp_all [edge, causalLE]

theorem MatrixD64Stage.edge_rank_strict {a b : MatrixD64Stage}
    (h : a.edge b) : a.rank < b.rank := by
  cases a <;> cases b <;> simp_all [edge, rank]

/-! ## Matrix trace specialization -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The arbitrary cyclic trace identity specializes to the ordinary matrix
trace for every star projection and every pair of matrix amplitudes. -/
theorem d64_matrix_chiral_mass_square_trace {p A C : Matrix n n ℂ}
    (hp : IsStarProjection p) :
    Matrix.trace (invS p * (peirceMassDirac p A C * peirceMassDirac p A C)) =
      Matrix.trace p - Matrix.trace (1 - p) := by
  have hP : p * p = p := hp.isIdempotentElem.eq
  exact peirce_cyclic_trace_mass_square hP Matrix.trace
    (fun X Y => Matrix.trace_add X Y)
    (fun X Y => Matrix.trace_sub X Y)
    (fun X Y => Matrix.trace_mul_comm X Y) A C

/-- The specialized formula makes explicit that changing either matrix
amplitude does not change the chiral mass-square trace. -/
theorem d64_matrix_chiral_trace_independent_of_amplitudes
    {p A C A' C' : Matrix n n ℂ} (hp : IsStarProjection p) :
    Matrix.trace (invS p * (peirceMassDirac p A C * peirceMassDirac p A C)) =
      Matrix.trace (invS p *
        (peirceMassDirac p A' C' * peirceMassDirac p A' C')) := by
  rw [d64_matrix_chiral_mass_square_trace hp,
    d64_matrix_chiral_mass_square_trace hp]

/-- Input for the matrix specialization of the chiral mass-square trace. -/
structure D64MatrixTraceInput (n : Type*) [Fintype n] [DecidableEq n] where
  projection : Matrix n n ℂ
  forwardAmplitude : Matrix n n ℂ
  backwardAmplitude : Matrix n n ℂ
  alternateForwardAmplitude : Matrix n n ℂ
  alternateBackwardAmplitude : Matrix n n ℂ
  projectionStar : IsStarProjection projection

/-- The generic cyclic-trace identity specializes to the native matrix trace
for every finite matrix size, arbitrary star projection, and both amplitudes. -/
def d64MatrixChiralTraceArchetype :
    TypedArchetype (D64MatrixTraceInput n) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.d64MatrixChiralTraceArchetype
  phase := 64
  claim := fun input =>
    Matrix.trace (invS input.projection *
      (peirceMassDirac input.projection input.forwardAmplitude
        input.backwardAmplitude *
       peirceMassDirac input.projection input.forwardAmplitude
        input.backwardAmplitude)) =
      Matrix.trace input.projection - Matrix.trace (1 - input.projection) ∧
    Matrix.trace (invS input.projection *
      (peirceMassDirac input.projection input.forwardAmplitude
        input.backwardAmplitude *
       peirceMassDirac input.projection input.forwardAmplitude
        input.backwardAmplitude)) =
      Matrix.trace (invS input.projection *
        (peirceMassDirac input.projection input.alternateForwardAmplitude
          input.alternateBackwardAmplitude *
         peirceMassDirac input.projection input.alternateForwardAmplitude
          input.alternateBackwardAmplitude))
  evidence := fun input =>
    ⟨d64_matrix_chiral_mass_square_trace input.projectionStar,
      d64_matrix_chiral_trace_independent_of_amplitudes
        input.projectionStar⟩

#register_archetype d64MatrixChiralTraceArchetype
#audit_archetype d64MatrixChiralTraceArchetype

end InfoGeometry.OperatorAlgebra.PeirceSpine

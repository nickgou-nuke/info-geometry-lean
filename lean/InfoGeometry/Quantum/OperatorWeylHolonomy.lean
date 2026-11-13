/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LatticeGauge.FinitePlaquette
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.PEquiv

/-!
# Operator-valued weighted permutation holonomy

The plaquette has a vertex loop labelled `V i` and an edge from `i` to `σ i`
labelled `U i`. Its ordered holonomy is `V i * U i * (V (σ i))⁻¹ * (U i)⁻¹`.
Gauge covariance is transported from the existing group-valued plaquette owner.

For units in an arbitrary coefficient ring, the diagonal vertex operator and
the weighted permutation shift are genuine units in the full matrix ring.
Their group commutator is exactly the diagonal operator-valued holonomy. No
coefficient commutativity, centrality of the holonomy, or scalar phase is used.
The index is finite only for the matrix realization; the group-level lattice
and its gauge covariance do not require finiteness.
-/

namespace InfoGeometry.Quantum.OperatorWeylHolonomy

open InfoGeometry.LatticeGauge

section GroupHolonomy

variable {ι G : Type*} [Group G]

/-- The two edge kinds are vertex loops and permutation edges, respectively.
Each face follows a loop, an edge, the reversed target loop, and the reversed edge. -/
def permutationLattice (σ : Equiv.Perm ι) : PlaquetteLattice ι (ι ⊕ ι) ι where
  source := Sum.elim id id
  target := Sum.elim id σ
  bottom := Sum.inl
  right := Sum.inr
  top i := Sum.inl (σ i)
  left := Sum.inr
  bottom_right _ := rfl
  right_top _ := rfl
  top_left _ := rfl
  left_bottom _ := rfl

/-- Operator units on the two kinds of directed edge. -/
def links (U V : ι → G) : Configuration (ι ⊕ ι) G := Sum.elim V U

/-- The braiding defect is an actual plaquette holonomy in the existing owner. -/
def holonomy (σ : Equiv.Perm ι) (U V : ι → G) : ι → G :=
  plaquetteHolonomy (permutationLattice σ) (links U V)

theorem holonomy_apply (σ : Equiv.Perm ι) (U V : ι → G) (i : ι) :
    holonomy σ U V i = V i * U i * (V (σ i))⁻¹ * (U i)⁻¹ := rfl

/-- The gauge action at the two endpoints of an edge. -/
def gaugeEdges (σ : Equiv.Perm ι) (g U : ι → G) : ι → G :=
  fun i => g i * U i * (g (σ i))⁻¹

/-- The vertex loop is transformed by conjugation at that vertex. -/
def gaugeVertices (g V : ι → G) : ι → G :=
  fun i => g i * V i * (g i)⁻¹

theorem links_gauge (σ : Equiv.Perm ι) (g U V : ι → G) :
    links (gaugeEdges σ g U) (gaugeVertices g V) =
      gaugeTransform (permutationLattice σ) g (links U V) := by
  funext e
  cases e <;> rfl

/-- Noncentral plaquette covariance, inherited through the explicit lattice map. -/
theorem holonomy_gauge_covariant (σ : Equiv.Perm ι) (g U V : ι → G) (i : ι) :
    holonomy σ (gaugeEdges σ g U) (gaugeVertices g V) i =
      g i * holonomy σ U V i * (g i)⁻¹ := by
  change plaquetteHolonomy (permutationLattice σ)
    (links (gaugeEdges σ g U) (gaugeVertices g V)) i = _
  rw [links_gauge]
  exact plaquetteHolonomy_gauge_covariant (permutationLattice σ) g (links U V) i

/-- The ordered defect compensates the failure to commute across an edge. -/
theorem holonomy_reorder (σ : Equiv.Perm ι) (U V : ι → G) (i : ι) :
    holonomy σ U V i * U i * V (σ i) = V i * U i := by
  rw [holonomy_apply]
  group

theorem holonomy_eq_one_iff_edge_commutes (σ : Equiv.Perm ι)
    (U V : ι → G) (i : ι) :
    holonomy σ U V i = 1 ↔ V i * U i = U i * V (σ i) := by
  constructor
  · intro h
    simpa [h] using (holonomy_reorder σ U V i).symm
  · intro h
    rw [holonomy_apply, h]
    group

end GroupHolonomy

section Matrices

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A]

/-- A diagonal matrix with operator entries; its entries need not be central. -/
def vertexMatrix (V : ι → Aˣ) : Matrix ι ι A :=
  Matrix.diagonal fun i => (V i : A)

/-- The row convention is `X i j = U i` when `j = σ i`. -/
def weightedShift (σ : Equiv.Perm ι) (U : ι → Aˣ) : Matrix ι ι A :=
  Matrix.diagonal (fun i => (U i : A)) * σ.toPEquiv.toMatrix

@[simp] theorem weightedShift_apply (σ : Equiv.Perm ι) (U : ι → Aˣ) (i j : ι) :
    weightedShift σ U i j = if σ i = j then (U i : A) else 0 := by
  unfold weightedShift
  rw [Matrix.diagonal_mul]
  change (U i : A) * (if j ∈ some (σ i) then 1 else 0) = _
  by_cases h : σ i = j
  · subst j
    simp
  · simp [h]

/-- Left multiplication by the shift samples one row and preserves coefficient order. -/
theorem weightedShift_mul_apply (σ : Equiv.Perm ι) (U : ι → Aˣ)
    (M : Matrix ι ι A) (i j : ι) :
    (weightedShift σ U * M) i j = (U i : A) * M (σ i) j := by
  simp only [weightedShift, Matrix.mul_assoc, Matrix.diagonal_mul,
    PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply, id_eq]

omit [Fintype ι] in
@[simp] theorem vertexMatrix_one : vertexMatrix (1 : ι → Aˣ) = 1 := by
  simp [vertexMatrix]

omit [Fintype ι] in
theorem vertexMatrix_injective :
    Function.Injective (vertexMatrix (ι := ι) (A := A)) := by
  intro V W h
  funext i
  apply Units.ext
  simpa [vertexMatrix] using congrArg (fun M : Matrix ι ι A => M i i) h

/-- The inverse of a vertex operator is the diagonal of the inverse units. -/
def vertexUnit (V : ι → Aˣ) : (Matrix ι ι A)ˣ where
  val := vertexMatrix V
  inv := vertexMatrix (fun i => (V i)⁻¹)
  val_inv := by simp [vertexMatrix, Matrix.diagonal_mul_diagonal]
  inv_val := by simp [vertexMatrix, Matrix.diagonal_mul_diagonal]

@[simp] theorem vertexUnit_one : vertexUnit (1 : ι → Aˣ) = 1 := by
  apply Units.ext
  exact vertexMatrix_one

theorem vertexUnit_injective :
    Function.Injective (vertexUnit (ι := ι) (A := A)) := by
  intro V W h
  apply vertexMatrix_injective
  exact congrArg (fun z : (Matrix ι ι A)ˣ => (z : Matrix ι ι A)) h

/-- The inverse shift uses the inverse permutation and reverses the edge unit. -/
def shiftUnit (σ : Equiv.Perm ι) (U : ι → Aˣ) : (Matrix ι ι A)ˣ where
  val := weightedShift σ U
  inv := weightedShift σ.symm (fun i => (U (σ.symm i))⁻¹)
  val_inv := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [weightedShift_mul_apply, weightedShift_apply]
    · simp [weightedShift_mul_apply, weightedShift_apply, hij]
  inv_val := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [weightedShift_mul_apply, weightedShift_apply]
    · simp [weightedShift_mul_apply, weightedShift_apply, hij]

/-- The Weyl relation with a noncentral, operator-valued braiding factor. -/
theorem braiding (σ : Equiv.Perm ι) (U V : ι → Aˣ) :
    vertexMatrix V * weightedShift σ U =
      vertexMatrix (holonomy σ U V) * weightedShift σ U * vertexMatrix V := by
  ext i j
  simp only [vertexMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul, weightedShift_apply]
  by_cases h : σ i = j
  · subst j
    simp only
    exact congrArg (fun z : Aˣ => (z : A)) (holonomy_reorder σ U V i).symm
  · simp only [ite_eq_right h, mul_zero, zero_mul]

theorem braiding_units (σ : Equiv.Perm ι) (U V : ι → Aˣ) :
    vertexUnit V * shiftUnit σ U =
      vertexUnit (holonomy σ U V) * shiftUnit σ U * vertexUnit V := by
  apply Units.ext
  change vertexMatrix V * weightedShift σ U =
    vertexMatrix (holonomy σ U V) * weightedShift σ U * vertexMatrix V
  exact braiding σ U V

/-- The operator-valued holonomy is exactly the group commutator of the invertible matrices. -/
theorem holonomyUnit_eq_group_commutator (σ : Equiv.Perm ι) (U V : ι → Aˣ) :
    vertexUnit (holonomy σ U V) =
      vertexUnit V * shiftUnit σ U * (vertexUnit V)⁻¹ * (shiftUnit σ U)⁻¹ := by
  calc
    vertexUnit (holonomy σ U V) =
        (vertexUnit (holonomy σ U V) * shiftUnit σ U * vertexUnit V) *
          (vertexUnit V)⁻¹ * (shiftUnit σ U)⁻¹ := by group
    _ = _ := by rw [← braiding_units σ U V]

theorem vertexMatrix_gauge_conjugation (g V : ι → Aˣ) :
    vertexMatrix (gaugeVertices g V) =
      vertexMatrix g * vertexMatrix V * vertexMatrix (fun i => (g i)⁻¹) := by
  simp [vertexMatrix, gaugeVertices, Matrix.diagonal_mul_diagonal]

/-- The two-endpoint edge gauge action is actual diagonal matrix conjugation. -/
theorem weightedShift_gauge_conjugation (σ : Equiv.Perm ι) (g U : ι → Aˣ) :
    weightedShift σ (gaugeEdges σ g U) =
      vertexMatrix g * weightedShift σ U * vertexMatrix (fun i => (g i)⁻¹) := by
  ext i j
  simp only [vertexMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul, weightedShift_apply]
  by_cases h : σ i = j
  · subst j
    simp [gaugeEdges]
  · simp [h]

theorem vertexUnit_gauge_conjugation (g V : ι → Aˣ) :
    vertexUnit (gaugeVertices g V) = vertexUnit g * vertexUnit V * (vertexUnit g)⁻¹ := by
  apply Units.ext
  change vertexMatrix (gaugeVertices g V) =
    vertexMatrix g * vertexMatrix V * vertexMatrix (fun i => (g i)⁻¹)
  exact vertexMatrix_gauge_conjugation g V

theorem shiftUnit_gauge_conjugation (σ : Equiv.Perm ι) (g U : ι → Aˣ) :
    shiftUnit σ (gaugeEdges σ g U) = vertexUnit g * shiftUnit σ U * (vertexUnit g)⁻¹ := by
  apply Units.ext
  change weightedShift σ (gaugeEdges σ g U) =
    vertexMatrix g * weightedShift σ U * vertexMatrix (fun i => (g i)⁻¹)
  exact weightedShift_gauge_conjugation σ g U

theorem holonomyUnit_gauge_conjugation (σ : Equiv.Perm ι) (g U V : ι → Aˣ) :
    vertexUnit (holonomy σ (gaugeEdges σ g U) (gaugeVertices g V)) =
      vertexUnit g * vertexUnit (holonomy σ U V) * (vertexUnit g)⁻¹ := by
  have h : holonomy σ (gaugeEdges σ g U) (gaugeVertices g V) =
      gaugeVertices g (holonomy σ U V) :=
    funext fun i => holonomy_gauge_covariant σ g U V i
  rw [h, vertexUnit_gauge_conjugation]

/-- Flatness is equivalent to commutation of the two invertible matrix operators. -/
theorem holonomy_eq_one_iff_matrix_commute (σ : Equiv.Perm ι) (U V : ι → Aˣ) :
    holonomy σ U V = 1 ↔ Commute (vertexUnit V) (shiftUnit σ U) := by
  constructor
  · intro h
    change vertexUnit V * shiftUnit σ U = shiftUnit σ U * vertexUnit V
    simpa [h] using braiding_units σ U V
  · intro h
    change vertexUnit V * shiftUnit σ U = shiftUnit σ U * vertexUnit V at h
    apply vertexUnit_injective
    rw [vertexUnit_one, holonomyUnit_eq_group_commutator, h]
    group

end Matrices

end InfoGeometry.Quantum.OperatorWeylHolonomy

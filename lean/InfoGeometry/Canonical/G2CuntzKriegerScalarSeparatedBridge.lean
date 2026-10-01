import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.RootSystem.G2CoxeterPlaneProjection

/-!
# Scalar-separated G2 Cuntz--Krieger bridge

This module repairs the scalar/operator conflation in the generic
Cuntz--Krieger prototype.

Adjacency coefficients live in a commutative scalar ring R.
Cuntz--Krieger generators live in a possibly noncommutative R-algebra A.
The adjacency coefficients act by scalar multiplication on range projections.

The concrete G2 graph is represented by a proof-carrying 12-vertex datum:
* Boolean adjacency;
* exactly three outgoing neighbors at every vertex;
* an involutive Garside permutation;
* invariance of adjacency under that permutation.

From these hypotheses we prove the constant-vector Perron readout with
eigenvalue 3.  No concrete 12x12 adjacency table is invented here, and no
Smith normal form / K-theory group is asserted until such a table is supplied.
-/

noncomputable section

namespace InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge

/-! ## 1. Scalar-separated Cuntz--Krieger generators -/

structure ScalarSeparatedCK
    (n : ℕ) (R A : Type*)
    [CommRing R] [Ring A] [Algebra R A] where
  adjacency : Fin n → Fin n → R
  S : Fin n → A
  Sstar : Fin n → A
  ck_relation :
    ∀ i : Fin n,
      Sstar i * S i =
        ∑ j : Fin n, adjacency i j • (S j * Sstar j)
  source_orthogonal :
    ∀ i j : Fin n, i ≠ j → Sstar i * S j = 0
  partial_isometry :
    ∀ i : Fin n, S i * Sstar i * S i = S i

namespace ScalarSeparatedCK

variable
  {n : ℕ} {R A : Type*}
  [CommRing R] [Ring A] [Algebra R A]
  (C : ScalarSeparatedCK n R A)

def rangeProjection (i : Fin n) : A :=
  C.S i * C.Sstar i

theorem rangeProjection_idempotent (i : Fin n) :
    C.rangeProjection i * C.rangeProjection i =
      C.rangeProjection i := by
  unfold rangeProjection
  calc
    (C.S i * C.Sstar i) * (C.S i * C.Sstar i) =
        (C.S i * C.Sstar i * C.S i) * C.Sstar i := by
          simp [mul_assoc]
    _ = C.S i * C.Sstar i := by
      rw [C.partial_isometry i]

theorem rangeProjection_orthogonal
    {i j : Fin n} (hij : i ≠ j) :
    C.rangeProjection i * C.rangeProjection j = 0 := by
  unfold rangeProjection
  calc
    (C.S i * C.Sstar i) * (C.S j * C.Sstar j) =
        C.S i * (C.Sstar i * C.S j) * C.Sstar j := by
          simp [mul_assoc]
    _ = 0 := by
      rw [C.source_orthogonal i j hij]
      simp

theorem ck_relation_rangeProjection (i : Fin n) :
    C.Sstar i * C.S i =
      ∑ j : Fin n, C.adjacency i j • C.rangeProjection j := by
  simpa [rangeProjection] using C.ck_relation i

theorem zero_transition_annihilation
    (i j : Fin n) (hzero : C.adjacency i j = 0) :
    C.adjacency i j • C.rangeProjection j = 0 := by
  rw [hzero]
  simp

end ScalarSeparatedCK

/-! ## 2. Proof-carrying finite G2 transition datum -/

abbrev G2Vertex := Fin 12

/-- A finite directed G2 transition graph with the structural facts needed
by the CK/KMS lane. -/
structure G2TransitionDatum where
  edge : G2Vertex → G2Vertex → Bool
  /-- Every root vertex has exactly three outgoing transitions. -/
  rowDegreeThree :
    ∀ i : G2Vertex,
      ((Finset.univ.filter fun j => edge i j).card) = 3
  /-- Garside/root antipodal permutation. -/
  theta : Equiv.Perm G2Vertex
  theta_involutive :
    Function.Involutive theta
  /-- Graph invariance under the Garside permutation. -/
  theta_invariant :
    ∀ i j : G2Vertex, edge (theta i) (theta j) = edge i j

namespace G2TransitionDatum

variable (G : G2TransitionDatum)

/-- Boolean adjacency lifted to an arbitrary commutative coefficient ring. -/
def adjacency {R : Type*} [CommRing R] :
    Matrix G2Vertex G2Vertex R :=
  fun i j => if G.edge i j then 1 else 0

@[simp] theorem adjacency_apply_true
    {R : Type*} [CommRing R]
    {i j : G2Vertex} (h : G.edge i j = true) :
    G.adjacency (R := R) i j = 1 := by
  simp [adjacency, h]

@[simp] theorem adjacency_apply_false
    {R : Type*} [CommRing R]
    {i j : G2Vertex} (h : G.edge i j = false) :
    G.adjacency (R := R) i j = 0 := by
  simp [adjacency, h]

/-- Garside invariance survives scalar lifting. -/
theorem adjacency_theta_invariant
    {R : Type*} [CommRing R]
    (i j : G2Vertex) :
    G.adjacency (R := R) (G.theta i) (G.theta j) =
      G.adjacency (R := R) i j := by
  simp [adjacency, G.theta_invariant i j]

/-- The Garside permutation squares to the identity. -/
theorem theta_sq (i : G2Vertex) :
    G.theta (G.theta i) = i :=
  G.theta_involutive i

/-- Scalar row sum is exactly 3. -/
theorem adjacency_row_sum_three
    (i : G2Vertex) :
    ∑ j : G2Vertex, G.adjacency (R := ℤ) i j = 3 := by
  classical
  unfold adjacency
  rw [← Finset.sum_filter]
  have hcard := G.rowDegreeThree i
  calc
    ∑ j ∈ Finset.univ.filter (fun j => G.edge i j), (1 : ℤ) =
        ((Finset.univ.filter fun j => G.edge i j).card : ℤ) := by simp
    _ = 3 := by exact_mod_cast hcard

/-- The all-ones vector is a right eigenvector of the integer adjacency
matrix with eigenvalue 3. -/
theorem adjacency_mulVec_one_eq_three
    (i : G2Vertex) :
    (G.adjacency (R := ℤ)).mulVec (fun _ => (1 : ℤ)) i = 3 := by
  simp [Matrix.mulVec, dotProduct, adjacency_row_sum_three G i]

/-- Pointwise Perron-style readout A * 1 = 3 * 1. -/
theorem adjacency_constant_eigenvector :
    (G.adjacency (R := ℤ)).mulVec (fun _ => (1 : ℤ)) =
      fun _ => (3 : ℤ) := by
  funext i
  exact G.adjacency_mulVec_one_eq_three i

/-! ## 3. Scalar-separated G2 CK realization socket -/

/-- A noncommutative CK realization of a supplied G2 transition datum. -/
structure Realization
    (R A : Type*) [CommRing R] [Ring A] [Algebra R A] where
  ck : ScalarSeparatedCK 12 R A
  adjacency_matches :
    ∀ i j,
      ck.adjacency i j =
        if G.edge i j then 1 else 0

namespace Realization

variable
  {R A : Type*}
  [CommRing R] [Ring A] [Algebra R A]
  (X : G.Realization R A)

theorem ck_transition_formula (i : G2Vertex) :
    X.ck.Sstar i * X.ck.S i =
      ∑ j : G2Vertex,
        (if G.edge i j then (1 : R) else 0) •
          X.ck.rangeProjection j := by
  rw [X.ck.ck_relation_rangeProjection]
  apply Finset.sum_congr rfl
  intro j _
  rw [X.adjacency_matches i j]

theorem forbidden_edge_annihilates
    (i j : G2Vertex) (h : G.edge i j = false) :
    X.ck.adjacency i j • X.ck.rangeProjection j = 0 := by
  apply X.ck.zero_transition_annihilation
  rw [X.adjacency_matches i j, h]
  simp

end Realization

end G2TransitionDatum

end InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge

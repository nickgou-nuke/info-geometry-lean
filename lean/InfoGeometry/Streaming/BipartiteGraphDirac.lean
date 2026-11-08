import InfoGeometry.Canonical.DiscreteDiracHodgeChiral
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# A concrete finite graph/cochain realization of the existing Dirac-Hodge algebra

The differential acts from vertices to edges. Its codifferential uses the
transpose incidence matrix for the displayed positive coordinate pairing.
Both nilpotences are derived from the bipartite construction. Boundary
conditions and continuum operator domains are not silently inferred.
-/

noncomputable section
namespace InfoGeometry.Streaming.BipartiteGraphDirac

open scoped BigOperators
open InfoGeometry.Canonical.DiscreteDiracHodgeChiral
variable {v e : Type*} [Fintype v] [Fintype e] [DecidableEq v] [DecidableEq e]

abbrev Cochain (v e : Type*) := (v → ℝ) × (e → ℝ)

/-- Incidence from chosen source and target functions; loops give zero rows. -/
def incidence (source target : e → v) : Matrix e v ℝ :=
  fun a i => (if target a = i then 1 else 0) - (if source a = i then 1 else 0)

/-- The graph differential on total zero- and one-cochains. -/
def differential (B : Matrix e v ℝ) : Module.End ℝ (Cochain v e) where
  toFun x := (0, B.mulVec x.1)
  map_add' x y := by
    apply Prod.ext
    · simp
    · funext a
      change (∑ i, B a i * (x.1 i + y.1 i)) =
        (∑ i, B a i * x.1 i) + ∑ i, B a i * y.1 i
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
  map_smul' r x := by
    apply Prod.ext
    · simp
    · funext a
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

/-- The transpose is the adjoint for the positive coordinate pairing used here. -/
def codifferential (B : Matrix e v ℝ) : Module.End ℝ (Cochain v e) where
  toFun x := (B.transpose.mulVec x.2, 0)
  map_add' x y := by
    apply Prod.ext
    · funext a
      change (∑ i, B.transpose a i * (x.2 i + y.2 i)) =
        (∑ i, B.transpose a i * x.2 i) + ∑ i, B.transpose a i * y.2 i
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · simp
  map_smul' r x := by
    apply Prod.ext
    · funext a
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
    · simp

/-- Positive coordinate pairing on the total cochain carrier. -/
def cochainPair (x y : Cochain v e) : ℝ :=
  (∑ i, x.1 i * y.1 i) + ∑ a, x.2 a * y.2 a

/-- The codifferential really is the adjoint for the displayed pairing. -/
theorem differential_adjoint (B : Matrix e v ℝ) (x y : Cochain v e) :
    cochainPair (differential B x) y = cochainPair x (codifferential B y) := by
  classical
  dsimp [cochainPair, differential, codifferential]
  simp only [zero_mul, mul_zero, Matrix.mulVec, dotProduct]
  simp only [Finset.sum_const_zero, Matrix.transpose_apply]
  rw [zero_add, add_zero]
  change (∑ a, (∑ i, B a i * x.1 i) * y.2 a) =
    ∑ i, x.1 i * (∑ a, B a i * y.2 a)
  calc
    (∑ a, (∑ i, B a i * x.1 i) * y.2 a) =
        ∑ a, ∑ i, (B a i * x.1 i) * y.2 a := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_mul]
    _ = ∑ i, ∑ a, (B a i * x.1 i) * y.2 a := Finset.sum_comm
    _ = ∑ i, x.1 i * (∑ a, B a i * y.2 a) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

/-- Actual even/odd cochain grading. -/
def grading : Module.End ℝ (Cochain v e) where
  toFun x := (x.1, -x.2)
  map_add' x y := by ext <;> simp [neg_add, add_comm]
  map_smul' r x := by simp

def graphDirac (B : Matrix e v ℝ) : Module.End ℝ (Cochain v e) :=
  diracHodge (differential B) (codifferential B)

theorem differential_sq (B : Matrix e v ℝ) : differential B * differential B = 0 := by
  apply LinearMap.ext
  intro x
  simp [differential, Module.End.mul_apply]

theorem codifferential_sq (B : Matrix e v ℝ) : codifferential B * codifferential B = 0 := by
  apply LinearMap.ext
  intro x
  simp [codifferential, Module.End.mul_apply]

/-- This discharges the nilpotence inputs of the repository's generic Hodge theorem. -/
theorem graphDirac_sq (B : Matrix e v ℝ) :
    graphDirac B * graphDirac B = hodgeLaplacian (differential B) (codifferential B) :=
  diracHodge_sq_eq_hodgeLaplacian _ _ (differential_sq B) (codifferential_sq B)

theorem graphDirac_apply (B : Matrix e v ℝ) (x : Cochain v e) :
    graphDirac B x = (B.transpose.mulVec x.2, B.mulVec x.1) := by
  simp [graphDirac, diracHodge, differential, codifferential]

/-- The coordinate pairing is symmetric. -/
theorem cochainPair_symm (x y : Cochain v e) :
    cochainPair x y = cochainPair y x := by
  simp only [cochainPair]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

/-- Pairing a matrix-vector product with a vector equals pairing with the
transpose matrix-vector product. -/
theorem transpose_mulVec_pairing (B : Matrix e v ℝ) (x : v → ℝ) (y : e → ℝ) :
    (∑ i, (B.transpose.mulVec y) i * x i) =
      ∑ a, y a * (B.mulVec x) a := by
  classical
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  calc
    (∑ i, (∑ a, B a i * y a) * x i) =
        ∑ i, ∑ a, (B a i * y a) * x i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
    _ = ∑ a, ∑ i, (B a i * y a) * x i := Finset.sum_comm
    _ = ∑ a, y a * (∑ i, B a i * x i) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring

/-- The graph Dirac operator is self-adjoint for the positive coordinate
pairing: the two off-diagonal blocks are transposes of one another. -/
theorem graphDirac_adjoint (B : Matrix e v ℝ) (x y : Cochain v e) :
    cochainPair (graphDirac B x) y = cochainPair x (graphDirac B y) := by
  rw [graphDirac_apply, graphDirac_apply]
  simp only [cochainPair]
  have h₁ := transpose_mulVec_pairing B y.1 x.2
  have h₂ := transpose_mulVec_pairing B x.1 y.2
  have h₂' :
      (∑ a, (B.mulVec x.1) a * y.2 a) =
        ∑ i, x.1 i * (B.transpose.mulVec y.2) i := by
    calc
      (∑ a, (B.mulVec x.1) a * y.2 a) =
          ∑ a, y.2 a * (B.mulVec x.1) a := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
      _ = ∑ i, (B.transpose.mulVec y.2) i * x.1 i := h₂.symm
      _ = ∑ i, x.1 i * (B.transpose.mulVec y.2) i := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
  calc
    (∑ i, (B.transpose.mulVec x.2) i * y.1 i) +
        ∑ a, (B.mulVec x.1) a * y.2 a =
      (∑ a, x.2 a * (B.mulVec y.1) a) +
        ∑ a, (B.mulVec x.1) a * y.2 a := by rw [h₁]
    _ = (∑ i, x.1 i * (B.transpose.mulVec y.2) i) +
        ∑ a, x.2 a * (B.mulVec y.1) a := by
      rw [h₂']
      rw [add_comm]

theorem grading_sq : (grading (v := v) (e := e)) * grading = 1 := by
  apply LinearMap.ext
  intro x
  simp [grading, Module.End.mul_apply]

theorem graphDirac_odd (B : Matrix e v ℝ) :
    graphDirac B * grading = -(grading * graphDirac B) := by
  apply LinearMap.ext
  intro x
  ext <;> simp [graphDirac_apply, grading, Module.End.mul_apply,
    Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]

/-- The grading is self-adjoint for the positive coordinate pairing. -/
theorem grading_adjoint (x y : Cochain v e) :
    cochainPair (grading x) y = cochainPair x (grading y) := by
  dsimp [grading, cochainPair]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The indefinite pairing induced by the bipartite grading.

On vertex coordinates it is positive and on edge coordinates negative. This
definition records the grading signature; it does not identify an arbitrary
plabic graph with a particular Kasteleyn orientation. -/
def kreinPair (x y : Cochain v e) : ℝ :=
  cochainPair x (grading y)

/-- The graph Dirac operator is Krein-skew-adjoint: it is self-adjoint for the
positive coordinate pairing and odd with respect to the fundamental symmetry. -/
theorem graphDirac_krein_skew_adjoint (B : Matrix e v ℝ) (x y : Cochain v e) :
    kreinPair (graphDirac B x) y = -kreinPair x (graphDirac B y) := by
  rw [kreinPair, graphDirac_adjoint B x (grading y)]
  have hodd := congrFun (congrArg DFunLike.coe (graphDirac_odd B)) y
  change graphDirac B (grading y) = -grading (graphDirac B y) at hodd
  rw [hodd]
  simp [kreinPair, cochainPair, Finset.sum_neg_distrib]
  abel

/-- The two Laplacian blocks are actual compositions B transpose B and B B transpose. -/
theorem graphDirac_square_blocks (B : Matrix e v ℝ) (x : Cochain v e) :
    (graphDirac B * graphDirac B) x =
      (B.transpose.mulVec (B.mulVec x.1), B.mulVec (B.transpose.mulVec x.2)) := by
  simp only [Module.End.mul_apply, graphDirac_apply]

/-- Graph incidence annihilates constant vertex functions. -/
theorem incidence_constant (source target : e → v) (c : ℝ) :
    (incidence source target).mulVec (fun _ => c) = 0 := by
  funext a
  simp [incidence, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

/-- The positive graph energy is a sum of squares, unlike a neutral Krein form. -/
def graphEnergy (B : Matrix e v ℝ) (x : v → ℝ) : ℝ := ∑ a, (B.mulVec x a) ^ 2

theorem graphEnergy_nonneg (B : Matrix e v ℝ) (x : v → ℝ) : 0 ≤ graphEnergy B x :=
  Finset.sum_nonneg (fun a _ => sq_nonneg _)

/-- The quadratic form of B transpose B is exactly the graph energy. -/
theorem graphEnergy_eq_quadratic (B : Matrix e v ℝ) (x : v → ℝ) :
    graphEnergy B x = ∑ i, x i * (B.transpose.mulVec (B.mulVec x)) i := by
  simp only [graphEnergy, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  calc
    _ = ∑ a, ∑ i, x i * B a i * (∑ j, B a j * x j) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_mul]
      have hsum : (∑ i, x i * B a i) = ∑ i, B a i * x i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsum]
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

end InfoGeometry.Streaming.BipartiteGraphDirac

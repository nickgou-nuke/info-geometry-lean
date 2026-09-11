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

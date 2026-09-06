import Mathlib.LinearAlgebra.Matrix.ToLin
import DAG.MatrixRepresentation
import DAG.HodgeTheorems

/-!
# Native linear-map readout of the finite DAG Hodge operator

`DAG.MatrixRepresentation` owns the finite rational matrix formulas.  This
file transports those matrices, without changing their meaning, to native
Mathlib endomorphisms of the finite cell function space.  It deliberately
does not identify that carrier with a split-octonion carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.DAGNativeHodgeLinearMapBridge

open Matrix
open DAG
open DAG.MatrixRepresentation

variable {α : Type*} [BEq α] [Hashable α]

abbrev DAGCell (tc : DAG.TwoComplex α) :=
  Cell tc.base.toGraph.nodes.size tc.edges.size
    (tc.faces.size + tc.digons.size)

abbrev DAGCellSpace (tc : DAG.TwoComplex α) :=
  DAGCell tc → ℚ

def dagBoundaryOneMatrix (tc : DAG.TwoComplex α) :
    Matrix (Fin tc.base.toGraph.nodes.size) (Fin tc.edges.size) ℚ :=
  (DAG.boundary1Matrix tc)ᵀ

def dagBoundaryTwoMatrix (tc : DAG.TwoComplex α) :
    Matrix (Fin tc.edges.size)
      (Fin (tc.faces.size + tc.digons.size)) ℚ :=
  (DAG.boundary2Matrix tc)ᵀ

def dagDiracMatrix (tc : DAG.TwoComplex α) :
    Matrix (DAGCell tc) (DAGCell tc) ℚ :=
  diracOp (dagBoundaryOneMatrix tc) (dagBoundaryTwoMatrix tc)

def cellSumEquiv {n0 n1 n2 : ℕ} :
    (Fin n0 ⊕ (Fin n1 ⊕ Fin n2)) ≃ Cell n0 n1 n2 where
  toFun := fun s =>
    match s with
    | Sum.inl i => Cell.zero i
    | Sum.inr (Sum.inl i) => Cell.one i
    | Sum.inr (Sum.inr i) => Cell.two i
  invFun := fun c =>
    match c with
    | Cell.zero i => Sum.inl i
    | Cell.one i => Sum.inr (Sum.inl i)
    | Cell.two i => Sum.inr (Sum.inr i)
  left_inv := by
    intro s
    cases s with
    | inl i => rfl
    | inr s => cases s <;> rfl
  right_inv := by intro c; cases c <;> rfl

theorem sum_cell {n0 n1 n2 : ℕ} (f : Cell n0 n1 n2 → ℚ) :
    (∑ c, f c) =
      (∑ i : Fin n0, f (Cell.zero i)) +
        (∑ i : Fin n1, f (Cell.one i)) +
          ∑ i : Fin n2, f (Cell.two i) := by
  let e := cellSumEquiv (n0 := n0) (n1 := n1) (n2 := n2)
  have h := Fintype.sum_equiv e (fun s => f (e s)) f (fun _ => rfl)
  rw [← h, Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type]
  simp [e, cellSumEquiv]
  abel

def dagLaplacianMatrix {n0 n1 n2 : ℕ}
    (B1 : Matrix (Fin n0) (Fin n1) ℚ)
    (B2 : Matrix (Fin n1) (Fin n2) ℚ) :
    Matrix (Cell n0 n1 n2) (Cell n0 n1 n2) ℚ
  | Cell.zero i, Cell.zero j =>
      ∑ k : Fin n1, B1 i k * B1 j k
  | Cell.one i, Cell.one j =>
      (∑ k : Fin n0, B1 k i * B1 k j) +
        ∑ k : Fin n2, B2 i k * B2 j k
  | Cell.two i, Cell.two j =>
      ∑ k : Fin n1, B2 k i * B2 k j
  | _, _ => 0

theorem dagDiracMatrix_sq_eq_laplacianMatrix
    {n0 n1 n2 : ℕ}
    (B1 : Matrix (Fin n0) (Fin n1) ℚ)
    (B2 : Matrix (Fin n1) (Fin n2) ℚ)
    (hboundary : B1 * B2 = 0) :
    diracOp B1 B2 * diracOp B1 B2 = dagLaplacianMatrix B1 B2 := by
  have hboundary_apply (i : Fin n0) (j : Fin n2) :
      (∑ k : Fin n1, B1 i k * B2 k j) = 0 := by
    simpa [Matrix.mul_apply] using congrArg (fun M => M i j) hboundary
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.mul_apply, diracOp, dagLaplacianMatrix]
  all_goals rw [sum_cell]
  all_goals simp
  all_goals try { exact hboundary_apply _ _ }
  all_goals try { simpa [mul_comm] using hboundary_apply _ _ }

def dagChiralityMatrix (tc : DAG.TwoComplex α) :
    Matrix (DAGCell tc) (DAGCell tc) ℚ :=
  chiralGamma

def dagDirac (tc : DAG.TwoComplex α) :
    Module.End ℚ (DAGCellSpace tc) :=
  Matrix.toLin' (dagDiracMatrix tc)

def dagLaplacian (tc : DAG.TwoComplex α) :
    Module.End ℚ (DAGCellSpace tc) :=
  Matrix.toLin'
    (dagLaplacianMatrix (dagBoundaryOneMatrix tc) (dagBoundaryTwoMatrix tc))

theorem dagDirac_sq_eq_laplacian
    (tc : DAG.TwoComplex α)
    (hboundary : dagBoundaryOneMatrix tc * dagBoundaryTwoMatrix tc = 0) :
    dagDirac tc * dagDirac tc = dagLaplacian tc := by
  have h := congrArg
    (Matrix.toLin' :
      Matrix (DAGCell tc) (DAGCell tc) ℚ →
        Module.End ℚ (DAGCellSpace tc))
    (dagDiracMatrix_sq_eq_laplacianMatrix
      (dagBoundaryOneMatrix tc) (dagBoundaryTwoMatrix tc) hboundary)
  simpa [dagDirac, dagLaplacian, dagDiracMatrix, Matrix.toLin'_mul] using h

def dagChirality (tc : DAG.TwoComplex α) :
    Module.End ℚ (DAGCellSpace tc) :=
  Matrix.toLin' (dagChiralityMatrix tc)

@[simp] theorem dagDirac_apply
    (tc : DAG.TwoComplex α) (x : DAGCellSpace tc) :
    dagDirac tc x = (dagDiracMatrix tc).mulVec x := by
  rfl

@[simp] theorem dagChirality_apply
    (tc : DAG.TwoComplex α) (x : DAGCellSpace tc) :
    dagChirality tc x = (dagChiralityMatrix tc).mulVec x := by
  rfl

theorem dagChiral_anticommutation
    (tc : DAG.TwoComplex α) :
    dagChirality tc * dagDirac tc +
        dagDirac tc * dagChirality tc = 0 := by
  apply LinearMap.ext
  intro x
  have h := congrArg
    (Matrix.toLin' :
      Matrix (DAGCell tc) (DAGCell tc) ℚ →
        Module.End ℚ (DAGCellSpace tc))
    (DAG.MatrixRepresentation.chiral_anticommutation
      (dagBoundaryOneMatrix tc) (dagBoundaryTwoMatrix tc))
  simpa [dagDirac, dagChirality, dagDiracMatrix, dagChiralityMatrix,
    Matrix.toLin'_mul] using
    congrArg (fun T : Module.End ℚ (DAGCellSpace tc) => T x) h

theorem dagChirality_commutes_laplacian
    (tc : DAG.TwoComplex α)
    (hboundary : dagBoundaryOneMatrix tc * dagBoundaryTwoMatrix tc = 0) :
    dagChirality tc * dagLaplacian tc =
      dagLaplacian tc * dagChirality tc := by
  rw [← dagDirac_sq_eq_laplacian tc hboundary]
  have hodd :
      dagChirality tc * dagDirac tc =
        -(dagDirac tc * dagChirality tc) :=
    eq_neg_of_add_eq_zero_left (dagChiral_anticommutation tc)
  calc
    dagChirality tc * (dagDirac tc * dagDirac tc) =
        (dagChirality tc * dagDirac tc) * dagDirac tc := by
          rw [mul_assoc]
    _ = (-(dagDirac tc * dagChirality tc)) * dagDirac tc := by
          rw [hodd]
    _ = -((dagDirac tc * dagChirality tc) * dagDirac tc) := by
          exact neg_mul (dagDirac tc * dagChirality tc) (dagDirac tc)
    _ = -(dagDirac tc * (dagChirality tc * dagDirac tc)) := by
          rw [mul_assoc]
    _ = -(dagDirac tc * (-(dagDirac tc * dagChirality tc))) := by
          rw [hodd]
    _ = dagDirac tc * (dagDirac tc * dagChirality tc) := by
          apply LinearMap.ext
          intro x
          simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]

/-! ## Native involution and chiral projectors

The matrix owner supplies the oddness relation.  The following lemmas keep
the grading and its half-projectors on the native `Module.End` carrier; no
split-octonion or exterior-algebra identification is used here.
-/

theorem dagChirality_sq
    (tc : DAG.TwoComplex α) :
    dagChirality tc * dagChirality tc = (1 : Module.End ℚ (DAGCellSpace tc)) := by
  have hmatrix :
      dagChiralityMatrix tc * dagChiralityMatrix tc =
        (1 : Matrix (DAGCell tc) (DAGCell tc) ℚ) := by
    rw [dagChiralityMatrix, chiralGamma,
      Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      cases i <;> simp [cellParity]
    · simp [hij]
  have h := congrArg
    (Matrix.toLin' :
      Matrix (DAGCell tc) (DAGCell tc) ℚ →
        Module.End ℚ (DAGCellSpace tc)) hmatrix
  simpa [dagChirality, dagChiralityMatrix, Matrix.toLin'_mul] using h

def dagChiralProjectorPlus (tc : DAG.TwoComplex α) :
    Module.End ℚ (DAGCellSpace tc) :=
  (1 / 2 : ℚ) •
    ((1 : Module.End ℚ (DAGCellSpace tc)) + dagChirality tc)

def dagChiralProjectorMinus (tc : DAG.TwoComplex α) :
    Module.End ℚ (DAGCellSpace tc) :=
  (1 / 2 : ℚ) •
    ((1 : Module.End ℚ (DAGCellSpace tc)) - dagChirality tc)

theorem dagChiralProjectors_commute_laplacian
    (tc : DAG.TwoComplex α)
    (hboundary : dagBoundaryOneMatrix tc * dagBoundaryTwoMatrix tc = 0) :
    dagChiralProjectorPlus tc * dagLaplacian tc =
        dagLaplacian tc * dagChiralProjectorPlus tc ∧
      dagChiralProjectorMinus tc * dagLaplacian tc =
        dagLaplacian tc * dagChiralProjectorMinus tc := by
  have hcomm (x : DAGCellSpace tc) :
      dagChirality tc (dagLaplacian tc x) =
        dagLaplacian tc (dagChirality tc x) :=
    congrArg (fun T : Module.End ℚ (DAGCellSpace tc) => T x)
      (dagChirality_commutes_laplacian tc hboundary)
  constructor
  · apply LinearMap.ext
    intro x
    simp only [dagChiralProjectorPlus, Module.End.mul_apply,
      LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
      map_smul, map_add]
    rw [hcomm]
  · apply LinearMap.ext
    intro x
    simp only [dagChiralProjectorMinus, Module.End.mul_apply,
      LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply,
      map_smul, map_sub]
    rw [hcomm]

theorem dagChiralProjectors_sum (tc : DAG.TwoComplex α) :
    dagChiralProjectorPlus tc + dagChiralProjectorMinus tc =
      (1 : Module.End ℚ (DAGCellSpace tc)) := by
  apply LinearMap.ext
  intro x
  simp [dagChiralProjectorPlus, dagChiralProjectorMinus]
  module

theorem dagDirac_anticommutes_chirality
    (tc : DAG.TwoComplex α) :
    dagChirality tc * dagDirac tc =
      -(dagDirac tc * dagChirality tc) :=
  eq_neg_of_add_eq_zero_left (dagChiral_anticommutation tc)

theorem dagChiralProjectorPlus_sq (tc : DAG.TwoComplex α) :
    dagChiralProjectorPlus tc * dagChiralProjectorPlus tc =
      dagChiralProjectorPlus tc := by
  apply LinearMap.ext
  intro x
  have hγ := congrArg (fun T : Module.End ℚ (DAGCellSpace tc) => T x)
    (dagChirality_sq tc)
  simp only [Module.End.mul_apply, Module.End.one_apply] at hγ
  change (1 / 2 : ℚ) •
      ((1 / 2 : ℚ) • (x + dagChirality tc x) +
        dagChirality tc ((1 / 2 : ℚ) • (x + dagChirality tc x))) =
    (1 / 2 : ℚ) • (x + dagChirality tc x)
  rw [map_smul]
  simp only [map_add, smul_add, smul_smul, hγ]
  module

theorem dagChiralProjectorMinus_sq (tc : DAG.TwoComplex α) :
    dagChiralProjectorMinus tc * dagChiralProjectorMinus tc =
      dagChiralProjectorMinus tc := by
  apply LinearMap.ext
  intro x
  have hγ := congrArg (fun T : Module.End ℚ (DAGCellSpace tc) => T x)
    (dagChirality_sq tc)
  simp only [Module.End.mul_apply, Module.End.one_apply] at hγ
  change (1 / 2 : ℚ) •
      ((1 / 2 : ℚ) • (x - dagChirality tc x) -
        dagChirality tc ((1 / 2 : ℚ) • (x - dagChirality tc x))) =
    (1 / 2 : ℚ) • (x - dagChirality tc x)
  rw [map_smul]
  simp only [map_sub, smul_sub, smul_smul, hγ]
  module

theorem dagChiralProjectors_orthogonal (tc : DAG.TwoComplex α) :
    dagChiralProjectorPlus tc * dagChiralProjectorMinus tc = 0 ∧
      dagChiralProjectorMinus tc * dagChiralProjectorPlus tc = 0 := by
  have hγ (x : DAGCellSpace tc) :
      dagChirality tc (dagChirality tc x) = x := by
    exact congrArg (fun T : Module.End ℚ (DAGCellSpace tc) => T x)
      (dagChirality_sq tc) ▸ rfl
  constructor
  · apply LinearMap.ext
    intro x
    change (1 / 2 : ℚ) •
        ((1 / 2 : ℚ) • (x - dagChirality tc x) +
          dagChirality tc ((1 / 2 : ℚ) • (x - dagChirality tc x))) = 0
    rw [map_smul]
    simp only [map_sub, smul_sub, hγ]
    module
  · apply LinearMap.ext
    intro x
    change (1 / 2 : ℚ) •
        ((1 / 2 : ℚ) • (x + dagChirality tc x) -
          dagChirality tc ((1 / 2 : ℚ) • (x + dagChirality tc x))) = 0
    rw [map_smul]
    simp only [map_add, smul_add, hγ]
    module

theorem dagDirac_comp_projectorPlus_eq_projectorMinus_comp
    (tc : DAG.TwoComplex α) :
    dagDirac tc * dagChiralProjectorPlus tc =
      dagChiralProjectorMinus tc * dagDirac tc := by
  apply LinearMap.ext
  intro x
  have hodd :
      dagChirality tc (dagDirac tc x) =
        -(dagDirac tc (dagChirality tc x)) := by
    exact congrArg (fun T : Module.End ℚ (DAGCellSpace tc) => T x)
      (dagDirac_anticommutes_chirality tc) ▸ rfl
  simp only [Module.End.mul_apply, dagChiralProjectorPlus,
    dagChiralProjectorMinus, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, map_smul, map_add,
    smul_add, smul_sub]
  rw [← smul_add, ← smul_sub]
  rw [hodd]
  module

theorem dagDirac_comp_projectorMinus_eq_projectorPlus_comp
    (tc : DAG.TwoComplex α) :
    dagDirac tc * dagChiralProjectorMinus tc =
      dagChiralProjectorPlus tc * dagDirac tc := by
  apply LinearMap.ext
  intro x
  have hodd :
      dagChirality tc (dagDirac tc x) =
        -(dagDirac tc (dagChirality tc x)) := by
    exact congrArg (fun T : Module.End ℚ (DAGCellSpace tc) => T x)
      (dagDirac_anticommutes_chirality tc) ▸ rfl
  simp only [Module.End.mul_apply, dagChiralProjectorPlus,
    dagChiralProjectorMinus, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, map_smul, map_sub,
    smul_add, smul_sub]
  rw [← smul_sub, ← smul_add]
  rw [hodd]
  module

/-! ## Chiral block readout

The two blocks below are endomorphisms of the doubled carrier.  Their source
and target chiral sectors are recorded by the surrounding projectors; no
additional identification of those sectors is asserted here.
-/

def dagChiralDiracPlus (tc : DAG.TwoComplex α) :
    Module.End ℚ (DAGCellSpace tc) :=
  dagChiralProjectorMinus tc * dagDirac tc * dagChiralProjectorPlus tc

def dagChiralDiracMinus (tc : DAG.TwoComplex α) :
    Module.End ℚ (DAGCellSpace tc) :=
  dagChiralProjectorPlus tc * dagDirac tc * dagChiralProjectorMinus tc

theorem dagChiralDiracPlus_eq_dirac_comp_projectorPlus
    (tc : DAG.TwoComplex α) :
    dagChiralDiracPlus tc = dagDirac tc * dagChiralProjectorPlus tc := by
  change (dagChiralProjectorMinus tc * dagDirac tc) *
      dagChiralProjectorPlus tc = _
  rw [← dagDirac_comp_projectorPlus_eq_projectorMinus_comp tc,
    mul_assoc, dagChiralProjectorPlus_sq]

theorem dagChiralDiracMinus_eq_dirac_comp_projectorMinus
    (tc : DAG.TwoComplex α) :
    dagChiralDiracMinus tc = dagDirac tc * dagChiralProjectorMinus tc := by
  change (dagChiralProjectorPlus tc * dagDirac tc) *
      dagChiralProjectorMinus tc = _
  rw [← dagDirac_comp_projectorMinus_eq_projectorPlus_comp tc,
    mul_assoc, dagChiralProjectorMinus_sq]

theorem dagDirac_eq_chiralDiracPlus_add_chiralDiracMinus
    (tc : DAG.TwoComplex α) :
    dagDirac tc = dagChiralDiracPlus tc + dagChiralDiracMinus tc := by
  rw [dagChiralDiracPlus_eq_dirac_comp_projectorPlus,
    dagChiralDiracMinus_eq_dirac_comp_projectorMinus]
  calc
    dagDirac tc = dagDirac tc * (1 : Module.End ℚ (DAGCellSpace tc)) := by simp
    _ = dagDirac tc *
        (dagChiralProjectorPlus tc + dagChiralProjectorMinus tc) := by
      rw [dagChiralProjectors_sum]
    _ = dagDirac tc * dagChiralProjectorPlus tc +
        dagDirac tc * dagChiralProjectorMinus tc := by rw [mul_add]

theorem dagChiralDiracPlus_sq_zero (tc : DAG.TwoComplex α) :
    dagChiralDiracPlus tc * dagChiralDiracPlus tc = 0 := by
  rw [dagChiralDiracPlus_eq_dirac_comp_projectorPlus]
  calc
    dagDirac tc * dagChiralProjectorPlus tc *
        (dagDirac tc * dagChiralProjectorPlus tc) =
        dagDirac tc * (dagChiralProjectorPlus tc * dagDirac tc) *
          dagChiralProjectorPlus tc := by simp [mul_assoc]
    _ = dagDirac tc * (dagDirac tc * dagChiralProjectorMinus tc) *
          dagChiralProjectorPlus tc := by
      rw [← dagDirac_comp_projectorMinus_eq_projectorPlus_comp]
    _ = 0 := by
      simp only [mul_assoc]
      rw [(dagChiralProjectors_orthogonal tc).2]
      simp

theorem dagChiralDiracMinus_sq_zero (tc : DAG.TwoComplex α) :
    dagChiralDiracMinus tc * dagChiralDiracMinus tc = 0 := by
  rw [dagChiralDiracMinus_eq_dirac_comp_projectorMinus]
  calc
    dagDirac tc * dagChiralProjectorMinus tc *
        (dagDirac tc * dagChiralProjectorMinus tc) =
        dagDirac tc * (dagChiralProjectorMinus tc * dagDirac tc) *
          dagChiralProjectorMinus tc := by simp [mul_assoc]
    _ = dagDirac tc * (dagDirac tc * dagChiralProjectorPlus tc) *
          dagChiralProjectorMinus tc := by
      rw [← dagDirac_comp_projectorPlus_eq_projectorMinus_comp]
    _ = 0 := by
      simp only [mul_assoc]
      rw [(dagChiralProjectors_orthogonal tc).1]
      simp

theorem dagChiralDiagonalPlus_zero (tc : DAG.TwoComplex α) :
    dagChiralProjectorPlus tc * dagDirac tc *
        dagChiralProjectorPlus tc = 0 := by
  rw [← dagDirac_comp_projectorMinus_eq_projectorPlus_comp tc]
  simp only [mul_assoc]
  rw [(dagChiralProjectors_orthogonal tc).2]
  simp

theorem dagChiralDiagonalMinus_zero (tc : DAG.TwoComplex α) :
    dagChiralProjectorMinus tc * dagDirac tc *
        dagChiralProjectorMinus tc = 0 := by
  rw [← dagDirac_comp_projectorPlus_eq_projectorMinus_comp tc]
  simp only [mul_assoc]
  rw [(dagChiralProjectors_orthogonal tc).1]
  simp

theorem dagDirac_sq_eq_chiralDirac_blocks
    (tc : DAG.TwoComplex α) :
    dagDirac tc * dagDirac tc =
      dagChiralDiracPlus tc * dagChiralDiracMinus tc +
        dagChiralDiracMinus tc * dagChiralDiracPlus tc := by
  rw [dagDirac_eq_chiralDiracPlus_add_chiralDiracMinus]
  simp only [add_mul, mul_add, dagChiralDiracPlus_sq_zero,
    dagChiralDiracMinus_sq_zero, zero_add, add_zero]
  ac_rfl

theorem dagLaplacian_eq_chiralDirac_blocks
    (tc : DAG.TwoComplex α)
    (hboundary : dagBoundaryOneMatrix tc * dagBoundaryTwoMatrix tc = 0) :
    dagLaplacian tc =
      dagChiralDiracPlus tc * dagChiralDiracMinus tc +
        dagChiralDiracMinus tc * dagChiralDiracPlus tc := by
  rw [← dagDirac_sq_eq_laplacian tc hboundary,
    dagDirac_sq_eq_chiralDirac_blocks]

/-! ## Canonical finite complexes

The generic factorization keeps its boundary-square hypothesis explicit.  The
small canonical complexes supplied by `DAG.HodgeTheorems` satisfy that
hypothesis by computation, so these are genuine native instances rather than
axiomatic witnesses.
-/

theorem dagCanonicalChain_boundary_square :
    dagBoundaryOneMatrix DAG.canonicalChainComplex *
        dagBoundaryTwoMatrix DAG.canonicalChainComplex = 0 := by
  native_decide

theorem dagCanonicalTriangle_boundary_square :
    dagBoundaryOneMatrix DAG.canonicalTriangleComplex *
        dagBoundaryTwoMatrix DAG.canonicalTriangleComplex = 0 := by
  native_decide

theorem dagCanonicalDigon_boundary_square :
    dagBoundaryOneMatrix DAG.canonicalDigonComplex *
        dagBoundaryTwoMatrix DAG.canonicalDigonComplex = 0 := by
  native_decide

theorem dagCanonicalChain_dirac_sq_eq_laplacian :
    dagDirac DAG.canonicalChainComplex * dagDirac DAG.canonicalChainComplex =
      dagLaplacian DAG.canonicalChainComplex := by
  exact dagDirac_sq_eq_laplacian _ dagCanonicalChain_boundary_square

theorem dagCanonicalTriangle_dirac_sq_eq_laplacian :
    dagDirac DAG.canonicalTriangleComplex *
        dagDirac DAG.canonicalTriangleComplex =
      dagLaplacian DAG.canonicalTriangleComplex := by
  exact dagDirac_sq_eq_laplacian _ dagCanonicalTriangle_boundary_square

theorem dagCanonicalDigon_dirac_sq_eq_laplacian :
    dagDirac DAG.canonicalDigonComplex * dagDirac DAG.canonicalDigonComplex =
      dagLaplacian DAG.canonicalDigonComplex := by
  exact dagDirac_sq_eq_laplacian _ dagCanonicalDigon_boundary_square

end InfoGeometry.Canonical.DAGNativeHodgeLinearMapBridge

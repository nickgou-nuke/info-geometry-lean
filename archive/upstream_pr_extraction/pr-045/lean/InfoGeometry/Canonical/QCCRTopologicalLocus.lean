import InfoGeometry.Canonical.MajoranaCARTopologicalLocus
import InfoGeometry.OperatorAlgebra.QCCRResidual
import InfoGeometry.Krein.Automorphisms
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Topological q-CCR locus for non-commutative endomorphisms

The parameter `q` interpolates the algebraic residual
`A * B - q • (B * A) - 1` inside the continuous-linear endomorphism ring.
The fibers `q = -1`, `q = 1`, and `q = 0` are respectively the CAR, CCR,
and Cuntz-limit relations.  This file records only closed loci and exact
finite-stage implications; it does not identify the fibers as representations.
-/

noncomputable section

namespace InfoGeometry.Canonical.QCCRTopologicalLocus

open CategoryTheory
open InfoGeometry.OperatorAlgebra.QCCRResidual
open InfoGeometry.Canonical.MajoranaCARTopologicalLocus
open InfoGeometry.Quantum.RealMajorana
open InfoGeometry.Krein

variable {S : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]

abbrev EndS := S →L[ℝ] S

def operatorQCCRResidual (q : ℝ) (A B : EndS (S := S)) : EndS (S := S) :=
  A * B - q • (B * A) - ContinuousLinearMap.id ℝ S

def operatorQCCRResidualMap :
    ContinuousMap (ℝ × (EndS (S := S) × EndS (S := S))) (EndS (S := S)) :=
  { toFun := fun p => operatorQCCRResidual p.1 p.2.1 p.2.2
    continuous_toFun := by
      change Continuous (fun p : ℝ × (EndS (S := S) × EndS (S := S)) =>
        p.2.1 * p.2.2 - p.1 • (p.2.2 * p.2.1) -
          ContinuousLinearMap.id ℝ S)
      fun_prop }

@[simp] theorem operatorQCCRResidualMap_apply
    (q : ℝ) (A B : EndS (S := S)) :
    operatorQCCRResidualMap (S := S) (q, (A, B)) =
      operatorQCCRResidual q A B :=
  rfl

def operatorQCCRLocus :
    Set (ℝ × (EndS (S := S) × EndS (S := S))) :=
  operatorQCCRResidualMap (S := S) ⁻¹' ({0} : Set (EndS (S := S)))

theorem operatorQCCRLocus_isClosed :
    IsClosed (operatorQCCRLocus (S := S)) := by
  exact isClosed_singleton.preimage
    (operatorQCCRResidualMap (S := S)).continuous

theorem operatorQCCRLocus_neg_one_iff
    (A B : EndS (S := S)) :
    (-1, (A, B)) ∈ operatorQCCRLocus (S := S) ↔
      A * B + B * A = ContinuousLinearMap.id ℝ S := by
  change operatorQCCRResidual (-1) A B = 0 ↔ _
  simp [operatorQCCRResidual, sub_eq_zero]

theorem operatorQCCRLocus_one_iff
    (A B : EndS (S := S)) :
    (1, (A, B)) ∈ operatorQCCRLocus (S := S) ↔
      A * B - B * A = ContinuousLinearMap.id ℝ S := by
  change operatorQCCRResidual 1 A B = 0 ↔ _
  simp [operatorQCCRResidual, sub_eq_zero]

theorem operatorQCCRLocus_zero_iff
    (A B : EndS (S := S)) :
    (0, (A, B)) ∈ operatorQCCRLocus (S := S) ↔
      A * B = ContinuousLinearMap.id ℝ S := by
  change operatorQCCRResidual 0 A B = 0 ↔ _
  simp [operatorQCCRResidual, sub_eq_zero]

/-- A normalized Majorana CAR pair is a point of the `q = -1` fiber. -/
theorem majorana_pair_mem_operatorQCCRLocus_neg_one
    [CompleteSpace S]
    (M : RealMajoranaDatum (S := S)) (u v : S)
    (h_norm : 2 * inner ℝ u v = 1) :
    (-1, (M.gamma u, M.gamma v)) ∈ operatorQCCRLocus (S := S) := by
  rw [operatorQCCRLocus_neg_one_iff]
  calc
    M.gamma u * M.gamma v + M.gamma v * M.gamma u =
        (2 * inner ℝ u v) • ContinuousLinearMap.id ℝ S := by
      simpa [anticommutator] using M.car u v
    _ = ContinuousLinearMap.id ℝ S := by rw [h_norm, one_smul]

/-- A Cuntz isometry pair lies in the zero-parameter fiber after reversing
the ordered pair: the residual becomes `S* * S - 1`. -/
theorem cuntz_isometry_mem_operatorQCCRLocus_zero
    (s sstar : EndS (S := S)) (h : sstar * s = ContinuousLinearMap.id ℝ S) :
    (0, (sstar, s)) ∈ operatorQCCRLocus (S := S) := by
  rw [operatorQCCRLocus_zero_iff]
  exact h

/-! Conjugation is the intrinsic topological symmetry of the noncommutative
operator ring.  It preserves every `q` fiber, not only the CAR fiber. -/
theorem conjugation_maps_operatorQCCRLocus
    (U : S ≃L[ℝ] S) (q : ℝ) (A B : EndS (S := S))
    (hp : (q, (A, B)) ∈ operatorQCCRLocus (S := S)) :
    (q, (conjugateCLM U A, conjugateCLM U B)) ∈
      operatorQCCRLocus (S := S) := by
  change operatorQCCRResidual q
    (conjugateCLM U A) (conjugateCLM U B) = 0
  rw [show operatorQCCRResidual q
      (conjugateCLM U A) (conjugateCLM U B) =
      conjugateCLM U (operatorQCCRResidual q A B) by
        simp only [operatorQCCRResidual, map_sub, conjugateCLM_mul,
          conjugateCLM_smul, conjugateCLM_id]]
  rw [show operatorQCCRResidual q A B = 0 from hp]
  exact map_zero (conjEnd U)

end InfoGeometry.Canonical.QCCRTopologicalLocus

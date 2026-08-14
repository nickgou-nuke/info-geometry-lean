import InfoGeometry.Lie.SplitOctonionEllClosedFlow
import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
import InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllClosedFlow

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionEllFlowOperator
open Real

noncomputable def diagCircularBasis : Module.Basis (Fin 8) ℝ CZ :=
  circularBasis.map cartesianZornLinearEquiv

@[simp] theorem diagCircularBasis_apply (i : Fin 8) :
    diagCircularBasis i = cartesianZornLinearEquiv (circularBasis i) := by
  exact Module.Basis.map_apply _ _ _

theorem diagCircularBasis_eigen (i : Fin 8) :
    diagEllGrading (diagCircularBasis i) =
      (if i = 0 then (0 : ℝ) else if i < 4 then 1 else if i = 4 then 0 else -1) •
        diagCircularBasis i := by
  rw [diagCircularBasis_apply]
  have hc : cartesianEllGrading (circularBasis i) =
      (if i = 0 then (0 : ℝ) else if i < 4 then 1 else if i = 4 then 0 else -1) •
        circularBasis i := by
    rw [circularBasis_apply]
    fin_cases i
    · simpa [circularFrame] using cartesianEllGrading_scalarPlus
    · simpa [circularFrame] using cartesianEllGrading_rootPlus 0
    · simpa [circularFrame] using cartesianEllGrading_rootPlus 1
    · simpa [circularFrame] using cartesianEllGrading_rootPlus 2
    · simpa [circularFrame] using cartesianEllGrading_scalarMinus
    · simpa [circularFrame] using cartesianEllGrading_rootMinus 0
    · simpa [circularFrame] using cartesianEllGrading_rootMinus 1
    · simpa [circularFrame] using cartesianEllGrading_rootMinus 2
  calc
    diagEllGrading (cartesianZornLinearEquiv (circularBasis i)) =
        cartesianZornLinearEquiv (cartesianEllGrading (circularBasis i)) := by
      rw [cartesianZorn_intertwines_ellGrading]
    _ = cartesianZornLinearEquiv
          ((if i = 0 then (0 : ℝ) else if i < 4 then 1 else if i = 4 then 0 else -1) •
            circularBasis i) := congrArg cartesianZornLinearEquiv hc
    _ = (if i = 0 then (0 : ℝ) else if i < 4 then 1 else if i = 4 then 0 else -1) •
          diagCircularBasis i := by
      rw [map_smul, diagCircularBasis_apply]

theorem ellFlowPhi_diagCircularBasis (t : ℝ) (i : Fin 8) :
    ellFlowPhi t (diagCircularBasis i) =
      (if i = 0 then 1 else if i < 4 then exp t else if i = 4 then 1 else exp (-t)) •
        diagCircularBasis i := by
  rw [diagCircularBasis_apply]
  calc
    ellFlowPhi t (cartesianZornLinearEquiv (circularBasis i)) =
        cartesianZornLinearEquiv (cartesianHyperbolicFlow t (circularBasis i)) := by
      rw [cartesianZorn_intertwines_closedFlow]
    _ = (if i = 0 then (1 : ℝ) else if i < 4 then exp t else if i = 4 then 1 else exp (-t)) •
          diagCircularBasis i := by
      rw [circularBasis_apply]
      fin_cases i
      · simp [circularFrame, scalarPlus, quaternionScalar, ellScalar,
          cartesianHyperbolicFlow]
      · simpa [circularFrame, diagCircularBasis_apply] using
          congrArg cartesianZornLinearEquiv (cartesianHyperbolicFlow_rootPlus t 0)
      · simpa [circularFrame, diagCircularBasis_apply] using
          congrArg cartesianZornLinearEquiv (cartesianHyperbolicFlow_rootPlus t 1)
      · simpa [circularFrame, diagCircularBasis_apply] using
          congrArg cartesianZornLinearEquiv (cartesianHyperbolicFlow_rootPlus t 2)
      · simp [circularFrame, scalarMinus, quaternionScalar, ellScalar,
          cartesianHyperbolicFlow]
      · simpa [circularFrame, diagCircularBasis_apply] using
          congrArg cartesianZornLinearEquiv (cartesianHyperbolicFlow_rootMinus t 0)
      · simpa [circularFrame, diagCircularBasis_apply] using
          congrArg cartesianZornLinearEquiv (cartesianHyperbolicFlow_rootMinus t 1)
      · simpa [circularFrame, diagCircularBasis_apply] using
          congrArg cartesianZornLinearEquiv (cartesianHyperbolicFlow_rootMinus t 2)

theorem ellQ_diagCircularBasis (i : Fin 8) :
    ellQ (diagCircularBasis i) =
      (if i = 0 then (0 : ℝ) else if i < 4 then 1 else if i = 4 then 0 else 1) •
        diagCircularBasis i := by
  change diagEllGrading (diagEllGrading (diagCircularBasis i)) = _
  rw [diagCircularBasis_eigen, map_smul, diagCircularBasis_eigen, smul_smul]
  split_ifs <;> norm_num

theorem trace_basis_smul {b : Module.Basis (Fin 8) ℝ CZ} (f : EndCZ) (w : Fin 8 → ℝ)
    (h : ∀ i, f (b i) = w i • b i) :
    LinearMap.trace ℝ CZ f = ∑ i, w i := by
  rw [LinearMap.trace_eq_matrix_trace ℝ b]
  simp only [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i hi
  change (LinearMap.toMatrix b b f i i) = w i
  rw [LinearMap.toMatrix_apply]
  change (b.repr (f (b i))) i = w i
  rw [h, map_smul]
  simp

theorem trace_ellGrading : LinearMap.trace ℝ CZ (diagEllGrading : EndCZ) = 0 := by
  calc
    LinearMap.trace ℝ CZ (diagEllGrading : EndCZ) =
        ∑ i, (if i = 0 then (0 : ℝ) else if i < 4 then 1 else if i = 4 then 0 else -1) :=
      trace_basis_smul _ _ diagCircularBasis_eigen
    _ = 0 := by
      simp [Fin.sum_univ_succ]

theorem trace_ellFlowPhi (t : ℝ) :
    LinearMap.trace ℝ CZ (ellFlowPhi t : EndCZ) = 2 + 3 * Real.exp t + 3 * Real.exp (-t) := by
  calc
    LinearMap.trace ℝ CZ (ellFlowPhi t : EndCZ) =
        ∑ i, (if i = 0 then 1 else if i < 4 then exp t else if i = 4 then 1 else exp (-t)) :=
      trace_basis_smul _ _ (ellFlowPhi_diagCircularBasis t)
    _ = 2 + 3 * Real.exp t + 3 * Real.exp (-t) := by
      simp [Fin.sum_univ_succ]
      ring

theorem trace_exp_neg_beta_Q (β : ℝ) :
    LinearMap.trace ℝ CZ ((Real.exp (-β) : ℝ) • ellQ : EndCZ) =
      6 * Real.exp (-β) := by
  let c : ℝ := Real.exp (-β)
  have hQ : ∀ i, ((Real.exp (-β) : ℝ) • ellQ : EndCZ)
      (diagCircularBasis i) =
        (c * (if i = 0 then (0 : ℝ) else if i < 4 then 1 else if i = 4 then 0 else 1)) •
          diagCircularBasis i := by
    intro i
    change (Real.exp (-β) : ℝ) • ellQ (diagCircularBasis i) = _
    rw [ellQ_diagCircularBasis]
    module
  calc
    LinearMap.trace ℝ CZ ((Real.exp (-β) : ℝ) • ellQ : EndCZ) =
        ∑ i, c * (if i = 0 then (0 : ℝ) else if i < 4 then 1 else if i = 4 then 0 else 1) :=
      trace_basis_smul _ _ hQ
    _ = 6 * Real.exp (-β) := by
      simp [Fin.sum_univ_succ, c]
      ring

end InfoGeometry.Lie.SplitOctonionEllClosedFlow

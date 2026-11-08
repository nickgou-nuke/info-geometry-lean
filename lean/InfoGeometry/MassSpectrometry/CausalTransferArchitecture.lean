import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.MassSpectrometry.CausalCrossGramian
import InfoGeometry.MassSpectrometry.CausalRetraction
import InfoGeometry.MassSpectrometry.ChiralDiscreteMajoranaBridge

/-!
# Fused causal transfer architecture

This capstone fuses the directed-source, causal-cone, KAN-style, chiral, and
Moore-Penrose layers without collapsing their proof obligations.

The transfer weight is the product of a cross-Gramian feature score and a
finite KAN-style log-mass potential, but only on certified edges of a
`ValuedFragmentationDAG`.  Consequently nonzero transfer entries inherit
strict physical mass loss from the DAG owner, independently of how the learned
score is parameterized.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open Matrix

/-- DAG-restricted cross-Gramian/KAN transfer. -/
def fusedCausalTransfer {n d q : ℕ}
    (D : ValuedFragmentationDAG n)
    (ZParent ZChild : Matrix (Fin n) (Fin d) ℝ)
    (Φ : FiniteKANCausalKernel q) : AssignmentMatrix n :=
  fun i j =>
    by
      classical
      exact if D.edge i j then
        crossGramOperator ZParent ZChild i j *
          Φ.causal (Real.log (D.massOf i)) (Real.log (D.massOf j))
      else 0

/-- Any nonzero fused transfer is a certified fragmentation edge. -/
theorem fusedCausalTransfer_support_edge
    {n d q : ℕ} (D : ValuedFragmentationDAG n)
    (ZParent ZChild : Matrix (Fin n) (Fin d) ℝ)
    (Φ : FiniteKANCausalKernel q) {i j : Fin n}
    (h : fusedCausalTransfer D ZParent ZChild Φ i j ≠ 0) :
    D.edge i j := by
  by_contra hedge
  have hz : fusedCausalTransfer D ZParent ZChild Φ i j = 0 := by
    simp [fusedCausalTransfer, hedge]
  exact h hz

/-- Nonzero fused transfer strictly decreases physical mass. -/
theorem fusedCausalTransfer_mass_decreases
    {n d q : ℕ} (D : ValuedFragmentationDAG n)
    (ZParent ZChild : Matrix (Fin n) (Fin d) ℝ)
    (Φ : FiniteKANCausalKernel q) {i j : Fin n}
    (h : fusedCausalTransfer D ZParent ZChild Φ i j ≠ 0) :
    D.massOf j < D.massOf i := by
  exact D.mass_decreases (fusedCausalTransfer_support_edge D ZParent ZChild Φ h)

/-- Nonzero fused transfer has strictly positive neutral loss. -/
theorem fusedCausalTransfer_deltaMass_pos
    {n d q : ℕ} (D : ValuedFragmentationDAG n)
    (ZParent ZChild : Matrix (Fin n) (Fin d) ℝ)
    (Φ : FiniteKANCausalKernel q) {i j : Fin n}
    (h : fusedCausalTransfer D ZParent ZChild Φ i j ≠ 0) :
    0 < D.deltaMass i j := by
  exact sub_pos.mpr (fusedCausalTransfer_mass_decreases D ZParent ZChild Φ h)

/-- A proof-carrying causal transfer together with its Moore-Penrose
reconstruction certificate. -/
structure CausalTransferSystem (n d q : ℕ) where
  valuedDag : ValuedFragmentationDAG n
  parentFeatures : Matrix (Fin n) (Fin d) ℝ
  childFeatures : Matrix (Fin n) (Fin d) ℝ
  kanKernel : FiniteKANCausalKernel q
  retraction :
    CausalRetraction
      (fusedCausalTransfer valuedDag parentFeatures childFeatures kanKernel)

namespace CausalTransferSystem

variable {n d q : ℕ} (S : CausalTransferSystem n d q)

/-- Forward causal transfer matrix. -/
def transfer : AssignmentMatrix n :=
  fusedCausalTransfer S.valuedDag S.parentFeatures S.childFeatures S.kanKernel

/-- Chiral doubled forward/reverse carrier. -/
def doubledTransfer : Matrix (DoubledIndex n) (DoubledIndex n) ℝ :=
  doubledOperator S.transfer

/-- Skew chiral Majorana shadow `Γ D_transfer`. -/
def majoranaShadow : Matrix (DoubledIndex n) (DoubledIndex n) ℝ :=
  directedMajoranaOperator S.transfer

/-- Moore-Penrose projectivity tensor of the fused transfer. -/
def projectivityTensor : Matrix (DoubledIndex n) (DoubledIndex n) ℝ :=
  S.retraction.causalProjectivityTensor

/-- Every nonzero transfer coefficient is an actual edge of the valued DAG. -/
theorem transfer_support_edge {i j : Fin n}
    (h : S.transfer i j ≠ 0) : S.valuedDag.edge i j := by
  exact fusedCausalTransfer_support_edge
    S.valuedDag S.parentFeatures S.childFeatures S.kanKernel h

/-- Every nonzero transfer coefficient strictly decreases physical mass. -/
theorem transfer_mass_decreases {i j : Fin n}
    (h : S.transfer i j ≠ 0) :
    S.valuedDag.massOf j < S.valuedDag.massOf i := by
  exact fusedCausalTransfer_mass_decreases
    S.valuedDag S.parentFeatures S.childFeatures S.kanKernel h

/-- Every nonzero transfer coefficient has positive neutral loss. -/
theorem transfer_deltaMass_pos {i j : Fin n}
    (h : S.transfer i j ≠ 0) :
    0 < S.valuedDag.deltaMass i j := by
  exact fusedCausalTransfer_deltaMass_pos
    S.valuedDag S.parentFeatures S.childFeatures S.kanKernel h

/-- The doubled transfer anticommutes with the chiral grading. -/
theorem doubledTransfer_anticommutes_grading :
    gradingMatrix n * S.doubledTransfer +
      S.doubledTransfer * gradingMatrix n = 0 := by
  exact grading_anticommute_doubledOperator S.transfer

/-- The Majorana shadow of the fused transfer is skew. -/
theorem majoranaShadow_transpose_eq_neg :
    S.majoranaShadow.transpose = -S.majoranaShadow := by
  exact directedMajoranaOperator_transpose_eq_neg S.transfer

/-- The Moore-Penrose forward/backward projectivity tensor is grading-even. -/
theorem projectivityTensor_commutes_grading :
    gradingMatrix n * S.projectivityTensor =
      S.projectivityTensor * gradingMatrix n := by
  exact S.retraction.projectivity_commutes_with_grading

/-- Grading conjugation fixes the Moore-Penrose projectivity tensor. -/
theorem grading_conjugates_projectivityTensor_to_self :
    gradingMatrix n * S.projectivityTensor * gradingMatrix n =
      S.projectivityTensor := by
  exact S.retraction.grading_conjugates_projectivity_to_self

end CausalTransferSystem

end InfoGeometry.MassSpectrometry

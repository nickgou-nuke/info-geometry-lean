import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace SarsChiralMassDilaton

open Real

abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

def PR : M2R := !![1, 0; 0, 0]
def PL : M2R := !![0, 0; 0, 1]
def I2 : M2R := 1
def Jmod : M2R := !![0, 1; 1, 0]
def diracMassCoupling (m : ℝ) : M2R := m • Jmod

def diagBlock (A : M2R) : M2R := !![A 0 0, 0; 0, A 1 1]
def offBlock (A : M2R) : M2R := !![0, A 0 1; A 1 0, 0]

@[simp] theorem projectors_orthogonal : PR * PL = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [PR, PL]

@[simp] theorem projectors_sum_identity : PR + PL = I2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [PR, PL, I2]

@[simp] theorem tomita_swaps_left_right : Jmod * PL * Jmod = PR := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [Jmod, PL, PR, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem tomita_swaps_right_left : Jmod * PR * Jmod = PL := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [Jmod, PR, PL, Matrix.mul_apply, Fin.sum_univ_two]

theorem diracMassCoupling_matrix (m : ℝ) :
    diracMassCoupling m = !![0, m; m, 0] := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [diracMassCoupling, Jmod]

@[simp] theorem diracMassCoupling_diag_zero (m : ℝ) :
    diagBlock (diracMassCoupling m) = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [diagBlock, diracMassCoupling, Jmod]

@[simp] theorem diracMassCoupling_offblock_self (m : ℝ) :
    offBlock (diracMassCoupling m) = diracMassCoupling m := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [offBlock, diracMassCoupling, Jmod]

def dilaton (lam : ℝ) : ℝ := Real.exp lam
def localMass (m0 lam : ℝ) : ℝ := m0 * dilaton lam
def comptonScale (hbar c m : ℝ) : ℝ := hbar / (m * c)
def zitterFrequency (hbar c m : ℝ) : ℝ := 2 * m * c^2 / hbar

theorem localMass_zero_base (lam : ℝ) : localMass 0 lam = 0 := by simp [localMass]

theorem localMass_positive {m0 lam : ℝ} (hm0 : 0 < m0) : 0 < localMass m0 lam := by
  unfold localMass dilaton
  exact mul_pos hm0 (Real.exp_pos lam)

def springPotential (m lam : ℝ) : ℝ := (m^2 * lam^2) / 2
def restoringForce (m lam : ℝ) : ℝ := - m^2 * lam

theorem springPotential_nonneg (m lam : ℝ) : 0 ≤ springPotential m lam := by
  unfold springPotential
  positivity

theorem springPotential_zero_at_vacuum (m : ℝ) : springPotential m 0 = 0 := by
  norm_num [springPotential]

theorem restoringForce_hooke (m lam : ℝ) : restoringForce m lam = - m^2 * lam := rfl

def localEntropyQuadratic (x : ℝ) : ℝ := x^2 / 2

theorem localEntropyQuadratic_nonneg (x : ℝ) : 0 ≤ localEntropyQuadratic x := by
  unfold localEntropyQuadratic
  positivity

theorem localEntropyQuadratic_zero : localEntropyQuadratic 0 = 0 := by
  norm_num [localEntropyQuadratic]

inductive ChiralMassConcept where
  | Left_Weyl_Sheet
  | Right_Weyl_Sheet
  | Tomita_Modular_Swap
  | Dirac_Mass_Coupling
  | Zitterbewegung
  | Dilaton_Weyl_Scale
  | Conformal_Spring
  | Orthogonal_Entropy_Transport
  deriving DecidableEq, Repr

inductive ChiralMassEdge where
  | swapped_by
  | couples_to
  | generates
  | breaks_weyl_scale_by
  | realizes_as
  | drives_orthogonal_transport
  deriving DecidableEq, Repr

def edgeHolds : ChiralMassConcept → ChiralMassEdge → ChiralMassConcept → Bool
  | ChiralMassConcept.Left_Weyl_Sheet, ChiralMassEdge.swapped_by, ChiralMassConcept.Tomita_Modular_Swap => true
  | ChiralMassConcept.Right_Weyl_Sheet, ChiralMassEdge.swapped_by, ChiralMassConcept.Tomita_Modular_Swap => true
  | ChiralMassConcept.Left_Weyl_Sheet, ChiralMassEdge.couples_to, ChiralMassConcept.Right_Weyl_Sheet => true
  | ChiralMassConcept.Dirac_Mass_Coupling, ChiralMassEdge.generates, ChiralMassConcept.Zitterbewegung => true
  | ChiralMassConcept.Dirac_Mass_Coupling, ChiralMassEdge.breaks_weyl_scale_by, ChiralMassConcept.Dilaton_Weyl_Scale => true
  | ChiralMassConcept.Dilaton_Weyl_Scale, ChiralMassEdge.realizes_as, ChiralMassConcept.Conformal_Spring => true
  | ChiralMassConcept.Conformal_Spring, ChiralMassEdge.drives_orthogonal_transport, ChiralMassConcept.Orthogonal_Entropy_Transport => true
  | _, _, _ => false

theorem chiral_mass_graph_kernel :
    edgeHolds ChiralMassConcept.Left_Weyl_Sheet ChiralMassEdge.swapped_by ChiralMassConcept.Tomita_Modular_Swap = true ∧
    edgeHolds ChiralMassConcept.Left_Weyl_Sheet ChiralMassEdge.couples_to ChiralMassConcept.Right_Weyl_Sheet = true ∧
    edgeHolds ChiralMassConcept.Dirac_Mass_Coupling ChiralMassEdge.generates ChiralMassConcept.Zitterbewegung = true ∧
    edgeHolds ChiralMassConcept.Dirac_Mass_Coupling ChiralMassEdge.breaks_weyl_scale_by ChiralMassConcept.Dilaton_Weyl_Scale = true ∧
    edgeHolds ChiralMassConcept.Dilaton_Weyl_Scale ChiralMassEdge.realizes_as ChiralMassConcept.Conformal_Spring = true ∧
    edgeHolds ChiralMassConcept.Conformal_Spring ChiralMassEdge.drives_orthogonal_transport ChiralMassConcept.Orthogonal_Entropy_Transport = true := by
  decide

theorem chiral_mass_dilaton_kernel :
    PR * PL = 0 ∧
    PR + PL = I2 ∧
    Jmod * PL * Jmod = PR ∧
    (∀ m : ℝ, diracMassCoupling m = !![0, m; m, 0]) ∧
    (∀ m : ℝ, diagBlock (diracMassCoupling m) = 0) ∧
    (∀ m : ℝ, offBlock (diracMassCoupling m) = diracMassCoupling m) ∧
    (∀ lam : ℝ, localMass 0 lam = 0) ∧
    (∀ m lam : ℝ, 0 ≤ springPotential m lam) ∧
    (∀ m : ℝ, springPotential m 0 = 0) ∧
    (∀ x : ℝ, 0 ≤ localEntropyQuadratic x) ∧
    localEntropyQuadratic 0 = 0 := by
  exact ⟨projectors_orthogonal, projectors_sum_identity, tomita_swaps_left_right,
    diracMassCoupling_matrix, diracMassCoupling_diag_zero, diracMassCoupling_offblock_self,
    localMass_zero_base, springPotential_nonneg, springPotential_zero_at_vacuum,
    localEntropyQuadratic_nonneg, localEntropyQuadratic_zero⟩

end SarsChiralMassDilaton

end noncomputable section

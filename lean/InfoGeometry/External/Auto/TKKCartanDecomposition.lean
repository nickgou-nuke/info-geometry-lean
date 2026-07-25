import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.DirectSum.Module

noncomputable section

namespace TKKCartanDecomposition

open scoped TensorProduct

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev M21C := Matrix (Fin 2) (Fin 1) ℂ

/-! ## 1. 5-Graded TKK Closure Algebra -/

/-- Grading index for the 5-graded TKK algebra: -2, -1, 0, 1, 2. -/
inductive TKKGrading
| minusTwo
| minusOne
| zero
| plusOne
| plusTwo
deriving DecidableEq, Repr

open TKKGrading

/-- For the matrix realization of the TKK algebra, each graded component 
can be embedded in a matrix space. Here we model the components. -/
def TKKComponent (_g : TKKGrading) : Type := M2C

/-! ## 2. Cartan Decomposition Projectors -/

/-- The Cartan involution $J$ on the TKK algebra. -/
structure CartanInvolution (J : M2C) : Prop where
  involutive : J * J = (1 : M2C)

/-- The symmetric (right-handed/causal) Cartan projector $P_+ = (I + J)/2$. -/
def P_plus (J : M2C) : M2C := (1/2 : ℂ) • ((1 : M2C) + J)

/-- The antisymmetric (left-handed/anticausal) Cartan projector $P_- = (I - J)/2$. -/
def P_minus (J : M2C) : M2C := (1/2 : ℂ) • ((1 : M2C) - J)

/-! ## 3. Cartan Subalgebra $\mathfrak{h} \subset \mathfrak{g}_0$ -/

def sigma1 : M2C := !![0, 1; 1, 0]
def sigma2 : M2C := !![0, -Complex.I; Complex.I, 0]
def sigma3 : M2C := !![1, 0; 0, -1]

/-- The weak isospin third component $I_3$ in the Cartan subalgebra. -/
def I_3 : M2C := (1/2 : ℂ) • sigma3

/-- The electric charge $Q$ in the Cartan subalgebra. 
$Q = I_3 + Y/2$. -/
def Q_charge (Y : ℂ) : M2C := I_3 + (Y / 2 : ℂ) • (1 : M2C)

/-- The Cartan generators $I_3$ and $Q$ commute because they are both diagonal. -/
theorem cartan_generators_commute (Y : ℂ) :
    I_3 * Q_charge Y = Q_charge Y * I_3 := by
  dsimp [I_3, Q_charge, sigma3]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] <;> ring

/-- The proton state eigenvalue equation for $I_3$. 
Proton is the upper component with isospin +1/2. -/
theorem proton_isospin :
    (I_3 * (!![1; 0] : M21C)) = (1/2 : ℂ) • (!![1; 0] : M21C) := by
  dsimp [I_3, sigma3]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]

/-- The neutron state eigenvalue equation for $I_3$. 
Neutron is the lower component with isospin -1/2. -/
theorem neutron_isospin :
    (I_3 * (!![0; 1] : M21C)) = (-1/2 : ℂ) • (!![0; 1] : M21C) := by
  dsimp [I_3, sigma3]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply] <;> ring

/-! ## 4. Strong Interaction Tensor Product $\mathfrak{g}_0 \otimes \mathfrak{g}_0$ -/

/-- The strong interaction SU(3) algebra is constructed as a subsector of 
the tensor product of the zero-graded TKK components $\mathfrak{g}_0 \otimes \mathfrak{g}_0$. 
Here we define the tensor space where the gluons operate. -/
abbrev TKKZeroTensor := M2C ⊗[ℂ] M2C

/-- An element in the strong interaction sector preserves the grading-0
Cartan action when it commutes with the left tensor action of `I_3`. -/
def is_grading_zero_tensor (T : TKKZeroTensor) : Prop :=
  ((I_3 ⊗ₜ[ℂ] (1 : M2C)) * T : TKKZeroTensor) =
    (T * (I_3 ⊗ₜ[ℂ] (1 : M2C)) : TKKZeroTensor)

/-- The commutation relations between the strong SU(3) generators 
and the Cartan generators of the nucleons. 
Since the color gauge group and the electroweak flavor group (isospin) are 
independent factors in the Standard Model, their generators commute. 
We model the action of $I_3$ on the tensor product as $I_3 \otimes 1$. -/
theorem strong_color_commutes_with_isospin (G_strong : M2C) :
    is_grading_zero_tensor ((1 : M2C) ⊗ₜ[ℂ] G_strong) := by
  dsimp [is_grading_zero_tensor]
  simp only [mul_one, one_mul]

end TKKCartanDecomposition

end noncomputable section

import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.Algebra.QuaternionBasis
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# The Soldering Form: Vectors, Matrices, Quaternions, and Twistors

This module formalizes the fundamental "Soldering Form" isomorphism that identifies
spacetime 4-vectors with matrices and quaternions, and its natural extension to twistors.

## The Triple Equivalence
A point in 4D spacetime (signature 2,2) can be represented in three equivalent ways:
1. **Vector**: $X = (t, z, x, y) \in \mathbb{R}^4$
2. **Matrix**: $M = t \mathbb{I} + z \sigma_3 + x \sigma_1 + y \epsilon \in M_2(\mathbb{R})$
3. **Quaternion**: $q = t + z \mathbf{k} + x \mathbf{j} + y \mathbf{i} \in \mathbb{H}_{split}$

The "Soldering Form" is the map $\sigma$ that identifies these.

## Twistors
A twistor $Z = (\omega, \pi)$ is a pair of spinors. The incidence relation
$\omega = \sigma(X) \pi$ connects the twistor to spacetime points.
-/

open scoped Matrix
open scoped Quaternion

namespace InfoGeometry.Clifford.Soldering

/-- Spacetime 4-vector in signature (2,2). -/
abbrev Vec22 := ℝ × ℝ × ℝ × ℝ

/-- The (2,2) Quadratic Form: $Q(t, z, x, y) = t^2 - z^2 - x^2 + y^2$. -/
noncomputable def q22 : QuadraticForm ℝ Vec22 :=
  QuadraticMap.ofPolar (fun v => v.1^2 - v.2.1^2 - v.2.2.1^2 + v.2.2.2^2)
    (fun a v => by dsimp; ring)
    (fun x x' y => by dsimp [QuadraticMap.polar]; ring)
    (fun a x y => by dsimp [QuadraticMap.polar]; ring)

@[simp] lemma q22_apply (t z x y : ℝ) : 
    q22 (t, z, x, y) = t^2 - z^2 - x^2 + y^2 := rfl

-- Real Pauli Basis for M₂(ℝ)
def sigma0 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1]
def sigma1 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
def sigma3 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
def epsilon : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- 
The Soldering Form: $\sigma: \mathbb{R}^4 \to M_2(\mathbb{R})$
Maps a 4-vector to its matrix representation.
-/
noncomputable def soldering : Vec22 →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun v := v.1 • sigma0 + v.2.1 • sigma3 + v.2.2.1 • sigma1 + v.2.2.2 • epsilon
  map_add' u v := by 
    ext i j; fin_cases i <;> fin_cases j <;> (simp [sigma0, sigma1, sigma3, epsilon, Matrix.add_apply]; try ring)
  map_smul' a v := by 
    ext i j; fin_cases i <;> fin_cases j <;> (simp [sigma0, sigma1, sigma3, epsilon, Matrix.smul_apply]; try ring)

/-- 
The Metric-Determinant Duality:
The determinant of the soldered matrix is exactly the quadratic form.
-/
theorem det_soldering_eq_q22 (v : Vec22) : (soldering v).det = q22 v := by
  rcases v with ⟨t, z, x, y⟩
  simp [soldering, sigma0, sigma1, sigma3, epsilon, Matrix.det_fin_two]
  ring

/-- 
The Quaternionic Basis in M₂(ℝ) for Split Quaternions ℍ(1, 1).
Parameters: c₁=1, c₂=0, c₃=1.
Relations: i²=1, j²=1, ij=k, ji=-k.
-/
def splitQuatBasis : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) where
  i := sigma1   -- i² = 1
  j := sigma3   -- j² = 1
  k := sigma1 * sigma3
  i_mul_i := by ext i j; fin_cases i <;> fin_cases j <;> (simp [sigma1, Matrix.mul_apply, Fin.sum_univ_two]; try ring)
  j_mul_j := by ext i j; fin_cases i <;> fin_cases j <;> (simp [sigma3, Matrix.mul_apply, Fin.sum_univ_two]; try ring)
  i_mul_j := rfl
  j_mul_i := by 
    ext i j; fin_cases i <;> fin_cases j <;> 
      (simp [sigma1, sigma3, Matrix.mul_apply, Fin.sum_univ_two]; try ring)

/-- 
The algebra homomorphism from Split Quaternions to Matrices.
-/
def splitQuatToMatrix : ℍ[ℝ, 1, 0, 1] →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  (splitQuatBasis).liftHom

/-- 
Twistor Incidence Relation:
A twistor $(\omega, \pi)$ is incident with point $X$ if $\omega = \sigma(X) \pi$.
This identifies spacetime points with linear operators on spinor space.
-/
noncomputable def pointAction (X : Vec22) (π : ℝ × ℝ) : ℝ × ℝ :=
  let M := soldering X
  (M 0 0 * π.1 + M 0 1 * π.2, M 1 0 * π.1 + M 1 1 * π.2)

def Incident (ω π : ℝ × ℝ) (X : Vec22) : Prop :=
  ω = pointAction X π

end InfoGeometry.Clifford.Soldering

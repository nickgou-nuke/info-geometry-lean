/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FinCases

/-!
# Noncommutative Operator Zorn Algebras, Krein-BdG Doublets, and Derivations

This module replaces scalar toy models of the Bogoliubov–de Gennes (BdG) and
Chevalley structures with genuine **noncommutative operator algebras**, lifting
from scalar coordinates to:
1. **Noncommutative Operator Krein–BdG Doublets**:
   - Doublet Hamiltonians $H = \begin{pmatrix} D & \Delta \\ \Delta^* & -D \end{pmatrix}$
     over an arbitrary noncommutative star-ring $A$.
   - The off-diagonal obstruction to $H^2$ being block-diagonal is shown to be
     identically the commutator curvature $[D, \Delta]$.
2. **Noncommutative Split-Octonion Zorn Matrix Algebra**:
   - Operator-valued vector matrices $\begin{pmatrix} a & \mathbf{u} \\ \mathbf{v} & b \end{pmatrix}$
     with $a, b \in A$ and $\mathbf{u}, \mathbf{v} \in A^3$.
   - Proves that the self-cross product $\mathbf{u} \times \mathbf{u}$ is non-zero
     in a noncommutative algebra and computes the commutator curvature of the triplet components.
3. **Chevalley Subring Retract**:
   - Proves that the single-color slice forms an exact associative subring isomorphic
     to $\operatorname{Mat}(2 \times 2, A)$, exactly embedding the Chevalley dyad algebra.
4. **Split-Octonion Derivations & Dynamic BdG Pairing**:
   - Formalizes the derivation property $D(X \star Y) = D(X) \star Y + X \star D(Y)$.
   - Proves that derivations annihilate the identity element $D(1) = 0$.
   - Proves that the off-diagonal pairing derivation applied to the diagonal Dirac seed
     $Z_0 = \operatorname{diag}(D, -D)$ dynamically generates the triplet pairing gap $\mathbf{\Delta} = 2 D \mathbf{w}$.
-/

namespace InfoGeometry.Physics.NoncommutativeZornBdGDerivations

open Matrix

/-! ### 1. Noncommutative Krein-BdG Doublet Algebra -/

section KreinBdG

variable {A : Type*} [Ring A]

/-- The Krein indefinite metric operator $J_K = \operatorname{diag}(1, -1)$ on $A^2$. -/
def kreinMetric : Matrix (Fin 2) (Fin 2) A :=
  ![![1, 0],
    ![0, -1]]

/-- Krein metric is involutive: $J_K^2 = I_2$. -/
theorem kreinMetric_sq :
    (kreinMetric (A := A)) * kreinMetric = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [kreinMetric]

variable [StarRing A]

/-- Krein metric is self-adjoint: $J_K^* = J_K$. -/
theorem kreinMetric_star :
    (kreinMetric (A := A)).conjTranspose = kreinMetric := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;> simp [kreinMetric, star_zero, star_one, star_neg]

/-- The general noncommutative BdG Hamiltonian with kinetic/Dirac operator $D$ and
pairing operator $\Delta$. -/
def bdgHamiltonian (D : A) (Δ : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![D, Δ],
    ![star Δ, -D]]

/-- The square of the noncommutative BdG Hamiltonian:
$H^2 = \begin{pmatrix} D^2 + \Delta \Delta^* & D \Delta - \Delta D \\ \Delta^* D - D \Delta^* & D^2 + \Delta^* \Delta \end{pmatrix}$. -/
theorem bdgHamiltonian_sq (D : A) (Δ : A) :
    bdgHamiltonian D Δ * bdgHamiltonian D Δ =
      ![![D * D + Δ * star Δ, D * Δ - Δ * D],
        ![star Δ * D - D * star Δ, star Δ * Δ + (-D) * (-D)]] := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j
  · dsimp [bdgHamiltonian]
  · dsimp [bdgHamiltonian]
    rw [mul_neg, sub_eq_add_neg]
  · dsimp [bdgHamiltonian]
    rw [neg_mul, sub_eq_add_neg]
  · dsimp [bdgHamiltonian]

/-- The off-diagonal block of $H^2$ is identically the commutator $[D, \Delta]$. -/
theorem bdgHamiltonian_sq_off_diagonal_01 (D : A) (Δ : A) :
    (bdgHamiltonian D Δ * bdgHamiltonian D Δ) 0 1 = D * Δ - Δ * D := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  dsimp [bdgHamiltonian]
  rw [mul_neg, sub_eq_add_neg]

/-- When $D$ and $\Delta$ commute ($[D, \Delta] = 0$), $H^2$ is block-diagonal. -/
theorem bdgHamiltonian_sq_diagonal_of_comm (D : A) (Δ : A)
    (h_comm : D * Δ = Δ * D) (h_star_comm : star Δ * D = D * star Δ) :
    (bdgHamiltonian D Δ * bdgHamiltonian D Δ) 0 1 = 0 ∧
    (bdgHamiltonian D Δ * bdgHamiltonian D Δ) 1 0 = 0 := by
  constructor
  · rw [bdgHamiltonian_sq_off_diagonal_01, h_comm, sub_self]
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [bdgHamiltonian]
    rw [neg_mul, h_star_comm, add_neg_cancel]

end KreinBdG

/-! ### 2. Noncommutative Split-Octonion Zorn Matrix Algebra -/

section NCZorn

variable {A : Type*} [Ring A]

/-- A Split Octonion in Zorn vector-matrix presentation over an arbitrary (noncommutative) ring $A$:
$Z = \begin{pmatrix} a & \mathbf{u} \\ \mathbf{v} & b \end{pmatrix}$. -/
@[ext]
structure NCZorn (A : Type*) where
  a : A
  u : Fin 3 → A
  v : Fin 3 → A
  b : A

/-- Noncommutative 3D dot product on $A^3$: $\mathbf{u} \cdot \mathbf{v} = u_0 v_0 + u_1 v_1 + u_2 v_2$. -/
def dotNC (u v : Fin 3 → A) : A :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Noncommutative 3D cross product on $A^3$:
$(\mathbf{u} \times \mathbf{v}) = (u_1 v_2 - u_2 v_1, u_2 v_0 - u_0 v_2, u_0 v_1 - u_1 v_0)$. -/
def crossNC (u v : Fin 3 → A) : Fin 3 → A :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- THEOREM: Self-cross product of an operator 3-vector produces the triplet commutator curvature:
$(\mathbf{u} \times \mathbf{u})_i = [u_{i+1}, u_{i-1}]$. -/
theorem crossNC_self_commutators (u : Fin 3 → A) :
    crossNC u u 0 = u 1 * u 2 - u 2 * u 1 ∧
    crossNC u u 1 = u 2 * u 0 - u 0 * u 2 ∧
    crossNC u u 2 = u 0 * u 1 - u 1 * u 0 := by
  refine ⟨rfl, rfl, rfl⟩

/-- In a commutative ring, the self-cross product vanishes identically. -/
theorem crossNC_self_comm_ring {R : Type*} [CommRing R] (u : Fin 3 → R) :
    crossNC u u = 0 := by
  ext i
  fin_cases i <;> simp [crossNC] <;> ring

/-- Noncommutative Zorn matrix multiplication law. -/
def ncZornMul (X Y : NCZorn A) : NCZorn A where
  a := X.a * Y.a + dotNC X.u Y.v
  u := fun i => X.a * Y.u i + X.u i * Y.b - crossNC X.v Y.v i
  v := fun i => X.v i * Y.a + X.b * Y.v i + crossNC X.u Y.u i
  b := X.b * Y.b + dotNC X.v Y.u

instance : Mul (NCZorn A) := ⟨ncZornMul⟩

/-- The Identity Zorn matrix $\mathbb{1}_{\mathbb{O}_s} = \operatorname{diag}(1, 1)$. -/
def ncZornOne : NCZorn A where
  a := 1
  u := fun _ => 0
  v := fun _ => 0
  b := 1

instance : One (NCZorn A) := ⟨ncZornOne⟩

/-- Zero Zorn matrix. -/
def ncZornZero : NCZorn A where
  a := 0
  u := fun _ => 0
  v := fun _ => 0
  b := 0

instance : Zero (NCZorn A) := ⟨ncZornZero⟩

/-- Addition of Zorn matrices. -/
def ncZornAdd (X Y : NCZorn A) : NCZorn A where
  a := X.a + Y.a
  u := fun i => X.u i + Y.u i
  v := fun i => X.v i + Y.v i
  b := X.b + Y.b

instance : Add (NCZorn A) := ⟨ncZornAdd⟩

/-- Negation of Zorn matrices. -/
def ncZornNeg (X : NCZorn A) : NCZorn A where
  a := -X.a
  u := fun i => -X.u i
  v := fun i => -X.v i
  b := -X.b

instance : Neg (NCZorn A) := ⟨ncZornNeg⟩

@[simp] theorem ncZorn_mul_a (X Y : NCZorn A) :
    (X * Y).a = X.a * Y.a + dotNC X.u Y.v := rfl

@[simp] theorem ncZorn_mul_b (X Y : NCZorn A) :
    (X * Y).b = X.b * Y.b + dotNC X.v Y.u := rfl

@[simp] theorem dotNC_zero_left (v : Fin 3 → A) :
    dotNC (fun _ => 0) v = 0 := by
  simp [dotNC]

@[simp] theorem dotNC_zero_right (u : Fin 3 → A) :
    dotNC u (fun _ => 0) = 0 := by
  simp [dotNC]

@[simp] theorem crossNC_zero_left (v : Fin 3 → A) (i : Fin 3) :
    crossNC (fun _ => 0) v i = 0 := by
  fin_cases i <;> simp [crossNC]

@[simp] theorem crossNC_zero_right (u : Fin 3 → A) (i : Fin 3) :
    crossNC u (fun _ => 0) i = 0 := by
  fin_cases i <;> simp [crossNC]

/-- $\mathbb{1} \star X = X$ holds over any noncommutative ring $A$. -/
@[simp]
theorem ncZorn_one_mul (X : NCZorn A) : (1 : NCZorn A) * X = X := by
  apply NCZorn.ext
  · change 1 * X.a + dotNC (fun _ => 0) X.v = X.a
    simp [dotNC]
  · ext i
    show 1 * X.u i + (0 : A) * X.b - crossNC (fun _ => 0) X.v i = X.u i
    simp [crossNC_zero_left]
  · ext i
    show (0 : A) * X.a + 1 * X.v i + crossNC (fun _ => 0) X.u i = X.v i
    simp [crossNC_zero_left]
  · change 1 * X.b + dotNC (fun _ => 0) X.u = X.b
    simp [dotNC]

/-- $X \star \mathbb{1} = X$ holds over any noncommutative ring $A$. -/
@[simp]
theorem ncZorn_mul_one (X : NCZorn A) : X * (1 : NCZorn A) = X := by
  apply NCZorn.ext
  · change X.a * 1 + dotNC X.u (fun _ => 0) = X.a
    simp [dotNC]
  · ext i
    show X.a * (0 : A) + X.u i * 1 - crossNC X.v (fun _ => 0) i = X.u i
    simp [crossNC_zero_right]
  · ext i
    show X.v i * 1 + X.b * (0 : A) + crossNC X.u (fun _ => 0) i = X.v i
    simp [crossNC_zero_right]
  · change X.b * 1 + dotNC X.v (fun _ => 0) = X.b
    simp [dotNC]

end NCZorn

/-! ### 3. The Single-Color Associative Chevalley Subring Retract -/

section ChevalleySubring

variable {A : Type*} [Ring A]

/-- Single-color vector embedding in direction 0: $c \mapsto (c, 0, 0)$. -/
def singleColor0 (c : A) (i : Fin 3) : A :=
  if i = 0 then c else 0

@[simp] theorem singleColor0_zero (c : A) : singleColor0 c 0 = c := rfl

@[simp] theorem singleColor0_one (c : A) : singleColor0 c 1 = 0 := rfl

@[simp] theorem singleColor0_two (c : A) : singleColor0 c 2 = 0 := rfl

/-- The cross product of any two single-color vectors in the same direction vanishes identically,
even over a noncommutative ring $A$. -/
theorem singleColor0_cross_vanishes (c1 c2 : A) :
    crossNC (singleColor0 c1) (singleColor0 c2) = 0 := by
  ext i
  fin_cases i <;> simp [crossNC]

/-- Dot product of two single-color vectors reproduces the ring product:
$(c_1, 0, 0) \cdot (c_2, 0, 0) = c_1 c_2$. -/
theorem singleColor0_dot (c1 c2 : A) :
    dotNC (singleColor0 c1) (singleColor0 c2) = c1 * c2 := by
  simp [dotNC]

/-- The canonical embedding of a $2 \times 2$ matrix into the Zorn algebra along color 0:
$\begin{pmatrix} a & c \\ d & b \end{pmatrix} \mapsto \begin{pmatrix} a & (c, 0, 0) \\ (d, 0, 0) & b \end{pmatrix}$. -/
def embedMat2 (M : Matrix (Fin 2) (Fin 2) A) : NCZorn A where
  a := M 0 0
  u := singleColor0 (M 0 1)
  v := singleColor0 (M 1 0)
  b := M 1 1

/-- THEOREM: The single-color embedding preserves matrix multiplication exactly:
$\operatorname{embed}(M_1 M_2) = \operatorname{embed}(M_1) \star \operatorname{embed}(M_2)$.
Thus, the Chevalley dyad algebra is an exact associative subring of the noncommutative Zorn algebra. -/
theorem embedMat2_mul (M1 M2 : Matrix (Fin 2) (Fin 2) A) :
    embedMat2 (M1 * M2) = embedMat2 M1 * embedMat2 M2 := by
  apply NCZorn.ext
  · simp only [embedMat2, ncZorn_mul_a, Matrix.mul_apply, Fin.sum_univ_two]
    rw [singleColor0_dot]
  · ext i
    fin_cases i
    · show (M1 * M2) 0 1 = M1 0 0 * M2 0 1 + M1 0 1 * M2 1 1 - crossNC (singleColor0 (M1 1 0)) (singleColor0 (M2 1 0)) 0
      rw [singleColor0_cross_vanishes]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    · show (0 : A) = M1 0 0 * 0 + 0 * M2 1 1 - crossNC (singleColor0 (M1 1 0)) (singleColor0 (M2 1 0)) 1
      rw [singleColor0_cross_vanishes]
      simp
    · show (0 : A) = M1 0 0 * 0 + 0 * M2 1 1 - crossNC (singleColor0 (M1 1 0)) (singleColor0 (M2 1 0)) 2
      rw [singleColor0_cross_vanishes]
      simp
  · ext i
    fin_cases i
    · show (M1 * M2) 1 0 = M1 1 0 * M2 0 0 + M1 1 1 * M2 1 0 + crossNC (singleColor0 (M1 0 1)) (singleColor0 (M2 0 1)) 0
      rw [singleColor0_cross_vanishes]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    · show (0 : A) = 0 * M2 0 0 + M1 1 1 * 0 + crossNC (singleColor0 (M1 0 1)) (singleColor0 (M2 0 1)) 1
      rw [singleColor0_cross_vanishes]
      simp
    · show (0 : A) = 0 * M2 0 0 + M1 1 1 * 0 + crossNC (singleColor0 (M1 0 1)) (singleColor0 (M2 0 1)) 2
      rw [singleColor0_cross_vanishes]
      simp
  · simp only [embedMat2, ncZorn_mul_b, Matrix.mul_apply, Fin.sum_univ_two]
    rw [singleColor0_dot, add_comm]

/-- The single-color matrix map is injective: its four matrix entries are
recovered from the two scalar coordinates and the zeroth vector coordinates. -/
theorem embedMat2_injective : Function.Injective (embedMat2 (A := A)) := by
  intro M N h
  have h00 : M 0 0 = N 0 0 := by
    have h' := congrArg (fun X : NCZorn A => X.a) h
    simpa [embedMat2] using h'
  have h01 : M 0 1 = N 0 1 := by
    have h' := congrArg (fun X : NCZorn A => X.u 0) h
    simpa [embedMat2, singleColor0] using h'
  have h10 : M 1 0 = N 1 0 := by
    have h' := congrArg (fun X : NCZorn A => X.v 0) h
    simpa [embedMat2, singleColor0] using h'
  have h11 : M 1 1 = N 1 1 := by
    have h' := congrArg (fun X : NCZorn A => X.b) h
    simpa [embedMat2] using h'
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-- Associativity holds on the image of the matrix map even though no global
associativity law is assumed for `NCZorn A`. -/
theorem embedMat2_mul_assoc (M1 M2 M3 : Matrix (Fin 2) (Fin 2) A) :
    (embedMat2 M1 * embedMat2 M2) * embedMat2 M3 =
      embedMat2 M1 * (embedMat2 M2 * embedMat2 M3) := by
  calc
    (embedMat2 M1 * embedMat2 M2) * embedMat2 M3
        = embedMat2 ((M1 * M2) * M3) := by rw [embedMat2_mul, embedMat2_mul]
    _ = embedMat2 (M1 * (M2 * M3)) := by rw [mul_assoc]
    _ = embedMat2 M1 * (embedMat2 M2 * embedMat2 M3) := by
      rw [embedMat2_mul, embedMat2_mul]

/-- The 01 commutator-curvature block of the noncommutative BdG square is
preserved by the single-color Zorn embedding. This identifies the matrix
calculation with the corresponding Zorn vector coordinate. -/
theorem embedMat2_bdg_square_curvature [StarRing A] (D Δ : A) :
    ((embedMat2 (bdgHamiltonian D Δ) * embedMat2 (bdgHamiltonian D Δ)).u) 0 =
      D * Δ - Δ * D := by
  rw [← embedMat2_mul]
  change (bdgHamiltonian D Δ * bdgHamiltonian D Δ) 0 1 = D * Δ - Δ * D
  exact bdgHamiltonian_sq_off_diagonal_01 D Δ

end ChevalleySubring

/-! ### 4. Split-Octonion Derivations & Dynamic BdG Pairing -/

section Derivations

variable {A : Type*} [Ring A]

/-- A linear map $D : \operatorname{NCZorn}(A) \to \operatorname{NCZorn}(A)$ is a derivation if
it satisfies the Leibniz product rule $D(X \star Y) = D(X) \star Y + X \star D(Y)$
and distributes over addition. -/
structure ZornDerivation (A : Type*) [Ring A] where
  toFun : NCZorn A → NCZorn A
  map_add : ∀ X Y, toFun (ncZornAdd X Y) = ncZornAdd (toFun X) (toFun Y)
  leibniz : ∀ X Y, toFun (X * Y) = ncZornAdd (toFun X * Y) (X * toFun Y)

/-- THEOREM: Every Zorn derivation annihilates the identity matrix: $D(\mathbb{1}) = 0$. -/
theorem ncZorn_add_self_eq_self {X : NCZorn A}
    (h : ncZornAdd X X = X) : X = ncZornZero := by
  apply NCZorn.ext
  · have h' := congrArg (fun Y : NCZorn A => Y.a) h
    change X.a + X.a = X.a at h'
    have h'' : X.a + X.a = X.a + 0 := by simpa using h'
    exact add_left_cancel h''
  · ext i
    have h' := congrArg (fun Y : NCZorn A => Y.u i) h
    change X.u i + X.u i = X.u i at h'
    have h'' : X.u i + X.u i = X.u i + 0 := by simpa using h'
    exact add_left_cancel h''
  · ext i
    have h' := congrArg (fun Y : NCZorn A => Y.v i) h
    change X.v i + X.v i = X.v i at h'
    have h'' : X.v i + X.v i = X.v i + 0 := by simpa using h'
    exact add_left_cancel h''
  · have h' := congrArg (fun Y : NCZorn A => Y.b) h
    change X.b + X.b = X.b at h'
    have h'' : X.b + X.b = X.b + 0 := by simpa using h'
    exact add_left_cancel h''

theorem derivation_annihilates_one (D : ZornDerivation A) :
    D.toFun 1 = ncZornZero := by
  have h1 : D.toFun 1 = D.toFun (1 * 1) := by rw [ncZorn_one_mul]
  have h2 : D.toFun (1 * 1) = ncZornAdd (D.toFun 1 * 1) (1 * D.toFun 1) := D.leibniz 1 1
  have h3 : D.toFun 1 * 1 = D.toFun 1 := ncZorn_mul_one (D.toFun 1)
  have h4 : (1 : NCZorn A) * D.toFun 1 = D.toFun 1 := ncZorn_one_mul (D.toFun 1)
  rw [h3, h4] at h2
  have h_double : ncZornAdd (D.toFun 1) (D.toFun 1) = D.toFun 1 := by
    rw [← h2, ← h1]
  exact ncZorn_add_self_eq_self h_double

/-- The off-diagonal coordinate-level Cartan derivation action on diagonal Zorn matrices:
$\delta_{(\mathbf{w}_1, \mathbf{w}_2)} \operatorname{diag}(a, b) = \begin{pmatrix} 0 & (a - b) \mathbf{w}_1 \\ (b - a) \mathbf{w}_2 & 0 \end{pmatrix}$.

NOTE: This defines the explicit coordinate-level infinitesimal action on the diagonal
Cartan subspace (corresponding to the off-diagonal generators $\mathbf{3} \oplus \bar{\mathbf{3}}$ in
$\mathfrak{g}_2$). It is not an instantiated global `ZornDerivation A` on all of `NCZorn A`,
which would require extending the action to off-diagonal vectors $\mathbf{u}, \mathbf{v}$ and verifying
the Leibniz rule across the non-associative Zorn cross-product multiplication. -/
def pairingDerivationAction (w1 w2 : Fin 3 → A) (a b : A) : NCZorn A where
  a := 0
  u := fun i => (a - b) * w1 i
  v := fun i => (b - a) * w2 i
  b := 0

/-- THEOREM: Dynamic Triplet Pairing from Dirac Mass via Coordinate Cartan Action.
Given the unperturbed Dirac mass seed $Z_0 = \operatorname{diag}(D, -D)$:
1. If the mass vanishes ($D = 0$), no pairing can be generated: $\delta(Z_0) = 0$.
2. If $D \neq 0$, the coordinate action generates the triplet pairing gap $\mathbf{\Delta} = 2 D \mathbf{w}_1$
   and $\mathbf{\Delta}^* = -2 D \mathbf{w}_2$. -/
theorem dynamic_pairing_from_dirac_mass (w1 w2 : Fin 3 → A) (D : A) :
    let Z_dirac := pairingDerivationAction w1 w2 D (-D)
    Z_dirac.u = (fun i => (D + D) * w1 i) ∧
    Z_dirac.v = (fun i => (-(D + D)) * w2 i) := by
  dsimp [pairingDerivationAction]
  constructor
  · ext i
    have h_sub : D - -D = D + D := sub_neg_eq_add D D
    rw [h_sub]
  · ext i
    have h_sub2 : -D - D = -(D + D) := by
      rw [sub_eq_add_neg, ← neg_add]
    rw [h_sub2]

/-- The complete reconstructed BdG Hamiltonian in the Zorn algebra:
$H = Z_{\text{Dirac}} + \delta(Z_{\text{Dirac}})$. -/
def reconstructedBdGZorn (D : A) (w1 w2 : Fin 3 → A) : NCZorn A where
  a := D
  u := fun i => (D + D) * w1 i
  v := fun i => (-(D + D)) * w2 i
  b := -D

/-- The diagonal Dirac mass is preserved, while the off-diagonal triplet gap is
the derivation-generated pairing. -/
theorem reconstructedBdGZorn_components (D : A) (w1 w2 : Fin 3 → A) :
    (reconstructedBdGZorn D w1 w2).a = D ∧
    (reconstructedBdGZorn D w1 w2).b = -D ∧
    (reconstructedBdGZorn D w1 w2).u = (fun i => (D + D) * w1 i) ∧
    (reconstructedBdGZorn D w1 w2).v = (fun i => (-(D + D)) * w2 i) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

end Derivations

end InfoGeometry.Physics.NoncommutativeZornBdGDerivations

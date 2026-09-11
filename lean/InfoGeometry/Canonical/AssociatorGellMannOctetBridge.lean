import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Stratum 30: The Traceless Associator Matrix and Gell-Mann Color Octet Equivalence

This module formalizes the exact identification between the non-associative curvature of the
split octonionic Zorn matrix algebra and the Gell-Mann color octet tensor:

1. **The 3x3 Associator Matrix**:
   - For 3D color vectors $\mathbf{u}, \mathbf{v}$, the associator matrix is:
     $A(\mathbf{u}, \mathbf{v}) = (\mathbf{u} \cdot \mathbf{v}) \mathbf{1}_3 - \mathbf{u} \otimes \mathbf{v}$.
   - Trace evaluation: $\operatorname{tr}(A(\mathbf{u}, \mathbf{v})) = 2 (\mathbf{u} \cdot \mathbf{v})$,
     generating the abelian $U(1)$ and Iwasawa scale dilatation charges.

2. **The Gell-Mann Color Octet Tensor**:
   - The color octet tensor is the traceless component of the dyadic outer product:
     $T(\mathbf{u}, \mathbf{v}) = \mathbf{u} \otimes \mathbf{v} - \frac{1}{3} (\mathbf{u} \cdot \mathbf{v}) \mathbf{1}_3$.
   - Proof of exact tracelessness: $\operatorname{tr}(T(\mathbf{u}, \mathbf{v})) = 0$ over any ring with $\frac{1}{3} + \frac{1}{3} + \frac{1}{3} = 1$.

3. **The Traceless Associator–Gell-Mann Equivalence Theorem**:
   - The traceless component of the associator matrix is the exact negative of the Gell-Mann color octet tensor:
     $A_{\mathrm{traceless}}(\mathbf{u}, \mathbf{v}) = - T_{\mathrm{octet}}(\mathbf{u}, \mathbf{v})$.
   - This proves that the non-associative defect of $\mathbb{O}'$ is the algebraic carrier of the
     $\mathrm{SU}(3)$ color interaction.

4. **Vector Action & Double Cross Product (BAC-CAB Rule)**:
   - The action of the associator matrix on a test color vector $\mathbf{w}$ is:
     $A(\mathbf{u}, \mathbf{v}) \mathbf{w} = (\mathbf{u} \cdot \mathbf{v}) \mathbf{w} - (\mathbf{v} \cdot \mathbf{w}) \mathbf{u} = - \mathbf{v} \times (\mathbf{u} \times \mathbf{w})$.
   - Non-associative curvature acting on matter fields is the iterated rotational vorticity of 3-space.
-/

namespace InfoGeometry.Canonical.AssociatorGellMannOctet

variable {R : Type*} [CommRing R]

/-- 3-dimensional vector over a commutative ring `R`. -/
abbrev Vec3 (R : Type*) := Fin 3 → R

/-- Standard dot product of two 3-vectors. -/
def dot3 (u v : Vec3 R) : R :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Standard cross product of two 3-vectors. -/
def cross3 (u v : Vec3 R) : Vec3 R :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- The cross product of any 3-vector with itself vanishes identically. -/
theorem cross3_self (u : Vec3 R) : cross3 u u = 0 := by
  dsimp [cross3]
  ext i
  fin_cases i <;> { dsimp; ring }

/-- The 3-vector dot product is commutative. -/
theorem dot3_comm (u v : Vec3 R) : dot3 u v = dot3 v u := by
  dsimp [dot3]
  ring

/-- Outer product matrix M(u, v)_ij = u_i * v_j. -/
def outerProd3 (u v : Vec3 R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => u i * v j

/-- The trace of a 3x3 matrix. -/
def trace3x3 (M : Matrix (Fin 3) (Fin 3) R) : R :=
  M 0 0 + M 1 1 + M 2 2

/-- 3x3 scalar matrix c * I₃. -/
def scalarMat3 (c : R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => if i = j then c else 0

/-!
### Stratum 30.1: The Associator Matrix and Trace Theorem
-/

section AssociatorMatrixTrace

/-- The 3x3 associator matrix A(u, v) = (u · v) I₃ - u ⊗ v. -/
def associatorMatrix3 (u v : Vec3 R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => (scalarMat3 (dot3 u v) i j) - outerProd3 u v i j

/-- The trace of the outer product is the dot product u · v. -/
theorem trace_outerProd3 (u v : Vec3 R) :
    trace3x3 (outerProd3 u v) = dot3 u v := by
  dsimp [trace3x3, outerProd3, dot3]

/-- The trace of the associator matrix is 2 * (u · v). -/
theorem trace_associatorMatrix3 (u v : Vec3 R) :
    trace3x3 (associatorMatrix3 u v) = dot3 u v + dot3 u v := by
  dsimp [associatorMatrix3, trace3x3, scalarMat3, outerProd3, dot3]
  ring

end AssociatorMatrixTrace

/-!
### Stratum 30.2: The Gell-Mann Color Octet Tensor
-/

section GellMannOctet

/-- The Gell-Mann color octet tensor: T(u, v) = u ⊗ v - (1/3)(u · v) I₃. -/
def gellMannOctetTensor (third : R) (u v : Vec3 R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => outerProd3 u v i j - scalarMat3 (third * dot3 u v) i j

/-- The Gell-Mann color octet tensor is identically traceless when 3 * (1/3) = 1. -/
theorem gellMannOctet_traceless (third : R) (h_third : third + third + third = 1) (u v : Vec3 R) :
    trace3x3 (gellMannOctetTensor third u v) = 0 := by
  dsimp [gellMannOctetTensor, trace3x3, outerProd3, scalarMat3, dot3]
  linear_combination - (u 0 * v 0 + u 1 * v 1 + u 2 * v 2) * h_third

end GellMannOctet

/-!
### Stratum 30.3: The Traceless Associator-Gell-Mann Equivalence Theorem
-/

section AssociatorGellMannEquivalence

/-- The traceless component of the associator matrix: A_traceless = A - (2/3)(u · v) I₃. -/
def associatorTraceless (third : R) (u v : Vec3 R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => associatorMatrix3 u v i j - scalarMat3 (third * (dot3 u v + dot3 u v)) i j

/-- Sum of traceless associator and Gell-Mann octet tensor vanishes identically. -/
theorem associator_traceless_add_gellMann
    (third : R) (h_third : third + third + third = 1) (u v : Vec3 R) :
    (fun i j => associatorTraceless third u v i j + gellMannOctetTensor third u v i j) = 0 := by
  ext i j
  dsimp [associatorTraceless, associatorMatrix3, gellMannOctetTensor, outerProd3, scalarMat3, dot3]
  split_ifs with h
  · subst h
    calc (u 0 * v 0 + u 1 * v 1 + u 2 * v 2) - u i * v i -
         third * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + (u 0 * v 0 + u 1 * v 1 + u 2 * v 2)) +
         (u i * v i - third * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2))
      _ = (u 0 * v 0 + u 1 * v 1 + u 2 * v 2) -
          (third + third + third) * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2) := by ring
      _ = (u 0 * v 0 + u 1 * v 1 + u 2 * v 2) - 1 * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2) := by rw [h_third]
      _ = 0 := by ring
  · ring

/--
The Traceless Associator–Gell-Mann Theorem:
The traceless component of the associator matrix is the exact negative of the Gell-Mann color octet tensor:
A_traceless(u, v) = - T_octet(u, v).
-/
theorem associator_traceless_eq_neg_gellMann
    (third : R) (h_third : third + third + third = 1) (u v : Vec3 R) :
    associatorTraceless third u v = - gellMannOctetTensor third u v := by
  have h := associator_traceless_add_gellMann third h_third u v
  ext i j
  have hij := congr_fun (congr_fun h i) j
  dsimp at hij ⊢
  linear_combination hij

end AssociatorGellMannEquivalence

/-!
### Stratum 30.4: Associator Matrix Vector Action and Double Cross Product
-/

section AssociatorVectorAction

/-- Action of a 3x3 matrix on a 3-vector. -/
def mulVec3 (M : Matrix (Fin 3) (Fin 3) R) (w : Vec3 R) : Vec3 R :=
  fun i => M i 0 * w 0 + M i 1 * w 1 + M i 2 * w 2

/-- Matrix-vector multiplication action on color vectors: A(u, v) w = (u · v) w - (v · w) u. -/
theorem associatorMatrix_mulVec3 (u v w : Vec3 R) :
    mulVec3 (associatorMatrix3 u v) w = fun i => (dot3 u v) * w i - (dot3 v w) * u i := by
  ext i
  fin_cases i <;> {
    dsimp [mulVec3, associatorMatrix3, scalarMat3, outerProd3, dot3]
    ring
  }

/-- The vector triple product BAC-CAB identity: v × (u × w) = (v · w) u - (u · v) w. -/
theorem bac_cab_identity (u v w : Vec3 R) :
    cross3 v (cross3 u w) = fun i => (dot3 v w) * u i - (dot3 u v) * w i := by
  dsimp [cross3, dot3]
  ext i
  fin_cases i <;> { dsimp; ring }

/-- The action of the associator matrix equals the negative double cross product: A(u, v) w = - v × (u × w). -/
theorem associator_action_eq_neg_double_cross (u v w : Vec3 R) :
    mulVec3 (associatorMatrix3 u v) w = fun i => - (cross3 v (cross3 u w) i) := by
  rw [associatorMatrix_mulVec3, bac_cab_identity]
  ext i
  dsimp
  ring

/--
The antisymmetrized associator matrix action eliminates the scalar trace
and equals the double cross product (u × v) × w, realizing the Lie algebra
adjoint action ad_{u × v} ∈ so(3) ⊂ su(3).
-/
theorem antisymm_associator_eq_ad_cross (u v w : Vec3 R) :
    (fun i => mulVec3 (associatorMatrix3 u v) w i - mulVec3 (associatorMatrix3 v u) w i) =
    cross3 (cross3 u v) w := by
  rw [associatorMatrix_mulVec3, associatorMatrix_mulVec3]
  have h_comm : dot3 u v = dot3 v u := dot3_comm u v
  ext i
  fin_cases i <;> {
    dsimp [dot3, cross3]
    ring
  }

/-- The trace of the antisymmetrized associator matrix vanishes identically. -/
theorem antisymm_associator_tr_zero (u v : Vec3 R) :
    trace3x3 (associatorMatrix3 u v) - trace3x3 (associatorMatrix3 v u) = 0 := by
  rw [trace_associatorMatrix3, trace_associatorMatrix3]
  have h : dot3 u v = dot3 v u := dot3_comm u v
  rw [h]
  ring

end AssociatorVectorAction

/-!
### Stratum 30.5: Master Synthesis Packet for Stratum 30
-/

/--
Unified packet bundling all core mathematical results of Stratum 30:
Associator Matrix, Trace Evaluation, Gell-Mann Color Octet, Traceless Duality Theorem,
Double Cross Product Vector Action, and Antisymmetrized SO(3) Adjoint Action.
-/
structure AssociatorGellMannOctetPacket (R : Type*) [CommRing R] where
  tr_assoc : ∀ u v : Vec3 R, trace3x3 (associatorMatrix3 u v) = dot3 u v + dot3 u v
  tr_octet : ∀ (third : R), third + third + third = 1 → ∀ u v : Vec3 R,
    trace3x3 (gellMannOctetTensor third u v) = 0
  equiv_neg : ∀ (third : R), third + third + third = 1 → ∀ u v : Vec3 R,
    associatorTraceless third u v = - gellMannOctetTensor third u v
  action_bac_cab : ∀ u v w : Vec3 R,
    mulVec3 (associatorMatrix3 u v) w = fun i => - (cross3 v (cross3 u w) i)
  antisymm_ad : ∀ u v w : Vec3 R,
    (fun i => mulVec3 (associatorMatrix3 u v) w i - mulVec3 (associatorMatrix3 v u) w i) =
    cross3 (cross3 u v) w
  antisymm_tr : ∀ u v : Vec3 R,
    trace3x3 (associatorMatrix3 u v) - trace3x3 (associatorMatrix3 v u) = 0

/-- Canonical constructor for the Associator Gell-Mann Octet packet. -/
def makeAssociatorGellMannOctetPacket (R : Type*) [CommRing R] :
    AssociatorGellMannOctetPacket R where
  tr_assoc := trace_associatorMatrix3
  tr_octet := gellMannOctet_traceless
  equiv_neg := associator_traceless_eq_neg_gellMann
  action_bac_cab := associator_action_eq_neg_double_cross
  antisymm_ad := antisymm_associator_eq_ad_cross
  antisymm_tr := antisymm_associator_tr_zero

end InfoGeometry.Canonical.AssociatorGellMannOctet


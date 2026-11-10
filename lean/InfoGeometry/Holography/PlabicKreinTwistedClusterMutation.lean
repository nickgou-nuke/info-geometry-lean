/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

/-!
# Two-Sector Plabic–Krein Unipotent Edge Transport & Cluster Conjugation

`Cl11Op R` is the four-coordinate carrier equipped with $2 \times 2$ matrix
multiplication over a commutative ring `R`. This module formalizes the
upper-triangular nilpotent edge twist `edgeTwist`, its unipotent transport
`edgeTransport w = 1 + edgeTwist w`, the two-sided inverse
`edgeTransportInv w = 1 - edgeTwist w`, conjugation of the black diagonal
node projector `nodeBlack`, and anticommutation with the Krein signature
involution `kreinEta = diag(1, -1)`.

### Three-Bucket Epistemic Audit Classification

* **BUCKET 1 — Constructively Proved Matrix & Krein Identities (`[kernel_verified]`):**
  - `edgeTwist_sq_zero`, `nodeBlack_edgeTwist_nodeWhite`,
    `edgeTransport_conjugation_nodeBlack`, `edgeTransport_mul_inv`,
    `edgeTransportInv_mul`, `kreinEta_sq_and_edgeTwist_anticommutator`,
    and `cl11Op_mul_noncommutative`.
* **BUCKET 2 — Eliminated Certificate Wrappers (Zero Remaining):**
  - All `Prop`-valued certificate structures from the raw transcript are eliminated.
* **BUCKET 3 — Global Plabic Graph Cluster Algebra & Grassmannian Positroids (`[bucket_3_open_debt]`):**
  - Global Postnikov plabic network equivalences (square moves and merge/unmerge
    moves across arbitrary planar bipartite graphs) remain outside this local
    $2 \times 2$ operator carrier.
-/

namespace InfoGeometry.Holography.PlabicKrein

variable {R : Type*} [Ring R]

/-- Four-coordinate carrier representing a $2 \times 2$ two-sector operator
$\begin{pmatrix} m_{11} & m_{12} \\ m_{21} & m_{22} \end{pmatrix}$ over `R`. -/
@[ext]
structure Cl11Op (R : Type*) where
  m11 : R
  m12 : R
  m21 : R
  m22 : R
  deriving DecidableEq

namespace Cl11Op

variable {R : Type*} [Ring R]

/-- Zero operator in `Cl11Op R`. -/
def zero : Cl11Op R := ⟨0, 0, 0, 0⟩

/-- Multiplicative identity operator $\mathrm{diag}(1, 1)$ in `Cl11Op R`. -/
def one : Cl11Op R := ⟨1, 0, 0, 1⟩

/-- Krein grading involution $\eta = \mathrm{diag}(1, -1)$ separating the black
($+1$) and white ($-1$) node sectors. -/
def kreinEta : Cl11Op R := ⟨1, 0, 0, -1⟩

/-- Componentwise addition on `Cl11Op R`. -/
def add (A B : Cl11Op R) : Cl11Op R :=
  ⟨A.m11 + B.m11, A.m12 + B.m12, A.m21 + B.m21, A.m22 + B.m22⟩

/-- Componentwise subtraction on `Cl11Op R`. -/
def sub (A B : Cl11Op R) : Cl11Op R :=
  ⟨A.m11 - B.m11, A.m12 - B.m12, A.m21 - B.m21, A.m22 - B.m22⟩

/-- Associative $2 \times 2$ matrix multiplication on `Cl11Op R`. -/
def mul (A B : Cl11Op R) : Cl11Op R :=
  ⟨A.m11 * B.m11 + A.m12 * B.m21, A.m11 * B.m12 + A.m12 * B.m22,
   A.m21 * B.m11 + A.m22 * B.m21, A.m21 * B.m12 + A.m22 * B.m22⟩

/-- Upper-left black-node diagonal element $\mathrm{diag}(x, 0)$. -/
def nodeBlack (x : R) : Cl11Op R := ⟨x, 0, 0, 0⟩

/-- Lower-right white-node diagonal element $\mathrm{diag}(0, y)$. -/
def nodeWhite (y : R) : Cl11Op R := ⟨0, 0, 0, y⟩

/-- Upper-triangular nilpotent edge twist $\begin{pmatrix} 0 & w \\ 0 & 0 \end{pmatrix}$. -/
def edgeTwist (w : R) : Cl11Op R := ⟨0, w, 0, 0⟩

/-- Lower-triangular nilpotent dual edge twist $\begin{pmatrix} 0 & 0 \\ w & 0 \end{pmatrix}$. -/
def dualEdgeTwist (w : R) : Cl11Op R := ⟨0, 0, w, 0⟩

/-- The finite unipotent element `1 + edgeTwist w`. -/
def edgeTransport (w : R) : Cl11Op R := add one (edgeTwist w)

/-- The explicit two-sided inverse candidate `1 - edgeTwist w`. -/
def edgeTransportInv (w : R) : Cl11Op R := sub one (edgeTwist w)

/-- The upper-triangular edge operator is nilpotent of order at most two. -/
theorem edgeTwist_sq_zero (w : R) :
    mul (edgeTwist w) (edgeTwist w) = zero := by
  dsimp [edgeTwist, mul, zero]
  ext <;> noncomm_ring

/-- Multiplication through the two diagonal sectors gives the displayed
upper-right matrix entry. This is a local matrix product identity. -/
theorem nodeBlack_edgeTwist_nodeWhite (x w y : R) :
    mul (mul (nodeBlack x) (edgeTwist w)) (nodeWhite y) =
      ⟨0, x * w * y, 0, 0⟩ := by
  dsimp [nodeBlack, edgeTwist, nodeWhite, mul]
  ext <;> noncomm_ring

/-- Conjugating the black diagonal element by the explicit unipotent element
has this finite matrix value. -/
theorem edgeTransport_conjugation_nodeBlack (x w : R) :
    mul (mul (edgeTransport w) (nodeBlack x)) (edgeTransportInv w) =
      ⟨x, -(x * w), 0, 0⟩ := by
  dsimp [edgeTransport, edgeTransportInv, nodeBlack, edgeTwist,
    one, add, sub, mul]
  ext <;> noncomm_ring

/-- Right cancellation of the two explicit unipotent factors. -/
theorem edgeTransport_mul_inv (w : R) :
    mul (edgeTransport w) (edgeTransportInv w) = one := by
  dsimp [edgeTransport, edgeTransportInv, edgeTwist, one, add, sub, mul]
  ext <;> noncomm_ring

/-- Left cancellation of the two explicit unipotent factors. -/
theorem edgeTransportInv_mul (w : R) :
    mul (edgeTransportInv w) (edgeTransport w) = one := by
  dsimp [edgeTransport, edgeTransportInv, edgeTwist, one, add, sub, mul]
  ext <;> noncomm_ring

/-- **Krein Involution & Chiral Anticommutation of `edgeTwist`
(`kreinEta_sq_and_edgeTwist_anticommutator`):**
The Krein grading operator $\eta = \mathrm{diag}(1, -1)$ squares to the identity
($\eta^2 = 1$) and strictly anticommutes with the off-diagonal edge twist
($\eta E(w) + E(w) \eta = 0$). -/
theorem kreinEta_sq_and_edgeTwist_anticommutator (w : R) :
    mul (kreinEta (R := R)) kreinEta = one ∧
    add (mul kreinEta (edgeTwist w)) (mul (edgeTwist w) kreinEta) = zero := by
  refine ⟨?_, ?_⟩
  · dsimp [kreinEta, mul, one]
    ext <;> noncomm_ring
  · dsimp [kreinEta, edgeTwist, mul, add, zero]
    ext <;> noncomm_ring

/-- Explicit non-commutativity witness on `Cl11Op ℤ`: the forward and backward
edge twists do not commute. -/
theorem cl11Op_mul_noncommutative :
    mul (edgeTwist (1 : ℤ)) (dualEdgeTwist 1) ≠
      mul (dualEdgeTwist 1) (edgeTwist 1) := by
  intro hEq
  have h11 : (mul (edgeTwist (1 : ℤ)) (dualEdgeTwist 1)).m11 =
      (mul (dualEdgeTwist 1) (edgeTwist 1)).m11 := congrArg Cl11Op.m11 hEq
  revert h11
  decide

end Cl11Op

end InfoGeometry.Holography.PlabicKrein

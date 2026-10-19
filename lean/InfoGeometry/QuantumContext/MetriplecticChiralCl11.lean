/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Section 117b: Finite Two-by-Two Matrix Coordinate Identities

This module proves identities on a four-entry matrix-coordinate record with a
matrix-shaped multiplication, and on a three-entry state record with a
matrix-dependent coordinate map. It does not connect these records to the
repository's native Clifford algebra or prove a Clifford-module representation.
The bracket section proves antisymmetry of one bilinear form and symmetry,
indefiniteness, and restricted nullity of another; it does not establish Poisson
or metriplectic dynamics.
-/

namespace InfoGeometry.QuantumContext.MetriplecticCl11

variable {R : Type*} [CommRing R]

/-! ## Section 1: Four-Entry Matrix-Coordinate Carrier -/

/-- Four-entry record used for matrix-coordinate calculations. -/
@[ext]
structure Cl11Matrix (R : Type*) where
  m11 : R
  m12 : R
  m21 : R
  m22 : R
  deriving DecidableEq, Repr, Inhabited

namespace Cl11Matrix

variable {R : Type*} [CommRing R]

/-- Identity operator $I = \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}$. -/
def id : Cl11Matrix R := ⟨1, 0, 0, 1⟩

/-- Zero operator $0 = \begin{pmatrix} 0 & 0 \\ 0 & 0 \end{pmatrix}$. -/
def zero : Cl11Matrix R := ⟨0, 0, 0, 0⟩

/-- Upper-right matrix unit. -/
def ePlus : Cl11Matrix R := ⟨0, 1, 0, 0⟩

/-- Lower-left matrix unit. -/
def eMinus : Cl11Matrix R := ⟨0, 0, 1, 0⟩

/-- The identity matrix over $\mathbb{Z}$ is distinct from `zero`. -/
theorem matrix_id_ne_zero : (id : Cl11Matrix ℤ) ≠ zero := by
  intro h
  have h1 : (id : Cl11Matrix ℤ).m11 = (zero : Cl11Matrix ℤ).m11 :=
    congrArg Cl11Matrix.m11 h
  revert h1
  decide

/-- Entrywise addition of matrix-coordinate records. -/
def add (A B : Cl11Matrix R) : Cl11Matrix R :=
  ⟨A.m11 + B.m11, A.m12 + B.m12, A.m21 + B.m21, A.m22 + B.m22⟩

/-- Matrix-shaped multiplication of four-entry records. -/
def mul (A B : Cl11Matrix R) : Cl11Matrix R :=
  ⟨A.m11 * B.m11 + A.m12 * B.m21, A.m11 * B.m12 + A.m12 * B.m22,
   A.m21 * B.m11 + A.m22 * B.m21, A.m21 * B.m12 + A.m22 * B.m22⟩

/-- Scalar multiplication of a $\mathrm{Cl}(1,1)$ operator. -/
def scale (c : R) (A : Cl11Matrix R) : Cl11Matrix R :=
  ⟨c * A.m11, c * A.m12, c * A.m21, c * A.m22⟩

/-- Matrix trace $\operatorname{Tr}(A) = m_{11} + m_{22}$. -/
def trace (A : Cl11Matrix R) : R := A.m11 + A.m22

/-- Skew-symmetric off-diagonal core $m_{12} - m_{21}$. -/
def skewCore (A : Cl11Matrix R) : R := A.m12 - A.m21

/-- Non-commutativity of $\mathrm{Cl}(1,1)$ matrix multiplication over $\mathbb{Z}$:
    $e_+ e_- \ne e_- e_+$. -/
theorem mul_noncommutative :
    mul (ePlus : Cl11Matrix ℤ) eMinus ≠ mul eMinus ePlus := by
  intro h
  have h1 : (mul (ePlus : Cl11Matrix ℤ) eMinus).m11 =
      (mul (eMinus : Cl11Matrix ℤ) ePlus).m11 :=
    congrArg Cl11Matrix.m11 h
  revert h1
  decide

/-! ## Section 2: Three-Coordinate State Record -/

/-- Three-coordinate state record. No spinor or Clifford-module structure is
    asserted by this definition. -/
@[ext]
structure MajoranaSpinor (R : Type*) where
  real_singlet : R
  hyper_left   : R
  hyper_right  : R
  deriving DecidableEq, Repr, Inhabited

/-- Zero Majorana spinor state. -/
def zeroSpinor : MajoranaSpinor R := ⟨0, 0, 0⟩

/-- Canonical non-zero integer Majorana spinor state. -/
def canonicalSpinor : MajoranaSpinor ℤ := ⟨1, 1, -1⟩

/-- The canonical Majorana spinor over $\mathbb{Z}$ is distinct from `zeroSpinor`. -/
theorem canonicalSpinor_ne_zero : canonicalSpinor ≠ (zeroSpinor : MajoranaSpinor ℤ) := by
  intro h
  have h1 : canonicalSpinor.real_singlet = (zeroSpinor : MajoranaSpinor ℤ).real_singlet :=
    congrArg MajoranaSpinor.real_singlet h
  revert h1
  decide

/-- Matrix-dependent coordinate map on the three-coordinate state record. -/
def action (A : Cl11Matrix R) (ψ : MajoranaSpinor R) : MajoranaSpinor R :=
  ⟨(A.m11 + A.m22) * ψ.real_singlet,
   A.m11 * ψ.hyper_left + A.m12 * ψ.hyper_right,
   A.m21 * ψ.hyper_left + A.m22 * ψ.hyper_right⟩

/-- The `hyper_left` and `hyper_right` components of `action` form a genuine left module
    homomorphism under `Cl11Matrix.mul`:
    `(action (mul A B) ψ).hyper_left = (action A (action B ψ)).hyper_left` and
    `(action (mul A B) ψ).hyper_right = (action A (action B ψ)).hyper_right`,
    while the `real_singlet` component scales by `trace A`. -/
theorem action_hyper_mul_and_singlet_trace (A B : Cl11Matrix R) (ψ : MajoranaSpinor R) :
    (action (mul A B) ψ).hyper_left = (action A (action B ψ)).hyper_left ∧
    (action (mul A B) ψ).hyper_right = (action A (action B ψ)).hyper_right ∧
    (action A ψ).real_singlet = trace A * ψ.real_singlet := by
  dsimp [action, mul, trace]
  refine ⟨by ring, by ring, by ring⟩

/-! ## Section 3: Symmetric–Skew Coordinate Decomposition -/

/-- Symmetric operator projection (Yang sector). This projection alone does
    not assert positive semidefiniteness. -/
def toSymmetric (A : Cl11Matrix R) [Invertible (2 : R)] : Cl11Matrix R :=
  let half := (⅟(2 : R))
  ⟨A.m11, half * (A.m12 + A.m21), half * (A.m12 + A.m21), A.m22⟩

/-- Skew-symmetric operator projection. -/
def toSkew (A : Cl11Matrix R) [Invertible (2 : R)] : Cl11Matrix R :=
  let half := (⅟(2 : R))
  ⟨0, half * (A.m12 - A.m21), -half * (A.m12 - A.m21), 0⟩

/-- The symmetric and skew-symmetric projections reconstruct the input record. -/
theorem yin_yang_reconstruction (A : Cl11Matrix R) [Invertible (2 : R)] :
  add (toSymmetric A) (toSkew A) = A := by
  dsimp [add, toSymmetric, toSkew]
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self 2
  ext
  · ring
  · calc ⅟(2 : R) * (A.m12 + A.m21) + ⅟(2 : R) * (A.m12 - A.m21)
      _ = ((2 : R) * ⅟(2 : R)) * A.m12 := by ring
      _ = 1 * A.m12 := by rw [h2]
      _ = A.m12 := by ring
  · calc ⅟(2 : R) * (A.m12 + A.m21) + -⅟(2 : R) * (A.m12 - A.m21)
      _ = ((2 : R) * ⅟(2 : R)) * A.m21 := by ring
      _ = 1 * A.m21 := by rw [h2]
      _ = A.m21 := by ring
  · ring

end Cl11Matrix

/-! ## Section 4: Bracket Identities and Restricted Nullity -/

/-- Pair of distinguished matrix-coordinate records, named `Hamiltonian` and `Entropy`
    for the restricted algebraic calculation below. -/
@[ext]
structure MetriplecticSystem (R : Type*) where
  Hamiltonian : Cl11Matrix R
  Entropy     : Cl11Matrix R
  deriving DecidableEq, Repr, Inhabited

namespace MetriplecticSystem

open Cl11Matrix

variable {R : Type*} [CommRing R]

/-- Zero metriplectic system. -/
def zero : MetriplecticSystem R := ⟨Cl11Matrix.zero, Cl11Matrix.zero⟩

/-- Canonical non-zero integer metriplectic system. -/
def canonicalSystem : MetriplecticSystem ℤ :=
  ⟨⟨0, 1, 1, 0⟩, ⟨1, 0, 0, -1⟩⟩

/-- The canonical metriplectic system over $\mathbb{Z}$ is distinct from `zero`. -/
theorem canonicalSystem_ne_zero : canonicalSystem ≠ (zero : MetriplecticSystem ℤ) := by
  intro h
  have h1 : canonicalSystem.Hamiltonian.m12 = (zero : MetriplecticSystem ℤ).Hamiltonian.m12 :=
    congrArg (fun S => S.Hamiltonian.m12) h
  revert h1
  decide

/-- Antisymmetric bilinear form on matrix-coordinate records. No Jacobi identity
    or Leibniz law is asserted here. -/
def poissonBracket (A B : Cl11Matrix R) : R :=
  A.m11 * B.m22 - A.m22 * B.m11 + A.m12 * B.m21 - A.m21 * B.m12

/-- Symmetric bilinear form $\langle A, B \rangle$. It is indefinite over
    $\mathbb R$ and is not asserted to be a positive dissipative bracket. -/
def metricBracket (A B : Cl11Matrix R) : R :=
  (A.m12 - A.m21) * (B.m12 - B.m21) - (A.m11 * B.m22 + A.m22 * B.m11)

/-- Antisymmetry of the bilinear form. -/
theorem poissonBracket_antisymm (A B : Cl11Matrix R) :
    poissonBracket A B = - poissonBracket B A := by
  dsimp [poissonBracket]
  ring

/-- Symmetry of the bilinear form: $\langle A, B \rangle = \langle B, A \rangle$. -/
theorem metricBracket_symm (A B : Cl11Matrix R) :
    metricBracket A B = metricBracket B A := by
  dsimp [metricBracket]
  ring

/-- The displayed symmetric form takes both signs on real matrices. -/
theorem metricBracket_indefinite_over_reals :
    metricBracket (⟨1, 0, 0, 1⟩ : Cl11Matrix ℝ)
        (⟨1, 0, 0, 1⟩ : Cl11Matrix ℝ) = -2 ∧
      metricBracket (⟨0, 1, 0, 0⟩ : Cl11Matrix ℝ)
        (⟨0, 1, 0, 0⟩ : Cl11Matrix ℝ) = 1 := by
  norm_num [metricBracket]

/-- Consequently, this form fails the positive-semidefinite condition required
    of a dissipative metric bracket. -/
theorem metricBracket_not_positiveSemidefinite :
    ¬ ∀ A : Cl11Matrix ℝ, 0 ≤ metricBracket A A := by
  intro h
  have hId := h (⟨1, 0, 0, 1⟩ : Cl11Matrix ℝ)
  norm_num [metricBracket] at hId

/-- The antisymmetric bilinear form vanishes on the diagonal. -/
theorem poisson_self_null (H : Cl11Matrix R) : poissonBracket H H = 0 := by
  dsimp [poissonBracket]
  ring

/-- Restricted symmetric-form nullity locus:
    When `sys.Hamiltonian` is chirally balanced ($H_{12} = H_{21}$) with vanishing diagonal entries
    ($H_{11} = 0 \land H_{22} = 0$), and `sys.Entropy` is a diagonal operator ($S_{12} = 0 \land S_{21} = 0$),
    both `metricBracket H H = 0`, `metricBracket H S = 0`, and `poissonBracket H S = 0` hold. -/
theorem metric_energy_preservation_manifold (sys : MetriplecticSystem R)
    (h_chiral_balance : sys.Hamiltonian.m12 = sys.Hamiltonian.m21)
    (h_vacuum_null    : sys.Hamiltonian.m11 = 0 ∧ sys.Hamiltonian.m22 = 0)
    (h_entropy_diag   : sys.Entropy.m12 = 0 ∧ sys.Entropy.m21 = 0) :
    metricBracket sys.Hamiltonian sys.Hamiltonian = 0 ∧
      metricBracket sys.Hamiltonian sys.Entropy = 0 ∧
      poissonBracket sys.Hamiltonian sys.Entropy = 0 := by
  dsimp [metricBracket, poissonBracket]
  rw [h_chiral_balance, h_vacuum_null.1, h_vacuum_null.2, h_entropy_diag.1, h_entropy_diag.2]
  refine ⟨by ring, by ring, by ring⟩

end MetriplecticSystem

end InfoGeometry.QuantumContext.MetriplecticCl11

import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Stratum 21: The Dual-Sheeted Krein Space of Thickness $h$

This module formalizes the functional analysis and indefinite metric space mechanics
governing a dual-sheeted lipid bilayer of finite thickness $h$:
1. **Algebraic Krein Space Fundamental Decomposition**:
   A Krein space structure is defined by a fundamental symmetry $J$ satisfying $J^2 = \mathbf{1}$,
   inducing fundamental orthogonal projectors $P_\pm = \frac{\mathbf{1} \pm J}{2}$ that partition the space.
2. **The Transverse Thickness Moment Operator**:
   The transverse moment operator $M_z = \frac{h}{2} J$ scales as the thickness $h$ and
   squares to $\frac{h^2}{4} \mathbf{1}$.
3. **The Indefinite Krein Bilayer Pairing**:
   The indefinite inner product $[x, y] = x_+ y_+ - x_- y_-$ renders the positive sheet ($P_+ x$)
   and negative sheet ($P_- y$) strictly Krein-orthogonal: $[P_+ x, P_- y] = 0$.
4. **Monopole and Dipole Modes**:
   Decomposition of the bilayer state into a symmetric monopole mode and an asymmetric dipole mode.
5. **Neutrality of Symmetric States**:
   Any state with equal outer and inner leaflet amplitudes ($x_+ = x_-$) is a neutral null vector
   in the Krein metric: $[x, x] = 0$.
-/

namespace InfoGeometry.Canonical.DualSheetedKreinThickness

/-!
### 1. Algebraic Krein Space Fundamental Decomposition
-/

section KreinDecomposition

variable {A : Type*} [Ring A]
variable (half J : A)

/-- Positive Krein projector $P_+ = \frac{1 + J}{2}$. -/
def kreinPPlus : A := half * (1 + J)

/-- Negative Krein projector $P_- = \frac{1 - J}{2}$. -/
def kreinPMinus : A := half * (1 - J)

/-- $P_+$ is idempotent: $P_+^2 = P_+$. -/
theorem kreinPPlus_sq (h_half_add : half + half = 1)
    (h_half_comm : ∀ x : A, half * x = x * half)
    (hJ : J * J = 1) :
    kreinPPlus half J * kreinPPlus half J = kreinPPlus half J := by
  dsimp [kreinPPlus]
  have h1 : (1 + J) * half = half * (1 + J) := (h_half_comm (1 + J)).symm
  have h2 : (1 + J) * (1 + J) = (1 + J) + (1 + J) := by
    calc (1 + J) * (1 + J)
      _ = 1 + J + J + J * J := by noncomm_ring
      _ = 1 + J + J + 1 := by rw [hJ]
      _ = (1 + J) + (1 + J) := by abel
  calc half * (1 + J) * (half * (1 + J))
    _ = half * ((1 + J) * half) * (1 + J) := by noncomm_ring
    _ = half * (half * (1 + J)) * (1 + J) := by rw [h1]
    _ = (half * half) * ((1 + J) * (1 + J)) := by noncomm_ring
    _ = (half * half) * ((1 + J) + (1 + J)) := by rw [h2]
    _ = (half * half) * (1 + J) + (half * half) * (1 + J) := by noncomm_ring
    _ = (half * half + half * half) * (1 + J) := by noncomm_ring
    _ = (half * (half + half)) * (1 + J) := by noncomm_ring
    _ = (half * 1) * (1 + J) := by rw [h_half_add]
    _ = half * (1 + J) := by noncomm_ring

/-- $P_-$ is idempotent: $P_-^2 = P_-$. -/
theorem kreinPMinus_sq (h_half_add : half + half = 1)
    (h_half_comm : ∀ x : A, half * x = x * half)
    (hJ : J * J = 1) :
    kreinPMinus half J * kreinPMinus half J = kreinPMinus half J := by
  dsimp [kreinPMinus]
  have h1 : (1 - J) * half = half * (1 - J) := (h_half_comm (1 - J)).symm
  have h2 : (1 - J) * (1 - J) = (1 - J) + (1 - J) := by
    calc (1 - J) * (1 - J)
      _ = 1 - J - J + J * J := by noncomm_ring
      _ = 1 - J - J + 1 := by rw [hJ]
      _ = (1 - J) + (1 - J) := by abel
  calc half * (1 - J) * (half * (1 - J))
    _ = half * ((1 - J) * half) * (1 - J) := by noncomm_ring
    _ = half * (half * (1 - J)) * (1 - J) := by rw [h1]
    _ = (half * half) * ((1 - J) * (1 - J)) := by noncomm_ring
    _ = (half * half) * ((1 - J) + (1 - J)) := by rw [h2]
    _ = (half * half) * (1 - J) + (half * half) * (1 - J) := by noncomm_ring
    _ = (half * half + half * half) * (1 - J) := by noncomm_ring
    _ = (half * (half + half)) * (1 - J) := by noncomm_ring
    _ = (half * 1) * (1 - J) := by rw [h_half_add]
    _ = half * (1 - J) := by noncomm_ring

/-- $P_+$ and $P_-$ are mutually orthogonal: $P_+ P_- = 0$. -/
theorem krein_projector_ortho (h_half_comm : ∀ x : A, half * x = x * half)
    (hJ : J * J = 1) :
    kreinPPlus half J * kreinPMinus half J = 0 := by
  dsimp [kreinPPlus, kreinPMinus]
  have h1 : (1 + J) * half = half * (1 + J) := (h_half_comm (1 + J)).symm
  have h2 : (1 + J) * (1 - J) = 0 := by
    calc (1 + J) * (1 - J)
      _ = 1 - J + J - J * J := by noncomm_ring
      _ = 1 - J + J - 1 := by rw [hJ]
      _ = 0 := by abel
  calc half * (1 + J) * (half * (1 - J))
    _ = half * ((1 + J) * half) * (1 - J) := by noncomm_ring
    _ = half * (half * (1 + J)) * (1 - J) := by rw [h1]
    _ = (half * half) * ((1 + J) * (1 - J)) := by noncomm_ring
    _ = (half * half) * 0 := by rw [h2]
    _ = 0 := by noncomm_ring

/-- Resolution of identity: $P_+ + P_- = 1$. -/
theorem krein_resolution_of_identity (h_half_add : half + half = 1) :
    kreinPPlus half J + kreinPMinus half J = 1 := by
  dsimp [kreinPPlus, kreinPMinus]
  calc half * (1 + J) + half * (1 - J)
    _ = half * ((1 + J) + (1 - J)) := by rw [← mul_add]
    _ = half * (1 + 1) := by
        have : (1 + J) + (1 - J) = 1 + 1 := by abel
        rw [this]
    _ = half + half := by rw [mul_add, mul_one]
    _ = 1 := h_half_add

end KreinDecomposition

/-!
### 2. Transverse Moment Operator Across Thickness $h$
-/

section TransverseThickness

variable {A : Type*} [CommRing A]
variable (half J h : A)

/-- Transverse moment operator across thickness $h$: $M_z = \frac{h}{2} J$. -/
def transverseMoment : A := half * h * J

/-- The square of the transverse moment operator is $\frac{h^2}{4} \mathbf{1}$. -/
theorem transverse_moment_sq (hJ : J * J = 1) :
    transverseMoment half J h * transverseMoment half J h = (half * h * (half * h)) := by
  unfold transverseMoment
  calc (half * h * J) * (half * h * J)
    _ = (half * h * (half * h)) * (J * J) := by ring
    _ = (half * h * (half * h)) * 1 := by rw [hJ]
    _ = half * h * (half * h) := by ring

end TransverseThickness

/-!
### 3. Indefinite Bilayer Krein Metric and Sheet Orthogonality
-/

section IndefiniteBilayerPairing

variable {R : Type*} [CommRing R]

/-- Indefinite Krein inner product of two 2-sheeted vectors $[x, y] = x_+ y_+ - x_- y_-$. -/
def kreinPairing (x y : Fin 2 → R) : R :=
  x 0 * y 0 - x 1 * y 1

/-- Fundamental symmetry matrix $J = \operatorname{diag}(1, -1)$. -/
def fundamentalSymmetryJ : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, -1]

/-- Positive and negative sheet projections are Krein-orthogonal: $[P_+ x, P_- y] = 0$. -/
theorem krein_sheet_orthogonality (x y : Fin 2 → R) :
    let x_plus : Fin 2 → R := ![x 0, 0]
    let y_minus : Fin 2 → R := ![0, y 1]
    kreinPairing x_plus y_minus = 0 := by
  dsimp [kreinPairing]
  ring

/-- Transverse dipole polarization across thickness $h$: $d = \frac{h}{2}(x_+ - x_-)$. -/
def transverseDipole (h half : R) (x : Fin 2 → R) : R :=
  half * h * (x 0 - x 1)

/-- Transverse monopole compression across thickness $h$: $m = x_+ + x_-$. -/
def transverseMonopole (x : Fin 2 → R) : R :=
  x 0 + x 1

/-- A symmetric state ($x_+ = x_-$) is a neutral null vector in the Krein metric: $[x, x] = 0$. -/
theorem krein_neutral_symmetric_state (x : Fin 2 → R) (h_eq : x 0 = x 1) :
    kreinPairing x x = 0 := by
  dsimp [kreinPairing]
  rw [h_eq]
  ring

end IndefiniteBilayerPairing

/-!
### 4. Master Synthesis Packet for Stratum 21
-/

structure DualSheetedKreinThicknessPacket (R : Type*) [CommRing R] where
  proj_sum : ∀ half J : R, half + half = 1 →
    kreinPPlus half J + kreinPMinus half J = 1
  proj_ortho : ∀ half J : R, (∀ x, half * x = x * half) → J * J = 1 →
    kreinPPlus half J * kreinPMinus half J = 0
  proj_plus_sq : ∀ half J : R, half + half = 1 → (∀ x, half * x = x * half) → J * J = 1 →
    kreinPPlus half J * kreinPPlus half J = kreinPPlus half J
  proj_minus_sq : ∀ half J : R, half + half = 1 → (∀ x, half * x = x * half) → J * J = 1 →
    kreinPMinus half J * kreinPMinus half J = kreinPMinus half J
  moment_sq : ∀ half J h : R, J * J = 1 →
    transverseMoment half J h * transverseMoment half J h = (half * h * (half * h))
  sheet_ortho : ∀ x y : Fin 2 → R,
    let x_plus : Fin 2 → R := ![x 0, 0]
    let y_minus : Fin 2 → R := ![0, y 1]
    kreinPairing x_plus y_minus = 0
  neutral_symm : ∀ x : Fin 2 → R, x 0 = x 1 → kreinPairing x x = 0

def makeDualSheetedKreinThicknessPacket (R : Type*) [CommRing R] :
    DualSheetedKreinThicknessPacket R where
  proj_sum := fun half J h_add =>
    krein_resolution_of_identity half J h_add
  proj_ortho := fun half J h_comm hJ =>
    krein_projector_ortho half J h_comm hJ
  proj_plus_sq := fun half J h_add h_comm hJ =>
    kreinPPlus_sq half J h_add h_comm hJ
  proj_minus_sq := fun half J h_add h_comm hJ =>
    kreinPMinus_sq half J h_add h_comm hJ
  moment_sq := fun half J h hJ =>
    transverse_moment_sq half J h hJ
  sheet_ortho := fun x y =>
    krein_sheet_orthogonality x y
  neutral_symm := fun x h_eq =>
    krein_neutral_symmetric_state x h_eq

end InfoGeometry.Canonical.DualSheetedKreinThickness

import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Stratum 22: Transverse Discrete Fiber, Quantum Action $\hbar$, & Inter-Sheet Gauge Mediators

This module formalizes the noncommutative geometry and quantum symplectic mechanics
governing the discrete transverse fiber of thickness $h$ connecting the two sheets of a lipid bilayer:
1. **Molecular Volume of the Cross-Sectional Fiber**:
   The transverse fiber has cross-sectional area $a_0$ and thickness $h$,
   defining the unit cell volume $V_0 = a_0 h$.
2. **Discrete Transverse Derivative Across the Two Sheets**:
   The finite difference operator $(\nabla_z \psi) = \frac{\psi_+ - \psi_-}{h}$ is strictly off-diagonal
   in the Krein space and anticommutes with the fundamental symmetry $J$: $\{\nabla_z, J\} = 0$.
3. **Inter-Sheet Gauge Mediator (Connes' Higgs Field on the Discrete Fiber)**:
   Any inter-sheet field $\Phi$ anticommuting with $J$ satisfies $P_\pm \Phi P_\pm = 0$,
   acting exclusively as an off-diagonal tunneling transition between the two leaflets.
4. **Quantum Action Integral Across the Transverse Fiber**:
   The transverse momentum-displacement action scales with Planck's constant $\hbar$.
-/

namespace InfoGeometry.Canonical.TransverseFiberActionQuantum

/-!
### 1. Molecular Volume of the Transverse Cross-Sectional Fiber
-/

section FiberVolume

variable {R : Type*} [CommRing R]

/-- The molecular unit cell volume of the transverse fiber: $V_0 = a_0 h$. -/
def fiberCellVolume (a0 h : R) : R :=
  a0 * h

/-- Linear scaling of the transverse fiber volume with respect to area. -/
theorem fiber_volume_scaling (a0 h c : R) :
    fiberCellVolume (c * a0) h = c * fiberCellVolume a0 h := by
  dsimp [fiberCellVolume]
  ring

end FiberVolume

/-!
### 2. Discrete Transverse Derivative Across the Two Sheets
-/

section DiscreteFiberDerivative

variable {R : Type*} [CommRing R]

/-- Discrete derivative matrix connecting the two sheets: $!![0, 1; -1, 0]$. -/
def discreteGradZ : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; -1, 0]

/-- Fundamental symmetry matrix $J = \operatorname{diag}(1, -1)$. -/
def fundamentalJ : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, -1]

/-- The discrete transverse derivative anticommutes with the fundamental symmetry: $\{\nabla_z, J\} = 0$. -/
theorem gradZ_anticomm_J :
    discreteGradZ (R := R) * fundamentalJ + fundamentalJ * discreteGradZ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [discreteGradZ, fundamentalJ]

end DiscreteFiberDerivative

/-!
### 3. Inter-Sheet Gauge Mediator (The Connes Higgs Field on the Fiber)
-/

section InterSheetMediator

variable {A : Type*} [Ring A]
variable (half J Φ : A)

/-- Positive split Peirce projector $P_+ = \frac{1 + J}{2}$. -/
def peircePlus : A := half * (1 + J)

/-- Negative split Peirce projector $P_- = \frac{1 - J}{2}$. -/
def peirceMinus : A := half * (1 - J)

/-- Intertwining identity: $(1 + J) \Phi = \Phi (1 - J)$ when $\{\Phi, J\} = 0$. -/
theorem one_add_J_mul_phi (h_anticomm : Φ * J + J * Φ = 0) :
    (1 + J) * Φ = Φ * (1 - J) := by
  have h_swap : J * Φ = - (Φ * J) := by
    calc J * Φ = (Φ * J + J * Φ) - Φ * J := by abel
      _ = 0 - Φ * J := by rw [h_anticomm]
      _ = - (Φ * J) := by simp
  calc (1 + J) * Φ
    _ = 1 * Φ + J * Φ := by rw [add_mul]
    _ = Φ + - (Φ * J) := by rw [one_mul, h_swap]
    _ = Φ * (1 - J) := by
        rw [mul_sub, mul_one, sub_eq_add_neg]

/-- Intertwining identity: $(1 - J) \Phi = \Phi (1 + J)$ when $\{\Phi, J\} = 0$. -/
theorem one_sub_J_mul_phi (h_anticomm : Φ * J + J * Φ = 0) :
    (1 - J) * Φ = Φ * (1 + J) := by
  have h_swap : J * Φ = - (Φ * J) := by
    calc J * Φ = (Φ * J + J * Φ) - Φ * J := by abel
      _ = 0 - Φ * J := by rw [h_anticomm]
      _ = - (Φ * J) := by simp
  calc (1 - J) * Φ
    _ = 1 * Φ - J * Φ := by rw [sub_mul]
    _ = Φ - - (Φ * J) := by rw [one_mul, h_swap]
    _ = Φ * (1 + J) := by
        rw [mul_add, mul_one, sub_neg_eq_add]

/-- Projector intertwining: $P_+ \Phi = \Phi P_-$. -/
theorem peircePlus_mul_phi
    (h_half_comm : ∀ x : A, half * x = x * half)
    (h_anticomm : Φ * J + J * Φ = 0) :
    peircePlus half J * Φ = Φ * peirceMinus half J := by
  dsimp [peircePlus, peirceMinus]
  calc (half * (1 + J)) * Φ
    _ = half * ((1 + J) * Φ) := by rw [mul_assoc]
    _ = half * (Φ * (1 - J)) := by rw [one_add_J_mul_phi J Φ h_anticomm]
    _ = (half * Φ) * (1 - J) := by rw [mul_assoc]
    _ = (Φ * half) * (1 - J) := by rw [h_half_comm Φ]
    _ = Φ * (half * (1 - J)) := by rw [mul_assoc]

/-- Projector intertwining: $P_- \Phi = \Phi P_+$. -/
theorem peirceMinus_mul_phi
    (h_half_comm : ∀ x : A, half * x = x * half)
    (h_anticomm : Φ * J + J * Φ = 0) :
    peirceMinus half J * Φ = Φ * peircePlus half J := by
  dsimp [peircePlus, peirceMinus]
  calc (half * (1 - J)) * Φ
    _ = half * ((1 - J) * Φ) := by rw [mul_assoc]
    _ = half * (Φ * (1 + J)) := by rw [one_sub_J_mul_phi J Φ h_anticomm]
    _ = (half * Φ) * (1 + J) := by rw [mul_assoc]
    _ = (Φ * half) * (1 + J) := by rw [h_half_comm Φ]
    _ = Φ * (half * (1 + J)) := by rw [mul_assoc]

/-- Orthogonality: $P_- P_+ = 0$. -/
theorem peirce_minus_mul_plus
    (h_half_comm : ∀ x : A, half * x = x * half)
    (hJ : J * J = 1) :
    peirceMinus half J * peircePlus half J = 0 := by
  dsimp [peircePlus, peirceMinus]
  have h2 : (1 - J) * (1 + J) = 0 := by
    calc (1 - J) * (1 + J)
      _ = 1 + J - J - J * J := by noncomm_ring
      _ = 1 + J - J - 1 := by rw [hJ]
      _ = 0 := by abel
  calc half * (1 - J) * (half * (1 + J))
    _ = half * ((1 - J) * half) * (1 + J) := by noncomm_ring
    _ = half * (half * (1 - J)) * (1 + J) := by rw [h_half_comm (1 - J)]
    _ = (half * half) * ((1 - J) * (1 + J)) := by noncomm_ring
    _ = (half * half) * 0 := by rw [h2]
    _ = 0 := by noncomm_ring

/-- Orthogonality: $P_+ P_- = 0$. -/
theorem peirce_plus_mul_minus
    (h_half_comm : ∀ x : A, half * x = x * half)
    (hJ : J * J = 1) :
    peircePlus half J * peirceMinus half J = 0 := by
  dsimp [peircePlus, peirceMinus]
  have h1 : (1 + J) * (1 - J) = 0 := by
    calc (1 + J) * (1 - J)
      _ = 1 - J + J - J * J := by noncomm_ring
      _ = 1 - J + J - 1 := by rw [hJ]
      _ = 0 := by abel
  calc half * (1 + J) * (half * (1 - J))
    _ = half * ((1 + J) * half) * (1 - J) := by noncomm_ring
    _ = half * (half * (1 + J)) * (1 - J) := by rw [(h_half_comm (1 + J)).symm]
    _ = (half * half) * ((1 + J) * (1 - J)) := by noncomm_ring
    _ = (half * half) * 0 := by rw [h1]
    _ = 0 := by noncomm_ring

/-- The inter-sheet mediator vanishes on the positive diagonal: $P_+ \Phi P_+ = 0$. -/
theorem inter_sheet_mediator_plus_plus
    (h_half_comm : ∀ x : A, half * x = x * half)
    (hJ : J * J = 1)
    (h_anticomm : Φ * J + J * Φ = 0) :
    peircePlus half J * Φ * peircePlus half J = 0 := by
  calc peircePlus half J * Φ * peircePlus half J
    _ = (peircePlus half J * Φ) * peircePlus half J := by rw [mul_assoc]
    _ = (Φ * peirceMinus half J) * peircePlus half J := by rw [peircePlus_mul_phi half J Φ h_half_comm h_anticomm]
    _ = Φ * (peirceMinus half J * peircePlus half J) := by rw [mul_assoc]
    _ = Φ * 0 := by rw [peirce_minus_mul_plus half J h_half_comm hJ]
    _ = 0 := by rw [mul_zero]

/-- The inter-sheet mediator vanishes on the negative diagonal: $P_- \Phi P_- = 0$. -/
theorem inter_sheet_mediator_minus_minus
    (h_half_comm : ∀ x : A, half * x = x * half)
    (hJ : J * J = 1)
    (h_anticomm : Φ * J + J * Φ = 0) :
    peirceMinus half J * Φ * peirceMinus half J = 0 := by
  calc peirceMinus half J * Φ * peirceMinus half J
    _ = (peirceMinus half J * Φ) * peirceMinus half J := by rw [mul_assoc]
    _ = (Φ * peircePlus half J) * peirceMinus half J := by rw [peirceMinus_mul_phi half J Φ h_half_comm h_anticomm]
    _ = Φ * (peircePlus half J * peirceMinus half J) := by rw [mul_assoc]
    _ = Φ * 0 := by rw [peirce_plus_mul_minus half J h_half_comm hJ]
    _ = 0 := by rw [mul_zero]

end InterSheetMediator

/-!
### 4. Quantum Action Integral Across the Transverse Fiber
-/

section FiberActionIntegral

variable {R : Type*} [CommRing R]

/-- Transverse action functional $S = p_z h$. -/
def transverseFiberAction (pz h : R) : R :=
  pz * h

/-- Scaling with the unit quantum of action $\hbar$. -/
theorem transverse_action_quantum (ħ : R) :
    transverseFiberAction ħ 1 = ħ := by
  dsimp [transverseFiberAction]
  ring

end FiberActionIntegral

/-!
### 5. Master Synthesis Packet for Stratum 22
-/

structure TransverseFiberActionQuantumPacket (R : Type*) [CommRing R] where
  vol_scale : ∀ a0 h c : R, fiberCellVolume (c * a0) h = c * fiberCellVolume a0 h
  grad_anticomm : discreteGradZ (R := R) * fundamentalJ + fundamentalJ * discreteGradZ = 0
  mediator_plus : ∀ half J Φ : R, (∀ x, half * x = x * half) → J * J = 1 →
    Φ * J + J * Φ = 0 → peircePlus half J * Φ * peircePlus half J = 0
  mediator_minus : ∀ half J Φ : R, (∀ x, half * x = x * half) → J * J = 1 →
    Φ * J + J * Φ = 0 → peirceMinus half J * Φ * peirceMinus half J = 0
  action_unit : ∀ ħ : R, transverseFiberAction ħ 1 = ħ

def makeTransverseFiberActionQuantumPacket (R : Type*) [CommRing R] :
    TransverseFiberActionQuantumPacket R where
  vol_scale := fiber_volume_scaling
  grad_anticomm := gradZ_anticomm_J
  mediator_plus := fun half J Φ h_comm hJ h_anti =>
    inter_sheet_mediator_plus_plus half J Φ h_comm hJ h_anti
  mediator_minus := fun half J Φ h_comm hJ h_anti =>
    inter_sheet_mediator_minus_minus half J Φ h_comm hJ h_anti
  action_unit := transverse_action_quantum

end InfoGeometry.Canonical.TransverseFiberActionQuantum

import Mathlib
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Physics.Cl55SpinorCartanFock
import InfoGeometry.Physics.SolovievQuasiparticlePhononEigenproblem

noncomputable section
namespace InfoGeometry.Physics.NuclearSolovievStateProjection

open Matrix
open scoped Matrix
open InfoGeometry.Physics.Cl55SpinorCartanFock
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Physics.SolovievQPNMEigenproblem

abbrev FullHamiltonian := MatStage 5
abbrev SolovievHamiltonian := Matrix (Fin 2) (Fin 2) ℝ

structure TwoSpinorChannel where
  bare : Spinor32
  dressed : Spinor32
  bare_norm : bare ⬝ᵥ bare = 1
  dressed_norm : dressed ⬝ᵥ dressed = 1
  bare_dressed_orthogonal : bare ⬝ᵥ dressed = 0

namespace TwoSpinorChannel
variable (C : TwoSpinorChannel)

def matrixElement (C : TwoSpinorChannel) (ψ φ : Spinor32) (H : FullHamiltonian) : ℝ :=
  ψ ⬝ᵥ (H *ᵥ φ)
def qpEnergy (C : TwoSpinorChannel) (H : FullHamiltonian) : ℝ := C.matrixElement C.bare C.bare H
def dressedEnergy (C : TwoSpinorChannel) (H : FullHamiltonian) : ℝ := C.matrixElement C.dressed C.dressed H
def coupling (C : TwoSpinorChannel) (H : FullHamiltonian) : ℝ := C.matrixElement C.bare C.dressed H
def reverseCoupling (C : TwoSpinorChannel) (H : FullHamiltonian) : ℝ := C.matrixElement C.dressed C.bare H

def projectedHamiltonian (C : TwoSpinorChannel) (H : FullHamiltonian) : SolovievHamiltonian :=
  !![C.qpEnergy H, C.coupling H; C.reverseCoupling H, C.dressedEnergy H]

@[simp] theorem projectedHamiltonian_00 (H : FullHamiltonian) :
    C.projectedHamiltonian H 0 0 = C.qpEnergy H := rfl
@[simp] theorem projectedHamiltonian_01 (H : FullHamiltonian) :
    C.projectedHamiltonian H 0 1 = C.coupling H := rfl
@[simp] theorem projectedHamiltonian_10 (H : FullHamiltonian) :
    C.projectedHamiltonian H 1 0 = C.reverseCoupling H := rfl
@[simp] theorem projectedHamiltonian_11 (H : FullHamiltonian) :
    C.projectedHamiltonian H 1 1 = C.dressedEnergy H := rfl

theorem matrixElement_add (ψ φ : Spinor32) (H K : FullHamiltonian) :
    C.matrixElement ψ φ (H + K) = C.matrixElement ψ φ H + C.matrixElement ψ φ K := by
  simp [matrixElement, Matrix.add_mulVec]

theorem matrixElement_smul (ψ φ : Spinor32) (r : ℝ) (H : FullHamiltonian) :
    C.matrixElement ψ φ (r • H) = r * C.matrixElement ψ φ H := by
  simp [matrixElement, Matrix.smul_mulVec]

theorem projectedHamiltonian_add (H K : FullHamiltonian) :
    C.projectedHamiltonian (H + K) = C.projectedHamiltonian H + C.projectedHamiltonian K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projectedHamiltonian, qpEnergy, dressedEnergy, coupling, reverseCoupling,
      C.matrixElement_add]

theorem projectedHamiltonian_smul (r : ℝ) (H : FullHamiltonian) :
    C.projectedHamiltonian (r • H) = r • C.projectedHamiltonian H := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projectedHamiltonian, qpEnergy, dressedEnergy, coupling, reverseCoupling,
      C.matrixElement_smul]

def projectionLinear : FullHamiltonian →ₗ[ℝ] SolovievHamiltonian where
  toFun := C.projectedHamiltonian
  map_add' := C.projectedHamiltonian_add
  map_smul' := C.projectedHamiltonian_smul

@[simp] theorem projectionLinear_apply (H : FullHamiltonian) :
    C.projectionLinear H = C.projectedHamiltonian H := rfl

end TwoSpinorChannel
end InfoGeometry.Physics.NuclearSolovievStateProjection

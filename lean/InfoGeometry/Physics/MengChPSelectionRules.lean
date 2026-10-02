import Mathlib

noncomputable section

namespace InfoGeometry.Physics.MengChPSelectionRules

variable {Space : Type*} [AddCommGroup Space] [Module ℂ Space]

def chiture (rotation exchange intrinsicParity : Module.End ℂ Space) :
    Module.End ℂ Space := rotation * exchange * intrinsicParity

def chiplex (chitureOp parity : Module.End ℂ Space) : Module.End ℂ Space :=
  chitureOp * parity

theorem chiplex_eigenvector
    (chitureOp parity : Module.End ℂ Space) (state : Space)
    (chitureValue parityValue : ℂ)
    (chiture_state : chitureOp state = chitureValue • state)
    (parity_state : parity state = parityValue • state) :
    chiplex chitureOp parity state = (chitureValue * parityValue) • state := by
  simp [chiplex, Module.End.mul_apply, parity_state, chiture_state, smul_smul,
    mul_comm]

theorem matrix_element_selection
    (symmetry transition : Module.End ℂ Space) (bra : Space →ₗ[ℂ] ℂ)
    (ket : Space) (initialValue finalValue character : ℂ)
    (ket_eigen : symmetry ket = initialValue • ket)
    (bra_eigen : ∀ state, bra (symmetry state) = finalValue * bra state)
    (covariance : symmetry * transition = character • (transition * symmetry))
    (mismatch : finalValue ≠ character * initialValue) :
    bra (transition ket) = 0 := by
  have action := congrArg (fun operator : Module.End ℂ Space => bra (operator ket)) covariance
  simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul,
    smul_eq_mul, ket_eigen, bra_eigen] at action
  have product_zero : (finalValue - character * initialValue) * bra (transition ket) = 0 := by
    linear_combination action
  exact (mul_eq_zero.mp product_zero).resolve_left (sub_ne_zero.mpr mismatch)

theorem chiplex_covariance
    (chitureOp parity transition : Module.End ℂ Space) (chitureSign paritySign : ℂ)
    (chiture_covariance : chitureOp * transition = chitureSign • (transition * chitureOp))
    (parity_covariance : parity * transition = paritySign • (transition * parity)) :
    chiplex chitureOp parity * transition =
      (chitureSign * paritySign) • (transition * chiplex chitureOp parity) := by
  calc
    chiplex chitureOp parity * transition = chitureOp * (parity * transition) := mul_assoc _ _ _
    _ = paritySign • ((chitureOp * transition) * parity) := by
      rw [parity_covariance, mul_smul_comm, ← mul_assoc]
    _ = (chitureSign * paritySign) • (transition * chiplex chitureOp parity) := by
      rw [chiture_covariance, smul_mul_assoc, smul_smul]
      simp [chiplex, mul_assoc, mul_comm paritySign chitureSign]

inductive Multipole
  | electricTwo
  | magneticOne
  | electricThree
  deriving DecidableEq, Fintype

def chitureCharacter : Multipole → ℂ
  | .electricTwo | .magneticOne => -1
  | .electricThree => 1

def parityCharacter : Multipole → ℂ
  | .electricTwo | .magneticOne => 1
  | .electricThree => -1

def exchangeParityCharacter : Multipole → ℂ
  | .electricTwo | .electricThree => 1
  | .magneticOne => -1

theorem chiplexCharacter (multipole : Multipole) :
    chitureCharacter multipole * parityCharacter multipole = -1 := by
  cases multipole <;> norm_num [chitureCharacter, parityCharacter]

theorem same_chiplex_transition_vanishes
    (multipole : Multipole) (chitureOp parity transition : Module.End ℂ Space)
    (bra : Space →ₗ[ℂ] ℂ) (ket : Space) (value : ℂ) (value_ne : value ≠ 0)
    (ket_eigen : chiplex chitureOp parity ket = value • ket)
    (bra_eigen : ∀ state, bra (chiplex chitureOp parity state) = value * bra state)
    (chiture_covariance : chitureOp * transition =
      chitureCharacter multipole • (transition * chitureOp))
    (parity_covariance : parity * transition =
      parityCharacter multipole • (transition * parity)) :
    bra (transition ket) = 0 := by
  apply matrix_element_selection (chiplex chitureOp parity) transition bra ket value value (-1)
    ket_eigen bra_eigen
  · simpa only [chiplexCharacter] using
      chiplex_covariance chitureOp parity transition _ _ chiture_covariance parity_covariance
  · intro equality
    apply value_ne
    linear_combination (1 / 2 : ℂ) * equality

end InfoGeometry.Physics.MengChPSelectionRules

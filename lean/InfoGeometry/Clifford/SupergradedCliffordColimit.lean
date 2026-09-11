import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Clifford.CliffordBitWordEquivalence
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Physics.ChiralSUSYBlockFactorization

/-!
# Supergraded chiral blocks over the Clifford/UHF colimit

This module is the finite-to-colimit interface for the chiral algebra.  The
carrier is the established `Cl11TensorTowerLimit.Limit`; chiral charges live
in its honest matrix extension `Matrix (Fin 2) (Fin 2) carrier`.  Finite
chiral blocks are transported entrywise through the stage injections, and the
result is then carried to the BitWord presentation by the proved colimit
equivalence.

No claim is made that the chiral 2 x 2 extension is itself the scalar UHF
carrier, and no analytic or Hilbert-space structure is introduced here.
-/

noncomputable section

namespace InfoGeometry.Clifford.SupergradedCliffordColimit

open Matrix
open InfoGeometry.Physics
open InfoGeometry.Algebra
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.CliffordBitWordEquivalence

abbrev Carrier := Cl11TensorTowerLimit.Limit
abbrev Stage (n : ℕ) := Cl11TensorTowerLimit.Stage n
abbrev ChiralCarrier := ChiralBlock Carrier
abbrev ChiralStage (n : ℕ) := ChiralBlock (Stage n)

/-! ## Entrywise stage maps -/

def chiralBond (n : ℕ) : ChiralStage n →+* ChiralStage (n + 1) where
  toFun := fun X i j => stageBond n (X i j)
  map_one' := by
    ext i j
    simp [Matrix.one_apply]
  map_mul' := by
    intro X Y
    ext i j
    simp [Matrix.mul_apply]
  map_zero' := by
    ext i j
    simp
  map_add' := by
    intro X Y
    ext i j
    simp

def chiralStageMap (n : ℕ) : ChiralStage n →+* ChiralCarrier where
  toFun := fun X i j => ofStage n (X i j)
  map_one' := by
    ext i j
    simp [Matrix.one_apply]
  map_mul' := by
    intro X Y
    ext i j
    simp [Matrix.mul_apply]
  map_zero' := by
    ext i j
    simp
  map_add' := by
    intro X Y
    ext i j
    simp

@[simp] theorem chiralStageMap_apply (n : ℕ) (X : ChiralStage n)
    (i j : Fin 2) :
    chiralStageMap n X i j = ofStage n (X i j) := rfl

theorem chiralStageMap_bond (n : ℕ) (X : ChiralStage n) :
    chiralStageMap (n + 1) (chiralBond n X) = chiralStageMap n X := by
  ext i j
  change ofStage (n + 1) (stageBond n (X i j)) = ofStage n (X i j)
  exact ofStage_apply_bond n (X i j)

/-! ## Finite chiral charges and their colimit readouts -/

@[simp] theorem chiralStageMap_qPlus (n : ℕ) (a : Stage n) :
    chiralStageMap n (chiralQPlus a) = chiralQPlus (ofStage n a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStageMap, chiralQPlus]

@[simp] theorem chiralStageMap_qMinus (n : ℕ) (b : Stage n) :
    chiralStageMap n (chiralQMinus b) = chiralQMinus (ofStage n b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStageMap, chiralQMinus]

@[simp] theorem chiralStageMap_parity (n : ℕ) :
    chiralStageMap n (chiralParity : ChiralStage n) =
      (chiralParity : ChiralCarrier) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStageMap, chiralParity]

@[simp] theorem chiralStageMap_dirac (n : ℕ) (a b : Stage n) :
    chiralStageMap n (chiralDirac a b) =
      chiralDirac (ofStage n a) (ofStage n b) := by
  simp [chiralDirac, map_add]

@[simp] theorem chiralStageMap_hamiltonian (n : ℕ) (a b : Stage n) :
    chiralStageMap n (chiralSUSYHamiltonian a b) =
      chiralSUSYHamiltonian (ofStage n a) (ofStage n b) := by
  simp [chiralSUSYHamiltonian, map_add, map_mul]

theorem carrier_qPlus_square (a : Carrier) :
    chiralQPlus a * chiralQPlus a = 0 :=
  chiralQPlus_sq a

theorem carrier_qMinus_square (b : Carrier) :
    chiralQMinus b * chiralQMinus b = 0 :=
  chiralQMinus_sq b

theorem carrier_parity_qPlus_anticomm (a : Carrier) :
    chiralParity * chiralQPlus a + chiralQPlus a * chiralParity = 0 :=
  chiralParity_qPlus_anticomm a

theorem carrier_parity_qMinus_anticomm (b : Carrier) :
    chiralParity * chiralQMinus b + chiralQMinus b * chiralParity = 0 :=
  chiralParity_qMinus_anticomm b

theorem carrier_parity_square :
    (chiralParity : ChiralCarrier) * chiralParity = 1 :=
  chiralParity_sq

theorem carrier_dirac_square (a b : Carrier) :
    chiralDirac a b * chiralDirac a b =
      chiralSUSYHamiltonian a b :=
  chiralDirac_sq_eq_susyHamiltonian a b

/-! ## The same chiral extension in the BitWord dialect -/

noncomputable def chiralCarrierEquiv :
    ChiralCarrier ≃+* ChiralBlock PrimonColimitAlgebra.PrimonUHFAlgebra where
  toFun := fun X i j => cliffordBitWordColimitEquiv (X i j)
  invFun := fun X i j => cliffordBitWordColimitEquiv.symm (X i j)
  left_inv := by
    intro X
    ext i j
    simp
  right_inv := by
    intro X
    ext i j
    simp
  map_mul' := by
    intro X Y
    ext i j
    simp [Matrix.mul_apply]
  map_add' := by
    intro X Y
    ext i j
    simp

@[simp] theorem chiralCarrierEquiv_stage (n : ℕ) (X : ChiralStage n) :
    chiralCarrierEquiv (chiralStageMap n X) =
      (fun i j => PrimonColimitAlgebra.toColimit n
        (clStageEquiv n (X i j))) := by
  ext i j
  simp [chiralCarrierEquiv, chiralStageMap, clStageEquiv]

@[simp] theorem chiralCarrierEquiv_qPlus (a : Carrier) :
    chiralCarrierEquiv (chiralQPlus a) =
      chiralQPlus (cliffordBitWordColimitEquiv a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralCarrierEquiv, chiralQPlus]

@[simp] theorem chiralCarrierEquiv_qMinus (b : Carrier) :
    chiralCarrierEquiv (chiralQMinus b) =
      chiralQMinus (cliffordBitWordColimitEquiv b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralCarrierEquiv, chiralQMinus]

@[simp] theorem chiralCarrierEquiv_parity :
    chiralCarrierEquiv (chiralParity : ChiralCarrier) =
      (chiralParity : ChiralBlock PrimonColimitAlgebra.PrimonUHFAlgebra) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralCarrierEquiv, chiralParity]

@[simp] theorem chiralCarrierEquiv_dirac (a b : Carrier) :
    chiralCarrierEquiv (chiralDirac a b) =
      chiralDirac (cliffordBitWordColimitEquiv a)
        (cliffordBitWordColimitEquiv b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralDirac, chiralCarrierEquiv, chiralQPlus, chiralQMinus]

@[simp] theorem chiralCarrierEquiv_hamiltonian (a b : Carrier) :
    chiralCarrierEquiv (chiralSUSYHamiltonian a b) =
      chiralSUSYHamiltonian (cliffordBitWordColimitEquiv a)
        (cliffordBitWordColimitEquiv b) := by
  simp only [chiralSUSYHamiltonian, map_add, map_mul,
    chiralCarrierEquiv_qPlus, chiralCarrierEquiv_qMinus]

/-! ## Trace transport on the chiral matrix extension -/

/-- The carrier equivalence commutes with the finite matrix trace.

This is the additive readout corresponding to the already established
entrywise ring equivalence; it keeps the chiral matrix extension distinct
from the scalar UHF carrier while making its trace transport explicit. -/
theorem chiralCarrierEquiv_trace (X : ChiralCarrier) :
    cliffordBitWordColimitEquiv (Matrix.trace X) =
      Matrix.trace (chiralCarrierEquiv X) := by
  simp [Matrix.trace, chiralCarrierEquiv]

/-- The normalized colimit readout sees the same scalar matrix trace before
and after the chiral carrier equivalence.  This is the scalar-state bridge for
the finite chiral extension; it does not identify the extension with the
scalar carrier. -/
theorem tauInfinity_chiralCarrierEquiv_trace (X : ChiralCarrier) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
        (cliffordBitWordColimitEquiv (Matrix.trace X)) =
      InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
        (Matrix.trace (chiralCarrierEquiv X)) := by
  rw [chiralCarrierEquiv_trace]

/-! The parity-inserted trace is the finite supertrace readout.  This is a
genuine transport identity for the existing chiral extension; it does not
identify this readout with a zeta or zero-counting formula. -/
theorem chiralCarrierEquiv_supertrace (X : ChiralCarrier) :
    cliffordBitWordColimitEquiv (Matrix.trace (chiralParity * X)) =
      Matrix.trace (chiralParity * chiralCarrierEquiv X) := by
  rw [chiralCarrierEquiv_trace, map_mul, chiralCarrierEquiv_parity]

/-- The parity-inserted trace annihilates the finite odd chiral charge. -/
theorem chiral_supertrace_qPlus_zero (a : Carrier) :
    Matrix.trace (chiralParity * chiralQPlus a) = 0 := by
  simp [chiralParity, chiralQPlus, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_two]

/-- The parity-inserted trace annihilates the finite odd chiral charge. -/
theorem chiral_supertrace_qMinus_zero (b : Carrier) :
    Matrix.trace (chiralParity * chiralQMinus b) = 0 := by
  simp [chiralParity, chiralQMinus, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_two]

/-- The parity-inserted trace annihilates the finite odd Dirac operator. -/
theorem chiral_supertrace_dirac_zero (a b : Carrier) :
    Matrix.trace (chiralParity * chiralDirac a b) = 0 := by
  simp only [chiralDirac, Matrix.mul_add, Matrix.trace_add,
    chiral_supertrace_qPlus_zero, chiral_supertrace_qMinus_zero, add_zero]

/-- The parity supertrace of the chiral SUSY Hamiltonian is the carrier
commutator of its two coefficient operators. -/
theorem chiral_supertrace_hamiltonian_eq_commutator (a b : Carrier) :
    Matrix.trace (chiralParity * chiralSUSYHamiltonian a b) =
      a * b - b * a := by
  simp [chiralParity, chiralSUSYHamiltonian, chiralQPlus, chiralQMinus,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]

/-- The finite chiral trace is transported entrywise to the BitWord colimit. -/
theorem chiralCarrierEquiv_stage_trace (n : ℕ) (X : ChiralStage n) :
    cliffordBitWordColimitEquiv
        (Matrix.trace (chiralStageMap n X)) =
      Matrix.trace (fun i j =>
        PrimonColimitAlgebra.toColimit n (clStageEquiv n (X i j))) := by
  rw [chiralCarrierEquiv_trace, chiralCarrierEquiv_stage]

/-- The supersymmetry square is preserved by the common-carrier equivalence. -/
theorem chiralCarrierEquiv_dirac_square (a b : Carrier) :
    chiralDirac (cliffordBitWordColimitEquiv a)
        (cliffordBitWordColimitEquiv b) *
        chiralDirac (cliffordBitWordColimitEquiv a)
          (cliffordBitWordColimitEquiv b) =
      chiralSUSYHamiltonian (cliffordBitWordColimitEquiv a)
        (cliffordBitWordColimitEquiv b) := by
  calc
    chiralDirac (cliffordBitWordColimitEquiv a)
          (cliffordBitWordColimitEquiv b) *
        chiralDirac (cliffordBitWordColimitEquiv a)
          (cliffordBitWordColimitEquiv b) =
        chiralCarrierEquiv (chiralDirac a b) *
        chiralCarrierEquiv (chiralDirac a b) := by
          rw [chiralCarrierEquiv_dirac]
    _ = chiralCarrierEquiv (chiralDirac a b * chiralDirac a b) := by
          rw [map_mul]
    _ = chiralCarrierEquiv (chiralSUSYHamiltonian a b) := by
          rw [carrier_dirac_square]
    _ = chiralSUSYHamiltonian (cliffordBitWordColimitEquiv a)
          (cliffordBitWordColimitEquiv b) :=
      chiralCarrierEquiv_hamiltonian a b

end InfoGeometry.Clifford.SupergradedCliffordColimit

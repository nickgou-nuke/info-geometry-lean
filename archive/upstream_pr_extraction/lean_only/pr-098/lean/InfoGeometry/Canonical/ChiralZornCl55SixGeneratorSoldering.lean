import InfoGeometry.Canonical.Cl55ThreeColorWittChannels
import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator

/-!
# Six-generator chiral soldering into the `Cl(5,5)` Witt carrier

The six operators are the existing three creation and three annihilation
channels.  This owner packages their componentwise readout and the already
proved operator-valued Hodge/bivector calculus.  It does not assert a
multiplicative embedding of the non-associative Zorn algebra.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.ChiralZornCl55SixGeneratorSoldering

open InfoGeometry.Canonical
open InfoGeometry.Canonical.Cl55ThreeColorWittChannels
open InfoGeometry.Canonical.Cl55WittLieRouting
open InfoGeometry.Clifford.Cl11TensorTower

abbrev GammaPlusVector : OperatorVector (MatStage 5) := GammaPlus
abbrev GammaMinusVector : OperatorVector (MatStage 5) := GammaMinus

@[simp] theorem GammaPlusVector_apply (i : Fin 3) :
    GammaPlusVector i = GammaPlus i := rfl

@[simp] theorem GammaMinusVector_apply (i : Fin 3) :
    GammaMinusVector i = GammaMinus i := rfl

theorem GammaPlus_metric_readout (i j : Fin 3) :
    GammaPlusVector i * GammaMinusVector j +
        GammaMinusVector j * GammaPlusVector i =
      if i = j then (1 : MatStage 5) else 0 :=
  Gamma_anticomm_metric_readout i j

theorem GammaPlus_hodge_bivector_readout (i j : Fin 3) :
    bracket (GammaPlusVector i) (GammaPlusVector j) =
      (2 : ℝ) • (GammaPlusVector i * GammaPlusVector j) :=
  GammaPlus_commutator_bivector_readout i j

theorem GammaMinus_hodge_bivector_readout (i j : Fin 3) :
    bracket (GammaMinusVector i) (GammaMinusVector j) =
      (2 : ℝ) • (GammaMinusVector i * GammaMinusVector j) :=
  GammaMinus_commutator_bivector_readout i j

theorem GammaPlus_mixed_grade_zero_readout (i j : Fin 3) :
    bracket (GammaPlusVector i) (GammaMinusVector j) =
      (2 : ℝ) • E (colorToCl55Index i) (colorToCl55Index j) :=
  Gamma_mixed_commutator_grade_zero_readout i j

def GammaPlusCommutatorVector : OperatorVector (MatStage 5) :=
  fun c => match c with
  | 0 => bracket (GammaPlusVector 1) (GammaPlusVector 2)
  | 1 => bracket (GammaPlusVector 2) (GammaPlusVector 0)
  | 2 => bracket (GammaPlusVector 0) (GammaPlusVector 1)

def GammaMinusCommutatorVector : OperatorVector (MatStage 5) :=
  fun c => match c with
  | 0 => bracket (GammaMinusVector 1) (GammaMinusVector 2)
  | 1 => bracket (GammaMinusVector 2) (GammaMinusVector 0)
  | 2 => bracket (GammaMinusVector 0) (GammaMinusVector 1)

theorem GammaPlus_hodge_self_eq_commutatorVector :
    operatorHodgeDual2 (operatorWedge2 GammaPlusVector GammaPlusVector) =
      GammaPlusCommutatorVector := by
  rw [operatorHodgeDual2_wedge_eq_operatorCross]
  funext c
  fin_cases c <;> rfl

theorem GammaMinus_hodge_self_eq_commutatorVector :
    operatorHodgeDual2 (operatorWedge2 GammaMinusVector GammaMinusVector) =
      GammaMinusCommutatorVector := by
  rw [operatorHodgeDual2_wedge_eq_operatorCross]
  funext c
  fin_cases c <;> rfl

theorem GammaPlusCommutatorVector_mem_wittPosTwo (c : Fin 3) :
    GammaPlusCommutatorVector c ∈ wittPosTwo := by
  fin_cases c
  · exact GammaPlus_commutator_mem_wittPosTwo 1 2
  · exact GammaPlus_commutator_mem_wittPosTwo 2 0
  · exact GammaPlus_commutator_mem_wittPosTwo 0 1

theorem GammaMinusCommutatorVector_mem_wittNegTwo (c : Fin 3) :
    GammaMinusCommutatorVector c ∈ wittNegTwo := by
  fin_cases c
  · exact GammaMinus_commutator_mem_wittNegTwo 1 2
  · exact GammaMinus_commutator_mem_wittNegTwo 2 0
  · exact GammaMinus_commutator_mem_wittNegTwo 0 1

theorem Gamma_mixed_commutator_mem_wittZero (i j : Fin 3) :
    bracket (GammaPlusVector i) (GammaMinusVector j) ∈ wittZero :=
  Cl55ThreeColorWittChannels.Gamma_mixed_commutator_mem_wittZero i j

end InfoGeometry.Canonical.ChiralZornCl55SixGeneratorSoldering

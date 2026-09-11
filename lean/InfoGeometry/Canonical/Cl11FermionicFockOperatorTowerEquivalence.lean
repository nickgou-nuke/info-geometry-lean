import InfoGeometry.Clifford.MatToCantorOperator
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.JordanWignerCantorColimit
import InfoGeometry.Canonical.JordanWignerCantorRepresentation
import InfoGeometry.Clifford.Cl11JordanWignerCARBridge

/-!
# `Cl(1,1)` tensor tower = finite fermionic Fock operator tower

The finite tensor stages are identified with endomorphism algebras of the
binary occupation modules.  This file is the canonical bridge between the
matrix presentation and the Fock presentation; it does not introduce a new
Fock carrier or a bosonic completion.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence

open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.MatToCantorOperator
open InfoGeometry.Clifford.Cl11JordanWignerCARBridge
open InfoGeometry.Canonical.JordanWignerCantorColimit
open InfoGeometry.Canonical.JordanWignerCantorRepresentation

abbrev FockStage (n : ℕ) : Type := Idx n → ℝ
abbrev FockOpStage (n : ℕ) : Type := Module.End ℝ (FockStage n)
abbrev ClStage (n : ℕ) : Type := MatStage n

noncomputable def clToFockOp (n : ℕ) : ClStage n ≃ₐ[ℝ] FockOpStage n :=
  matToCantor n

@[simp] theorem clToFockOp_apply (n : ℕ) (A : ClStage n) :
    clToFockOp n A = Matrix.toLin' A := by
  rfl

noncomputable def fockOpBond (n : ℕ) :
    FockOpStage n →ₐ[ℝ] FockOpStage (n + 1) := cantorOpEmbed n

theorem clToFockOp_natural (n : ℕ) (A : ClStage n) :
    fockOpBond n (clToFockOp n A) =
      clToFockOp (n + 1) (matStageEmbed n A) := by
  exact cantorOpEmbed_matToCantor n A

theorem clToFockOp_symm_natural (n : ℕ) (T : FockOpStage n) :
    matStageEmbed n ((clToFockOp n).symm T) =
      (clToFockOp (n + 1)).symm (fockOpBond n T) := by
  exact inverse_coherence n T

def fockCreation (n : ℕ) (k : Fin n) : FockOpStage n :=
  clToFockOp n (jwCreation n k)

def fockAnnihilation (n : ℕ) (k : Fin n) : FockOpStage n :=
  clToFockOp n (jwAnnihilation n k)

@[simp] theorem fockCreation_bond (n : ℕ) (k : Fin n) :
    fockOpBond n (fockCreation n k) =
      fockCreation (n + 1) k.castSucc := by
  unfold fockCreation
  rw [clToFockOp_natural]
  exact congrArg (clToFockOp (n + 1)) (matStageEmbed_jwCreation k)

@[simp] theorem fockAnnihilation_bond (n : ℕ) (k : Fin n) :
    fockOpBond n (fockAnnihilation n k) =
      fockAnnihilation (n + 1) k.castSucc := by
  unfold fockAnnihilation
  rw [clToFockOp_natural]
  exact congrArg (clToFockOp (n + 1)) (matStageEmbed_jwAnnihilation k)

theorem fock_same_site_car (n : ℕ) (k : Fin n) :
    fockAnnihilation n k * fockCreation n k +
      fockCreation n k * fockAnnihilation n k = 1 := by
  unfold fockCreation fockAnnihilation
  rw [← map_mul, ← map_mul, ← map_add, jw_same_site_car]
  exact map_one (clToFockOp n)

theorem fock_creation_cross_site_car (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    fockCreation n i * fockCreation n j +
      fockCreation n j * fockCreation n i = 0 := by
  unfold fockCreation
  rw [← map_mul, ← map_mul, ← map_add]
  rw [InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.creation_cross_site_anticommute
    n i j hij]
  exact map_zero (clToFockOp n)

theorem fock_annihilation_cross_site_car (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    fockAnnihilation n i * fockAnnihilation n j +
      fockAnnihilation n j * fockAnnihilation n i = 0 := by
  unfold fockAnnihilation
  rw [← map_mul, ← map_mul, ← map_add]
  rw [InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.annihilation_cross_site_anticommute
    n i j hij]
  exact map_zero (clToFockOp n)

theorem fock_mixed_car (n : ℕ) (i j : Fin n) :
    fockAnnihilation n i * fockCreation n j +
      fockCreation n j * fockAnnihilation n i = if i = j then 1 else 0 := by
  unfold fockCreation fockAnnihilation
  simpa using congrArg (clToFockOp n)
    (jwAnnihilation_creation_anticommutator n i j)

abbrev FockOpLimit : Type := RealCantorOpInf
abbrev ClLimit : Type := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

noncomputable def clLimitFockOpAlgEquiv : ClLimit ≃ₐ[ℝ] FockOpLimit :=
  InfoGeometry.Canonical.JordanWignerCantorRepresentation.globalRealCantorAlgEquiv

noncomputable def clLimitFockOpEquiv : ClLimit ≃+* FockOpLimit :=
  clLimitFockOpAlgEquiv.toRingEquiv

@[simp] theorem clLimitFockOpEquiv_ofStage (n : ℕ) (A : ClStage n) :
    clLimitFockOpEquiv (MatOfStage n A) =
      realCantorOfStage n (clToFockOp n A) := by
  exact InfoGeometry.Canonical.JordanWignerCantorRepresentation.globalRealCantorAlgEquiv_ofStage
    n A

@[simp] theorem clLimitFockOpEquiv_symm_ofStage (n : ℕ) (T : FockOpStage n) :
    clLimitFockOpEquiv.symm (realCantorOfStage n T) =
      MatOfStage n ((clToFockOp n).symm T) := by
  exact InfoGeometry.Canonical.JordanWignerCantorRepresentation.globalCantorInverseEquiv_ofStage
    n T

theorem cl11_fermionicFock_operator_tower_packet (n : ℕ) (k : Fin n) :
    (fockOpBond n (clToFockOp n (1 : ClStage n)) =
      clToFockOp (n + 1) (matStageEmbed n (1 : ClStage n))) ∧
    (fockAnnihilation n k * fockCreation n k +
      fockCreation n k * fockAnnihilation n k = 1) := by
  exact ⟨clToFockOp_natural n 1, fock_same_site_car n k⟩

end InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence

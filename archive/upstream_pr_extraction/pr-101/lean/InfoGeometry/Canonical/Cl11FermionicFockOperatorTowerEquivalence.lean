import InfoGeometry.Clifford.MatToCantorOperator
import InfoGeometry.Canonical.JordanWignerCantorColimit
import InfoGeometry.Canonical.JordanWignerCantorRepresentation
import InfoGeometry.Clifford.Cl11JordanWignerCARBridge

/-!
# `Cl(1,1)` tensor tower = finite fermionic Fock operator tower

The finite `Cl(1,1)` tensor stage is the full matrix algebra on `2^n`
occupation states.  The corresponding finite fermionic Fock state space is the
real function space on the binary occupation basis, and its operator algebra is
its full endomorphism algebra.

This owner gives the dimensionally correct equivalence

`MatStage n ≃ₐ[ℝ] End(FockStage n)`

and reuses the already-proved naturality of `Matrix.toLinAlgEquiv'` under the
tensor-with-identity bonding maps.  It then identifies the direct limit of the
Clifford matrix tower with the direct limit of these finite Fock operator
algebras.

This is an algebraic fermionic Fock-operator theorem.  It is not an
identification with the external bosonic `ChargedFockSpace`, which is a
Heisenberg Verma module and requires a separate bosonization intertwiner.
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

/-- Finite fermionic occupation/Fock state space on the native binary basis. -/
abbrev FockStage (n : ℕ) : Type := Idx n → ℝ

/-- Full operator algebra on the finite fermionic Fock stage. -/
abbrev FockOpStage (n : ℕ) : Type := Module.End ℝ (FockStage n)

/-- The finite Clifford tensor stage. -/
abbrev ClStage (n : ℕ) : Type := MatStage n

/-- The exact finite-stage algebra equivalence
`Cl(1,1)^{⊗ n} ≃ End(Fock_n)`. -/
noncomputable def clToFockOp (n : ℕ) :
    ClStage n ≃ₐ[ℝ] FockOpStage n :=
  matToCantor n

@[simp] theorem clToFockOp_apply (n : ℕ) (A : ClStage n) :
    clToFockOp n A = Matrix.toLin' A := by
  rfl

/-- The Fock-operator bonding map induced by adjoining one binary occupation
site.  It is the transport of `A ↦ A ⊗ I₂` through the finite algebra
equivalence. -/
noncomputable def fockOpBond (n : ℕ) :
    FockOpStage n →ₐ[ℝ] FockOpStage (n + 1) :=
  cantorOpEmbed n

/-- The finite Clifford/Fock equivalences form a natural isomorphism of the two
successor towers. -/
theorem clToFockOp_natural (n : ℕ) (A : ClStage n) :
    fockOpBond n (clToFockOp n A) =
      clToFockOp (n + 1) (matStageEmbed n A) := by
  exact cantorOpEmbed_matToCantor n A

/-- The inverse equivalences satisfy the same naturality square. -/
theorem clToFockOp_symm_natural (n : ℕ) (T : FockOpStage n) :
    matStageEmbed n ((clToFockOp n).symm T) =
      (clToFockOp (n + 1)).symm (fockOpBond n T) := by
  exact inverse_coherence n T

/-- Finite fermionic creation operator: the Jordan--Wigner creation matrix
viewed as an actual endomorphism of the occupation-space module. -/
def fockCreation (n : ℕ) (k : Fin n) : FockOpStage n :=
  clToFockOp n (jwCreation n k)

/-- Finite fermionic annihilation operator. -/
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

/-- Same-site finite fermionic CAR in the Fock-operator presentation. -/
theorem fock_same_site_car (n : ℕ) (k : Fin n) :
    fockAnnihilation n k * fockCreation n k +
      fockCreation n k * fockAnnihilation n k = 1 := by
  unfold fockCreation fockAnnihilation
  rw [← map_mul, ← map_mul, ← map_add, jw_same_site_car]
  exact map_one (clToFockOp n)

/-- Creation operators anticommute at distinct sites. -/
theorem fock_creation_cross_site_car
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    fockCreation n i * fockCreation n j +
      fockCreation n j * fockCreation n i = 0 := by
  unfold fockCreation
  rw [← map_mul, ← map_mul, ← map_add]
  rw [InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.creation_cross_site_anticommute
    n i j hij]
  exact map_zero (clToFockOp n)

/-- Annihilation operators anticommute at distinct sites. -/
theorem fock_annihilation_cross_site_car
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    fockAnnihilation n i * fockAnnihilation n j +
      fockAnnihilation n j * fockAnnihilation n i = 0 := by
  unfold fockAnnihilation
  rw [← map_mul, ← map_mul, ← map_add]
  rw [InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.annihilation_cross_site_anticommute
    n i j hij]
  exact map_zero (clToFockOp n)

/-- Mixed creation/annihilation CAR at arbitrary sites. -/
theorem fock_mixed_car (n : ℕ) (i j : Fin n) :
    fockAnnihilation n i * fockCreation n j +
      fockCreation n j * fockAnnihilation n i =
        if i = j then 1 else 0 := by
  unfold fockCreation fockAnnihilation
  rw [← map_mul, ← map_mul, ← map_add,
    jwAnnihilation_creation_anticommutator]
  by_cases hij : i = j <;> simp [hij]

/-- Algebraic direct limit of the finite fermionic Fock operator tower. -/
abbrev FockOpLimit : Type := RealLimit

/-- Algebraic direct limit of the `Cl(1,1)` tensor tower. -/
abbrev ClLimit : Type := MatLimit

/-- Canonical global ring equivalence induced by the natural finite-stage
Clifford/Fock operator equivalences. -/
noncomputable def clLimitFockOpEquiv : ClLimit ≃+* FockOpLimit :=
  globalCantorInverseEquiv.symm

/-- Global algebra equivalence with the native scalar actions. -/
noncomputable def clLimitFockOpAlgEquiv :
    InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit ≃ₐ[ℝ]
      InfoGeometry.Canonical.JordanWignerCantorRepresentation.RealCantorOpInf :=
  InfoGeometry.Canonical.JordanWignerCantorRepresentation.globalRealCantorAlgEquiv

/-- The global equivalence is induced stagewise by `clToFockOp`. -/
@[simp] theorem clLimitFockOpEquiv_ofStage (n : ℕ) (A : ClStage n) :
    clLimitFockOpEquiv (MatOfStage n A) =
      realOfStage n (clToFockOp n A) := by
  exact matToRealLimit_ofStage n A

/-- The inverse global equivalence recovers every finite Clifford representative. -/
@[simp] theorem clLimitFockOpEquiv_symm_ofStage
    (n : ℕ) (T : FockOpStage n) :
    clLimitFockOpEquiv.symm (realOfStage n T) =
      MatOfStage n ((clToFockOp n).symm T) := by
  exact realToMatLimit_ofStage n T

/-- Consolidated finite-to-infinite theorem: the `Cl(1,1)` tensor tower and
finite fermionic Fock operator tower are naturally stagewise equivalent, their
creation/annihilation channels satisfy CAR, and the natural equivalence descends
to an equivalence of algebraic direct limits. -/
theorem cl11_fermionicFock_operator_tower_packet (n : ℕ) (k : Fin n) :
    (fockOpBond n (clToFockOp n (1 : ClStage n)) =
      clToFockOp (n + 1) (matStageEmbed n (1 : ClStage n))) ∧
    (fockAnnihilation n k * fockCreation n k +
      fockCreation n k * fockAnnihilation n k = 1) := by
  exact ⟨clToFockOp_natural n 1, fock_same_site_car n k⟩

end InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence

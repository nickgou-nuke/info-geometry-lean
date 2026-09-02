import Mathlib.Tactic
import InfoGeometry.Canonical.Cl55ChiralOccupationFiveGradeBridge
import InfoGeometry.Canonical.Cl11WittOccupationParityFactorization

/-!
# Cl(5,5) chiral parity, centering, and projector intertwiners

This owner completes the finite algebraic bridge between:

* one-mode occupation `e_i f_i`;
* the local chirality factor `1 - 2 e_i f_i = -2 H_i`;
* the centered five-grade Cartan operator;
* global spinor chirality as the ordered product of the five local factors;
* chiral projectors and the odd CAR sheet-changing operators.

The scalar `5/2` is recorded only as the exact finite centering constant. No
claim is made here that it is, by itself, a physical Hamiltonian vacuum energy.
Likewise, the global product is the native ordered noncommutative tensor-stage
product, not an unordered `Finset.prod`.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55ChiralParityNormalOrderingBridge

open scoped Matrix Kronecker BigOperators
open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Canonical.Cl55WittLieRouting
open InfoGeometry.Physics.Cl55SpinorCartanFock
open InfoGeometry.Canonical.Cl55ChiralOccupationFiveGradeBridge
open InfoGeometry.Canonical.Cl11WittOccupationParityFactorization

abbrev FockOp := InfoGeometry.Clifford.Cl11TensorTower.MatStage 5

/-- Occupation of one native Witt-CAR mode. -/
def cl55ModeOccupation (i : Fin 5) : FockOp :=
  creation i * annihilation i

/-- Vacancy of one native Witt-CAR mode. -/
def cl55ModeVacancy (i : Fin 5) : FockOp :=
  annihilation i * creation i

/-- The chirality convention compatible with `gamma_chiral_base`:
`K_i = 1 - 2 e_i f_i`. -/
def cl55ModeChiralityFactor (i : Fin 5) : FockOp :=
  (1 : FockOp) - (2 : ℝ) • cl55ModeOccupation i

/-- Occupation and vacancy resolve the identity. -/
theorem cl55ModeOccupation_add_vacancy (i : Fin 5) :
    cl55ModeOccupation i + cl55ModeVacancy i = 1 := by
  simpa [cl55ModeOccupation, cl55ModeVacancy] using
    creation_annihilation_same_site i

/-- One-mode occupation is an idempotent. -/
theorem cl55ModeOccupation_idempotent (i : Fin 5) :
    cl55ModeOccupation i * cl55ModeOccupation i = cl55ModeOccupation i := by
  unfold cl55ModeOccupation
  have hcar := creation_annihilation_same_site i
  have hswap :
      annihilation i * creation i =
        1 - creation i * annihilation i :=
    eq_sub_of_add_eq' hcar
  calc
    (creation i * annihilation i) *
        (creation i * annihilation i) =
      creation i * (annihilation i * creation i) * annihilation i := by
        noncomm_ring
    _ = creation i * (1 - creation i * annihilation i) * annihilation i := by
      rw [hswap]
    _ = creation i * annihilation i := by
      rw [show creation i * (1 - creation i * annihilation i) * annihilation i =
          creation i * annihilation i -
            (creation i * creation i) *
              (annihilation i * annihilation i) by noncomm_ring]
      rw [creation_same_site_sq, annihilation_same_site_sq]
      simp

/-- The native chirality convention is vacancy minus occupation. -/
theorem cl55ModeChiralityFactor_eq_vacancy_sub_occupation (i : Fin 5) :
    cl55ModeChiralityFactor i =
      cl55ModeVacancy i - cl55ModeOccupation i := by
  have hcar := cl55ModeOccupation_add_vacancy i
  rw [show (1 : FockOp) =
      cl55ModeOccupation i + cl55ModeVacancy i by exact hcar.symm]
  unfold cl55ModeChiralityFactor
  module

/-- The local chirality factor is the `-2` normalization of the centered Cartan
mode `H_i = e_i f_i - 1/2`. -/
theorem cl55ModeChiralityFactor_eq_neg_two_smul_H (i : Fin 5) :
    cl55ModeChiralityFactor i = (-2 : ℝ) • H i := by
  change
    (1 : FockOp) - (2 : ℝ) • (creation i * annihilation i) =
      (-2 : ℝ) •
        (creation i * annihilation i -
          (1 / 2 : ℝ) • (1 : FockOp))
  module

/-- Every local chirality factor is an involution. -/
theorem cl55ModeChiralityFactor_sq (i : Fin 5) :
    cl55ModeChiralityFactor i * cl55ModeChiralityFactor i = 1 := by
  unfold cl55ModeChiralityFactor
  have hN := cl55ModeOccupation_idempotent i
  noncomm_ring [hN]

/-- The fixed-stage factor is definitionally the general tensor-tower factor. -/
theorem cl55ModeChiralityFactor_eq_towerFactor (i : Fin 5) :
    cl55ModeChiralityFactor i = modeChiralityFactor 5 i := by
  rfl

/-- The canonical five-mode ordered product. -/
def cl55OrderedModeChiralityProduct : FockOp :=
  orderedModeChiralityProduct 5

/-- Global `Cl(5,5)` spinor chirality is exactly the ordered product of the five
local algebraic factors `1 - 2 e_i f_i`. -/
theorem gammaChiral_eq_cl55OrderedModeChiralityProduct :
    gammaChiral = cl55OrderedModeChiralityProduct := by
  simpa [gammaChiral, cl55OrderedModeChiralityProduct] using
    (orderedModeChiralityProduct_eq_globalChirality 5).symm

/-- The ordered local-parity product is an involution. -/
theorem cl55OrderedModeChiralityProduct_sq :
    cl55OrderedModeChiralityProduct * cl55OrderedModeChiralityProduct = 1 := by
  simpa [cl55OrderedModeChiralityProduct] using
    orderedModeChiralityProduct_sq 5

/-! ## Finite centering / normal-ordering readout -/

/-- Finite centered occupation, obtained by subtracting the exact scalar
`5/2` shift. This is the finite Cartan centering readout. -/
def centeredFockNumber : FockOp :=
  rawFockNumber - (5 / 2 : ℝ) • (1 : FockOp)

/-- Finite centered occupation is exactly the repository-owned five-grade
Cartan generator. -/
theorem centeredFockNumber_eq_numberOperator :
    centeredFockNumber = numberOperator := by
  unfold centeredFockNumber
  rw [rawFockNumber_eq_numberOperator_add_five_halves]
  module

/-- The exact centering shift leaves the adjoint action unchanged. -/
theorem centeredFockNumber_bracket (X : FockOp) :
    bracket centeredFockNumber X = bracket rawFockNumber X := by
  rw [centeredFockNumber_eq_numberOperator,
    rawFockNumber_bracket_eq_numberOperator_bracket]

/-! ## Native `Commute` packets -/

/-- Raw occupation commutes with spinor chirality. -/
theorem rawFockNumber_commute_gammaChiral :
    Commute rawFockNumber gammaChiral := by
  show rawFockNumber * gammaChiral = gammaChiral * rawFockNumber
  exact gammaChiral_rawFockNumber_comm.symm

/-- Raw occupation commutes with the positive chiral projector. -/
theorem rawFockNumber_commute_PPlus :
    Commute rawFockNumber PPlus := by
  show rawFockNumber * PPlus = PPlus * rawFockNumber
  exact rawFockNumber_PPlus_comm

/-- Raw occupation commutes with the negative chiral projector. -/
theorem rawFockNumber_commute_PMinus :
    Commute rawFockNumber PMinus := by
  show rawFockNumber * PMinus = PMinus * rawFockNumber
  exact rawFockNumber_PMinus_comm

/-! ## Direct projector intertwiners -/

/-- Positive projector moved through creation becomes the negative projector. -/
@[simp] theorem PPlus_mul_creation_eq_creation_mul_PMinus (i : Fin 5) :
    PPlus * creation i = creation i * PMinus := by
  unfold PPlus PMinus
  have he := gammaChiral_e_anticomm i
  noncomm_ring [he]

/-- Negative projector moved through creation becomes the positive projector. -/
@[simp] theorem PMinus_mul_creation_eq_creation_mul_PPlus (i : Fin 5) :
    PMinus * creation i = creation i * PPlus := by
  unfold PPlus PMinus
  have he := gammaChiral_e_anticomm i
  noncomm_ring [he]

/-- Positive projector moved through annihilation becomes the negative projector. -/
@[simp] theorem PPlus_mul_annihilation_eq_annihilation_mul_PMinus (i : Fin 5) :
    PPlus * annihilation i = annihilation i * PMinus := by
  unfold PPlus PMinus
  have hf := gammaChiral_f_anticomm i
  noncomm_ring [hf]

/-- Negative projector moved through annihilation becomes the positive projector. -/
@[simp] theorem PMinus_mul_annihilation_eq_annihilation_mul_PPlus (i : Fin 5) :
    PMinus * annihilation i = annihilation i * PPlus := by
  unfold PPlus PMinus
  have hf := gammaChiral_f_anticomm i
  noncomm_ring [hf]

/-- Right-sided creation intertwiner. -/
theorem creation_mul_PPlus_eq_PMinus_mul_creation (i : Fin 5) :
    creation i * PPlus = PMinus * creation i :=
  (PMinus_mul_creation_eq_creation_mul_PPlus i).symm

/-- Right-sided creation intertwiner on the other sheet. -/
theorem creation_mul_PMinus_eq_PPlus_mul_creation (i : Fin 5) :
    creation i * PMinus = PPlus * creation i :=
  (PPlus_mul_creation_eq_creation_mul_PMinus i).symm

/-- Right-sided annihilation intertwiner. -/
theorem annihilation_mul_PPlus_eq_PMinus_mul_annihilation (i : Fin 5) :
    annihilation i * PPlus = PMinus * annihilation i :=
  (PMinus_mul_annihilation_eq_annihilation_mul_PPlus i).symm

/-- Right-sided annihilation intertwiner on the other sheet. -/
theorem annihilation_mul_PMinus_eq_PPlus_mul_annihilation (i : Fin 5) :
    annihilation i * PMinus = PPlus * annihilation i :=
  (PPlus_mul_annihilation_eq_annihilation_mul_PMinus i).symm

/-- Direct intertwiner derivation of the positive-to-negative creation route. -/
theorem creation_sheet_transition_from_intertwining (i : Fin 5) :
    PMinus * creation i * PPlus = creation i * PPlus := by
  rw [PMinus_mul_creation_eq_creation_mul_PPlus, ← mul_assoc, PPlus_sq]

/-- Direct intertwiner derivation of the positive-to-negative annihilation route. -/
theorem annihilation_sheet_transition_from_intertwining (i : Fin 5) :
    PMinus * annihilation i * PPlus = annihilation i * PPlus := by
  rw [PMinus_mul_annihilation_eq_annihilation_mul_PPlus, ← mul_assoc, PPlus_sq]

/-- Complete finite parity/centering/intertwining packet. -/
theorem cl55_parity_normal_ordering_intertwining_packet (i : Fin 5) :
    cl55ModeChiralityFactor i = (-2 : ℝ) • H i ∧
    gammaChiral = cl55OrderedModeChiralityProduct ∧
    centeredFockNumber = numberOperator ∧
    Commute rawFockNumber gammaChiral ∧
    PPlus * creation i = creation i * PMinus ∧
    PMinus * annihilation i = annihilation i * PPlus := by
  exact ⟨cl55ModeChiralityFactor_eq_neg_two_smul_H i,
    gammaChiral_eq_cl55OrderedModeChiralityProduct,
    centeredFockNumber_eq_numberOperator,
    rawFockNumber_commute_gammaChiral,
    PPlus_mul_creation_eq_creation_mul_PMinus i,
    PMinus_mul_annihilation_eq_annihilation_mul_PPlus i⟩

end InfoGeometry.Canonical.Cl55ChiralParityNormalOrderingBridge

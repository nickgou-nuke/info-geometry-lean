import Mathlib.Tactic
import InfoGeometry.Physics.Cl55SpinorCartanFock
import InfoGeometry.Canonical.Cl55WittLieRouting

/-!
# Cl(5,5) chiral occupation and five-grade bridge

This owner separates and then relates four native notions:

* raw Fock occupation `N_F = Σᵢ eᵢ fᵢ`;
* the centered Cartan/five-grade generator `N_C = Σᵢ Eᵢᵢ`;
* spinor chirality `Γ_*` and its complementary projectors `P_±`;
* projected chiral occupations `N_± = P_± N_F P_±`.

The scalar shift between `N_F` and `N_C` is invisible to commutator grading but
is essential for the particle-number interpretation.  The final section shows
that `N_±` and one CAR creation/annihilation pair reconstruct an exact real
four-component causal potential.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55ChiralOccupationFiveGradeBridge

open scoped Matrix Kronecker BigOperators
open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Canonical.Cl55WittLieRouting
open InfoGeometry.Physics.Cl55SpinorCartanFock

abbrev FockOp := InfoGeometry.Clifford.Cl11TensorTower.MatStage 5
abbrev RealFockFourPotential := Fin 4 → FockOp

/-- Raw five-mode occupation operator `N_F = Σᵢ eᵢ fᵢ`. -/
def rawFockNumber : FockOp :=
  ∑ i : Fin 5, creation i * annihilation i

/-- The centered five-grade Cartan generator differs from raw occupation by
`5/2` times the identity. -/
theorem rawFockNumber_eq_numberOperator_add_five_halves :
    rawFockNumber = numberOperator + (5 / 2 : ℝ) • (1 : FockOp) := by
  unfold rawFockNumber numberOperator E
  rw [Fin.sum_univ_five, Fin.sum_univ_five]
  simp
  module

/-- Raw occupation and the centered Cartan operator induce the same adjoint
grading because their difference is central. -/
theorem rawFockNumber_bracket_eq_numberOperator_bracket (X : FockOp) :
    bracket rawFockNumber X = bracket numberOperator X := by
  rw [rawFockNumber_eq_numberOperator_add_five_halves]
  unfold bracket
  simp

/-- Raw occupation has grade `+1` on every creation generator. -/
theorem rawFockNumber_creation (i : Fin 5) :
    bracket rawFockNumber (creation i) = creation i := by
  rw [rawFockNumber_bracket_eq_numberOperator_bracket]
  exact numberOperator_creation i

/-- Raw occupation has grade `-1` on every annihilation generator. -/
theorem rawFockNumber_annihilation (i : Fin 5) :
    bracket rawFockNumber (annihilation i) = -annihilation i := by
  rw [rawFockNumber_bracket_eq_numberOperator_bracket]
  exact numberOperator_annihilation i

/-- Each even occupation bilinear commutes with spinor chirality; hence so does
`N_F`. -/
theorem gammaChiral_rawFockNumber_comm :
    gammaChiral * rawFockNumber = rawFockNumber * gammaChiral := by
  unfold rawFockNumber
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have he := gammaChiral_e_anticomm i
  have hf := gammaChiral_f_anticomm i
  change gammaChiral * (creation i * annihilation i) =
    (creation i * annihilation i) * gammaChiral
  change gammaChiral * creation i = -(creation i * gammaChiral) at he
  change gammaChiral * annihilation i = -(annihilation i * gammaChiral) at hf
  calc
    gammaChiral * (creation i * annihilation i) =
        (gammaChiral * creation i) * annihilation i := by
          rw [mul_assoc]
    _ = (-(creation i * gammaChiral)) * annihilation i := by rw [he]
    _ = -(creation i * (gammaChiral * annihilation i)) := by noncomm_ring
    _ = -(creation i * (-(annihilation i * gammaChiral))) := by rw [hf]
    _ = (creation i * annihilation i) * gammaChiral := by noncomm_ring

/-- Positive-chirality occupation. -/
def chiralNumberPlus : FockOp :=
  PPlus * rawFockNumber * PPlus

/-- Negative-chirality occupation. -/
def chiralNumberMinus : FockOp :=
  PMinus * rawFockNumber * PMinus

/-- The raw occupation commutes with the positive chiral projector. -/
theorem rawFockNumber_PPlus_comm :
    rawFockNumber * PPlus = PPlus * rawFockNumber := by
  unfold PPlus
  noncomm_ring [gammaChiral_rawFockNumber_comm]

/-- The raw occupation commutes with the negative chiral projector. -/
theorem rawFockNumber_PMinus_comm :
    rawFockNumber * PMinus = PMinus * rawFockNumber := by
  unfold PMinus
  noncomm_ring [gammaChiral_rawFockNumber_comm]

/-- Sheet-sum occupation reconstructs the raw Fock number. -/
theorem chiralNumber_sum :
    chiralNumberPlus + chiralNumberMinus = rawFockNumber := by
  unfold chiralNumberPlus chiralNumberMinus PPlus PMinus
  noncomm_ring [gammaChiral_sq, gammaChiral_rawFockNumber_comm]

/-- Sheet-difference occupation is chirality times total occupation. -/
theorem chiralNumber_difference :
    chiralNumberPlus - chiralNumberMinus = gammaChiral * rawFockNumber := by
  unfold chiralNumberPlus chiralNumberMinus PPlus PMinus
  noncomm_ring [gammaChiral_sq, gammaChiral_rawFockNumber_comm]

/-- The two chiral occupations therefore give exact sum/difference coordinates
for total and signed occupation. -/
theorem chiralNumber_sum_difference_packet :
    chiralNumberPlus + chiralNumberMinus = rawFockNumber ∧
    chiralNumberPlus - chiralNumberMinus = gammaChiral * rawFockNumber :=
  ⟨chiralNumber_sum, chiralNumber_difference⟩

/-- Odd creation flips chirality from the positive to the negative sheet. -/
theorem creation_flips_plus_to_minus (i : Fin 5) :
    PMinus * creation i * PPlus = creation i * PPlus := by
  unfold PMinus PPlus
  have he := gammaChiral_e_anticomm i
  noncomm_ring [gammaChiral_sq, he]

/-- Odd creation flips chirality from the negative to the positive sheet. -/
theorem creation_flips_minus_to_plus (i : Fin 5) :
    PPlus * creation i * PMinus = creation i * PMinus := by
  unfold PMinus PPlus
  have he := gammaChiral_e_anticomm i
  noncomm_ring [gammaChiral_sq, he]

/-- Odd annihilation flips chirality from the positive to the negative sheet. -/
theorem annihilation_flips_plus_to_minus (i : Fin 5) :
    PMinus * annihilation i * PPlus = annihilation i * PPlus := by
  unfold PMinus PPlus
  have hf := gammaChiral_f_anticomm i
  noncomm_ring [gammaChiral_sq, hf]

/-- Odd annihilation flips chirality from the negative to the positive sheet. -/
theorem annihilation_flips_minus_to_plus (i : Fin 5) :
    PPlus * annihilation i * PMinus = annihilation i * PMinus := by
  unfold PMinus PPlus
  have hf := gammaChiral_f_anticomm i
  noncomm_ring [gammaChiral_sq, hf]

/-! ## Chiral occupation as a real four-component operator potential -/

/-- For one selected CAR mode, package total/signed chiral occupation and the
symmetric/antisymmetric CAR combinations into causal four coordinates. -/
def chiralOccupationFourPotential (i : Fin 5) : RealFockFourPotential :=
  ![(1 / 2 : ℝ) • (chiralNumberPlus + chiralNumberMinus),
    (1 / 2 : ℝ) • (annihilation i + creation i),
    (1 / 2 : ℝ) • (creation i - annihilation i),
    (1 / 2 : ℝ) • (chiralNumberPlus - chiralNumberMinus)]

@[simp] theorem chiralOccupationFourPotential_scalar (i : Fin 5) :
    chiralOccupationFourPotential i 0 = (1 / 2 : ℝ) • rawFockNumber := by
  simp [chiralOccupationFourPotential, chiralNumber_sum]

@[simp] theorem chiralOccupationFourPotential_chiral (i : Fin 5) :
    chiralOccupationFourPotential i 3 =
      (1 / 2 : ℝ) • (gammaChiral * rawFockNumber) := by
  simp [chiralOccupationFourPotential, chiralNumber_difference]

/-- Exact real causal/Nambu readout of the chiral occupation potential. -/
theorem chiralOccupationFourPotential_matrix (i : Fin 5) :
    !![chiralOccupationFourPotential i 0 + chiralOccupationFourPotential i 3,
       chiralOccupationFourPotential i 1 - chiralOccupationFourPotential i 2;
       chiralOccupationFourPotential i 1 + chiralOccupationFourPotential i 2,
       chiralOccupationFourPotential i 0 - chiralOccupationFourPotential i 3] =
      !![chiralNumberPlus, annihilation i;
         creation i, chiralNumberMinus] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [chiralOccupationFourPotential] <;>
    module

/-- Compact closure packet: raw occupation, centered five-grade generator,
chiral sum/difference coordinates, odd sheet-changing action, and the exact
four-component matrix readout. -/
theorem cl55_chiral_occupation_five_grade_packet (i : Fin 5) :
    rawFockNumber = numberOperator + (5 / 2 : ℝ) • (1 : FockOp) ∧
    bracket rawFockNumber (creation i) = creation i ∧
    bracket rawFockNumber (annihilation i) = -annihilation i ∧
    chiralNumberPlus + chiralNumberMinus = rawFockNumber ∧
    chiralNumberPlus - chiralNumberMinus = gammaChiral * rawFockNumber ∧
    PMinus * creation i * PPlus = creation i * PPlus ∧
    PMinus * annihilation i * PPlus = annihilation i * PPlus ∧
    (!![chiralOccupationFourPotential i 0 + chiralOccupationFourPotential i 3,
        chiralOccupationFourPotential i 1 - chiralOccupationFourPotential i 2;
        chiralOccupationFourPotential i 1 + chiralOccupationFourPotential i 2,
        chiralOccupationFourPotential i 0 - chiralOccupationFourPotential i 3] =
      !![chiralNumberPlus, annihilation i;
         creation i, chiralNumberMinus]) := by
  exact ⟨rawFockNumber_eq_numberOperator_add_five_halves,
    rawFockNumber_creation i,
    rawFockNumber_annihilation i,
    chiralNumber_sum,
    chiralNumber_difference,
    creation_flips_plus_to_minus i,
    annihilation_flips_plus_to_minus i,
    chiralOccupationFourPotential_matrix i⟩

end InfoGeometry.Canonical.Cl55ChiralOccupationFiveGradeBridge

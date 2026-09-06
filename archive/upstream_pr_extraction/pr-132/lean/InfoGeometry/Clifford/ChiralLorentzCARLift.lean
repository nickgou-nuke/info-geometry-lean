import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ChiralProjectorFromInvolution

/-!
# Chiral Lorentz operators and the CAR lift

This file supplies the algebraic action layer between the existing finite
`Cl(1,1)`/Jones packet and the existing CAR and `Cl(5,5)` owners.  It does
not introduce a quantum-group deformation: units act by the genuine inner
automorphism `x ↦ u x u⁻¹`.
-/

noncomputable section

namespace InfoGeometry.Clifford.ChiralLorentzCARLift

open InfoGeometry.OperatorAlgebra

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]

/-! ## Inner operator action -/

/-- Conjugation by a unit of an associative operator algebra. -/
def unitConjugation (u : Opˣ) (x : Op) : Op :=
  (u : Op) * x * (↑(u⁻¹) : Op)

omit [Algebra ℝ Op] in
@[simp] theorem unitConjugation_one (u : Opˣ) :
    unitConjugation u (1 : Op) = 1 := by
  simp [unitConjugation]

omit [Algebra ℝ Op] in
theorem unitConjugation_add (u : Opˣ) (x y : Op) :
    unitConjugation u (x + y) = unitConjugation u x + unitConjugation u y := by
  simp [unitConjugation, mul_add, add_mul]

omit [Algebra ℝ Op] in
theorem unitConjugation_mul (u : Opˣ) (x y : Op) :
    unitConjugation u (x * y) = unitConjugation u x * unitConjugation u y := by
  simp only [unitConjugation]
  calc
    (u : Op) * (x * y) * (↑(u⁻¹) : Op) =
        ((u : Op) * x * (↑(u⁻¹) : Op)) *
          ((u : Op) * y * (↑(u⁻¹) : Op)) := by
            simp [mul_assoc]
    _ = unitConjugation u x * unitConjugation u y := rfl

theorem unitConjugation_smul (u : Opˣ) (r : ℝ) (x : Op) :
    unitConjugation u (r • x) = r • unitConjugation u x := by
  simp [unitConjugation]

/-- Inner conjugation by a unit is a genuine ring equivalence of the operator
algebra. -/
def unitConjugationRingEquiv (u : Opˣ) : Op ≃+* Op where
  toFun := unitConjugation u
  invFun := unitConjugation u⁻¹
  left_inv := by
    intro x
    simp [unitConjugation, mul_assoc]
  right_inv := by
    intro x
    simp [unitConjugation, mul_assoc]
  map_add' := unitConjugation_add u
  map_mul' := unitConjugation_mul u

omit [Algebra ℝ Op] in
@[simp] theorem unitConjugationRingEquiv_apply (u : Opˣ) (x : Op) :
    unitConjugationRingEquiv u x = unitConjugation u x := rfl

omit [Algebra ℝ Op] in
theorem unitConjugation_comp (u v : Opˣ) (x : Op) :
    unitConjugation (u * v) x = unitConjugation u (unitConjugation v x) := by
  simp [unitConjugation, mul_assoc]

omit [Algebra ℝ Op] in
@[simp] theorem unitConjugationRingEquiv_one :
    unitConjugationRingEquiv (1 : Opˣ) = RingEquiv.refl Op := by
  ext x
  simp [unitConjugationRingEquiv, unitConjugation]

/-- Units act on the operator algebra by an honest algebra action. -/
def unitConjugationAction : ChiralInvolutionAction Opˣ Op where
  act := unitConjugation
  map_one := unitConjugation_one
  map_add := unitConjugation_add
  map_mul := unitConjugation_mul
  map_smul := unitConjugation_smul

omit [Algebra ℝ Op] in
theorem unitConjugation_fixed_of_commute (u : Opˣ) (chi : Op)
    (hcomm : (u : Op) * chi = chi * (u : Op)) :
    unitConjugation u chi = chi := by
  dsimp [unitConjugation]
  calc
    (u : Op) * chi * (↑(u⁻¹) : Op) =
        chi * (u : Op) * (↑(u⁻¹) : Op) := by rw [hcomm]
    _ = chi := by simp [mul_assoc]

theorem unitConjugation_fixed_Pleft
    (C : ChiralInvolution Op) (u : Opˣ)
    (hcomm : (u : Op) * C.chi = C.chi * (u : Op)) :
    unitConjugation u C.Pleft = C.Pleft := by
  apply (unitConjugationAction (Op := Op)).map_Pleft_of_chi_invariant C u
  exact unitConjugation_fixed_of_commute u C.chi hcomm

theorem unitConjugation_fixed_Pright
    (C : ChiralInvolution Op) (u : Opˣ)
    (hcomm : (u : Op) * C.chi = C.chi * (u : Op)) :
    unitConjugation u C.Pright = C.Pright := by
  apply (unitConjugationAction (Op := Op)).map_Pright_of_chi_invariant C u
  exact unitConjugation_fixed_of_commute u C.chi hcomm

/-! ## Even/odd operator coordinates for a chiral involution -/

/-- The even component of an operator relative to `chi`. -/
def evenPart (chi A : Op) : Op :=
  (1 / 2 : ℝ) • (A + chi * A * chi)

/-- The odd component of an operator relative to `chi`. -/
def oddPart (chi A : Op) : Op :=
  (1 / 2 : ℝ) • (A - chi * A * chi)

theorem evenPart_add_oddPart (chi A : Op) :
    evenPart chi A + oddPart chi A = A := by
  dsimp [evenPart, oddPart]
  rw [← smul_add]
  calc
    (1 / 2 : ℝ) • (A + chi * A * chi + (A - chi * A * chi)) =
        (1 / 2 : ℝ) • ((2 : ℝ) • A) := by
          congr 1
          calc
            (A + chi * A * chi) + (A - chi * A * chi) = A + A := by abel
            _ = (2 : ℝ) • A := by rw [two_smul]
    _ = A := by rw [smul_smul]; norm_num

theorem chi_mul_evenPart_eq_evenPart_mul_chi (chi A : Op)
    (hchi : chi * chi = 1) :
    chi * evenPart chi A = evenPart chi A * chi := by
  dsimp [evenPart]
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  calc
    chi * (A + chi * A * chi) = chi * A + (chi * chi) * A * chi := by
      noncomm_ring
    _ = chi * A + A * chi := by rw [hchi]; simp
    _ = A * chi + chi * A := by rw [add_comm]
    _ = (A + chi * A * chi) * chi := by
      rw [add_mul]
      rw [mul_assoc, hchi, mul_one]

theorem chi_mul_oddPart_eq_neg_oddPart_mul_chi (chi A : Op)
    (hchi : chi * chi = 1) :
    chi * oddPart chi A = -(oddPart chi A * chi) := by
  dsimp [oddPart]
  have hinner : chi * (A - chi * A * chi) =
      -((A - chi * A * chi) * chi) := by
    calc
    chi * (A - chi * A * chi) = chi * A - (chi * chi) * A * chi := by
      noncomm_ring
    _ = chi * A - A * chi := by rw [hchi]; simp
    _ = -(A * chi - chi * A) := by abel
    _ = -((A - chi * A * chi) * chi) := by
      rw [sub_mul, mul_assoc, hchi, mul_one]
  simpa only [smul_mul_assoc, mul_smul_comm, neg_smul, smul_neg] using
    congrArg (fun z : Op => (1 / 2 : ℝ) • z) hinner

theorem evenPart_eq_of_commute (chi A : Op) (hchi : chi * chi = 1)
    (hcomm : chi * A = A * chi) :
    evenPart chi A = A := by
  dsimp [evenPart]
  have hinner : chi * A * chi = A := by
    rw [hcomm, mul_assoc, hchi, mul_one]
  rw [hinner]
  rw [show A + A = (2 : ℝ) • A by rw [two_smul]]
  rw [smul_smul]
  norm_num

theorem oddPart_eq_zero_of_commute (chi A : Op) (hchi : chi * chi = 1)
    (hcomm : chi * A = A * chi) :
    oddPart chi A = 0 := by
  dsimp [oddPart]
  have hinner : chi * A * chi = A := by
    rw [hcomm, mul_assoc, hchi, mul_one]
  rw [hinner, sub_self, smul_zero]

/-! ## Quadratic CAR generators -/

/-- The quadratic number operator associated with a CAR pair. -/
def numberOperator (creation annihilation : Op) : Op := creation * annihilation

/-- The algebra commutator. -/
def algebraCommutator (x y : Op) : Op := x * y - y * x

omit [Algebra ℝ Op] in
theorem numberOperator_commutator_annihilation
    (creation annihilation : Op)
    (hannihilation : annihilation * annihilation = 0)
    (hcar : creation * annihilation + annihilation * creation = 1) :
    algebraCommutator (numberOperator creation annihilation) annihilation =
      -annihilation := by
  dsimp [algebraCommutator, numberOperator]
  calc
    creation * annihilation * annihilation - annihilation * (creation * annihilation) =
        creation * (annihilation * annihilation) -
          annihilation * (creation * annihilation) := by
            rw [mul_assoc]
    _ = 0 - annihilation * (creation * annihilation) := by
      rw [hannihilation, mul_zero]
    _ = -annihilation := by
      have h := congrArg (fun z : Op => z * annihilation) hcar
      dsimp at h
      rw [add_mul, mul_assoc, hannihilation, mul_zero, zero_add, one_mul] at h
      have hneg := congrArg (fun z : Op => -z) h
      calc
        0 - annihilation * (creation * annihilation) =
            -(annihilation * (creation * annihilation)) := by simp
        _ = -(annihilation * creation * annihilation) := by rw [mul_assoc]
        _ = -annihilation := hneg

omit [Algebra ℝ Op] in
theorem numberOperator_commutator_creation
    (creation annihilation : Op)
    (hcreation : creation * creation = 0)
    (hcar : creation * annihilation + annihilation * creation = 1) :
    algebraCommutator (numberOperator creation annihilation) creation =
      creation := by
  dsimp [algebraCommutator, numberOperator]
  calc
    creation * annihilation * creation - creation * (creation * annihilation) =
        creation * annihilation * creation - 0 := by
          rw [← mul_assoc, hcreation]
          simp
    _ = creation := by
      have h := congrArg (fun z : Op => creation * z) hcar
      dsimp at h
      rw [mul_add] at h
      rw [← mul_assoc, hcreation, zero_mul, zero_add, mul_one] at h
      calc
        creation * annihilation * creation - 0 =
            creation * (annihilation * creation) := by simp [mul_assoc]
        _ = creation := h

end InfoGeometry.Clifford.ChiralLorentzCARLift

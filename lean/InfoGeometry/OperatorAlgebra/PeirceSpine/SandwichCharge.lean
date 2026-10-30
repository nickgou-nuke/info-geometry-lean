import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# Charges of corner sandwiches

Dependency order: Peirce corner relations → five charge identities → finite
iteration polynomial. These are identities in an arbitrary associative ring.
They do not assert a direct-sum decomposition of eigenspaces, or identify a
Kantor Lie algebra. In small characteristic the integer charges can coincide.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine
variable {B : Type*} [Ring B]

def sandwich (U W X : B) : B := U * X * W

def charge (P : B) (K : B → B) (X : B) : B :=
  comm P (K X) - K (comm P X)

def chargeIter (P : B) (K : B → B) : ℕ → B → B
  | 0 => K
  | n + 1 => charge P (chargeIter P K n)

def cornerOperatorSum (P A C X : B) : B :=
  sandwich (coneMinus P C) (coneMinus P C) X + comm (coneMinus P C) X +
  sandwichCross P A C X + comm (conePlus P A) X +
  sandwich (conePlus P A) (conePlus P A) X

/-- The charge of a two-sided multiplication is the sum of its two charges. -/
theorem charge_sandwich (P U W X : B) :
    charge P (sandwich U W) X =
      comm P U * X * W + U * X * comm P W := by
  simp only [charge, sandwich, comm, mul_sub, sub_mul, mul_assoc]
  abel

variable {P : B} (hP : P * P = P) (A C X : B)
include hP

theorem charge_plus_sandwich :
    charge P (sandwich (conePlus P A) (conePlus P A)) X =
      (2 : ℤ) • sandwich (conePlus P A) (conePlus P A) X := by
  unfold charge sandwich
  peirce_nf hP

theorem charge_minus_sandwich :
    charge P (sandwich (coneMinus P C) (coneMinus P C)) X =
      -((2 : ℤ) • sandwich (coneMinus P C) (coneMinus P C) X) := by
  unfold charge sandwich
  peirce_nf hP

theorem charge_plus_comm :
    charge P (comm (conePlus P A)) X = comm (conePlus P A) X := by
  unfold charge
  peirce_nf hP

theorem charge_minus_comm :
    charge P (comm (coneMinus P C)) X = -comm (coneMinus P C) X := by
  unfold charge
  peirce_nf hP

theorem charge_cross_sandwich :
    charge P (sandwichCross P A C) X = 0 := by
  unfold charge sandwichCross
  peirce_nf hP

theorem plus_comm_square :
    comm (conePlus P A) (comm (conePlus P A) X) =
      -((2 : ℤ) • sandwich (conePlus P A) (conePlus P A) X) := by
  unfold sandwich
  peirce_nf hP

theorem minus_comm_square :
    comm (coneMinus P C) (comm (coneMinus P C) X) =
      -((2 : ℤ) • sandwich (coneMinus P C) (coneMinus P C) X) := by
  unfold sandwich
  peirce_nf hP

theorem plus_sandwich_square :
    sandwich (conePlus P A) (conePlus P A)
      (sandwich (conePlus P A) (conePlus P A) X) = 0 := by
  unfold sandwich
  peirce_nf hP

theorem minus_sandwich_square :
    sandwich (coneMinus P C) (coneMinus P C)
      (sandwich (coneMinus P C) (coneMinus P C) X) = 0 := by
  unfold sandwich
  peirce_nf hP

theorem charge_total_first :
    charge P (cornerOperatorSum P A C) X =
      -((2 : ℤ) • sandwich (coneMinus P C) (coneMinus P C) X) -
      comm (coneMinus P C) X + comm (conePlus P A) X +
      (2 : ℤ) • sandwich (conePlus P A) (conePlus P A) X := by
  unfold charge cornerOperatorSum sandwichCross sandwich
  peirce_nf hP

theorem charge_total_second :
    chargeIter P (cornerOperatorSum P A C) 2 X =
      (4 : ℤ) • sandwich (coneMinus P C) (coneMinus P C) X +
      comm (coneMinus P C) X + comm (conePlus P A) X +
      (4 : ℤ) • sandwich (conePlus P A) (conePlus P A) X := by
  simp only [chargeIter, charge, cornerOperatorSum, sandwichCross, sandwich]
  peirce_nf hP

theorem charge_iter_cubic_difference :
    chargeIter P (cornerOperatorSum P A C) 3 X -
      chargeIter P (cornerOperatorSum P A C) 1 X =
      (6 : ℤ) • (sandwich (conePlus P A) (conePlus P A) X -
        sandwich (coneMinus P C) (coneMinus P C) X) := by
  simp only [chargeIter, charge, cornerOperatorSum, sandwichCross, sandwich]
  peirce_nf hP

theorem plus_comm_sandwich_zero :
    comm (conePlus P A) (sandwich (conePlus P A) (conePlus P A) X) = 0 := by
  unfold sandwich
  peirce_nf hP

theorem plus_sandwich_comm_zero :
    sandwich (conePlus P A) (conePlus P A) (comm (conePlus P A) X) = 0 := by
  unfold sandwich
  peirce_nf hP

theorem plus_sandwich_opposite :
    sandwich (conePlus P A) (conePlus P A) (coneMinus P C) = genV P A C * (conePlus P A) := by
  unfold sandwich
  peirce_nf hP

theorem plus_sandwich_alternating :
    sandwich (conePlus P A) (conePlus P A) (sandwich (coneMinus P C) (coneMinus P C) (conePlus P A)) =
      (genV P A C * genV P A C) * (conePlus P A) := by
  unfold sandwich
  peirce_nf hP

theorem minus_comm_sandwich_zero :
    comm (coneMinus P C) (sandwich (coneMinus P C) (coneMinus P C) X) = 0 := by
  unfold sandwich
  peirce_nf hP

theorem minus_sandwich_comm_zero :
    sandwich (coneMinus P C) (coneMinus P C) (comm (coneMinus P C) X) = 0 := by
  unfold sandwich
  peirce_nf hP

theorem minus_sandwich_opposite :
    sandwich (coneMinus P C) (coneMinus P C) (conePlus P A) = genV P A C * (coneMinus P C) := by
  unfold sandwich
  peirce_nf hP

theorem minus_sandwich_alternating :
    sandwich (coneMinus P C) (coneMinus P C) (sandwich (conePlus P A) (conePlus P A) (coneMinus P C)) =
      (genV P A C * genV P A C) * (coneMinus P C) := by
  unfold sandwich
  peirce_nf hP

/-- The actual fifth-degree annihilator, with no division by charge differences. -/
theorem charge_iter_fifth_annihilator :
    chargeIter P (cornerOperatorSum P A C) 5 X -
      (5 : ℤ) • chargeIter P (cornerOperatorSum P A C) 3 X +
      (4 : ℤ) • chargeIter P (cornerOperatorSum P A C) 1 X = 0 := by
  simp only [chargeIter, charge, cornerOperatorSum, sandwichCross, sandwich]
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine

import InfoGeometry.OperatorAlgebra.PeirceSpine.SandwichCharge

/-!
# Commutators of corner multiplication operators

Contract: identities of endomorphisms evaluated at arbitrary X in a ring.
In composing sandwiches, the right factors occur in reverse order. In
particular the extremal bracket has cross corners, not diagonal corners.
The charge equations below do not assert a KKT identification or closure of
the span of only five chosen operators.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine
variable {B : Type*} [Ring B]

theorem sandwich_composition (U W V Z X : B) :
    sandwich U W (sandwich V Z X) = sandwich (U * V) (Z * W) X := by
  simp only [sandwich, mul_assoc]

theorem comm_sandwich_commutator (U V W X : B) :
    comm U (sandwich V W X) - sandwich V W (comm U X) =
      sandwich (comm U V) W X + sandwich V (comm U W) X := by
  simp only [comm, sandwich, sub_mul, mul_sub, mul_add, add_mul, mul_assoc]
  abel

theorem extremal_sandwich_commutator (U W X : B) :
    sandwich U U (sandwich W W X) - sandwich W W (sandwich U U X) =
      sandwich (U * W) (W * U) X - sandwich (W * U) (U * W) X := by
  rw [sandwich_composition, sandwich_composition]

variable {P : B} (hP : P * P = P) (A C X : B)
include hP

theorem corner_commutator_pair :
    comm (conePlus P A) (comm (coneMinus P C) X) -
      comm (coneMinus P C) (comm (conePlus P A) X) = comm (genSig P A C) X := by
  peirce_nf hP

theorem raising_lowering_sandwich_bracket :
    comm (conePlus P A) (sandwich (coneMinus P C) (coneMinus P C) X) -
      sandwich (coneMinus P C) (coneMinus P C) (comm (conePlus P A) X) =
      sandwich (genSig P A C) (coneMinus P C) X +
      sandwich (coneMinus P C) (genSig P A C) X := by
  unfold sandwich
  peirce_nf hP

theorem lowering_raising_sandwich_bracket :
    comm (coneMinus P C) (sandwich (conePlus P A) (conePlus P A) X) -
      sandwich (conePlus P A) (conePlus P A) (comm (coneMinus P C) X) =
      -(sandwich (genSig P A C) (conePlus P A) X +
      sandwich (conePlus P A) (genSig P A C) X) := by
  unfold sandwich
  peirce_nf hP

theorem charge_spin_comm :
    charge P (comm (genSig P A C)) X = 0 := by
  unfold charge
  peirce_nf hP

theorem charge_spin_lower_sandwich :
    charge P (fun Y => sandwich (genSig P A C) (coneMinus P C) Y +
      sandwich (coneMinus P C) (genSig P A C) Y) X =
      -(sandwich (genSig P A C) (coneMinus P C) X +
      sandwich (coneMinus P C) (genSig P A C) X) := by
  unfold charge sandwich
  peirce_nf hP

theorem charge_spin_upper_sandwich :
    charge P (fun Y => sandwich (genSig P A C) (conePlus P A) Y +
      sandwich (conePlus P A) (genSig P A C) Y) X =
      sandwich (genSig P A C) (conePlus P A) X +
      sandwich (conePlus P A) (genSig P A C) X := by
  unfold charge sandwich
  peirce_nf hP

theorem charge_extremal_bracket :
    charge P (fun Y =>
      sandwich (conePlus P A) (conePlus P A)
        (sandwich (coneMinus P C) (coneMinus P C) Y) -
      sandwich (coneMinus P C) (coneMinus P C)
        (sandwich (conePlus P A) (conePlus P A) Y)) X = 0 := by
  unfold charge sandwich
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine

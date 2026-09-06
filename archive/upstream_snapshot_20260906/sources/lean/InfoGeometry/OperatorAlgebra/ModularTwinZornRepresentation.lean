import InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce
import InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge

/-!
# Modular algebra--commutant twin in an operator-Zorn block

This file formalizes the exact algebraic content of the proposed "twin wave"
interpretation.  Two commuting representations of a star ring `A` act in an
ambient noncommutative operator ring `B`.  A plain ring involution `J` exchanges
the represented algebra and commutant after applying `star` to the source.

The resulting diagonal entries are the two boundary/operator waves.  The
off-diagonal entries remain independent inter-sheet operators.  The modular
involution has square `+1`; it is not identified with the Kramers antiunitary
whose square is `-1`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ModularTwinZornRepresentation

open InfoGeometry.Physics
open InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce

variable {A B : Type*}
variable [Ring A] [StarRing A]
variable [Ring B] [StarRing B]

/-- Algebraic representation of an algebra and its commuting twin, together
with a Tomita-style involution exchanging them. -/
structure ModularTwinRepresentation (A B : Type*)
    [Ring A] [StarRing A] [Ring B] [StarRing B] where
  leftRep : A ->+* B
  rightRep : A ->+* B
  left_right_commute : forall a b,
    leftRep a * rightRep b = rightRep b * leftRep a
  modularConjugation : B ≃+* B
  modularConjugation_involutive :
    Function.Involutive modularConjugation
  modular_left_to_right : forall a,
    modularConjugation (leftRep a) = rightRep (star a)
  modular_right_to_left : forall a,
    modularConjugation (rightRep a) = leftRep (star a)

namespace ModularTwinRepresentation

variable (P : ModularTwinRepresentation A B)

/-- The represented algebra and commutant have zero ordinary commutator. -/
theorem left_right_commutator_zero (a b : A) :
    P.leftRep a * P.rightRep b - P.rightRep b * P.leftRep a = 0 := by
  rw [P.left_right_commute]
  exact sub_self _

/-- Diagonal two-boundary operator block. -/
def boundaryBlock (a b : A) : ZornBlock B :=
  ⟨P.leftRep a, P.rightRep b, 0, 0⟩

/-- General modular twin block with arbitrary inter-sheet channels. -/
def twinBlock (a b : A) (qPlus qMinus : B) : ZornBlock B :=
  ⟨P.leftRep a, P.rightRep b, qPlus, qMinus⟩

/-- Entrywise modular conjugation followed by sheet exchange. -/
def modularExchange (Z : ZornBlock B) : ZornBlock B :=
  ⟨P.modularConjugation Z.n_minus_op,
    P.modularConjugation Z.n_plus_op,
    P.modularConjugation Z.sigma_minus_op,
    P.modularConjugation Z.sigma_plus_op⟩

@[simp] theorem modularExchange_n_plus (Z : ZornBlock B) :
    (P.modularExchange Z).n_plus_op =
      P.modularConjugation Z.n_minus_op := rfl

@[simp] theorem modularExchange_n_minus (Z : ZornBlock B) :
    (P.modularExchange Z).n_minus_op =
      P.modularConjugation Z.n_plus_op := rfl

@[simp] theorem modularExchange_sigma_plus (Z : ZornBlock B) :
    (P.modularExchange Z).sigma_plus_op =
      P.modularConjugation Z.sigma_minus_op := rfl

@[simp] theorem modularExchange_sigma_minus (Z : ZornBlock B) :
    (P.modularExchange Z).sigma_minus_op =
      P.modularConjugation Z.sigma_plus_op := rfl

/-- The modular sheet exchange is involutive. -/
@[simp] theorem modularExchange_involutive (Z : ZornBlock B) :
    P.modularExchange (P.modularExchange Z) = Z := by
  apply zornBlock_ext <;>
    simp [modularExchange, P.modularConjugation_involutive]

/-- The modular sheet exchange is an automorphism of the associative block
product. -/
theorem modularExchange_mul (X Y : ZornBlock B) :
    P.modularExchange (X * Y) =
      P.modularExchange X * P.modularExchange Y := by
  apply zornBlock_ext <;>
    simp [modularExchange, add_comm]

/-- The two diagonal boundary operators are exchanged and starred. -/
theorem modularExchange_boundaryBlock (a b : A) :
    P.modularExchange (P.boundaryBlock a b) =
      P.boundaryBlock (star b) (star a) := by
  apply zornBlock_ext <;>
    simp [modularExchange, boundaryBlock,
      P.modular_left_to_right, P.modular_right_to_left]

/-- On a self-adjoint pair, modular exchange simply swaps the two boundary
operators. -/
theorem modularExchange_boundaryBlock_of_selfAdjoint
    {a b : A} (ha : star a = a) (hb : star b = b) :
    P.modularExchange (P.boundaryBlock a b) =
      P.boundaryBlock b a := by
  rw [P.modularExchange_boundaryBlock, ha, hb]

/-- Algebraic left-to-right twisted intertwiner condition. -/
def IsLeftToRightChannel (q : B) : Prop :=
  forall a : A,
    q * P.leftRep a = P.rightRep (star a) * q

/-- Algebraic right-to-left twisted intertwiner condition. -/
def IsRightToLeftChannel (q : B) : Prop :=
  forall a : A,
    q * P.rightRep a = P.leftRep (star a) * q

/-- The closed two-step channel `qMinus*qPlus` commutes with the represented
left algebra.  Both opposite intertwining laws are essential. -/
theorem paired_channels_product_commutes_left
    {qPlus qMinus : B}
    (hPlus : P.IsLeftToRightChannel qPlus)
    (hMinus : P.IsRightToLeftChannel qMinus)
    (a : A) :
    (qMinus * qPlus) * P.leftRep a =
      P.leftRep a * (qMinus * qPlus) := by
  calc
    (qMinus * qPlus) * P.leftRep a =
        qMinus * (qPlus * P.leftRep a) := by rw [mul_assoc]
    _ = qMinus * (P.rightRep (star a) * qPlus) := by
      rw [hPlus a]
    _ = (qMinus * P.rightRep (star a)) * qPlus := by
      rw [← mul_assoc]
    _ = (P.leftRep (star (star a)) * qMinus) * qPlus := by
      rw [hMinus (star a)]
    _ = P.leftRep a * (qMinus * qPlus) := by
      simp [mul_assoc]

/-- Dually, `qPlus*qMinus` commutes with the represented right algebra. -/
theorem paired_channels_product_commutes_right
    {qPlus qMinus : B}
    (hPlus : P.IsLeftToRightChannel qPlus)
    (hMinus : P.IsRightToLeftChannel qMinus)
    (a : A) :
    (qPlus * qMinus) * P.rightRep a =
      P.rightRep a * (qPlus * qMinus) := by
  calc
    (qPlus * qMinus) * P.rightRep a =
        qPlus * (qMinus * P.rightRep a) := by rw [mul_assoc]
    _ = qPlus * (P.leftRep (star a) * qMinus) := by
      rw [hMinus a]
    _ = (qPlus * P.leftRep (star a)) * qMinus := by
      rw [← mul_assoc]
    _ = (P.rightRep (star (star a)) * qPlus) * qMinus := by
      rw [hPlus (star a)]
    _ = P.rightRep a * (qPlus * qMinus) := by
      simp [mul_assoc]

/-- A modularly paired pair of channels is exchanged by `J`. -/
def ChannelsAreModularPartners (qPlus qMinus : B) : Prop :=
  P.modularConjugation qPlus = qMinus ∧
    P.modularConjugation qMinus = qPlus

/-- A star-conjugate diagonal pair with modularly paired off-diagonal channels
is fixed by the full modular sheet exchange. -/
theorem modularExchange_twinBlock_fixed
    {a b : A} {qPlus qMinus : B}
    (ha : star a = b) (hb : star b = a)
    (hq : P.ChannelsAreModularPartners qPlus qMinus) :
    P.modularExchange (P.twinBlock a b qPlus qMinus) =
      P.twinBlock a b qPlus qMinus := by
  apply zornBlock_ext
  · simpa [twinBlock, P.modular_right_to_left, hb]
  · simpa [twinBlock, P.modular_left_to_right, ha]
  · simpa [twinBlock] using hq.2
  · simpa [twinBlock] using hq.1

end ModularTwinRepresentation

end InfoGeometry.OperatorAlgebra.ModularTwinZornRepresentation

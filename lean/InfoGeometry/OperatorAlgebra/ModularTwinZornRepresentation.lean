import InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce

/-! An algebraic carrier for two commuting representations and an involutive
exchange.  This is only a ring-theoretic twin representation; it is not a
Tomita conjugation or an anti-linear time-reversal operator. -/

namespace InfoGeometry.OperatorAlgebra.ModularTwinZornRepresentation

variable {A B : Type*} [Ring A] [StarRing A] [Ring B] [StarRing B]

structure ModularTwinRepresentation (A B : Type*)
    [Ring A] [StarRing A] [Ring B] [StarRing B] where
  leftRep : A →+* B
  rightRep : A →+* B
  left_right_commute : ∀ a b, leftRep a * rightRep b = rightRep b * leftRep a
  modularConjugation : B ≃+* B
  modularConjugation_involutive : Function.Involutive modularConjugation
  modular_left_to_right : ∀ a,
    modularConjugation (leftRep a) = rightRep (star a)
  modular_right_to_left : ∀ a,
    modularConjugation (rightRep a) = leftRep (star a)

namespace ModularTwinRepresentation

variable (T : ModularTwinRepresentation A B)

theorem exchange_left (a : A) :
    T.modularConjugation (T.leftRep a) = T.rightRep (star a) :=
  T.modular_left_to_right a

theorem exchange_right (a : A) :
    T.modularConjugation (T.rightRep a) = T.leftRep (star a) :=
  T.modular_right_to_left a

theorem exchange_involutive (x : B) :
    T.modularConjugation (T.modularConjugation x) = x :=
  T.modularConjugation_involutive x

theorem paired_product_commutes (a b : A) :
    T.leftRep a * T.rightRep b = T.rightRep b * T.leftRep a :=
  T.left_right_commute a b

end ModularTwinRepresentation

end InfoGeometry.OperatorAlgebra.ModularTwinZornRepresentation

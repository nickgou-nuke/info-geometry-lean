import Mathlib

/-!
# Finite Kantor-pair contract

This is the algebraic interface used by the standard five-graded Lie
envelope.  It records the two Kantor identities, but deliberately does not
claim that a particular nonassociative carrier (such as split octonions)
already supplies this structure.
-/

namespace InfoGeometry.Lie

structure KantorPairSkeleton (Kplus Kminus : Type*)
    [AddGroup Kplus] [AddGroup Kminus] where
  triplePlus : Kplus → Kminus → Kplus → Kplus
  tripleMinus : Kminus → Kplus → Kminus → Kminus
  /-- The `K`-operator on the plus component, written
  `K a b z = {a,z,b} - {b,z,a}`. -/
  kPlus : Kplus → Kplus → Kminus → Kplus
  /-- The `K`-operator on the minus component. -/
  kMinus : Kminus → Kminus → Kplus → Kminus
  kPlus_def : ∀ a b z,
    kPlus a b z = triplePlus a z b - triplePlus b z a
  kMinus_def : ∀ a b z,
    kMinus a b z = tripleMinus a z b - tripleMinus b z a
  kp1Plus : ∀ x y z w t,
    triplePlus x y (triplePlus z w t) -
        triplePlus z w (triplePlus x y t) =
      triplePlus (triplePlus x y z) w t -
        triplePlus z (tripleMinus y x w) t
  kp1Minus : ∀ x y z w t,
    tripleMinus x y (tripleMinus z w t) -
        tripleMinus z w (tripleMinus x y t) =
      tripleMinus (tripleMinus x y z) w t -
        tripleMinus z (triplePlus y x w) t
  /-- (KP2) for the plus polarity, with all compositions typed explicitly. -/
  kp2Plus : ∀ a b y x z,
    kPlus a b (tripleMinus x y z) +
        triplePlus y x (kPlus a b z) =
      kPlus (kPlus a b x) y z
  /-- (KP2) for the minus polarity. -/
  kp2Minus : ∀ a b y x z,
    kMinus a b (triplePlus x y z) +
        tripleMinus y x (kMinus a b z) =
      kMinus (kMinus a b x) y z

namespace KantorPair

variable {Kplus Kminus : Type*}
variable [AddGroup Kplus] [AddGroup Kminus]
variable (K : KantorPairSkeleton Kplus Kminus)

theorem k_plus_def (a b : Kplus) (z : Kminus) :
    K.kPlus a b z = K.triplePlus a z b - K.triplePlus b z a :=
  K.kPlus_def a b z

theorem k_minus_def (a b : Kminus) (z : Kplus) :
    K.kMinus a b z = K.tripleMinus a z b - K.tripleMinus b z a :=
  K.kMinus_def a b z

theorem kp1_plus (x : Kplus) (y : Kminus) (z : Kplus)
    (w : Kminus) (t : Kplus) :
    K.triplePlus x y (K.triplePlus z w t) -
        K.triplePlus z w (K.triplePlus x y t) =
      K.triplePlus (K.triplePlus x y z) w t -
        K.triplePlus z (K.tripleMinus y x w) t :=
  K.kp1Plus x y z w t

theorem kp1_minus (x : Kminus) (y : Kplus) (z : Kminus)
    (w : Kplus) (t : Kminus) :
    K.tripleMinus x y (K.tripleMinus z w t) -
        K.tripleMinus z w (K.tripleMinus x y t) =
      K.tripleMinus (K.tripleMinus x y z) w t -
        K.tripleMinus z (K.triplePlus y x w) t :=
  K.kp1Minus x y z w t

theorem kp2_plus (a b y : Kplus) (x z : Kminus) :
    K.kPlus a b (K.tripleMinus x y z) +
        K.triplePlus y x (K.kPlus a b z) =
      K.kPlus (K.kPlus a b x) y z :=
  K.kp2Plus a b y x z

theorem kp2_minus (a b y : Kminus) (x z : Kplus) :
    K.kMinus a b (K.triplePlus x y z) +
        K.tripleMinus y x (K.kMinus a b z) =
      K.kMinus (K.kMinus a b x) y z :=
  K.kp2Minus a b y x z

end KantorPair

end InfoGeometry.Lie

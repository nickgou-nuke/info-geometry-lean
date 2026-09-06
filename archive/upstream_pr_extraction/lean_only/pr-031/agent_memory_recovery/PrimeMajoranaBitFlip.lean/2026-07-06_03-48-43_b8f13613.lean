structure PrimeMajoranaCARGate
  (PrimeLabel Operator : Type*) where
  majorana : PrimeLabel → Operator
  IsSelfAdjoint : Operator → Prop
  CliffordPair : Operator → Operator → Prop
  ImplementsBitFlip : PrimeLabel → Operator → Prop
  is_self_adjoint_law : ∀ p, IsSelfAdjoint (majorana p)
  clifford_pair_law : ∀ p q, CliffordPair (majorana p) (majorana q)
  implements_bit_flip_law : ∀ p, ImplementsBitFlip p (majorana p)

namespace PrimeMajoranaCARGate

/-- Explicit debt: the generic operator carrier has no owner CAR proof here. -/
theorem clifford_holds
    {PrimeLabel Operator : Type*}
    (G : PrimeMajoranaCARGate PrimeLabel Operator)
    (p q : PrimeLabel) :
    G.CliffordPair (G.majorana p) (G.majorana q) :=
    G.clifford_pair_law p q

/-- Explicit debt: matching an abstract operator to the finite flip needs an owner model. -/
theorem bit_flip_model
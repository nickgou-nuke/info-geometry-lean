import InfoGeometry.Algebra.Zorn.G2FixedPrefixResidualConstraints

namespace InfoGeometry.Algebra.Zorn.G2ResidualUpperPairClassification

open _root_.InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2PeirceFibration
open InfoGeometry.Algebra.Zorn.G2FixedPrefixResidualConstraints

def upperVector (x0 x1 x2 : Bool) : SplitOctF2 :=
  ⟨false, false, x0, x1, x2, false, false, false⟩

theorem canonical_peirce_upper_support
    (a : SplitOctF2)
    (hL : mul ePlus a = a)
    (hR : mul a ePlus = zero) :
    a = upperVector a.x0 a.x1 a.x2 := by
  native_decide +revert

theorem upperVector_injective :
    Function.Injective (fun q : Bool × Bool × Bool => upperVector q.1 q.2.1 q.2.2) := by
  intro q r h
  cases q with
  | mk q0 q12 =>
    cases q12 with
    | mk q1 q2 =>
      cases r with
      | mk r0 r12 =>
        cases r12 with
        | mk r1 r2 =>
          simp only [upperVector] at h
          cases h
          rfl

def upperBits (a : SplitOctF2) : Bool × Bool × Bool :=
  (a.x0, a.x1, a.x2)

theorem upperVector_eq_of_bits_eq
    {a b : SplitOctF2}
    (ha : a = upperVector a.x0 a.x1 a.x2)
    (hb : b = upperVector b.x0 b.x1 b.x2)
    (hbits : upperBits a = upperBits b) :
    a = b := by
  rw [ha, hb]
  exact congrArg (fun q : Bool × Bool × Bool => upperVector q.1 q.2.1 q.2.2) hbits

theorem residualUpperPair_card_le_64_of_ePlus
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (hp : p.1 = ePlus) :
    Fintype.card (ResidualUpperPair p x) ≤ 64 := by
  have hinj : Function.Injective
      (@InfoGeometry.Algebra.Zorn.G2FixedPrefixResidualConstraints.residualUpperPairBits p x) :=
    InfoGeometry.Algebra.Zorn.G2FixedPrefixResidualConstraints.residualUpperPairBits_injective_of_ePlus hp
  have hcard : Fintype.card (Fin 6 → Bool) = 64 := by
    native_decide
  rw [← hcard]
  exact Fintype.card_le_of_injective
    InfoGeometry.Algebra.Zorn.G2FixedPrefixResidualConstraints.residualUpperPairBits hinj

theorem residualFiber_card_le_64_of_ePlus
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (hp : p.1 = ePlus) :
    Fintype.card (ResidualFiber p x) ≤ 64 := by
  rw [Fintype.card_congr (residualFiberEquivResidualUpperPair p x)]
  exact residualUpperPair_card_le_64_of_ePlus hp

end InfoGeometry.Algebra.Zorn.G2ResidualUpperPairClassification

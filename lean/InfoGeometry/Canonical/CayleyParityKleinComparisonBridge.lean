import InfoGeometry.Canonical.CayleyParityUnitsBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CayleyDualityUnitsBridge

/-!
# Abstract comparison of the two native Klein packets

The parity and Cayley/Hodge packets are distinct subsets of the same
endomorphism-unit group.  This owner records only their abstract group
isomorphism, transported through the common Klein model
`Multiplicative (ZMod 2 × ZMod 2)`.  It deliberately does not identify their
operators, actions, or geometric meanings.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyParityKleinComparisonBridge

open InfoGeometry.Canonical.CayleyParityUnitsBridge
open InfoGeometry.Canonical.CayleyDualityUnitsBridge

noncomputable def parity_to_cayley_mulEquiv :
    parityKleinSubgroup ≃* cayleyDualityKleinSubgroup :=
  parityKleinSubgroup_mulEquiv.symm.trans cayleyDualityKleinSubgroup_mulEquiv

theorem parity_to_cayley_mulEquiv_symm :
    parity_to_cayley_mulEquiv.symm =
      cayleyDualityKleinSubgroup_mulEquiv.symm.trans
        parityKleinSubgroup_mulEquiv := by
  rfl

theorem parity_cayley_klein_packets_isomorphic :
    Nonempty (parityKleinSubgroup ≃* cayleyDualityKleinSubgroup) :=
  ⟨parity_to_cayley_mulEquiv⟩

end InfoGeometry.Canonical.CayleyParityKleinComparisonBridge

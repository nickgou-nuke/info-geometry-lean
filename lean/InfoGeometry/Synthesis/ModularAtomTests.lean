import InfoGeometry.Synthesis.ModularAtom

namespace InfoGeometry.Synthesis.ModularAtomTests

open InfoGeometry.Canonical.PrimeCl11ModularAtomCore
open InfoGeometry.Physics
open InfoGeometry.Synthesis.ModularAtom

variable {Carrier : Type*} [Ring Carrier] [StarRing Carrier]

example (atom : Cl11Atom Carrier) : atom.mobiusParity * atom.mobiusParity = 1 :=
  atom.mobiusParity_sq_eq_one

example (atom : Cl11Atom Carrier) (krein : KasparovKreinData Carrier)
    (metric_eq : krein.eta = atom.c) (spacelike_skewadjoint : star atom.d = -atom.d) :
    krein.diracAdjoint atom.mobiusParity = -atom.mobiusParity :=
  parity_krein_skewadjoint atom krein metric_eq spacelike_skewadjoint

example (krein : KasparovKreinData Carrier) (first second : Carrier) :
    krein.diracAdjoint (first * second) =
      krein.diracAdjoint second * krein.diracAdjoint first :=
  krein.diracAdjoint_mul first second

#print axioms metric_conjugation_negates_parity
#print axioms parity_krein_skewadjoint
#print axioms commute_iff_diracAdjoint

end InfoGeometry.Synthesis.ModularAtomTests

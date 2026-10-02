import InfoGeometry.Canonical.PrimeCl11ModularAtomCore
import InfoGeometry.Physics.KreinDiracKasparovSpinorBilinear

namespace InfoGeometry.Synthesis.ModularAtom

open InfoGeometry.Canonical.PrimeCl11ModularAtomCore
open InfoGeometry.Physics

variable {Carrier : Type*} [Ring Carrier]

theorem metric_conjugation_negates_parity (atom : Cl11Atom Carrier) :
    atom.c * atom.mobiusParity * atom.c = -atom.mobiusParity := by
  rw [atom.c_anticommutes_mobiusParity, neg_mul, mul_assoc, atom.c_sq, mul_one]

section Adjoint

variable [StarRing Carrier]

theorem parity_star_self (atom : Cl11Atom Carrier)
    (timelike_selfadjoint : star atom.c = atom.c)
    (spacelike_skewadjoint : star atom.d = -atom.d) :
    star atom.mobiusParity = atom.mobiusParity := by
  simp only [Cl11Atom.mobiusParity, star_mul, timelike_selfadjoint,
    spacelike_skewadjoint, neg_mul, atom.d_mul_c_eq_neg_c_mul_d, neg_neg]

theorem parity_krein_skewadjoint (atom : Cl11Atom Carrier)
    (krein : KasparovKreinData Carrier) (metric_eq : krein.eta = atom.c)
    (spacelike_skewadjoint : star atom.d = -atom.d) :
    krein.diracAdjoint atom.mobiusParity = -atom.mobiusParity := by
  have timelike_selfadjoint : star atom.c = atom.c := by
    rw [← metric_eq]
    exact krein.property.2.1
  unfold KasparovKreinData.diracAdjoint
  rw [parity_star_self atom timelike_selfadjoint spacelike_skewadjoint, metric_eq]
  exact metric_conjugation_negates_parity atom

theorem diracAdjoint_preserves_commutation (krein : KasparovKreinData Carrier)
    (first second : Carrier) (commutes : Commute first second) :
    Commute (krein.diracAdjoint first) (krein.diracAdjoint second) := by
  change krein.diracAdjoint first * krein.diracAdjoint second =
    krein.diracAdjoint second * krein.diracAdjoint first
  simpa only [krein.diracAdjoint_mul] using congrArg krein.diracAdjoint commutes.eq.symm

theorem commute_iff_diracAdjoint (krein : KasparovKreinData Carrier)
    (first second : Carrier) :
    Commute first second ↔ Commute (krein.diracAdjoint first) (krein.diracAdjoint second) := by
  constructor
  · exact diracAdjoint_preserves_commutation krein first second
  · intro commutes
    simpa only [krein.diracAdjoint_involution] using
      diracAdjoint_preserves_commutation krein (krein.diracAdjoint first)
        (krein.diracAdjoint second) commutes

end Adjoint

end InfoGeometry.Synthesis.ModularAtom

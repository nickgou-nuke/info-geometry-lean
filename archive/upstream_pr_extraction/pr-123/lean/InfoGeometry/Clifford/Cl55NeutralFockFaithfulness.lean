import Mathlib
import InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry

namespace InfoGeometry.Clifford.Cl55NeutralFockFaithfulness

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor

noncomputable section

noncomputable instance neutralClifford_isSimpleRing :
    IsSimpleRing
      (CliffordAlgebra
        (canonicalNeutralFormUnscaled (E := V5))) :=
  IsSimpleRing.of_ringEquiv
    Cl55NeutralHyperbolicIsometry.neutralCliffordMatrixAlgEquiv.toRingEquiv.symm
    inferInstance

theorem neutralCliffordRep_injective :
    Function.Injective neutralCliffordRep := by
  let K : TwoSidedIdeal
      (CliffordAlgebra (canonicalNeutralFormUnscaled (E := V5))) :=
    TwoSidedIdeal.comap neutralCliffordRep.toRingHom.toNonUnitalRingHom ⊥
  rcases IsSimpleOrder.eq_bot_or_eq_top K with hK | hK
  · intro x y hxy
    have hdiff : x - y ∈ K := by
      rw [TwoSidedIdeal.mem_comap]
      change neutralCliffordRep (x - y) = 0
      rw [map_sub, hxy, sub_self]
    rw [hK] at hdiff
    exact sub_eq_zero.mp (by
      simpa only [TwoSidedIdeal.mem_bot] using hdiff)
  · exfalso
    have h1 :
        (1 : CliffordAlgebra (canonicalNeutralFormUnscaled (E := V5))) ∈ K := by
      rw [hK]
      exact TwoSidedIdeal.mem_top _
    rw [TwoSidedIdeal.mem_comap, TwoSidedIdeal.mem_bot] at h1
    change neutralCliffordRep 1 = 0 at h1
    simpa using h1

end
end InfoGeometry.Clifford.Cl55NeutralFockFaithfulness

import InfoGeometry.OperatorAlgebra.PeirceSpine.ChargeSectors
import InfoGeometry.OperatorAlgebra.LieJordanBoundaryComposition

/-!
# Concrete corner operators in native charge sectors

Reuses the existing LieJordan sandwich, inner derivation and cross-transport
endomorphisms. The five pointwise charge identities become submodule membership
statements; the opposite inner derivations bracket to the Sigma derivation.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.LieJordan
variable {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B)
include hP

/-- Double raising is a charge-two endomorphism. -/
theorem plus_sandwich_mem_sector :
    sandwichOp ℤ (conePlus P A) (conePlus P A) ∈ chargeSector P 2 := by
  rw [mem_chargeSector]
  ext X
  exact charge_plus_sandwich hP A X

theorem minus_sandwich_mem_sector :
    sandwichOp ℤ (coneMinus P C) (coneMinus P C) ∈ chargeSector P (-2) := by
  rw [mem_chargeSector]
  ext X
  change charge P (sandwich (coneMinus P C) (coneMinus P C)) X =
    (-2 : ℤ) • sandwich (coneMinus P C) (coneMinus P C) X
  simpa only [neg_smul] using charge_minus_sandwich hP C X

theorem plus_lie_mem_sector :
    lieOp ℤ (conePlus P A) ∈ chargeSector P 1 := by
  rw [mem_chargeSector, one_smul]
  ext X
  exact charge_plus_comm hP A X

theorem minus_lie_mem_sector :
    lieOp ℤ (coneMinus P C) ∈ chargeSector P (-1) := by
  rw [mem_chargeSector, neg_one_smul]
  ext X
  exact charge_minus_comm hP C X

theorem cross_transport_mem_sector :
    crossTransport ℤ (conePlus P A) (coneMinus P C) ∈ chargeSector P 0 := by
  rw [mem_chargeSector, zero_smul]
  ext X
  exact charge_cross_sandwich hP A C X

theorem sigma_lie_mem_sector :
    lieOp ℤ (genSig P A C) ∈ chargeSector P 0 := by
  have hOpposite :
      comm (lieOp ℤ (conePlus P A)) (lieOp ℤ (coneMinus P C)) =
        lieOp ℤ (genSig P A C) := by
    simpa [comm, genSig] using
      (InfoGeometry.OperatorAlgebra.LieJordan.lie_lie ℤ
        (conePlus P A) (coneMinus P C))
  have h := comm_mem_chargeSector (m := 1) (n := -1)
    (plus_lie_mem_sector hP A) (minus_lie_mem_sector hP C)
  simpa only [hOpposite, Int.reduceAdd] using h

end InfoGeometry.OperatorAlgebra.PeirceSpine

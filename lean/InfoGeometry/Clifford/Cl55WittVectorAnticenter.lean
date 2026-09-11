import InfoGeometry.Clifford.Cl55WittVectorCommutant
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55RealSplitPinVolumeAnticommutation

namespace InfoGeometry.Clifford.Clifford55

/-!
# The uniform anticommutant of the Witt vector space

This is the companion carrier to `wittVectorCenter`.  It records the
uniformly anticommuting branch of the real split-Pin kernel reduction without
identifying it with the ordinary algebra center.
-/

def wittVectorAnticenter : Submodule ℝ Cl55 where
  carrier := {a | ∀ v : V55, a * ι55 v = -(ι55 v * a)}
  zero_mem' := by
    intro v
    simp
  add_mem' := by
    intro a b ha hb v
    rw [add_mul, mul_add, ha v, hb v, neg_add]
  smul_mem' := by
    intro r a ha v
    rw [smul_mul_assoc, mul_smul_comm, ha v, smul_neg]

theorem realSplitPin_kernel_mem_wittVectorAnticenter_of_involute_eq_neg
    (g : realSplitPin55)
    (hg : g ∈ (realSplitPinOrthogonalAction).ker)
    (hinv : CliffordAlgebra.involute (Q := Q55) ((g : Cl55ˣ) : Cl55) =
      -((g : Cl55ˣ) : Cl55)) :
    ((g : Cl55ˣ) : Cl55) ∈ wittVectorAnticenter := by
  intro v
  have hcomm := realSplitPin_kernel_twisted_commutation g hg v
  calc
    ((g : Cl55ˣ) : Cl55) * ι55 v =
        -(CliffordAlgebra.involute (Q := Q55)
          ((g : Cl55ˣ) : Cl55) * ι55 v) := by
            rw [hinv]
            noncomm_ring
    _ = -(ι55 v * ((g : Cl55ˣ) : Cl55)) := by rw [hcomm]

theorem cl55WittVolume_mem_wittVectorAnticenter :
    cl55WittVolume ∈ wittVectorAnticenter := by
  intro v
  have h := cl55WittVolume_anticommutes v
  calc
    cl55WittVolume * ι55 v =
        -(-(cl55WittVolume * ι55 v)) := by simp
    _ = -(ι55 v * cl55WittVolume) := by rw [h]

end InfoGeometry.Clifford.Clifford55

import InfoGeometry.Clifford.Cl55RealSplitPinReverseNorm
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55Q55NativeSplitBridge
import InfoGeometry.Clifford.Cl55SpinorAlgebraEquiv

namespace InfoGeometry.Clifford.Clifford55

/-!
# Scalar central branch of the split-Pin kernel

This is the exact conditional central branch.  It deliberately takes the
matrix algebra equivalence as an argument, and also exposes the specialization
to the native spinor algebra equivalence.
-/

theorem realSplitPin_kernel_pm_one_of_center
    (e : Cl55 ≃ₐ[ℝ] Matrix (Fin 32) (Fin 32) ℝ)
    (g : realSplitPin55)
    (hcenter : ((g : Cl55ˣ) : Cl55) ∈ Subalgebra.center ℝ Cl55) :
    (g : Cl55ˣ) = 1 ∨ (g : Cl55ˣ) = -1 := by
  obtain ⟨r, hr⟩ := center_scalar_of_algEquiv_matrix e hcenter
  exact realSplitPin_scalar_coe_eq_pm_one_of_reverse_norm
    g ⟨r, hr⟩
      (realSplitPin_reverse_mul_coe_eq_one_or_neg
      (g : Cl55ˣ) g.property)

theorem realSplitPin_kernel_pm_one_of_native_center
    (g : realSplitPin55)
    (hcenter : ((g : Cl55ˣ) : Cl55) ∈ Subalgebra.center ℝ Cl55) :
    (g : Cl55ˣ) = 1 ∨ (g : Cl55ˣ) = -1 := by
  exact realSplitPin_kernel_pm_one_of_center cl55SpinorAlgEquiv g hcenter

theorem realSplitPin_kernel_pm_one_of_spinor_surjective_of_center
    [FiniteDimensional ℝ Cl55]
    (hs : Function.Surjective cl55SpinorRepresentation)
    (hfin : Module.finrank ℝ Cl55 =
      Module.finrank ℝ (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5))
    (g : realSplitPin55)
    (hcenter : ((g : Cl55ˣ) : Cl55) ∈ Subalgebra.center ℝ Cl55) :
    (g : Cl55ˣ) = 1 ∨ (g : Cl55ˣ) = -1 := by
  exact realSplitPin_kernel_pm_one_of_center
    (cl55SpinorAlgEquiv_of_surjective hs hfin) g hcenter

end InfoGeometry.Clifford.Clifford55

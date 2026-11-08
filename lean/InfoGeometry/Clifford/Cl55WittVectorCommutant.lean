import InfoGeometry.Clifford.Cl55RealSplitPinKernelReduction
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford.Clifford55

/-!
# The Clifford vector commutant

This is the native algebraic carrier for the remaining Pin-kernel proof.  It
records commutation with every embedded quadratic-space vector and makes no
claim yet that the carrier is only the scalar line.
-/

def wittTwistedVectorCommutant : Submodule ℝ Cl55 where
  carrier := {a | ∀ v : V55,
    CliffordAlgebra.involute (Q := Q55) a * ι55 v = ι55 v * a}
  zero_mem' := by
    intro v
    simp
  add_mem' := by
    intro a b ha hb v
    rw [map_add, add_mul, mul_add, ha v, hb v]
  smul_mem' := by
    intro r a ha v
    rw [map_smul, smul_mul_assoc, mul_smul_comm, ha v]

theorem algebraMap_mem_wittTwistedVectorCommutant (r : ℝ) :
    algebraMap ℝ Cl55 r ∈ wittTwistedVectorCommutant := by
  intro v
  simpa [CliffordAlgebra.involute] using Algebra.commutes r (ι55 v)

theorem scalarLine_le_wittTwistedVectorCommutant :
    Submodule.span ℝ (Set.range (algebraMap ℝ Cl55)) ≤
      wittTwistedVectorCommutant := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨r, rfl⟩
  exact algebraMap_mem_wittTwistedVectorCommutant r

def wittVectorCenter : Submodule ℝ Cl55 where
  carrier := {a | ∀ v : V55, a * ι55 v = ι55 v * a}
  zero_mem' := by
    intro v
    simp
  add_mem' := by
    intro a b ha hb v
    rw [add_mul, mul_add, ha v, hb v]
  smul_mem' := by
    intro r a ha v
    rw [smul_mul_assoc, mul_smul_comm, ha v]

theorem wittVectorCenter_commutes
    {a : Cl55} (ha : a ∈ wittVectorCenter) (b : Cl55) :
    a * b = b * a := by
  induction b using CliffordAlgebra.induction with
  | algebraMap r =>
      exact (Algebra.commutes r a).symm
  | ι v =>
      exact ha v
  | mul b c hb hc =>
      calc
        a * (b * c) = (a * b) * c := (mul_assoc a b c).symm
        _ = (b * a) * c := by rw [hb]
        _ = b * (a * c) := mul_assoc b a c
        _ = b * (c * a) := congrArg (fun z => b * z) hc
        _ = b * c * a := (mul_assoc b c a).symm
  | add b c hb hc =>
      rw [mul_add, add_mul, hb, hc]

theorem mem_subalgebraCenter_iff_mem_wittVectorCenter (a : Cl55) :
    a ∈ Subalgebra.center ℝ Cl55 ↔ a ∈ wittVectorCenter := by
  constructor
  · intro ha v
    exact ((Subalgebra.mem_center_iff.mp ha) (ι55 v)).symm
  · intro ha
    rw [Subalgebra.mem_center_iff]
    intro b
    exact (wittVectorCenter_commutes ha b).symm

theorem scalarLine_le_wittVectorCenter :
    Submodule.span ℝ (Set.range (algebraMap ℝ Cl55)) ≤
      wittVectorCenter := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨r, rfl⟩ v
  exact Algebra.commutes r (ι55 v)

theorem realSplitPin_kernel_coe_mem_wittVectorCommutant
    (g : realSplitPin55)
    (hg : g ∈ (realSplitPinOrthogonalAction).ker) :
    ((g : Cl55ˣ) : Cl55) ∈ wittTwistedVectorCommutant := by
  intro v
  exact realSplitPin_kernel_twisted_commutation g hg v

end InfoGeometry.Clifford.Clifford55

import InfoGeometry.Clifford.Cl55RealSplitPinKernelReduction

namespace InfoGeometry.Clifford.Clifford55

/-!
# Central reduction for the real split-Pin kernel

The kernel reduction gives a commuting or anticommuting alternative on the
embedded Clifford vectors.  This file proves the genuine algebraic part of
the commuting branch: it lies in the native algebra center.  The remaining
identification of that center with the scalar line is intentionally separate.
-/

theorem realSplitPin_kernel_mem_center_of_involute_eq
    (g : realSplitPin55)
    (hg : g ∈ (realSplitPinOrthogonalAction).ker)
    (hinv : CliffordAlgebra.involute (Q := Q55) ((g : Cl55ˣ) : Cl55) =
      ((g : Cl55ˣ) : Cl55)) :
    ((g : Cl55ˣ) : Cl55) ∈ Subalgebra.center ℝ Cl55 := by
  rw [Subalgebra.mem_center_iff]
  intro x
  have hx : x ∈ Algebra.adjoin ℝ (Set.range (ι55)) := by
    rw [CliffordAlgebra.adjoin_range_ι (Q := Q55)]
    trivial
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
  · intro z hz
    rcases hz with ⟨v, rfl⟩
    have hcomm := realSplitPin_kernel_twisted_commutation g hg v
    simpa [hinv] using hcomm.symm
  · intro r
    exact Algebra.commutes r ((g : Cl55ˣ) : Cl55)
  · intro a b ha hb hxa hxb
    rw [add_mul, mul_add, hxa, hxb]
  · intro a b ha hb hxa hxb
    calc
      (a * b) * ((g : Cl55ˣ) : Cl55) =
          a * (b * ((g : Cl55ˣ) : Cl55)) := by rw [mul_assoc]
      _ = a * (((g : Cl55ˣ) : Cl55) * b) := by rw [hxb]
      _ = (a * ((g : Cl55ˣ) : Cl55)) * b := by rw [← mul_assoc]
      _ = (((g : Cl55ˣ) : Cl55) * a) * b := by rw [hxa]
      _ = ((g : Cl55ˣ) : Cl55) * (a * b) := by rw [mul_assoc]

theorem realSplitPin_kernel_center_or_uniform_anticommutation
    (g : realSplitPin55)
    (hg : g ∈ (realSplitPinOrthogonalAction).ker) :
    ((g : Cl55ˣ) : Cl55) ∈ Subalgebra.center ℝ Cl55 ∨
      ∀ v : V55,
        ((g : Cl55ˣ) : Cl55) * ι55 v =
          -(ι55 v * ((g : Cl55ˣ) : Cl55)) := by
  rcases realSplitPin_involute_eq_or_neg (g : Cl55ˣ) g.property with hinv | hinv
  · left
    exact realSplitPin_kernel_mem_center_of_involute_eq g hg hinv
  · right
    intro v
    have hcomm := realSplitPin_kernel_twisted_commutation g hg v
    calc
      ((g : Cl55ˣ) : Cl55) * ι55 v =
          -(CliffordAlgebra.involute (Q := Q55)
            ((g : Cl55ˣ) : Cl55) * ι55 v) := by
              rw [hinv]
              noncomm_ring
      _ = -(ι55 v * ((g : Cl55ˣ) : Cl55)) := by rw [hcomm]

end InfoGeometry.Clifford.Clifford55

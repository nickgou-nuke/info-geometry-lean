import InfoGeometry.Clifford.Cl55RealSplitPinKernelCenter
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford.Clifford55

/-!
# Volume reduction of the residual split-Pin kernel branch

This is the algebraic reduction used after the symbolic computation has
identified the even volume as the only possible uniform anticommutant.  It
does not assume a matrix classification.  The concrete `Cl(5,5)` volume
instance and the scalarity of the native center remain separate theorems.
-/

theorem cl55_product_mem_center_of_uniform_anticommutation
    (x : Cl55) (w : Cl55ˣ)
    (hx : ∀ v : V55, x * ι55 v = -(ι55 v * x))
    (hw : ∀ v : V55,
      (w : Cl55) * ι55 v = -(ι55 v * (w : Cl55))) :
    x * (w : Cl55) ∈ Subalgebra.center ℝ Cl55 := by
  rw [Subalgebra.mem_center_iff]
  intro z
  have hz : z ∈ Algebra.adjoin ℝ (Set.range (ι55)) := by
    rw [CliffordAlgebra.adjoin_range_ι (Q := Q55)]
    trivial
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hz
  · intro v hv
    rcases hv with ⟨v, rfl⟩
    calc
      ι55 v * (x * (w : Cl55)) =
          (ι55 v * x) * (w : Cl55) := by rw [mul_assoc]
      _ = (-(x * ι55 v)) * (w : Cl55) := by
        rw [hx]
        simp
      _ = -(x * (ι55 v * (w : Cl55))) := by
        simp only [neg_mul, mul_assoc]
      _ = -(x * (-(w : Cl55) * ι55 v)) := by
        have hwi : ι55 v * (w : Cl55) =
            -((w : Cl55) * ι55 v) := by
          simpa using (congrArg Neg.neg (hw v)).symm
        simpa [neg_mul] using congrArg (fun y : Cl55 => -(x * y)) hwi
      _ = (x * (w : Cl55)) * ι55 v := by noncomm_ring
  · intro r
    exact Algebra.commutes r (x * (w : Cl55))
  · intro a b ha hb hza hzb
    rw [add_mul, mul_add, hza, hzb]
  · intro a b ha hb hza hzb
    calc
      (a * b) * (x * (w : Cl55)) =
          a * (b * (x * (w : Cl55))) := by rw [mul_assoc]
      _ = a * ((x * (w : Cl55)) * b) := by rw [hzb]
      _ = (a * (x * (w : Cl55))) * b := by rw [← mul_assoc]
      _ = ((x * (w : Cl55)) * a) * b := by rw [hza]
      _ = (x * (w : Cl55)) * (a * b) := by rw [mul_assoc]

theorem realSplitPin_kernel_neg_involute_impossible_of_antivolume
    (g : realSplitPin55)
    (hg : g ∈ (realSplitPinOrthogonalAction).ker)
    (hinv : CliffordAlgebra.involute (Q := Q55)
        ((g : Cl55ˣ) : Cl55) = -((g : Cl55ˣ) : Cl55))
    (w : Cl55ˣ)
    (hw_anti : ∀ v : V55,
      (w : Cl55) * ι55 v = -(ι55 v * (w : Cl55)))
    (hw_involute : CliffordAlgebra.involute (Q := Q55) (w : Cl55) = w)
    (center_scalar : ∀ {z : Cl55},
      z ∈ Subalgebra.center ℝ Cl55 →
        ∃ r : ℝ, algebraMap ℝ Cl55 r = z) :
    False := by
  let x : Cl55 := ((g : Cl55ˣ) : Cl55)
  have hanti : ∀ v : V55, x * ι55 v = -(ι55 v * x) := by
    intro v
    have hanti' := realSplitPin_kernel_center_or_uniform_anticommutation g hg |>.resolve_left
      (fun hcenter => by
        have hscalar := center_scalar hcenter
        rcases hscalar with ⟨r, hr⟩
        have hunit : x ≠ 0 := Units.ne_zero (g : Cl55ˣ)
        have hneg : x = -x := by
          calc
            x = algebraMap ℝ Cl55 r := hr.symm
            _ = CliffordAlgebra.involute (Q := Q55) x := by
              change algebraMap ℝ Cl55 r =
                CliffordAlgebra.involute (Q := Q55)
                  ((g : Cl55ˣ) : Cl55)
              rw [← hr]
              exact (CliffordAlgebra.involute (Q := Q55)).commutes r |>.symm
            _ = -x := by simpa [x] using hinv
        have hadd : x + x = 0 := by
          calc
            x + x = -x + x := congrArg (fun z : Cl55 => z + x) hneg
            _ = 0 := neg_add_cancel x
        have htwo : (2 : ℝ) • x = 0 := by
          simpa [two_smul] using hadd
        exact hunit ((smul_eq_zero.mp htwo).resolve_left (by norm_num)))
    simpa [x] using hanti' v
  have hcenter : x * (w : Cl55) ∈ Subalgebra.center ℝ Cl55 :=
    cl55_product_mem_center_of_uniform_anticommutation x w hanti hw_anti
  rcases center_scalar hcenter with ⟨r, hr⟩
  have hprod : CliffordAlgebra.involute (Q := Q55) x * (w : Cl55) =
      x * (w : Cl55) := by
    calc
      CliffordAlgebra.involute (Q := Q55) x * (w : Cl55) =
          CliffordAlgebra.involute (Q := Q55) x *
            CliffordAlgebra.involute (Q := Q55) (w : Cl55) := by
              rw [hw_involute]
      _ = CliffordAlgebra.involute (Q := Q55) (x * (w : Cl55)) := by
            rw [map_mul]
      _ = CliffordAlgebra.involute (Q := Q55) (algebraMap ℝ Cl55 r) := by
            rw [hr]
      _ = algebraMap ℝ Cl55 r := by simp
      _ = x * (w : Cl55) := hr
  have hx : CliffordAlgebra.involute (Q := Q55) x = x := by
    have hcancel := congrArg (fun y : Cl55 =>
      y * (↑((w : Cl55ˣ)⁻¹) : Cl55)) hprod
    simpa [x, mul_assoc] using hcancel
  have hxneg : x = -x := by
    calc
      x = CliffordAlgebra.involute (Q := Q55) x := hx.symm
      _ = -x := by simpa [x] using hinv
  have hxzero : x = 0 := by
    have hadd : x + x = 0 := by
      calc
        x + x = -x + x := congrArg (fun z : Cl55 => z + x) hxneg
        _ = 0 := neg_add_cancel x
    have htwo : (2 : ℝ) • x = 0 := by simpa [two_smul] using hadd
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact (Units.ne_zero (g : Cl55ˣ)) hxzero

end InfoGeometry.Clifford.Clifford55

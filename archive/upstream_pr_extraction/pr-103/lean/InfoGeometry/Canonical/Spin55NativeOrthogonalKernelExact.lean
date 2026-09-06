import InfoGeometry.Canonical.Spin55NativeOrthogonalCentralKernel
import InfoGeometry.Clifford.Cl55NativeCenterScalar

namespace InfoGeometry.Clifford.Clifford55

/-!
# Exact kernel of the native `Spin(5,5)` orthogonal action

The kernel is reduced intrinsically: a kernel element commutes with the
Clifford vector generators, hence is central; the faithful matrix centre is
scalar, and the native `star` norm reduces that scalar to `+1` or `-1`.
-/

theorem spinNativeOrthogonalAction_kernel_mem_center
    (g : Spin55)
    (hg : g ∈ (spinNativeOrthogonalAction).ker) :
    (g : Cl55) ∈ Subalgebra.center ℝ Cl55 := by
  rw [Subalgebra.mem_center_iff]
  intro x
  have hx : x ∈ Algebra.adjoin ℝ (Set.range (ι55)) := by
    rw [CliffordAlgebra.adjoin_range_ι (Q := Q55)]
    trivial
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
  · intro z hz
    rcases hz with ⟨v, rfl⟩
    have hfixed : spinAction g v = v :=
      (spinNativeOrthogonalAction_mem_kernel_iff g).mp hg v
    have hread := pinTwistedAction_apply_ι (spinToPin g) v
    have hu : pinToUnits (spinToPin g) = spinGroup.toUnits g := by
      apply Units.ext
      rfl
    have hinv :
        CliffordAlgebra.involute (spinGroup.toUnits g : Cl55) =
          (spinGroup.toUnits g : Cl55) := by
      simpa using (spinGroup.involute_eq g.property)
    have hread' :
        ι55 (spinAction g v) =
          (spinGroup.toUnits g : Cl55) * ι55 v *
            (↑((spinGroup.toUnits g)⁻¹) : Cl55) := by
      simpa only [spinAction, pinTwistedAdj, hu, hinv] using hread
    rw [hfixed] at hread'
    have hconj :
        (g : Cl55) * ι55 v *
            (↑((spinGroup.toUnits g)⁻¹) : Cl55) = ι55 v := by
      exact hread'.symm
    have hunit :
        (↑((spinGroup.toUnits g)⁻¹) : Cl55) * (g : Cl55) = 1 := by
      exact Units.inv_mul (spinGroup.toUnits g)
    calc
      ι55 v * (g : Cl55) =
          ((g : Cl55) * ι55 v *
            (↑((spinGroup.toUnits g)⁻¹) : Cl55)) * (g : Cl55) := by
              rw [hconj]
      _ = (g : Cl55) * ι55 v *
            ((↑((spinGroup.toUnits g)⁻¹) : Cl55) * (g : Cl55)) := by
              simp only [mul_assoc]
      _ = (g : Cl55) * ι55 v := by rw [hunit, mul_one]
  · intro r
    exact Algebra.commutes r (g : Cl55)
  · intro a b ha hb hxa hxb
    rw [add_mul, mul_add, hxa, hxb]
  · intro a b ha hb hxa hxb
    calc
      (a * b) * (g : Cl55) = a * (b * (g : Cl55)) := by rw [mul_assoc]
      _ = a * ((g : Cl55) * b) := by rw [hxb]
      _ = (a * (g : Cl55)) * b := by rw [← mul_assoc]
      _ = ((g : Cl55) * a) * b := by rw [hxa]
      _ = (g : Cl55) * (a * b) := by rw [mul_assoc]

theorem spinNativeOrthogonalAction_kernel_coe_eq_pm_one
    (g : Spin55)
    (hg : g ∈ (spinNativeOrthogonalAction).ker) :
    (g : Cl55) = 1 ∨ (g : Cl55) = -1 := by
  obtain ⟨r, hr⟩ := cl55_center_scalar
    (spinNativeOrthogonalAction_kernel_mem_center g hg)
  have hsq : r * r = 1 := by
    apply (algebraMap ℝ Cl55).injective
    calc
      algebraMap ℝ Cl55 (r * r) =
          algebraMap ℝ Cl55 r * algebraMap ℝ Cl55 r := by rw [map_mul]
      _ = star (g : Cl55) * (g : Cl55) := by
        rw [← hr, CliffordAlgebra.star_algebraMap]
      _ = 1 := by exact spinGroup.star_mul_self_of_mem g.property
  rcases (mul_self_eq_one_iff.mp hsq) with hr_one | hr_neg
  · left
    calc
      (g : Cl55) = algebraMap ℝ Cl55 r := hr.symm
      _ = 1 := by simp [hr_one]
  · right
    calc
      (g : Cl55) = algebraMap ℝ Cl55 r := hr.symm
      _ = -1 := by simp [hr_neg]

theorem negOneSpin_coe : (negOneSpin : Cl55) = -1 := by
  have h := congrArg (fun p : Pin55 => (p : Cl55)) spinToPin_negOneSpin
  change (negOneSpin : Cl55) = (negOnePin : Cl55) at h
  rw [h, negOnePin_coe]

theorem spinNativeOrthogonalAction_mem_kernel_iff_pm_one
    (g : Spin55) :
    g ∈ (spinNativeOrthogonalAction).ker ↔
      g = 1 ∨ g = negOneSpin := by
  constructor
  · intro hg
    rcases spinNativeOrthogonalAction_kernel_coe_eq_pm_one g hg with h | h
    · left
      apply Subtype.ext
      exact h
    · right
      apply Subtype.ext
      exact h.trans negOneSpin_coe.symm
  · intro hg
    rcases hg with rfl | rfl
    · exact (spinNativeOrthogonalAction).ker.one_mem
    · exact negOneSpin_mem_kernel

theorem spinNativeOrthogonalAction_kernel_eq_spinSignSubgroup :
    (spinNativeOrthogonalAction).ker = spinSignSubgroup := by
  ext g
  rw [spinNativeOrthogonalAction_mem_kernel_iff_pm_one,
    mem_spinSignSubgroup_iff]

end InfoGeometry.Clifford.Clifford55

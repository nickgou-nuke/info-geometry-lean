import InfoGeometry.Clifford.Cl55RealSplitPinVolumeAnticommutation
import InfoGeometry.Clifford.Cl55RealSplitPinKernelEvidence

namespace InfoGeometry.Clifford.Clifford55

theorem realSplitPinOrthogonalAction_mem_kernel_iff_pm_one
    (g : realSplitPin55) :
    g ∈ (realSplitPinOrthogonalAction).ker ↔
      (g : Cl55ˣ) = 1 ∨ (g : Cl55ˣ) = -1 := by
  constructor
  · exact realSplitPin_kernel_pm_one g
  · rintro h
    rcases h with h | h
    · have hg : g = 1 := by
        apply Subtype.ext
        exact h
      rw [hg]
      simp
    · have hg : g = realSplitNegOne := by
        apply Subtype.ext
        apply Units.ext
        have hcoe := congrArg (fun u : Cl55ˣ => (u : Cl55)) h
        calc
          ((g : Cl55ˣ) : Cl55) = -1 := hcoe
          _ = ((realSplitNegOne : Cl55ˣ) : Cl55) := realSplitNegOne_coe.symm
      rw [hg]
      exact realSplitNegOne_mem_kernel

def realSplitPinSignSubgroup : Subgroup realSplitPin55 where
  carrier := {g | (g : Cl55ˣ) = 1 ∨ (g : Cl55ˣ) = -1}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro g h hg hh
    rcases hg with hg | hg <;> rcases hh with hh | hh
    · left
      simp [hg, hh]
    · right
      simp [hg, hh]
    · right
      simp [hg, hh]
    · left
      simp [hg, hh]
  inv_mem' := by
    intro g hg
    rcases hg with hg | hg
    · left
      simp [hg]
    · right
      simp [hg]

instance realSplitPinSignSubgroup_normal :
    realSplitPinSignSubgroup.Normal where
  conj_mem g hg h := by
    rcases hg with hg | hg
    · left
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hg]
      simp
    · right
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hg]
      simp

theorem realSplitPinOrthogonalAction_kernel_eq_signSubgroup :
    (realSplitPinOrthogonalAction).ker = realSplitPinSignSubgroup := by
  ext g
  exact realSplitPinOrthogonalAction_mem_kernel_iff_pm_one g

theorem realSplitPinSignSubgroup_inclusion_mulExact :
    Function.MulExact
      (realSplitPinSignSubgroup.subtype :
        realSplitPinSignSubgroup →* realSplitPin55)
      realSplitPinOrthogonalAction := by
  intro g
  constructor
  · intro hg
    have hsign : g ∈ realSplitPinSignSubgroup :=
      (realSplitPinOrthogonalAction_kernel_eq_signSubgroup).symm ▸ hg
    exact ⟨⟨g, hsign⟩, rfl⟩
  · intro hg
    rcases hg with ⟨h, hh⟩
    rw [← hh]
    change realSplitPinOrthogonalAction (h : realSplitPin55) = 1
    exact (realSplitPinOrthogonalAction_mem_kernel_iff_pm_one
      (h : realSplitPin55)).mpr h.property

end InfoGeometry.Clifford.Clifford55

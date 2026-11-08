import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

namespace Omega.RecursiveAddressing

/-- If the intrinsic hidden subgroup is contained in the strict hidden subgroup, the quotient by
the intrinsic subgroup maps naturally and surjectively onto the strict visible quotient.
    cor:prefix-site-intrinsic-to-strict-visible -/
theorem paper_prefix_site_intrinsic_to_strict_visible
    {A : Type*} [AddCommGroup A] (K H : AddSubgroup A) (hKH : K ≤ H) :
    ∃ q : A ⧸ K →+ A ⧸ H, Function.Surjective q := by
  have hK : K ≤ H.comap (AddMonoidHom.id A) := by
    intro a ha
    exact hKH ha
  let q : A ⧸ K →+ A ⧸ H :=
    QuotientAddGroup.map K H (AddMonoidHom.id A) hK
  refine ⟨q, ?_⟩
  intro y
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective H y
  exact ⟨QuotientAddGroup.mk' K a, by
    change QuotientAddGroup.map K H (AddMonoidHom.id A) hK (QuotientAddGroup.mk' K a) =
      QuotientAddGroup.mk' H a
    rw [QuotientAddGroup.map_mk']
    rfl⟩

end Omega.RecursiveAddressing

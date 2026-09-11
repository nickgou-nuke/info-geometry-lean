import Mathlib.Algebra.Group.Subgroup.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Set.Basic

namespace InfoGeometry.Foundations

section TitsExhaustion

variable {G : Type*} [Group G]

def leftStabilizer (U : Set G) : Subgroup G where
  carrier := {g | ∀ x, x ∈ U ↔ g * x ∈ U}
  one_mem' := by simp
  mul_mem' := by
    intro g₁ g₂ hg₁ hg₂ x
    exact (hg₂ x).trans (by simpa [mul_assoc] using hg₁ (g₂ * x))
  inv_mem' := by
    intro g hg x
    simpa [mul_assoc] using (hg (g⁻¹ * x)).symm

@[simp] theorem mem_leftStabilizer_iff (U : Set G) (g : G) :
    g ∈ leftStabilizer U ↔ ∀ x, x ∈ U ↔ g * x ∈ U := Iff.rfl

theorem tits_exhaustion_of_closure_top (U : Set G) (h1 : (1 : G) ∈ U)
    (S : Set G) (h_gen : Subgroup.closure S = ⊤)
    (h_stab : S ⊆ leftStabilizer U) : U = Set.univ := by
  have hclosure : Subgroup.closure S ≤ leftStabilizer U :=
    (Subgroup.closure_le _).2 h_stab
  ext g
  simp only [Set.mem_univ, iff_true]
  have hg : g ∈ Subgroup.closure S := by rw [h_gen]; simp
  have hmem : g * 1 ∈ U :=
    ((mem_leftStabilizer_iff U g).mp (hclosure hg) 1).mp h1
  simpa using hmem

theorem closure_subset_of_leftStabilizer
    (U : Set G) (h1 : (1 : G) ∈ U)
    (S : Set G) (hstab : S ⊆ leftStabilizer U) :
    (Subgroup.closure S : Set G) ⊆ U := by
  have hclosure : Subgroup.closure S ≤ leftStabilizer U :=
    (Subgroup.closure_le _).2 hstab
  intro g hg
  have hgstab : g ∈ leftStabilizer U := hclosure hg
  simpa using ((mem_leftStabilizer_iff U g).mp hgstab 1).mp h1

theorem mem_leftStabilizer_of_involution_mapsTo
    (U : Set G) (s : G) (hsq : s * s = 1)
    (hmap : Set.MapsTo (fun x => s * x) U U) :
    s ∈ leftStabilizer U := by
  intro x
  constructor
  · intro hx
    exact hmap hx
  · intro hsx
    have hback : s * (s * x) ∈ U := hmap hsx
    simpa [← mul_assoc, hsq] using hback

theorem mem_leftStabilizer_of_involutive_left_invariant
    (U : Set G) {r : G} (hr : r * r = 1)
    (hforward : ∀ {x : G}, x ∈ U → r * x ∈ U) :
    r ∈ leftStabilizer U := by
  apply mem_leftStabilizer_of_involution_mapsTo U r hr
  intro x hx
  exact hforward hx

theorem tits_exhaustion_of_involutive_generators
    (U : Set G) (h1 : (1 : G) ∈ U) (S : Set G)
    (hgen : Subgroup.closure S = ⊤)
    (hinvol : ∀ s ∈ S, s * s = 1)
    (hinvariant : ∀ s ∈ S, Set.MapsTo (fun x => s * x) U U) :
    U = Set.univ := by
  apply tits_exhaustion_of_closure_top U h1 S hgen
  intro s hs
  exact mem_leftStabilizer_of_involution_mapsTo U s
    (hinvol s hs) (hinvariant s hs)

end TitsExhaustion

end InfoGeometry.Foundations

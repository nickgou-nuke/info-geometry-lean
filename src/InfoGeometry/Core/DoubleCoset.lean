import Mathlib.Algebra.Group.Subgroup.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Set.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic

/-!
# Generic double cosets

The relation `x = h * y * k`, with `h ∈ H` and `k ∈ K`, is the canonical
equivalence relation whose classes are the double cosets `H y K`.
-/

namespace InfoGeometry.Foundations.GroupTheory

variable {G : Type*} [Group G]

def doubleCoset (H : Subgroup G) (g : G) (K : Subgroup G) : Set G :=
  {x | ∃ h ∈ H, ∃ k ∈ K, x = h * g * k}

theorem mem_doubleCoset_self (H K : Subgroup G) (g : G) :
    g ∈ doubleCoset H g K := by
  refine ⟨1, H.one_mem, 1, K.one_mem, ?_⟩
  simp

theorem mem_doubleCoset_iff (H K : Subgroup G) (x g : G) :
    x ∈ doubleCoset H g K ↔ ∃ h ∈ H, ∃ k ∈ K, x = h * g * k :=
  Iff.rfl

theorem doubleCoset_symm (H K : Subgroup G) {x y : G}
    (hxy : x ∈ doubleCoset H y K) :
    y ∈ doubleCoset H x K := by
  rcases hxy with ⟨h, hh, k, hk, rfl⟩
  refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
  group

theorem doubleCoset_trans (H K : Subgroup G) {x y z : G}
    (hxy : x ∈ doubleCoset H y K)
    (hyz : y ∈ doubleCoset H z K) :
    x ∈ doubleCoset H z K := by
  rcases hxy with ⟨h₁, hh₁, k₁, hk₁, rfl⟩
  rcases hyz with ⟨h₂, hh₂, k₂, hk₂, rfl⟩
  refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₂ * k₁, K.mul_mem hk₂ hk₁, ?_⟩
  group

def doubleCosetSetoid (H K : Subgroup G) : Setoid G where
  r x y := x ∈ doubleCoset H y K
  iseqv := {
    refl := mem_doubleCoset_self H K
    symm := fun h => doubleCoset_symm H K h
    trans := fun h₁ h₂ => doubleCoset_trans H K h₁ h₂
  }

theorem doubleCoset_eq_iff (H K : Subgroup G) (x y : G) :
    doubleCoset H x K = doubleCoset H y K ↔
      x ∈ doubleCoset H y K := by
  constructor
  · intro hxy
    exact hxy ▸ mem_doubleCoset_self H K x
  · intro hxy
    ext z
    constructor
    · intro hzx
      exact doubleCoset_trans H K hzx hxy
    · intro hzy
      exact doubleCoset_trans H K hzy (doubleCoset_symm H K hxy)

theorem iUnion_doubleCoset_eq_univ (H K : Subgroup G) :
    (⋃ g : G, doubleCoset H g K) = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    rw [Set.mem_iUnion]
    exact ⟨x, mem_doubleCoset_self H K x⟩

/-! The product action records the two-sided multiplication directly.  The
    inverse on the right factor is harmless because `K` is a group, and makes
    this a genuine left action. -/

instance doubleCosetMulAction (H K : Subgroup G) : MulAction (H × K) G where
  smul p x := (p.1 : G) * x * (p.2 : G)⁻¹
  one_smul x := by
    change (1 : G) * x * (1 : G)⁻¹ = x
    simp
  mul_smul p q x := by
    change ((p.1 * q.1 : H) : G) * x * ((p.2 * q.2 : K) : G)⁻¹ =
      (p.1 : G) * ((q.1 : G) * x * (q.2 : G)⁻¹) * (p.2 : G)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group

theorem orbit_eq_doubleCoset (H K : Subgroup G) (g : G) :
    MulAction.orbit (H × K) g = doubleCoset H g K := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨p, rfl⟩
    refine ⟨p.1, p.1.2, (p.2 : G)⁻¹, K.inv_mem p.2.2, ?_⟩
    rfl
  · intro hx
    rcases hx with ⟨h, hh, k, hk, rfl⟩
    refine ⟨⟨⟨h, hh⟩, ⟨k⁻¹, K.inv_mem hk⟩⟩, ?_⟩
    change (h : G) * g * ((⟨k⁻¹, K.inv_mem hk⟩ : K) : G)⁻¹ =
      (h : G) * g * k
    simp

theorem doubleCoset_eq_or_disjoint (H K : Subgroup G) (x y : G) :
    doubleCoset H x K = doubleCoset H y K ∨
      Disjoint (doubleCoset H x K) (doubleCoset H y K) := by
  by_cases hxy : x ∈ doubleCoset H y K
  · left
    ext z
    constructor
    · intro hz
      exact doubleCoset_trans H K hz hxy
    · intro hz
      exact doubleCoset_trans H K hz (doubleCoset_symm H K hxy)
  · right
    rw [Set.disjoint_left]
    intro z hzx hzy
    apply hxy
    exact doubleCoset_trans H K (doubleCoset_symm H K hzx) hzy

end InfoGeometry.Foundations.GroupTheory

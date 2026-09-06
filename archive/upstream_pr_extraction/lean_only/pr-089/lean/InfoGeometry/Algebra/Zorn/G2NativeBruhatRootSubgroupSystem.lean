import InfoGeometry.Algebra.Zorn.G2NativeRootSubgroupSystem
import InfoGeometry.Algebra.Zorn.G2TwoExplicitGenerators

namespace InfoGeometry.Algebra.Zorn.G2NativeBruhatRootSubgroupSystem

open InfoGeometry.Algebra.Zorn.G2NativeRootSubgroupSystem
open InfoGeometry.Algebra.Zorn.G2RootSubgroup
open InfoGeometry.Algebra.Zorn.G2RootSubgroupBaseEquiv
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2Unipotent
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-! The native root-subgroup interface needed by a later Bruhat owner.  The
    product normal form and rank-one peeling laws are deliberately not fields
    here: they require additional Chevalley/BN-pair mathematics. -/
structure System extends G2NativeRootSubgroupSystem.System where
  root_mem : ∀ (α : G2Root) (t : Bool),
    xRoot α t ∈ rootSubgroup α

noncomputable def native : System where
  parameter := rootSubgroupEquivBool
  root_zero := by
    intro α
    exact xRoot_false α
  root_additive := by
    intro α s t
    exact xRoot_add α s t
  root_injective := by
    intro α
    intro s t h
    exact (rootSubgroupEquivBool α).injective h
  cTransport := rootSubgroupEquiv_c_apply
  sTransport := rootSubgroupEquiv_s_apply
  root_mem α t := (rootSubgroupMap α t).property

theorem native_root_mem (α : G2Root) (t : Bool) :
    xRoot α t ∈ rootSubgroup α := by
  exact native.root_mem α t

theorem native_root_zero (α : G2Root) :
    xRoot α false = 1 := by
  exact native.root_zero α

theorem native_root_additive (α : G2Root) (s t : Bool) :
    xRoot α (s ^^ t) = xRoot α s * xRoot α t := by
  exact native.root_additive α s t

theorem native_root_inverse (α : G2Root) (t : Bool) :
    (xRoot α t)⁻¹ = xRoot α t := by
  cases t
  · simp [xRoot_false]
  · rw [xRoot_true]
    exact inv_eq_of_mul_eq_one_left (rootAut_sq α)

theorem native_root_subgroup_card (α : G2Root) :
    Nat.card (rootSubgroup α) = 2 := by
  exact rootSubgroup_card α

theorem native_root_commutator_short_0_2 :
    automorphismCommutator
        (xRoot (RootLength.Short, 0) true)
        (xRoot (RootLength.Short, 2) true) =
      xRoot (RootLength.Short, 1) true := by
  simpa [xRoot] using rootAut_commutator_S0_S2

theorem native_root_commutator_short_0_2_ne_one :
    automorphismCommutator
        (xRoot (RootLength.Short, 0) true)
        (xRoot (RootLength.Short, 2) true) ≠
      (1 : SplitOctF2Aut) := by
  rw [native_root_commutator_short_0_2]
  simpa [xRoot] using rootAut_ne_one (RootLength.Short, 1)

theorem native_root_commutator_short_0_2_mem :
    automorphismCommutator
        (xRoot (RootLength.Short, 0) true)
        (xRoot (RootLength.Short, 2) true) ∈
      rootSubgroup (RootLength.Short, 1) := by
  rw [native_root_commutator_short_0_2]
  exact native_root_mem (RootLength.Short, 1) true

theorem native_root_injective (α : G2Root) :
    Function.Injective (xRoot α) := by
  intro s t h
  apply native.root_injective α
  apply Subtype.ext
  exact h

theorem native_c_conjugate_mem (α : G2Root) (t : Bool) :
    c * xRoot α t * c⁻¹ ∈ rootSubgroup (cAction α) := by
  have h := c_xRoot_c α t
  rw [h]
  exact native_root_mem (cAction α) t

theorem native_s_conjugate_mem (α : G2Root) (t : Bool) :
    s * xRoot α t * s⁻¹ ∈ rootSubgroup (sAction α) := by
  have hs : s⁻¹ = s := by
    apply mul_left_cancel (a := s)
    simp [s_sq]
  rw [hs, s_xRoot_s]
  exact native_root_mem (sAction α) t

theorem native_c_conjugate_eq (α : G2Root) (t : Bool) :
    c * xRoot α t * c⁻¹ = xRoot (cAction α) t := by
  exact c_xRoot_c α t

theorem native_s_conjugate_eq (α : G2Root) (t : Bool) :
    s * xRoot α t * s⁻¹ = xRoot (sAction α) t := by
  have hs : s⁻¹ = s := by
    apply mul_left_cancel (a := s)
    simp [s_sq]
  rw [hs]
  exact s_xRoot_s α t

end InfoGeometry.Algebra.Zorn.G2NativeBruhatRootSubgroupSystem

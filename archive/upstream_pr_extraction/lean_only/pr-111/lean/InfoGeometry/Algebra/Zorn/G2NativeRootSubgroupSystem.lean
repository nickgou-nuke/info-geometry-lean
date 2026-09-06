import InfoGeometry.Algebra.Zorn.G2RootSubgroupBaseEquiv

namespace InfoGeometry.Algebra.Zorn.G2NativeRootSubgroupSystem

open InfoGeometry.Algebra.Zorn.G2RootSubgroup
open InfoGeometry.Algebra.Zorn.G2RootSubgroupBaseEquiv
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2

structure System where
  parameter : ∀ α, Bool ≃ rootSubgroup α
  root_zero : ∀ (α : G2Root), (parameter α false).1 = 1
  root_additive : ∀ (α : G2Root) (a b : Bool),
    (parameter α (a ^^ b)).1 = (parameter α a).1 * (parameter α b).1
  root_injective : ∀ (α : G2Root), Function.Injective (parameter α)
  cTransport : ∀ α t,
    (rootSubgroupEquiv_c α).toEquiv (parameter α t) =
      parameter (cAction α) t
  sTransport : ∀ α t,
    (rootSubgroupEquiv_s α).toEquiv (parameter α t) =
      parameter (sAction α) t

noncomputable def native : System where
  parameter := rootSubgroupEquivBool
  root_zero := by
    intro (α : G2Root)
    rfl
  root_additive := by
    intro (α : G2Root) a b
    change xRoot α (a ^^ b) = xRoot α a * xRoot α b
    exact xRoot_add α a b
  root_injective := by
    intro (α : G2Root)
    exact (rootSubgroupEquivBool α).injective
  cTransport := rootSubgroupEquiv_c_apply
  sTransport := rootSubgroupEquiv_s_apply

theorem native_parameter_card (α : G2Root) :
    Nat.card (rootSubgroup α) = 2 := by
  simpa using rootSubgroup_card α

theorem native_parameter_mem (α : G2Root) (t : Bool) :
    (native.parameter α t : rootSubgroup α).1 ∈ rootSubgroup α := by
  exact (native.parameter α t).2

theorem native_parameter_surjective (α : G2Root) :
    Function.Surjective (native.parameter α) := by
  exact (native.parameter α).surjective

theorem native_root_element (α : G2Root) (t : Bool) :
    ((native.parameter α t : rootSubgroup α) :
      OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut) =
      xRoot α t := by
  rfl

theorem native_root_zero (α : G2Root) :
    xRoot α false =
      (1 : OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut) := by
  exact native.root_zero α

theorem native_root_additive (α : G2Root) (a b : Bool) :
    xRoot α (a ^^ b) = xRoot α a * xRoot α b := by
  exact native.root_additive α a b

theorem native_root_inverse (α : G2Root) (t : Bool) :
    (xRoot α t)⁻¹ = xRoot α t := by
  cases t
  · simp [xRoot_false]
  · rw [xRoot_true]
    exact inv_eq_of_mul_eq_one_left (rootAut_sq α)

theorem native_root_injective (α : G2Root) :
    Function.Injective (fun t : Bool => xRoot α t) := by
  intro a b hab
  apply native.root_injective α
  apply Subtype.ext
  exact hab

theorem native_c_transport (α : G2Root) (t : Bool) :
    (rootSubgroupEquiv_c α).toEquiv (native.parameter α t) =
      native.parameter (cAction α) t := by
  exact native.cTransport α t

theorem native_s_transport (α : G2Root) (t : Bool) :
    (rootSubgroupEquiv_s α).toEquiv (native.parameter α t) =
      native.parameter (sAction α) t := by
  exact native.sTransport α t

end InfoGeometry.Algebra.Zorn.G2NativeRootSubgroupSystem

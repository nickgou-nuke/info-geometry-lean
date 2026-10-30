/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.RootSystem.D4WeylGroup

/-!
# D₄ Weyl symmetries on lattice-indexed bit configurations

Every integral D₄ Weyl automorphism reindexes Boolean configurations on the
root lattice. This is the direct action on a symbolic Cantor-style
configuration space; it does not identify this Weyl group with a Brin or
Thompson group.
-/

namespace InfoGeometry.RootSystem.D4

/-- A Boolean configuration whose coordinates are indexed by the D₄ root
lattice. -/
abbrev D4BitConfiguration := Lattice → Bool

/-- The integral D₄ Weyl group acts on lattice-indexed configurations by
inverse reindexing. -/
instance d4WeylGroupBitConfigurationAction :
    MulAction d4WeylGroup D4BitConfiguration where
  smul g f x := f (((g⁻¹ : d4WeylGroup) : Lattice ≃ Lattice) x)
  one_smul := by
    intro f
    funext x
    change f ((1 : Lattice ≃ Lattice) x) = f x
    rfl
  mul_smul := by
    intro g h f
    funext x
    change f (((h⁻¹ : d4WeylGroup) : Lattice ≃ Lattice)
      (((g⁻¹ : d4WeylGroup) : Lattice ≃ Lattice) x)) =
      f ((((g * h)⁻¹ : d4WeylGroup) : Lattice ≃ Lattice) x)
    congr 1

@[simp] theorem smul_bitConfiguration_apply (g : d4WeylGroup)
    (f : D4BitConfiguration) (x : Lattice) :
    (g • f) x = f (((g⁻¹ : d4WeylGroup) : Lattice ≃ Lattice) x) := rfl

/-- The action on all Boolean lattice configurations separates distinct
integral Weyl automorphisms. -/
instance d4WeylGroup_faithfulSMul : FaithfulSMul d4WeylGroup D4BitConfiguration := by
  rw [faithfulSMul_iff]
  intro g hg
  have hinv : (g⁻¹ : Lattice ≃ Lattice) = 1 := by
    apply Equiv.ext
    intro x
    have hbit := congrArg (fun f : D4BitConfiguration => f x)
      (hg fun y => decide (y = x))
    rw [smul_bitConfiguration_apply] at hbit
    have hx : ((g⁻¹ : d4WeylGroup) : Lattice ≃ Lattice) x = x := by
      exact of_decide_eq_true (by simpa using hbit)
    exact hx
  apply Subtype.ext
  simpa using congrArg Inv.inv hinv

/-- The induced permutation representation of the D₄ Weyl group on
lattice-indexed Boolean configurations. -/
def d4BitConfigurationPermRep :
    d4WeylGroup →* Equiv.Perm D4BitConfiguration :=
  MulAction.toPermHom d4WeylGroup D4BitConfiguration

/-- The D₄ Weyl group embeds in permutations of its lattice-indexed Boolean
configuration space. -/
theorem d4BitConfigurationPermRep_injective :
    Function.Injective d4BitConfigurationPermRep := by
  intro g h hgh
  apply FaithfulSMul.eq_of_smul_eq_smul (M := d4WeylGroup)
    (α := D4BitConfiguration)
  intro f
  have hfg := congrArg (fun p : Equiv.Perm D4BitConfiguration => p f) hgh
  change g • f = h • f at hfg
  exact hfg

/-- The simple lattice reflection acts on configurations by reindexing with
the same reflection. -/
theorem simpleReflection_smul_apply (i : Fin 4) (f : D4BitConfiguration)
    (x : Lattice) :
    ((⟨simpleReflectionEquiv i, simpleReflectionEquiv_mem_d4WeylGroup i⟩ :
      d4WeylGroup) • f) x = f (simpleReflectionEquiv i x) := by
  change f (((simpleReflectionEquiv i)⁻¹) x) = f (simpleReflectionEquiv i x)
  rw [inv_eq_of_mul_eq_one_left (simpleReflectionEquiv_square i)]

end InfoGeometry.RootSystem.D4

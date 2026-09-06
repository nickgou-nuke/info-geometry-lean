import InfoGeometry.Lie.CanonicalZornG2CartanWeylSymmetrizedMellin
import InfoGeometry.Lie.CanonicalZornG2WeylGroupAction

/-!
# Native-Cartan readout of the finite Weyl-symmetrized Mellin kernel

The finite orbit-sum owner is written on the traceless Cartan model, while the
native Weyl-group owner acts by linear equivalences on the canonical Cartan.
This file transports the former readout through the existing Cartan
equivalence.  It proves generator-level compatibility only; it does not claim
that the explicit twelve-term list is a quotient presentation of the native
subgroup.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2NativeWeylMellinBridge

open InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylBridge
open InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylInvariant
open InfoGeometry.Lie.CanonicalZornG2CartanWeylSymmetrizedMellin
open InfoGeometry.Lie.CanonicalZornG2CartanConcreteReflectionEquiv
open InfoGeometry.Lie.CanonicalZornG2WeylGroupAction

abbrev Cartan := CanonicalZornG2WeylGroupAction.Cartan

def nativeWeylMellinOrbitSum
    (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) : ℂ :=
  weylMellinOrbitSum
    (c.comp cartanToTraceless.symm.toLinearMap)
    (cartanToTraceless x)

theorem nativeWeylMellinOrbitSum_apply
    (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    nativeWeylMellinOrbitSum c x =
      weylMellinOrbitSum
        (c.comp cartanToTraceless.symm.toLinearMap)
        (cartanToTraceless x) := rfl

theorem cartanToTraceless_shortReflectionEquiv_apply (x : Cartan) :
    cartanToTraceless (canonicalShortReflectionEquiv x) =
      s (cartanToTraceless x) := by
  rw [canonicalShortReflectionEquiv_apply]
  simp [canonicalShortReflection, LinearMap.comp_apply]

theorem cartanToTraceless_longReflectionEquiv_apply (x : Cartan) :
    cartanToTraceless (canonicalLongReflectionEquiv x) =
      l (cartanToTraceless x) := by
  rw [canonicalLongReflectionEquiv_apply]
  simp [canonicalLongReflection, LinearMap.comp_apply]

theorem nativeWeylMellinOrbitSum_shortGenerator_invariant
    (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    nativeWeylMellinOrbitSum c
        (canonicalShortReflectionEquiv x) =
      nativeWeylMellinOrbitSum c x := by
  rw [nativeWeylMellinOrbitSum_apply,
    nativeWeylMellinOrbitSum_apply,
    cartanToTraceless_shortReflectionEquiv_apply,
    weylMellinOrbitSum_apply_s]

theorem nativeWeylMellinOrbitSum_longGenerator_invariant
    (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    nativeWeylMellinOrbitSum c
        (canonicalLongReflectionEquiv x) =
      nativeWeylMellinOrbitSum c x := by
  rw [nativeWeylMellinOrbitSum_apply,
    nativeWeylMellinOrbitSum_apply,
    cartanToTraceless_longReflectionEquiv_apply,
    weylMellinOrbitSum_apply_l]

theorem nativeWeylMellinOrbitSum_cartanAction_shortGenerator_invariant
    (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    nativeWeylMellinOrbitSum c
        (cartanAction ⟨shortGenerator, shortGenerator_mem⟩ x) =
      nativeWeylMellinOrbitSum c x := by
  simpa using nativeWeylMellinOrbitSum_shortGenerator_invariant c x

theorem nativeWeylMellinOrbitSum_cartanAction_longGenerator_invariant
    (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    nativeWeylMellinOrbitSum c
        (cartanAction ⟨longGenerator, longGenerator_mem⟩ x) =
      nativeWeylMellinOrbitSum c x := by
  simpa using nativeWeylMellinOrbitSum_longGenerator_invariant c x

end InfoGeometry.Lie.CanonicalZornG2NativeWeylMellinBridge

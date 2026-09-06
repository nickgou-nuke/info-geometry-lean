import InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylBridge
import InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariant

/-!
# Concrete involutive Cartan reflection equivalences

The native short and long G₂ reflections are already proved involutive as
linear maps on the traceless Cartan carrier.  Transporting them through the
canonical Cartan equivalence gives actual `LinearEquiv`s.  This file adds no
group quotient or finite orbit construction.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2CartanConcreteReflectionEquiv

open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylBridge
open InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariant
open InfoGeometry.Lie.CanonicalZornCartanRootReflections

abbrev Cartan := CanonicalZornG2CartanMellinWeylBridge.Cartan

theorem canonicalShortReflection_involutive (x : Cartan) :
    canonicalShortReflection (canonicalShortReflection x) = x := by
  have h := congrArg (fun f => f (cartanToTraceless x))
    shortReflectionOnCartan_sq
  simpa [canonicalShortReflection, LinearMap.comp_apply] using
    congrArg cartanToTraceless.symm h

theorem canonicalLongReflection_involutive (x : Cartan) :
    canonicalLongReflection (canonicalLongReflection x) = x := by
  have h := congrArg (fun f => f (cartanToTraceless x))
    longReflectionOnCartan_sq
  simpa [canonicalLongReflection, LinearMap.comp_apply] using
    congrArg cartanToTraceless.symm h

/-- The native short G₂ reflection as an honest linear equivalence. -/
def canonicalShortReflectionEquiv : Cartan ≃ₗ[ℝ] Cartan :=
  LinearEquiv.ofInvolutive canonicalShortReflection
    canonicalShortReflection_involutive

/-- The native long G₂ reflection as an honest linear equivalence. -/
def canonicalLongReflectionEquiv : Cartan ≃ₗ[ℝ] Cartan :=
  LinearEquiv.ofInvolutive canonicalLongReflection
    canonicalLongReflection_involutive

abbrev Parameter := Fin 2 → ℝ

def canonicalShortParameterDualLinear : Parameter →ₗ[ℝ] Parameter where
  toFun := canonicalShortReflectionDualReal
  map_add' := by
    intro s t
    ext i
    fin_cases i <;> simp [canonicalShortReflectionDualReal] <;> ring
  map_smul' := by
    intro a s
    ext i
    fin_cases i <;> simp [canonicalShortReflectionDualReal] <;> ring

def canonicalLongParameterDualLinear : Parameter →ₗ[ℝ] Parameter where
  toFun := canonicalLongReflectionDualReal
  map_add' := by
    intro s t
    ext i
    fin_cases i <;> simp [canonicalLongReflectionDualReal] <;> ring
  map_smul' := by
    intro a s
    ext i
    fin_cases i <;> simp [canonicalLongReflectionDualReal] <;> ring

def canonicalShortParameterDualEquiv : Parameter ≃ₗ[ℝ] Parameter :=
  LinearEquiv.ofInvolutive canonicalShortParameterDualLinear
    shortDual_involution

def canonicalLongParameterDualEquiv : Parameter ≃ₗ[ℝ] Parameter :=
  LinearEquiv.ofInvolutive canonicalLongParameterDualLinear
    longDual_involution

@[simp] theorem canonicalShortParameterDualEquiv_apply (s : Parameter) :
    canonicalShortParameterDualEquiv s = canonicalShortReflectionDualReal s := rfl

@[simp] theorem canonicalLongParameterDualEquiv_apply (s : Parameter) :
    canonicalLongParameterDualEquiv s = canonicalLongReflectionDualReal s := rfl

theorem short_pairing_equiv_linear (s J : Parameter) :
    (∑ i : Fin 2, s i * canonicalShortReflectionChargeReal J i) =
      (∑ i : Fin 2, canonicalShortParameterDualEquiv s i * J i) := by
  simpa using short_pairing_equiv s J

theorem long_pairing_equiv_linear (s J : Parameter) :
    (∑ i : Fin 2, s i * canonicalLongReflectionChargeReal J i) =
      (∑ i : Fin 2, canonicalLongParameterDualEquiv s i * J i) := by
  simpa using long_pairing_equiv s J

@[simp] theorem canonicalShortReflectionEquiv_apply (x : Cartan) :
    canonicalShortReflectionEquiv x = canonicalShortReflection x := rfl

@[simp] theorem canonicalLongReflectionEquiv_apply (x : Cartan) :
    canonicalLongReflectionEquiv x = canonicalLongReflection x := rfl

end InfoGeometry.Lie.CanonicalZornG2CartanConcreteReflectionEquiv

import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
import InfoGeometry.Algebra.Zorn.G2ImaginaryPointPermutation
import InfoGeometry.Algebra.Zorn.G2FlagIncidenceAction
import InfoGeometry.Algebra.Zorn.G2CASNativePointAction

/-!
# Explicit transport boundary for the finite incidence certificate

The certificate is indexed by `Fin 63`, while the native carrier is the
isotropic trace-zero point type.  This file gives the exact conjugation map
between the two incidence predicates.  It deliberately leaves preservation
of the exported certificate as a concrete proposition rather than assuming it.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeCertificateTransport

open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2ImaginaryPointAction
open InfoGeometry.Algebra.Zorn.G2ImaginaryPointPermutation
open InfoGeometry.Algebra.Zorn.G2FlagIncidenceAction
open InfoGeometry.Algebra.Zorn.G2HexagonIncidence
open InfoGeometry.Algebra.Zorn.G2ParabolicIncidenceCertificate
open InfoGeometry.Algebra.Zorn.G2CASNativePointEnumeration

noncomputable def nativePointEnum : Fin 63 ≃
    InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.OctImIsotropicPoint :=
  pointEnum.trans pointOctImEquiv

def nativeIncident
    (p l : InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.OctImIsotropicPoint) : Prop :=
  nativePointEnum.symm p ∈ parabolicCertificate.linePoints (nativePointEnum.symm l)

def NativePreservesIncidence
    (π : Equiv.Perm
      InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.OctImIsotropicPoint) : Prop :=
  ∀ p l, nativeIncident p l ↔ nativeIncident (π p) (π l)

noncomputable def certificatePermOfNative
    (π : Equiv.Perm
      InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.OctImIsotropicPoint) :
    Equiv.Perm (Fin 63) :=
  nativePointEnum.trans (π.trans nativePointEnum.symm)

theorem certificatePermOfNative_apply
    (π : Equiv.Perm
      InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.OctImIsotropicPoint)
    (i : Fin 63) :
    certificatePermOfNative π i = nativePointEnum.symm (π (nativePointEnum i)) := by
  rfl

theorem preservesIncidence_iff_native
    (π : Equiv.Perm
      InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.OctImIsotropicPoint) :
    PreservesIncidence (certificatePermOfNative π) ↔
      NativePreservesIncidence π := by
  constructor
  · intro h p l
    let i := nativePointEnum.symm p
    let j := nativePointEnum.symm l
    have h' := h i j
    simpa [nativeIncident, certificatePermOfNative, i, j] using h'
  · intro h i l
    have h' := h (nativePointEnum i) (nativePointEnum l)
    simpa [nativeIncident, certificatePermOfNative] using h'

theorem nativePreserves_one :
    NativePreservesIncidence
      (1 : Equiv.Perm
        InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.OctImIsotropicPoint) := by
  intro p l
  rfl

theorem nativePreserves_mul
    {π₁ π₂ : Equiv.Perm
      InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.OctImIsotropicPoint}
    (h₁ : NativePreservesIncidence π₁)
    (h₂ : NativePreservesIncidence π₂) :
    NativePreservesIncidence (π₁ * π₂) := by
  intro p l
  exact (h₂ p l).trans (h₁ (π₂ p) (π₂ l))

theorem nativePreserves_symm
    {π : Equiv.Perm
      InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.OctImIsotropicPoint}
    (h : NativePreservesIncidence π) :
    NativePreservesIncidence π.symm := by
  intro p l
  have h' := h (π.symm p) (π.symm l)
  simpa using h'.symm

theorem nativePreserves_closure
    (S : Set InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut)
    (hS : ∀ g ∈ S,
      NativePreservesIncidence (octImPointPerm g))
    {g : InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut}
    (hg : g ∈ Subgroup.closure S) :
    NativePreservesIncidence (octImPointPerm g) := by
  refine Subgroup.closure_induction (fun g hg => hS g hg) ?_ ?_ ?_ hg
  · simpa [octImPointPerm_one] using nativePreserves_one
  · intro g h _ _ hg hh
    rw [octImPointPerm_mul]
    exact nativePreserves_mul hg hh
  · intro g _ hg
    have hperm : octImPointPerm g⁻¹ = (octImPointPerm g)⁻¹ := by
      have hmul := octImPointPerm_mul g g⁻¹
      rw [mul_inv_cancel, octImPointPerm_one] at hmul
      exact eq_inv_of_mul_eq_one_right hmul.symm
    rw [hperm]
    exact nativePreserves_symm hg

end InfoGeometry.Algebra.Zorn.G2NativeCertificateTransport

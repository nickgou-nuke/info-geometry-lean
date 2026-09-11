import InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirror
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitReversal

/-!
# `CompHaus` adapter for compatible readout-family mirrors

This is the compact-Hausdorff specialization of the explicit mirror-data
owner.  It transports the already proved generic reversal results; it does
not assert that a canonical mirror, a C*-completion, or a K-theory class has
been constructed.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirrorCompHaus

open InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirror
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitReversal
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitOrbitClosureCompHaus
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitOrbitClosureFlowCompHaus
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitSymbolicLatentFlow

abbrev carrier := CompatibleContinuousReadoutFamily
abbrev flow := RealUHFCompatibleReadoutFamilyMirror.flow

noncomputable def orbitClosureIso
    [CompactSpace carrier] [T2Space carrier]
    (M : Data)
    (hM : ∀ (t : ℝ) (ρ : carrier),
      involution M (flow.act t ρ) = flow.act (-t) (involution M ρ))
    (ρ : carrier) :
    orbitClosureCompHaus ρ ≅ orbitClosureCompHaus (involution M ρ) :=
  (reversalData (involution M) hM).orbitClosureCompHausIso ρ

@[simp] theorem orbitClosureIso_hom_apply
    [CompactSpace carrier] [T2Space carrier]
    (M : Data)
    (hM : ∀ (t : ℝ) (ρ : carrier),
      involution M (flow.act t ρ) = flow.act (-t) (involution M ρ))
    (ρ : carrier) (y : orbitClosureCompHaus ρ) :
    (orbitClosureIso M hM ρ).hom y =
      (reversalData (involution M) hM).orbitClosureMap ρ y :=
  rfl

theorem orbitClosureFlow_naturality
    [CompactSpace carrier] [T2Space carrier]
    (M : Data)
    (hM : ∀ (t : ℝ) (ρ : carrier),
      involution M (flow.act t ρ) = flow.act (-t) (involution M ρ))
    (ρ : carrier) (t : ℝ) (y : orbitClosureCompHaus ρ) :
    ((orbitClosureIso M hM (flow.act t ρ)).hom
        ((orbitClosureFlowCompHausIso ρ t).hom y)).1 =
      ((orbitClosureFlowCompHausIso (involution M ρ) (-t)).hom
        ((orbitClosureIso M hM ρ).hom y)).1 := by
  exact (reversalData (involution M) hM).orbitClosureFlowCompHaus_naturality ρ t y

theorem fixedPoint_orbitClosure_invariant
    [CompactSpace carrier] [T2Space carrier]
    (M : Data)
    (hM : ∀ (t : ℝ) (ρ : carrier),
      involution M (flow.act t ρ) = flow.act (-t) (involution M ρ))
    (ρ : carrier) (hρ : involution M ρ = ρ) :
    involution M '' flow.orbitClosure ρ = flow.orbitClosure ρ := by
  exact (reversalData (involution M) hM).fixedPoint_orbitClosure_invariant ρ hρ

noncomputable def fixedPointOrbitClosure
    [CompactSpace carrier] [T2Space carrier]
    (M : Data)
    (hM : ∀ (t : ℝ) (ρ : carrier),
      involution M (flow.act t ρ) = flow.act (-t) (involution M ρ))
    (ρ : carrier) (hρ : involution M ρ = ρ) : CompHaus :=
  (reversalData (involution M) hM).orbitClosureFixedPointCompHaus ρ hρ

noncomputable def fixedPointOrbitClosureHom
    [CompactSpace carrier] [T2Space carrier]
    (M : Data)
    (hM : ∀ (t : ℝ) (ρ : carrier),
      involution M (flow.act t ρ) = flow.act (-t) (involution M ρ))
    (ρ : carrier) (hρ : involution M ρ = ρ) :
    fixedPointOrbitClosure M hM ρ hρ ⟶ orbitClosureCompHaus ρ :=
  (reversalData (involution M) hM).orbitClosureFixedPointCompHausHom ρ hρ

theorem fixedPointOrbitClosureHom_forget
    [CompactSpace carrier] [T2Space carrier]
    (M : Data)
    (hM : ∀ (t : ℝ) (ρ : carrier),
      involution M (flow.act t ρ) = flow.act (-t) (involution M ρ))
    (ρ : carrier) (hρ : involution M ρ = ρ) :
    compHausToTop.map (fixedPointOrbitClosureHom M hM ρ hρ) =
      (reversalData (involution M) hM).orbitClosureFixedPointInclusion ρ hρ := by
  exact (reversalData (involution M) hM).orbitClosureFixedPointCompHausHom_forget ρ hρ

end InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirrorCompHaus
end

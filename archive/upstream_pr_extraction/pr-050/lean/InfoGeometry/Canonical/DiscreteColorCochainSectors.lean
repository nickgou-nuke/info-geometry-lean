import Mathlib
import InfoGeometry.Canonical.DiscreteOrientedCellComplex

namespace InfoGeometry.Canonical

/-!
Pointwise coefficient sectors for cellular cochains.  These definitions use
only the submodule structure of the coefficient carrier; no multiplication
on the split-octonion coordinates is involved.
-/

def cochainSector
    (K : FiniteOrientedCellComplex)
    (p : ℕ)
    (S : Submodule ℤ StandardIntegralSplitOctonion) :
    Submodule ℤ (ColorCochain K p) where
  carrier := {omega | ∀ sigma, omega sigma ∈ S}
  zero_mem' := by
    intro sigma
    exact S.zero_mem
  add_mem' := by
    intro omega psi hOmega hPsi sigma
    exact S.add_mem (hOmega sigma) (hPsi sigma)
  smul_mem' := by
    intro a omega hOmega sigma
    exact S.smul_mem a (hOmega sigma)

def redCochainSector
    (K : FiniteOrientedCellComplex) (p : ℕ) :
    Submodule ℤ (ColorCochain K p) :=
  cochainSector K p redIntegralSector

def greenCochainSector
    (K : FiniteOrientedCellComplex) (p : ℕ) :
    Submodule ℤ (ColorCochain K p) :=
  cochainSector K p greenIntegralSector

def blueCochainSector
    (K : FiniteOrientedCellComplex) (p : ℕ) :
    Submodule ℤ (ColorCochain K p) :=
  cochainSector K p blueIntegralSector

def sharedAxisCochainSector
    (K : FiniteOrientedCellComplex) (p : ℕ) :
    Submodule ℤ (ColorCochain K p) :=
  cochainSector K p sharedIntegralHyperbolicAxis

theorem colorCoboundary_preserves_sector
    (K : FiniteOrientedCellComplex)
    (p : ℕ)
    (S : Submodule ℤ StandardIntegralSplitOctonion)
    {omega : ColorCochain K p}
    (hOmega : omega ∈ cochainSector K p S) :
    colorCoboundary K p omega ∈ cochainSector K (p + 1) S := by
  classical
  letI := K.fintypeCell p
  intro sigma
  change
    (∑ tau : K.Cell p, K.incidence p sigma tau • omega tau) ∈ S
  exact S.sum_mem (fun tau _ => S.smul_mem _ (hOmega tau))

theorem coboundary_preserves_redSector
    (K : FiniteOrientedCellComplex)
    (p : ℕ)
    {omega : ColorCochain K p}
    (hOmega : omega ∈ redCochainSector K p) :
    colorCoboundary K p omega ∈ redCochainSector K (p + 1) :=
  colorCoboundary_preserves_sector K p redIntegralSector hOmega

theorem coboundary_preserves_greenSector
    (K : FiniteOrientedCellComplex)
    (p : ℕ)
    {omega : ColorCochain K p}
    (hOmega : omega ∈ greenCochainSector K p) :
    colorCoboundary K p omega ∈ greenCochainSector K (p + 1) :=
  colorCoboundary_preserves_sector K p greenIntegralSector hOmega

theorem coboundary_preserves_blueSector
    (K : FiniteOrientedCellComplex)
    (p : ℕ)
    {omega : ColorCochain K p}
    (hOmega : omega ∈ blueCochainSector K p) :
    colorCoboundary K p omega ∈ blueCochainSector K (p + 1) :=
  colorCoboundary_preserves_sector K p blueIntegralSector hOmega

theorem coboundary_preserves_sharedAxis
    (K : FiniteOrientedCellComplex)
    (p : ℕ)
    {omega : ColorCochain K p}
    (hOmega : omega ∈ sharedAxisCochainSector K p) :
    colorCoboundary K p omega ∈ sharedAxisCochainSector K (p + 1) :=
  colorCoboundary_preserves_sector K p sharedIntegralHyperbolicAxis hOmega

end InfoGeometry.Canonical

import InfoGeometry.Canonical.CantorProjectiveLimitTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorBoundaryReadoutTopCat

/-!
# Readout transported to the coherent projective-limit carrier

The projective-limit carrier reconstructs a Cantor stream through `toCantor`.
This owner packages that reconstruction and the binary readout as `TopCat`
maps, and proves the expected compatibility with the Cantor-side readout.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorProjectiveLimitReadoutTopCat

open CategoryTheory
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimitTopCat
open InfoGeometry.Canonical.CantorBoundaryReadoutTopCat

def toCantorTopCatHom :
    TopCat.of PrefixProjectiveLimit ⟶ TopCat.of CantorBoundary :=
  TopCat.ofHom
    { toFun := toCantor
      continuous_toFun := continuous_toCantor }

def projectiveLimitReadoutTopCatHom :
    TopCat.of PrefixProjectiveLimit ⟶ TopCat.of ℝ :=
  toCantorTopCatHom ≫ readoutTopCatHom

@[simp] theorem toCantorTopCatHom_apply (p : PrefixProjectiveLimit) :
    toCantorTopCatHom p = toCantor p := rfl

@[simp] theorem projectiveLimitReadoutTopCatHom_apply
    (p : PrefixProjectiveLimit) :
    projectiveLimitReadoutTopCatHom p = realBinaryReadout (toCantor p) := by
  rfl

theorem projectiveLimitReadout_cantor_compatibility :
    cantorProjectiveLimitTopCatIso.hom ≫ projectiveLimitReadoutTopCatHom =
      readoutTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rw [TopCat.comp_app]
  change realBinaryReadout (toCantor (ofCantor x)) = realBinaryReadout x
  rw [toCantor_ofCantor]

end InfoGeometry.Canonical.CantorProjectiveLimitReadoutTopCat

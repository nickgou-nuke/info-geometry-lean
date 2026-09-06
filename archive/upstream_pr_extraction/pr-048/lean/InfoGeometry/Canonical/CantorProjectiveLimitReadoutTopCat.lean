import InfoGeometry.Canonical.CantorProjectiveLimitTopCat
import InfoGeometry.Canonical.CantorBoundaryReadoutTopCat
import InfoGeometry.Canonical.CantorBoundaryReadoutIntervalApproximation

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
open InfoGeometry.Canonical.CantorBoundaryReadoutIntervalApproximation

def toCantorTopCatHom :
    TopCat.of PrefixProjectiveLimit ⟶ TopCat.of (ℕ → Bool) :=
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

theorem projectiveLimitReadout_range_eq_unitInterval :
    Set.range (fun p : PrefixProjectiveLimit =>
      realBinaryReadout (toCantor p)) = Set.Icc (0 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact realBinaryReadout_mem_unitInterval (toCantor p)
  · intro hy
    rw [← realBinaryReadout_range_eq_unitInterval] at hy
    obtain ⟨x, hx⟩ := hy
    refine ⟨ofCantor x, ?_⟩
    simpa [toCantor_ofCantor] using hx

end InfoGeometry.Canonical.CantorProjectiveLimitReadoutTopCat

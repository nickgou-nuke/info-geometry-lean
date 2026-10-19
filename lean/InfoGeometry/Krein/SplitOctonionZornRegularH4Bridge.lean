/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.MajoranaBdGSheetBridge
import InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner

/-!
# Zorn split-octonion regular operators on the doubled real Krein carrier

The canonical Zorn split-octonion carrier is linearly equivalent to the
eight-dimensional Nambu carrier through its exterior-Fock model. Composing
that equivalence with the existing Nambu-to-doubled-Krein equivalence transports
the already-proved right-regular root operators to endomorphisms of
`DoubledSpace (EuclideanSpace ℝ (Fin 4))`.

This is an operator transport on a real-linear carrier equivalence. It does not
assert that split-octonion multiplication is associative, that the equivalence
preserves multiplication, or that these three-mode Fock operators coincide
with the separately defined one-mode sheet connectors.
-/

noncomputable section

namespace InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge

open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner
open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
open InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionCircularZ3Grading
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionEllCircularCAR
open InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford
open InfoGeometry.Krein.MajoranaBdGSheetBridge

abbrev CZ := InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.CZ
abbrev H4 := InfoGeometry.Krein.MajoranaBdGSheetBridge.H4
abbrev EndH4 := Module.End ℝ H4

/-- Identify the Zorn carrier with the doubled real Nambu/Krein carrier. -/
noncomputable def zornToDoubleKrein : CZ ≃ₗ[ℝ] H4 :=
  fockBdGEquiv.symm.trans (exterior3PeirceBasis.equivFun.trans nambuDoubledEquiv)

/-- Conjugate an operator on the Zorn carrier to the doubled Krein carrier. -/
def transportZornOperator (T : Module.End ℝ CZ) : EndH4 :=
  zornToDoubleKrein.toLinearMap ∘ₗ T ∘ₗ zornToDoubleKrein.symm.toLinearMap

@[simp] theorem transportZornOperator_one :
    transportZornOperator (1 : Module.End ℝ CZ) = (1 : EndH4) := by
  apply LinearMap.ext
  intro z
  simp [transportZornOperator, LinearMap.comp_apply]

theorem transportZornOperator_mul (S T : Module.End ℝ CZ) :
    transportZornOperator (S * T) =
      transportZornOperator S * transportZornOperator T := by
  apply LinearMap.ext
  intro z
  simp [transportZornOperator, LinearMap.comp_apply, Module.End.mul_apply]

theorem transportZornOperator_add (S T : Module.End ℝ CZ) :
    transportZornOperator (S + T) =
      transportZornOperator S + transportZornOperator T := by
  apply LinearMap.ext
  intro z
  change zornToDoubleKrein
      (S (zornToDoubleKrein.symm z) + T (zornToDoubleKrein.symm z)) = _
  rw [map_add]
  rfl

@[simp] theorem transportZornOperator_apply (T : Module.End ℝ CZ) (z : H4) :
    transportZornOperator T z = zornToDoubleKrein (T (zornToDoubleKrein.symm z)) := rfl

/-- The right-regular action of a Zorn element, transported to the doubled
real Krein carrier. -/
def rightRegularOnDoubleKrein (x : CZ) : EndH4 :=
  transportZornOperator (rightRegular x)

@[simp] theorem rightRegularOnDoubleKrein_apply (x : CZ) (z : H4) :
    rightRegularOnDoubleKrein x z = zornToDoubleKrein
      (rightRegular x (zornToDoubleKrein.symm z)) := rfl

/-- The root creation/annihilation pair on the doubled real Krein carrier
retains the CAR anticommutator relation. -/
theorem rightRegularOnDoubleKrein_root_CAR (i : Fin 3) :
    rightRegularOnDoubleKrein (rootMinus i) * rightRegularOnDoubleKrein (rootPlus i) +
      rightRegularOnDoubleKrein (rootPlus i) * rightRegularOnDoubleKrein (rootMinus i) =
        (1 : EndH4) := by
  change transportZornOperator (rightRegular (rootMinus i)) *
      transportZornOperator (rightRegular (rootPlus i)) +
    transportZornOperator (rightRegular (rootPlus i)) *
      transportZornOperator (rightRegular (rootMinus i)) = _
  rw [← transportZornOperator_mul, ← transportZornOperator_mul,
    ← transportZornOperator_add]
  rw [← transportZornOperator_one]
  exact congrArg transportZornOperator (rightRegular_root_CAR i)

/-- The exterior-Fock realization intertwines with the resulting operators on
the doubled real Krein carrier through the composed carrier equivalence. -/
theorem rightRegularOnDoubleKrein_intertwines_fock
    (i : Fin 3)
    (ψ : InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3) :
    rightRegularOnDoubleKrein (rootPlus i) (zornToDoubleKrein (fockBdGEquiv ψ)) =
      zornToDoubleKrein (fockBdGEquiv (exteriorWedge3 (modeVector i) ψ)) := by
  rw [rightRegularOnDoubleKrein_apply, zornToDoubleKrein.symm_apply_apply,
    fockBdGEquiv_apply]
  change zornToDoubleKrein
      (rightRegular (rootPlus i) (fockToZorn ψ)) =
    zornToDoubleKrein (fockToZorn (exteriorWedge3 (modeVector i) ψ))
  exact congrArg zornToDoubleKrein (fockToZorn_creation_mode i ψ).symm

/-- The exterior-Fock annihilator also intertwines with the transported
right-regular negative root on the doubled real Krein carrier. -/
theorem rightRegularOnDoubleKrein_intertwines_fock_annihilation
    (i : Fin 3)
    (ψ : InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3) :
    rightRegularOnDoubleKrein (rootMinus i) (zornToDoubleKrein (fockBdGEquiv ψ)) =
      zornToDoubleKrein
        (fockBdGEquiv (exteriorContract3 (modeCovector i) ψ)) := by
  rw [rightRegularOnDoubleKrein_apply, zornToDoubleKrein.symm_apply_apply,
    fockBdGEquiv_apply]
  change zornToDoubleKrein
      (rightRegular (rootMinus i) (fockToZorn ψ)) =
    zornToDoubleKrein
      (fockToZorn (exteriorContract3 (modeCovector i) ψ))
  exact congrArg zornToDoubleKrein (fockToZorn_annihilation i ψ).symm

end InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge

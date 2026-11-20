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

@[simp] theorem transportZornOperator_zero :
    transportZornOperator (0 : Module.End ℝ CZ) = 0 := by
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

/-- Right multiplication on the split-octonion carrier represents its Jordan
anticommutator as the operator anticommutator. The statement retains the
nonassociative Zorn product inside the represented right multiplication. -/
theorem rightRegularOnDoubleKrein_anticommutator (x y : CZ) :
    rightRegularOnDoubleKrein x * rightRegularOnDoubleKrein y +
      rightRegularOnDoubleKrein y * rightRegularOnDoubleKrein x =
        rightRegularOnDoubleKrein (x * y + y * x) := by
  change transportZornOperator (rightRegular x) *
      transportZornOperator (rightRegular y) +
    transportZornOperator (rightRegular y) *
      transportZornOperator (rightRegular x) =
    transportZornOperator (rightRegular (x * y + y * x))
  rw [← transportZornOperator_mul, ← transportZornOperator_mul,
    ← transportZornOperator_add, rightRegular_anticommutator]

/-- The failure of the right-regular representation to preserve ordered
products is exactly the Zorn associator, transported to the doubled real
Krein carrier. This records the nonassociative defect explicitly instead
of treating `rightRegular` as an algebra homomorphism. -/
theorem rightRegularOnDoubleKrein_associator_defect (x y : CZ) (z : H4) :
    (rightRegularOnDoubleKrein x * rightRegularOnDoubleKrein y -
        rightRegularOnDoubleKrein (y * x)) z =
      zornToDoubleKrein
        ((zornToDoubleKrein.symm z * y) * x - zornToDoubleKrein.symm z * (y * x)) := by
  simp only [LinearMap.sub_apply, Module.End.mul_apply,
    rightRegularOnDoubleKrein_apply, rightRegular_apply]
  rw [zornToDoubleKrein.symm_apply_apply]
  rw [map_sub]

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

/-- The transported negative circular root remains nilpotent on the doubled
Krein carrier. -/
theorem rightRegularOnDoubleKrein_rootMinus_sq (i : Fin 3) :
    rightRegularOnDoubleKrein (rootMinus i) *
      rightRegularOnDoubleKrein (rootMinus i) = 0 := by
  change transportZornOperator (rightRegular (rootMinus i)) *
      transportZornOperator (rightRegular (rootMinus i)) = 0
  rw [← transportZornOperator_mul, rightRegular_rootMinus_sq]
  simp [transportZornOperator]

/-- The transported positive circular root remains nilpotent on the doubled
Krein carrier. -/
theorem rightRegularOnDoubleKrein_rootPlus_sq (i : Fin 3) :
    rightRegularOnDoubleKrein (rootPlus i) *
      rightRegularOnDoubleKrein (rootPlus i) = 0 := by
  change transportZornOperator (rightRegular (rootPlus i)) *
      transportZornOperator (rightRegular (rootPlus i)) = 0
  rw [← transportZornOperator_mul, rightRegular_rootPlus_sq]
  simp [transportZornOperator]

/-- Distinct circular creation roots anticommute after transport to the
doubled real Krein carrier. -/
theorem rightRegularOnDoubleKrein_creation_anticommutator (i j : Fin 3) :
    rightRegularOnDoubleKrein (rootPlus i) * rightRegularOnDoubleKrein (rootPlus j) +
      rightRegularOnDoubleKrein (rootPlus j) * rightRegularOnDoubleKrein (rootPlus i) = 0 := by
  change transportZornOperator (rightRegular (rootPlus i)) *
      transportZornOperator (rightRegular (rootPlus j)) +
    transportZornOperator (rightRegular (rootPlus j)) *
      transportZornOperator (rightRegular (rootPlus i)) = 0
  rw [← transportZornOperator_mul, ← transportZornOperator_mul,
    ← transportZornOperator_add, rightRegular_rootPlus_anticommutator]
  simp [transportZornOperator]

/-- Distinct circular annihilation roots anticommute after transport to the
doubled real Krein carrier. -/
theorem rightRegularOnDoubleKrein_annihilation_anticommutator (i j : Fin 3) :
    rightRegularOnDoubleKrein (rootMinus i) * rightRegularOnDoubleKrein (rootMinus j) +
      rightRegularOnDoubleKrein (rootMinus j) * rightRegularOnDoubleKrein (rootMinus i) = 0 := by
  change transportZornOperator (rightRegular (rootMinus i)) *
      transportZornOperator (rightRegular (rootMinus j)) +
    transportZornOperator (rightRegular (rootMinus j)) *
      transportZornOperator (rightRegular (rootMinus i)) = 0
  rw [← transportZornOperator_mul, ← transportZornOperator_mul,
    ← transportZornOperator_add, rightRegular_rootMinus_anticommutator]
  simp [transportZornOperator]

/-- The full three-channel creation/annihilation relation on the doubled
real Krein carrier. -/
theorem rightRegularOnDoubleKrein_mixed_anticommutator (i j : Fin 3) :
    rightRegularOnDoubleKrein (rootMinus j) * rightRegularOnDoubleKrein (rootPlus i) +
      rightRegularOnDoubleKrein (rootPlus i) * rightRegularOnDoubleKrein (rootMinus j) =
        if i = j then (1 : EndH4) else 0 := by
  change transportZornOperator (rightRegular (rootMinus j)) *
      transportZornOperator (rightRegular (rootPlus i)) +
    transportZornOperator (rightRegular (rootPlus i)) *
      transportZornOperator (rightRegular (rootMinus j)) = _
  rw [← transportZornOperator_mul, ← transportZornOperator_mul,
    ← transportZornOperator_add]
  have h := congrArg transportZornOperator (rightRegular_root_anticommutator i j)
  by_cases hij : i = j
  · simp [hij] at h ⊢
    exact h
  · simp [hij] at h ⊢
    exact h

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

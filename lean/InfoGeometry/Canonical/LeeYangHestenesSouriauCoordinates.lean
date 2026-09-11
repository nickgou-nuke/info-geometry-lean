import Mathlib.Algebra.Polynomial.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Canonical.CompletedXiHestenesHomogeneousCoordinates
import InfoGeometry.Canonical.PrimeLeeYangConcreteN2

/-!
# Lee--Yang potentials in Hestenes--Souriau coordinates

This owner keeps three layers distinct:

* the Hestenes homogeneous coordinate `τ = p/q`;
* a finite Lee--Yang partition polynomial in fugacity;
* the logarithmic Massieu/grand potential readout.

The Lee--Yang zero set is proved algebraically.  No thermodynamic-limit or
phase-transition theorem is asserted: such a theorem needs a convergence and
zero-accumulation hypothesis.
-/

noncomputable section

namespace InfoGeometry.Canonical.LeeYangHestenesSouriauCoordinates

open Polynomial
open InfoGeometry.Canonical.CompletedXiHestenesHomogeneousCoordinates
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

abbrev HomogeneousPair :=
  InfoGeometry.Canonical.CompletedXiHestenesHomogeneousCoordinates.HomogeneousPair

/-! ## Adapted Souriau/Hestenes coordinates -/

/-- The Souriau temperature difference used by a grand-canonical readout. -/
def souriauTemperature (β μ : ℂ) : ℂ := β - μ

/-- Fugacity in the Hestenes homogeneous chart. -/
def hestenesFugacity (s : ℂ) : ℂ :=
  tauCoord (homogeneousPsi s)

@[simp]
theorem hestenesFugacity_eq_cayley (s : ℂ) :
    hestenesFugacity s =
      InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.cayleyToFugacity s := by
  rfl

theorem hestenesFugacity_functionalReflection (s : ℂ) :
    hestenesFugacity (1 - s) = (hestenesFugacity s)⁻¹ := by
  exact tauCoord_functionalReflection s

theorem hestenesFugacity_cartanFlow
    (t : ℝ) (P : HomogeneousPair) (hq : P.2 ≠ 0) :
    tauCoord (actCartan t P) =
      (Real.exp (2 * t) : ℂ) * tauCoord P := by
  rcases P with ⟨p, q⟩
  exact tauCoord_actCartan t p q hq

theorem criticalLine_iff_hestenesFugacity_unitCircle (s : ℂ) :
    InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.OnCriticalLine s ↔
      InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.OnLeeYangCircle
        (hestenesFugacity s) := by
  change
    InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.OnCriticalLine s ↔
      InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.OnLeeYangCircle
        (InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.cayleyToFugacity s)
  exact
    InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.criticalLine_iff_cayley_unitCircle s

/-! ## Finite partition polynomial and potentials -/

/-- A finite fugacity partition polynomial. -/
structure LeeYangPartition where
  polynomial : Polynomial ℂ

/-- The finite partition function evaluated at fugacity `z`. -/
def partitionValue (P : LeeYangPartition) (z : ℂ) : ℂ :=
  P.polynomial.eval z

/-- The Lee--Yang zero locus of a finite partition polynomial. -/
def leeYangZero (P : LeeYangPartition) (z : ℂ) : Prop :=
  partitionValue P z = 0

/-- The Massieu potential, defined only as a logarithmic readout. -/
def massieuPotential (P : LeeYangPartition) (z : ℂ) : ℂ :=
  Complex.log (partitionValue P z)

/-- The grand potential in a real positive-temperature chart. -/
def grandPotential (P : LeeYangPartition) (β : ℝ) (z : ℂ) : ℂ :=
  -((β : ℂ)⁻¹) * massieuPotential P z

@[simp]
theorem partitionValue_eq_eval (P : LeeYangPartition) (z : ℂ) :
    partitionValue P z = P.polynomial.eval z := rfl

theorem leeYangZero_iff (P : LeeYangPartition) (z : ℂ) :
    leeYangZero P z ↔ P.polynomial.eval z = 0 := Iff.rfl

theorem massieuPotential_eq_log_partition (P : LeeYangPartition) (z : ℂ) :
    massieuPotential P z = Complex.log (partitionValue P z) := rfl

/-! ## Weyl-symmetric partition data -/

/-- A finite partition polynomial with the Hestenes Weyl inversion symmetry. -/
structure WeylInvariantLeeYangPartition extends LeeYangPartition where
  inversion : ∀ z : ℂ, partitionValue toLeeYangPartition z⁻¹ =
    partitionValue toLeeYangPartition z

namespace WeylInvariantLeeYangPartition

theorem zero_inversion
    (P : WeylInvariantLeeYangPartition) (z : ℂ)
    (hz : leeYangZero P.toLeeYangPartition z) :
    leeYangZero P.toLeeYangPartition z⁻¹ := by
  unfold leeYangZero at hz ⊢
  rw [P.inversion z]
  exact hz

theorem massieu_inversion (P : WeylInvariantLeeYangPartition) (z : ℂ) :
    massieuPotential P.toLeeYangPartition z⁻¹ =
      massieuPotential P.toLeeYangPartition z := by
  unfold massieuPotential
  rw [P.inversion z]

theorem grandPotential_inversion
    (P : WeylInvariantLeeYangPartition) (β : ℝ) (z : ℂ) :
    grandPotential P.toLeeYangPartition β z⁻¹ =
      grandPotential P.toLeeYangPartition β z := by
  unfold grandPotential
  rw [massieu_inversion P z]

end WeylInvariantLeeYangPartition

/-! ## Pullback to the completed Hestenes coordinate -/

def leeYangZeroAtTemperature (P : LeeYangPartition) (s : ℂ) : Prop :=
  leeYangZero P (hestenesFugacity s)

def massieuAtTemperature (P : LeeYangPartition) (s : ℂ) : ℂ :=
  massieuPotential P (hestenesFugacity s)

theorem zero_at_functional_reflection
    (P : WeylInvariantLeeYangPartition) (s : ℂ)
    (hs : leeYangZeroAtTemperature P.toLeeYangPartition s) :
    leeYangZeroAtTemperature P.toLeeYangPartition (1 - s) := by
  unfold leeYangZeroAtTemperature at *
  rw [hestenesFugacity_functionalReflection]
  exact P.zero_inversion _ hs

theorem massieu_at_functional_reflection
    (P : WeylInvariantLeeYangPartition) (s : ℂ) :
    massieuAtTemperature P.toLeeYangPartition (1 - s) =
      massieuAtTemperature P.toLeeYangPartition s := by
  unfold massieuAtTemperature
  rw [hestenesFugacity_functionalReflection]
  exact P.massieu_inversion _

/-! ## A closed concrete two-site Lee--Yang case -/

open InfoGeometry.Canonical.PrimeLeeYangConcreteN2

/-- The repository's explicit two-site Lee--Yang polynomial as a partition
polynomial in the present finite fugacity carrier. -/
noncomputable def n2Partition : LeeYangPartition :=
  ⟨partitionPolyN2⟩

@[simp]
theorem n2Partition_value (z : ℂ) :
    partitionValue n2Partition z = partitionPolyN2.eval z :=
  rfl

/-- Every zero of the concrete two-site partition is on the Lee--Yang circle.
This is the finite polynomial theorem, not a thermodynamic-limit statement. -/
theorem n2_zero_on_leeYang_circle
    {z : ℂ}
    (hz : leeYangZero n2Partition z) :
    OnLeeYangCircle z := by
  apply leeYangStabilityN2
  exact hz

/-- The Cayley inverse of every concrete two-site zero lies on the critical
line, with the pole exclusion discharged by the explicit polynomial proof. -/
theorem n2_zero_on_critical_line
    {z : ℂ}
    (hz : leeYangZero n2Partition z) :
    OnCriticalLine (cayleyToTemperature z) := by
  apply partitionPolyN2_root_mapsToCriticalLine
  exact hz

/-- The Hestenes fugacity chart recovers the original fugacity at every
concrete two-site zero after the Cayley temperature inverse. -/
theorem n2_zero_hestenes_roundtrip
    {z : ℂ}
    (hz : leeYangZero n2Partition z) :
    hestenesFugacity (cayleyToTemperature z) = z := by
  rw [hestenesFugacity_eq_cayley]
  apply cayleyToFugacity_cayleyToTemperature
  intro hpole
  apply partitionPolyN2_root_re_ne_neg_one hz
  have hre : 1 + z.re = 0 := by
    simpa using congrArg Complex.re hpole
  linarith

/-- Transport of the concrete N=2 Lee--Yang zero into the Hestenes--Souriau
temperature chart. -/
theorem n2_zero_at_hestenes_temperature
    {z : ℂ}
    (hz : leeYangZero n2Partition z) :
    leeYangZeroAtTemperature n2Partition (cayleyToTemperature z) := by
  unfold leeYangZeroAtTemperature
  rw [n2_zero_hestenes_roundtrip hz]
  exact hz

/-- The complete finite `N = 2` Lee--Yang certificate in the present chart.
    Every root has unit fugacity norm, the exact quadratic coordinates, a
    critical-line Cayley image, and an exact Hestenes round trip. -/
theorem n2_leeYang_complete
    {z : ℂ}
    (hz : leeYangZero n2Partition z) :
    OnLeeYangCircle z ∧
      z.re = (1 / 2 : ℝ) ∧
      z.im * z.im = (3 / 4 : ℝ) ∧
      OnCriticalLine (cayleyToTemperature z) ∧
      hestenesFugacity (cayleyToTemperature z) = z := by
  refine ⟨n2_zero_on_leeYang_circle hz, ?_⟩
  rcases partitionPolyN2_root_coordinates hz with ⟨hre, him⟩
  exact ⟨hre, him, n2_zero_on_critical_line hz,
    n2_zero_hestenes_roundtrip hz⟩

end InfoGeometry.Canonical.LeeYangHestenesSouriauCoordinates

end noncomputable section

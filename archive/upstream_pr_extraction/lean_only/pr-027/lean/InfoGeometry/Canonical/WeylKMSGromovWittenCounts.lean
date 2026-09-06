/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.WeylKMSGromovWittenCounts

Weyl/KMS weighted zero-mode orbit counts.

This is the theorem-safe bridge:

* Drazin--Hodge zero-mode orbit sectors;
* Weyl gauge weights;
* KMS/Jaynes reproducing weights;
* calibrated effective volume;
* projective count coordinates;
* witness-gated (Native Closure Mandated: Closure Debt) Fierz--Klein readout.

The Gromov--Witten interpretation is explicitly calibration data.  The raw
finite object is a real weighted zero-mode orbit count.
-/

noncomputable section

namespace InfoGeometry.Canonical.WeylKMSGromovWittenCounts

open scoped BigOperators

/-- Supergraded finite orbit-sector space. -/
abbrev SuperOrbitSpace (Γ : Type*) := Γ → Bool

namespace SuperOrbitSpace

/-- Projection-compatible name for the direct parity function. -/
abbrev parity {Γ : Type*} (S : SuperOrbitSpace Γ) : Γ → Bool := S

end SuperOrbitSpace

/-- Real Witten sign of an orbit sector. -/
def paritySign {Γ : Type*} (S : SuperOrbitSpace Γ) (γ : Γ) : ℝ :=
  if S γ then -1 else 1

/-- A Weyl gauge assigns a positive local dilation weight to each orbit sector. -/
structure WeylGaugeWeight (Γ : Type*) where
  weight : Γ → ℝ
  positive : ∀ γ, 0 < weight γ

/--
A KMS/Jaynes reproducing state on orbit projectors.

`expect γ` is the real expectation value of the projector/indicator for the
orbit sector `γ`.
-/
structure KMSOrbitState (Γ : Type*) where
  expect : Γ → ℝ
  nonnegative : ∀ γ, 0 ≤ expect γ

/--
Weyl/KMS weighted signed zero-mode count.

This is the discrete GW-type volume before projectivization.
-/
def weightedZeroModeCount
    {Γ : Type*}
    [Fintype Γ]
    (S : SuperOrbitSpace Γ)
    (Ω : WeylGaugeWeight Γ)
    (φ : KMSOrbitState Γ) : ℝ :=
  Finset.univ.sum
    (fun γ : Γ => paritySign S γ * Ω.weight γ * φ.expect γ)

/-- Partition function / total KMS-Weyl mass of the zero-mode orbit space. -/
def orbitPartitionFunction
    {Γ : Type*}
    [Fintype Γ]
    (Ω : WeylGaugeWeight Γ)
    (φ : KMSOrbitState Γ) : ℝ :=
  Finset.univ.sum (fun γ : Γ => Ω.weight γ * φ.expect γ)

/--
Projective normalized orbit coordinate.

This is the local projective geometry of counts.  Nonzero denominator and
normalization properties are deliberately left to downstream calibration.
-/
def projectiveOrbitCoordinate
    {Γ : Type*}
    [Fintype Γ]
    (Ω : WeylGaugeWeight Γ)
    (φ : KMSOrbitState Γ)
    (γ : Γ) : ℝ :=
  Ω.weight γ * φ.expect γ / orbitPartitionFunction Ω φ

/--
Witness that zero-mode orbit sectors are identified with curve/stable-map
sectors of a GW-type theory.

This prevents the overclaim that every zero-mode count is automatically a
Gromov--Witten invariant.
-/
structure GromovWittenCalibration
    {Γ : Type*}
    [Fintype Γ]
    (Ω : WeylGaugeWeight Γ)
    (φ : KMSOrbitState Γ) where
  curveClass : Γ → Type*
  gwWeight : Γ → ℝ
  gwWeight_eq_weylKMS :
    ∀ γ : Γ, gwWeight γ = Ω.weight γ * φ.expect γ

namespace GromovWittenCalibration

/--
The total calibrated Gromov--Witten weight is the Weyl/KMS orbit partition
function.
-/
theorem sum_gwWeight_eq_orbitPartitionFunction
    {Γ : Type*}
    [Fintype Γ]
    {Ω : WeylGaugeWeight Γ}
    {φ : KMSOrbitState Γ}
    (C : GromovWittenCalibration Ω φ) :
    Finset.univ.sum C.gwWeight =
      orbitPartitionFunction Ω φ := by
  unfold orbitPartitionFunction
  apply Finset.sum_congr rfl
  intro γ _
  exact C.gwWeight_eq_weylKMS γ

end GromovWittenCalibration

/--
A calibrated effective volume law.

The effective volume equals a scale times the Weyl/KMS zero-mode count only
under this explicit calibration.
-/
structure WeylKMSVolumeCalibration
    {Γ : Type*}
    [Fintype Γ]
    (S : SuperOrbitSpace Γ)
    (Ω : WeylGaugeWeight Γ)
    (φ : KMSOrbitState Γ) where

  volume : ℝ
  scale : ℝ

  volume_eq_weighted_count :
    volume = scale * weightedZeroModeCount S Ω φ

/-- Read back the calibrated effective volume law. -/
theorem effective_volume_from_weyl_kms_counts
    {Γ : Type*}
    [Fintype Γ]
    (S : SuperOrbitSpace Γ)
    (Ω : WeylGaugeWeight Γ)
    (φ : KMSOrbitState Γ)
    (C : WeylKMSVolumeCalibration S Ω φ) :
    C.volume = C.scale * weightedZeroModeCount S Ω φ :=
  C.volume_eq_weighted_count

/--
Real Fierz channels for projective count readout.

The `rotor` channel is the real Hestenes/Krein replacement for scalar complex
phase language.
-/
inductive FierzChannel where
  | scalar
  | rotor
  | vector
  | axial
  | area
  deriving DecidableEq, Fintype

/-- Fierz coordinates are projective functions of Weyl/KMS orbit counts. -/
abbrev FierzFromProjectiveCounts (Γ : Type*) [Fintype Γ] :=
  FierzChannel → (Γ → ℝ) → ℝ

/-- Residual measuring failure of the intended Fierz--Klein relation. -/
abbrev FierzKleinResidual := (FierzChannel → ℝ) → ℝ

namespace FierzKleinResidual

/-- Projection-compatible name for the direct residual function. -/
abbrev residual (R : FierzKleinResidual) : (FierzChannel → ℝ) → ℝ := R

end FierzKleinResidual

/--
Projective Weyl/KMS count readout data for Fierz--Klein coordinates.

This structure intentionally contains only data.  The removed quadric placeholder
claimed the Fierz--Klein relation by storing the target proposition as a field,
and the downstream theorem merely read that field back.  A concrete model must
now prove any equation such as `residual.residual coords = 0` directly from its
definitions and lower lemmas.
-/
structure ProjectiveCountFierzKleinData
    (Γ : Type*)
    [Fintype Γ] where

  S : SuperOrbitSpace Γ
  Ω : WeylGaugeWeight Γ
  φ : KMSOrbitState Γ

  readout : FierzFromProjectiveCounts Γ
  residual : FierzKleinResidual

namespace ProjectiveCountFierzKleinData

/-- Projective Fierz coordinates derived from the supplied readout and orbit data. -/
def coords {Γ : Type*} [Fintype Γ]
    (D : ProjectiveCountFierzKleinData Γ) : FierzChannel → ℝ :=
  fun ch =>
    D.readout ch
      (fun γ => projectiveOrbitCoordinate D.Ω D.φ γ)

end ProjectiveCountFierzKleinData

end InfoGeometry.Canonical.WeylKMSGromovWittenCounts

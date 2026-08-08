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
* property-gated (Native Closure Mandated: Closure Debt) Fierz--Klein readout.

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
abbrev WeylGaugeWeight (Γ : Type*) :=
  {weight : Γ → ℝ // ∀ γ, 0 < weight γ}

namespace WeylGaugeWeight

abbrev weight {Γ : Type*} (Ω : WeylGaugeWeight Γ) : Γ → ℝ := Ω.1

abbrev positive {Γ : Type*} (Ω : WeylGaugeWeight Γ) : ∀ γ, 0 < Ω.weight γ := Ω.2

end WeylGaugeWeight

/--
A KMS/Jaynes reproducing state on orbit projectors.

`expect γ` is the real expectation value of the projector/indicator for the
orbit sector `γ`.
-/
abbrev KMSOrbitState (Γ : Type*) :=
  {expect : Γ → ℝ // ∀ γ, 0 ≤ expect γ}

namespace KMSOrbitState

abbrev expect {Γ : Type*} (φ : KMSOrbitState Γ) : Γ → ℝ := φ.1

abbrev nonnegative {Γ : Type*} (φ : KMSOrbitState Γ) : ∀ γ, 0 ≤ φ.expect γ := φ.2

end KMSOrbitState

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

/-- A finite weight function has the Weyl/KMS orbit sum when its pointwise
    values are identified with the corresponding Weyl/KMS weights. -/
theorem sum_gwWeight_eq_orbitPartitionFunction
    {Γ : Type*}
    [Fintype Γ]
    {Ω : WeylGaugeWeight Γ}
    {φ : KMSOrbitState Γ}
    (gwWeight : Γ → ℝ)
    (h_gwWeight_eq_weylKMS :
      ∀ γ : Γ, gwWeight γ = Ω.weight γ * φ.expect γ) :
    Finset.univ.sum gwWeight =
      orbitPartitionFunction Ω φ := by
  unfold orbitPartitionFunction
  apply Finset.sum_congr rfl
  intro γ _
  exact h_gwWeight_eq_weylKMS γ

/- A calibrated effective volume law is stated directly as an equality. -/
theorem volume_eq_weighted_count
    {Γ : Type*} [Fintype Γ]
    {S : SuperOrbitSpace Γ} {Ω : WeylGaugeWeight Γ} {φ : KMSOrbitState Γ}
    (volume scale : ℝ)
    (h : volume = scale * weightedZeroModeCount S Ω φ) :
    volume = scale * weightedZeroModeCount S Ω φ :=
  h

/-- Read back the calibrated effective volume law. -/
theorem effective_volume_from_weyl_kms_counts
    {Γ : Type*}
    [Fintype Γ]
    (S : SuperOrbitSpace Γ)
    (Ω : WeylGaugeWeight Γ)
    (φ : KMSOrbitState Γ)
    (volume scale : ℝ)
    (h : volume = scale * weightedZeroModeCount S Ω φ) :
    volume = scale * weightedZeroModeCount S Ω φ :=
  volume_eq_weighted_count volume scale h

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

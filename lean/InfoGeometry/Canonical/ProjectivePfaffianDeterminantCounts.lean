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

import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.SocketTarget

/-!
# InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts

Projective Pfaffian/determinant count socket.

The theorem-safe doctrine is:

* determinant = even/bosonic source--sink path-volume readout;
* Pfaffian = oriented fermionic pairing amplitude;
* `Pf^2 = det` is supplied as a skew-kernel witness;
* Drazin data separates regular determinant support from harmonic zero modes;
* Weyl/KMS projectivization and Fierz--Klein geometry are calibration/readout
  layers, not automatic identities.
-/

noncomputable section

namespace InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts

open scoped BigOperators

/-! ## Source--sink determinant path counts -/

/-- Source--sink weighted path kernel. -/
@[rep_depth operator]
structure SourceSinkKernel (Source Sink : Type*) where
  K : Source → Sink → ℝ

/-- Square matrix associated to a source--sink kernel with the same index type. -/
@[rep_depth operator]
def SourceSinkKernel.matrix
    {I : Type*}
    (K : SourceSinkKernel I I) : Matrix I I ℝ :=
  fun i j => K.K i j

/--
Determinant path count.

The field `detCount_eq_det` is the calibration/readback that the scalar count is
the determinant of the source--sink transfer matrix.
-/
@[rep_depth operator]
structure DeterminantPathCount
    (I : Type*)
    [Fintype I] [DecidableEq I] where

  kernel : SourceSinkKernel I I
  detCount : ℝ

  detCount_eq_det :
    detCount = (SourceSinkKernel.matrix kernel).det

/-- Read back the determinant path-count law. -/
@[rep_depth operator]
theorem determinantPathCount_eq_det
    {I : Type*}
    [Fintype I] [DecidableEq I]
    (D : DeterminantPathCount I) :
    D.detCount = (SourceSinkKernel.matrix D.kernel).det :=
  D.detCount_eq_det

/-! ## Fermionic skew kernels and Pfaffian square law -/

/--
Fermionic skew kernel whose Pfaffian squares to the determinant.

This is the signed/oriented square-root layer.  It does not reuse the
positive-branch Pfaffian automatically; the signed Pfaffian is model data.
-/
@[rep_depth operator]
structure PfaffianKernel
    (I : Type*)
    [Fintype I] [DecidableEq I] where

  omega : Matrix I I ℝ

  skew :
    ∀ i j, omega i j = -omega j i

  pfaffian : ℝ

  pf_sq_eq_det :
    pfaffian * pfaffian = omega.det

/-- Read back that the fermionic Pfaffian amplitude squares to determinant. -/
@[rep_depth operator]
theorem pfaffianKernel_sq_eq_det
    {I : Type*}
    [Fintype I] [DecidableEq I]
    (P : PfaffianKernel I) :
    P.pfaffian * P.pfaffian = P.omega.det :=
  P.pf_sq_eq_det

/--
Determinant as the even shadow of the Pfaffian amplitude.

This is a naming theorem for downstream readouts.
-/
@[rep_depth operator]
theorem determinant_even_shadow_of_pfaffian
    {I : Type*}
    [Fintype I] [DecidableEq I]
    (P : PfaffianKernel I) :
    P.omega.det = P.pfaffian * P.pfaffian :=
  P.pf_sq_eq_det.symm

/-! ## Drazin regular determinant data -/

/--
Drazin determinant data.

The regular determinant is a readout on the Drazin regular support
`Preg = L * LD`; the harmonic projector `H = 1 - Preg` is kept separately.
-/
@[rep_depth operator]
structure DrazinDeterminantData
    (V : Type*)
    [Fintype V] [DecidableEq V] where

  L : Matrix V V ℝ
  LD : Matrix V V ℝ
  Preg : Matrix V V ℝ
  H : Matrix V V ℝ

  Preg_def :
    Preg = L * LD

  H_def :
    H = 1 - Preg

  Preg_idempotent :
    Preg * Preg = Preg

  H_idempotent :
    H * H = H

  det_regular : ℝ

/-- Read back the Drazin regular support. -/
@[rep_depth operator]
theorem drazinRegularProjector_eq
    {V : Type*}
    [Fintype V] [DecidableEq V]
    (D : DrazinDeterminantData V) :
    D.Preg = D.L * D.LD :=
  D.Preg_def

/-- Read back the harmonic Drazin projector. -/
@[rep_depth operator]
theorem drazinHarmonicProjector_eq
    {V : Type*}
    [Fintype V] [DecidableEq V]
    (D : DrazinDeterminantData V) :
    D.H = 1 - D.Preg :=
  D.H_def

/-! ## Weyl/KMS projective determinant readout -/

/-- Weyl weight attached to determinant/Pfaffian path sectors. -/
structure WeylPathWeight (Γ : Type*) where
  weight : Γ → ℝ
  positive : ∀ γ, 0 < weight γ

/-- KMS/Jaynes expectation weight attached to determinant/Pfaffian path sectors. -/
structure KMSPathState (Γ : Type*) where
  expect : Γ → ℝ
  nonnegative : ∀ γ, 0 ≤ expect γ

/-- Weighted projective determinant-sector mass. -/
def determinantSectorMass
    {Γ : Type*}
    [Fintype Γ]
    (Ω : WeylPathWeight Γ)
    (φ : KMSPathState Γ) : ℝ :=
  Finset.univ.sum (fun γ : Γ => Ω.weight γ * φ.expect γ)

/-- Projective determinant coordinate for a path sector. -/
def projectiveDeterminantCoordinate
    {Γ : Type*}
    [Fintype Γ]
    (Ω : WeylPathWeight Γ)
    (φ : KMSPathState Γ)
    (γ : Γ) : ℝ :=
  Ω.weight γ * φ.expect γ / determinantSectorMass Ω φ

/--
Projective Weyl/KMS determinant calibration.

This says a determinant-like volume readout is a scaled representative of the
Weyl/KMS projective count line.
-/
structure ProjectiveDeterminantCalibration
    {Γ : Type*}
    [Fintype Γ]
    (Ω : WeylPathWeight Γ)
    (φ : KMSPathState Γ) where

  determinantVolume : ℝ
  scale : ℝ

  determinantVolume_eq_scaled_mass :
    determinantVolume = scale * determinantSectorMass Ω φ

/-- Read back the calibrated projective determinant volume law. -/
theorem projective_determinant_volume_eq_scaled_mass
    {Γ : Type*}
    [Fintype Γ]
    (Ω : WeylPathWeight Γ)
    (φ : KMSPathState Γ)
    (C : ProjectiveDeterminantCalibration Ω φ) :
    C.determinantVolume = C.scale * determinantSectorMass Ω φ :=
  C.determinantVolume_eq_scaled_mass

/-! ## Pluecker/Fierz--Klein projective shadow -/

/-- Real projective count channels for determinant/Pfaffian readout. -/
inductive ProjectiveCountChannel where
  | scalar
  | rotor
  | vector
  | axial
  | area
  deriving DecidableEq, Fintype

/-- Readout from projective determinant coordinates to Fierz/Klein coordinates. -/
structure ProjectiveDeterminantReadout (Γ : Type*) [Fintype Γ] where
  coord : ProjectiveCountChannel → (Γ → ℝ) → ℝ

/-- Residual for the Pluecker/Klein quadric shadow. -/
structure KleinResidual where
  residual : (ProjectiveCountChannel → ℝ) → ℝ

/--
Witness that the projective determinant/Pfaffian count ray lies on the intended
Fierz--Klein/Pluecker residual locus.
-/
structure ProjectivePfaffianKleinLaw
    (Γ : Type*)
    [Fintype Γ] where

  Ω : WeylPathWeight Γ
  φ : KMSPathState Γ
  readout : ProjectiveDeterminantReadout Γ
  residual : KleinResidual

  coords : ProjectiveCountChannel → ℝ :=
    fun ch =>
      readout.coord ch
        (fun γ => projectiveDeterminantCoordinate Ω φ γ)

  klein_True :
    residual.residual coords = 0

/-- Read back the witness-gated (Native Closure Mandated: Closure Debt) Klein residual law. -/
theorem projective_pfaffian_counts_lie_on_klein
    {Γ : Type*}
    [Fintype Γ]
    (K : ProjectivePfaffianKleinLaw Γ) :
    K.residual.residual K.coords = 0 :=
  K.klein_True

/-- The projective Pfaffian count ray lies on the Fierz--Klein residual locus. -/
theorem projective_pfaffian_counts_lie_on_fierz_klein
    {Γ : Type*}
    [Fintype Γ]
    (K : ProjectivePfaffianKleinLaw Γ) :
    K.residual.residual K.coords = 0 :=
  K.klein_True

end InfoGeometry.Canonical.ProjectivePfaffianDeterminantCounts

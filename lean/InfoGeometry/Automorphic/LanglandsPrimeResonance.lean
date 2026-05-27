/-
InfoGeometry/Automorphic/LanglandsPrimeResonance.lean

Langlands prime resonance / Sugawara bridge socket.

This module sits above the operator-first Siegel-Eisenstein splitting and the
existing automorphic L-function resonance socket.

It does not prove E9, affine Sugawara, Virasoro, geometric Langlands, Euler
products, functional equations, or zero theorems.

It packages the conservative bridge:

  Sugawara central/stress readout on the Siegel boundary
    =
  completed L-function readout on the same boundary datum.

Consequences proved here:

* central-zero iff completed-L zero;
* boundary resonance iff Sugawara central zero;
* bulk resonance is read through the Siegel constant term;
* applying the boundary projector does not change the resonance readout.

This is the PR-safe closure of the AQL-discovered Langlands/Siegel corridor.
-/

import Mathlib
import InfoGeometry.Automorphic.SiegelResonance
import InfoGeometry.Automorphic.LFunctionResonance
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.Automorphic.LanglandsPrimeResonance

open InfoGeometry.Automorphic.SiegelResonance
open InfoGeometry.Automorphic.LFunctionResonance

universe uBulk uBoundary uStress uSpectral uScalar uHecke

variable {Bulk : Type uBulk} {Boundary : Type uBoundary}
variable [AddCommGroup Bulk] [Module ℝ Bulk]
variable [AddCommGroup Boundary] [Module ℝ Boundary]

/-! ## 1. Completed L-function and Sugawara readout sockets -/

/--
Completed L-function readout attached to Siegel boundary data.

`Spectral` is the spectral/Langlands parameter type.
`Scalar` is the value type, usually `ℂ`.

The functional equation remains a law/certificate socket.  This file only uses
the pointwise completed-L readout and its zero locus.
-/
structure CompletedLReadout
    (Boundary : Type uBoundary)
    (Spectral : Type uSpectral)
    (Scalar : Type uScalar)
    [Zero Scalar] where
  /-- Spectral parameter extracted from boundary data. -/
  spectralOfBoundary :
    Boundary → Spectral

  /-- Completed L-function value. -/
  completedL :
    Spectral → Scalar

  /-- Model-specific completed functional-equation law. -/
  functional_equation_law :
    Prop

  /-- Certificate for the functional-equation law. -/
  functional_equation_certificate :
    functional_equation_law

namespace CompletedLReadout

variable
    {Spectral : Type uSpectral}
    {Scalar : Type uScalar}
    [Zero Scalar]

variable (L : CompletedLReadout Boundary Spectral Scalar)

/-- Boundary datum lies on the completed-L zero locus. -/
def IsBoundaryLZero
    (b : Boundary) : Prop :=
  L.completedL (L.spectralOfBoundary b) = 0

end CompletedLReadout

/--
Affine/Sugawara stress readout attached to Siegel boundary data.

This is deliberately abstract.  Later E9/Virasoro modules may instantiate
`Stress` with boundary stress modes or affine current/Sugawara data.
-/
structure SugawaraCentralReadout
    (Boundary : Type uBoundary)
    (Stress : Type uStress)
    (Scalar : Type uScalar)
    [Zero Scalar] where
  /-- Boundary stress/current datum. -/
  stressOfBoundary :
    Boundary → Stress

  /-- Central/stress/anomaly scalar readout. -/
  centralReadout :
    Stress → Scalar

  /-- Model-specific Sugawara/affine stress law. -/
  sugawara_law :
    Prop

  /-- Certificate for the Sugawara/affine law. -/
  sugawara_certificate :
    sugawara_law

namespace SugawaraCentralReadout

variable
    {Stress : Type uStress}
    {Scalar : Type uScalar}
    [Zero Scalar]

variable (S : SugawaraCentralReadout Boundary Stress Scalar)

/-- Boundary datum has zero Sugawara central/stress readout. -/
def HasCentralZero
    (b : Boundary) : Prop :=
  S.centralReadout (S.stressOfBoundary b) = 0

end SugawaraCentralReadout

/-! ## 2. Siegel/Sugawara/completed-L bridge -/

/--
Siegel/Sugawara bridge.

The bridge says that the Sugawara central/stress readout of the Siegel boundary
datum equals the completed L-function readout at the corresponding spectral
parameter.
-/
structure LanglandsSugawaraBridge
    (W : SiegelEisensteinWitness Bulk Boundary)
    {Stress : Type uStress}
    {Spectral : Type uSpectral}
    {Scalar : Type uScalar}
    [Zero Scalar]
    (L : CompletedLReadout Boundary Spectral Scalar)
    (S : SugawaraCentralReadout Boundary Stress Scalar) where
  /-- Central/stress readout equals completed-L readout on the Siegel boundary. -/
  central_eq_completedL_on_boundary :
    ∀ b : Boundary,
      S.centralReadout (S.stressOfBoundary b) =
        L.completedL (L.spectralOfBoundary b)

namespace LanglandsSugawaraBridge

variable
    {W : SiegelEisensteinWitness Bulk Boundary}
    {Stress : Type uStress}
    {Spectral : Type uSpectral}
    {Scalar : Type uScalar}
    [Zero Scalar]
    {L : CompletedLReadout Boundary Spectral Scalar}
    {S : SugawaraCentralReadout Boundary Stress Scalar}

/-- Sugawara central-zero iff completed-L zero on a boundary datum. -/
theorem central_zero_iff_L_zero
    (B : LanglandsSugawaraBridge W L S)
    (b : Boundary) :
    S.HasCentralZero b ↔ L.IsBoundaryLZero b := by
  dsimp [SugawaraCentralReadout.HasCentralZero,
    CompletedLReadout.IsBoundaryLZero]
  rw [LanglandsSugawaraBridge.central_eq_completedL_on_boundary B b]

/-- Completed-L zero implies Sugawara central-zero. -/
theorem central_zero_of_L_zero
    (B : LanglandsSugawaraBridge W L S)
    (b : Boundary)
    (h : L.IsBoundaryLZero b) :
    S.HasCentralZero b :=
  (central_zero_iff_L_zero B b).mpr h

/-- Sugawara central-zero implies completed-L zero. -/
theorem L_zero_of_central_zero
    (B : LanglandsSugawaraBridge W L S)
    (b : Boundary)
    (h : S.HasCentralZero b) :
    L.IsBoundaryLZero b :=
  (central_zero_iff_L_zero B b).mp h

end LanglandsSugawaraBridge

/-! ## 3. Bulk resonance through Siegel boundary extraction -/

/--
A bulk state has Langlands prime resonance when its Siegel boundary datum lies
on the completed-L zero locus.
-/
def IsBulkLanglandsPrimeResonance
    (W : SiegelEisensteinWitness Bulk Boundary)
    {Spectral : Type uSpectral}
    {Scalar : Type uScalar}
    [Zero Scalar]
    (L : CompletedLReadout Boundary Spectral Scalar)
    (F : Bulk) : Prop :=
  L.IsBoundaryLZero (W.siegel F)

/--
A bulk state has Sugawara central-zero when the Sugawara readout of its Siegel
boundary datum vanishes.
-/
def HasBulkSugawaraCentralZero
    (W : SiegelEisensteinWitness Bulk Boundary)
    {Stress : Type uStress}
    {Scalar : Type uScalar}
    [Zero Scalar]
    (S : SugawaraCentralReadout Boundary Stress Scalar)
    (F : Bulk) : Prop :=
  S.HasCentralZero (W.siegel F)

namespace LanglandsSugawaraBridge

variable
    {W : SiegelEisensteinWitness Bulk Boundary}
    {Stress : Type uStress}
    {Spectral : Type uSpectral}
    {Scalar : Type uScalar}
    [Zero Scalar]
    {L : CompletedLReadout Boundary Spectral Scalar}
    {S : SugawaraCentralReadout Boundary Stress Scalar}

/-- For bulk states, Sugawara central-zero iff completed-L prime resonance. -/
theorem bulk_central_zero_iff_prime_resonance
    (B : LanglandsSugawaraBridge W L S)
    (F : Bulk) :
    HasBulkSugawaraCentralZero W S F ↔
      IsBulkLanglandsPrimeResonance W L F := by
  dsimp [HasBulkSugawaraCentralZero,
    IsBulkLanglandsPrimeResonance]
  exact central_zero_iff_L_zero B (W.siegel F)

/-- A bulk Sugawara central-zero condition gives Langlands prime resonance. -/
theorem bulk_prime_resonance_of_central_zero
    (B : LanglandsSugawaraBridge W L S)
    (F : Bulk)
    (h : HasBulkSugawaraCentralZero W S F) :
  IsBulkLanglandsPrimeResonance W L F :=
  (bulk_central_zero_iff_prime_resonance B F).mp h

/-- A bulk Langlands prime resonance gives Sugawara central-zero. -/
theorem bulk_central_zero_of_prime_resonance
    (B : LanglandsSugawaraBridge W L S)
    (F : Bulk)
    (h : IsBulkLanglandsPrimeResonance W L F) :
  HasBulkSugawaraCentralZero W S F :=
  (bulk_central_zero_iff_prime_resonance B F).mpr h

/--
Applying the boundary projector does not change the bulk prime-resonance
readout, because it does not change the Siegel boundary datum.
-/
theorem bulk_prime_resonance_boundaryProjector_iff
    (_B : LanglandsSugawaraBridge W L S)
    (F : Bulk) :
    IsBulkLanglandsPrimeResonance W L (W.boundaryProjector F) ↔
      IsBulkLanglandsPrimeResonance W L F := by
  dsimp [IsBulkLanglandsPrimeResonance]
  have h :
      W.siegel (W.boundaryProjector F) = W.siegel F := by
    have h0 :=
      congrArg
        (fun f : Bulk →ₗ[ℝ] Boundary => f F)
        W.siegel_comp_boundaryProjector
    simp [LinearMap.comp_apply] at h0 ⊢
  rw [h]

/--
Applying the boundary projector does not change the bulk Sugawara central-zero
readout.
-/
theorem bulk_central_zero_boundaryProjector_iff
    (_B : LanglandsSugawaraBridge W L S)
    (F : Bulk) :
    HasBulkSugawaraCentralZero W S (W.boundaryProjector F) ↔
      HasBulkSugawaraCentralZero W S F := by
  dsimp [HasBulkSugawaraCentralZero]
  have h :
      W.siegel (W.boundaryProjector F) = W.siegel F := by
    have h0 :=
      congrArg
        (fun f : Bulk →ₗ[ℝ] Boundary => f F)
        W.siegel_comp_boundaryProjector
    simp [LinearMap.comp_apply] at h0 ⊢
  rw [h]

end LanglandsSugawaraBridge

/-! ## 4. Prime resonance witness package -/

/--
Langlands prime resonance witness.

This combines the existing automorphic L-resonance package with the new
Sugawara/completed-L bridge.
-/
structure LanglandsPrimeResonanceWitness
    (W : SiegelEisensteinWitness Bulk Boundary)
    {Stress : Type uStress}
    {Spectral : Type uSpectral}
    {Scalar : Type uScalar}
    [Zero Scalar] where
  /-- Existing automorphic L-resonance data. -/
  automorphic :
    AutomorphicLResonanceWitness.{uBulk, uBoundary, uHecke} W

  /-- Completed L-function readout on boundary data. -/
  completed :
    CompletedLReadout Boundary Spectral Scalar

  /-- Sugawara central/stress readout on boundary data. -/
  sugawara :
    SugawaraCentralReadout Boundary Stress Scalar

  /-- Bridge equating the Sugawara and completed-L readouts. -/
  bridge :
    LanglandsSugawaraBridge W completed sugawara

namespace LanglandsPrimeResonanceWitness

variable
    {W : SiegelEisensteinWitness Bulk Boundary}
    {Stress : Type uStress}
    {Spectral : Type uSpectral}
    {Scalar : Type uScalar}
    [Zero Scalar]

variable
    (R :
      LanglandsPrimeResonanceWitness.{uBulk, uBoundary, uStress, uSpectral, uScalar, uHecke}
        (Bulk := Bulk) (Boundary := Boundary)
        (Stress := Stress) (Spectral := Spectral) (Scalar := Scalar) W)

/-- Bulk central-zero iff bulk prime resonance for the witness. -/
theorem bulk_central_zero_iff_prime_resonance
    (F : Bulk) :
    HasBulkSugawaraCentralZero W R.sugawara F ↔
      IsBulkLanglandsPrimeResonance W R.completed F :=
  LanglandsSugawaraBridge.bulk_central_zero_iff_prime_resonance R.bridge F

/-- Sugawara central-zero produces Langlands prime resonance for the witness. -/
theorem bulk_prime_resonance_of_central_zero
    (F : Bulk)
    (h : HasBulkSugawaraCentralZero W R.sugawara F) :
    IsBulkLanglandsPrimeResonance W R.completed F :=
  LanglandsSugawaraBridge.bulk_prime_resonance_of_central_zero R.bridge F h

/-- The boundary projector preserves the witness's prime-resonance readout. -/
theorem boundaryProjector_preserves_prime_resonance
    (F : Bulk) :
    IsBulkLanglandsPrimeResonance W R.completed (W.boundaryProjector F) ↔
      IsBulkLanglandsPrimeResonance W R.completed F :=
  LanglandsSugawaraBridge.bulk_prime_resonance_boundaryProjector_iff R.bridge F

end LanglandsPrimeResonanceWitness

/-! ## 5. Admissibility and owner target -/

/--
Admissibility package for constructing a Langlands prime resonance witness.

This keeps the owner target conditional: arbitrary Siegel splittings do not
automatically carry completed L-functions or Sugawara stress readouts.
-/
structure LanglandsPrimeResonanceAdmissible
    (W : SiegelEisensteinWitness Bulk Boundary)
    {Stress : Type uStress}
    {Spectral : Type uSpectral}
    {Scalar : Type uScalar}
    [Zero Scalar] where
  automorphic :
    AutomorphicLResonanceWitness.{uBulk, uBoundary, uHecke} W

  completed :
    CompletedLReadout Boundary Spectral Scalar

  sugawara :
    SugawaraCentralReadout Boundary Stress Scalar

  bridge :
    LanglandsSugawaraBridge W completed sugawara

/-- A Langlands prime resonance witness exists from admissible data. -/
theorem langlandsPrimeResonanceWitness_nonempty_of_admissible
    {W : SiegelEisensteinWitness Bulk Boundary}
    {Stress : Type uStress}
    {Spectral : Type uSpectral}
    {Scalar : Type uScalar}
    [Zero Scalar]
    (h :
      LanglandsPrimeResonanceAdmissible.{uBulk, uBoundary, uStress, uSpectral, uScalar, uHecke}
        (Bulk := Bulk) (Boundary := Boundary)
        (Stress := Stress) (Spectral := Spectral) (Scalar := Scalar) W) :
    Nonempty
      (LanglandsPrimeResonanceWitness.{uBulk, uBoundary, uStress, uSpectral, uScalar, uHecke}
        (Bulk := Bulk) (Boundary := Boundary)
        (Stress := Stress) (Spectral := Spectral) (Scalar := Scalar) W) :=
  ⟨{
    automorphic := h.automorphic
    completed := h.completed
    sugawara := h.sugawara
    bridge := h.bridge
  }⟩

/--
Conditional owner target for Langlands prime resonance.

The target is intentionally conditional on admissible automorphic, completed-L,
and Sugawara bridge data.
-/
@[owner_target_tag]
def LanglandsPrimeResonanceOwnerTarget : Prop :=
  ∀ (Bulk : Type uBulk) [AddCommGroup Bulk] [Module ℝ Bulk],
  ∀ (Boundary : Type uBoundary) [AddCommGroup Boundary] [Module ℝ Boundary],
  ∀ (Stress : Type uStress),
  ∀ (Spectral : Type uSpectral),
  ∀ (Scalar : Type uScalar) [Zero Scalar],
  ∀ W : SiegelEisensteinWitness Bulk Boundary,
    LanglandsPrimeResonanceAdmissible.{uBulk, uBoundary, uStress, uSpectral, uScalar, uHecke}
      (Bulk := Bulk) (Boundary := Boundary)
      (Stress := Stress) (Spectral := Spectral) (Scalar := Scalar) W →
      Nonempty
        (LanglandsPrimeResonanceWitness.{uBulk, uBoundary, uStress, uSpectral, uScalar, uHecke}
          (Bulk := Bulk) (Boundary := Boundary)
          (Stress := Stress) (Spectral := Spectral) (Scalar := Scalar) W)

/--
The Langlands prime resonance owner target follows from the supplied
admissibility data.
-/
theorem langlandsPrimeResonanceOwnerTarget :
    LanglandsPrimeResonanceOwnerTarget := by
  intro Bulk _ _ Boundary _ _ Stress Spectral Scalar _ W h
  exact langlandsPrimeResonanceWitness_nonempty_of_admissible h

end InfoGeometry.Automorphic.LanglandsPrimeResonance

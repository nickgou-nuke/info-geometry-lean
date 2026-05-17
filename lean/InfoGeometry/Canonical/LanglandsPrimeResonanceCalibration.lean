import Mathlib
import InfoGeometry.Meta.CalibrationReexport
import InfoGeometry.Automorphic.SiegelResonance
import InfoGeometry.Automorphic.LanglandsPrimeResonance

/-!
# InfoGeometry.Canonical.LanglandsPrimeResonanceCalibration

Canonical wrapper for the existing Langlands prime resonance bridge.

This file adds no new analytic content. It re-exports the already-native
bridge theorems under a canonical owner-facing namespace.
-/

noncomputable section

namespace InfoGeometry.Canonical.LanglandsPrimeResonanceCalibration

open InfoGeometry.Automorphic
open InfoGeometry.Automorphic.SiegelResonance
open InfoGeometry.Automorphic.LanglandsPrimeResonance
open InfoGeometry.Automorphic.LanglandsPrimeResonance.LanglandsSugawaraBridge
open InfoGeometry.Automorphic.LanglandsPrimeResonance.LanglandsPrimeResonanceWitness

universe uBulk uBoundary uStress uSpectral uScalar uHecke

/-- Canonical re-export of the central-zero / completed-L equivalence. -/
theorem central_zero_iff_L_zero
    {Bulk Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    {Stress Spectral Scalar : Type*}
    [Zero Scalar]
    {L : CompletedLReadout Boundary Spectral Scalar}
    {S : SugawaraCentralReadout Boundary Stress Scalar}
    (B : LanglandsSugawaraBridge W L S)
    (b : Boundary) :
    S.HasCentralZero b ↔ L.IsBoundaryLZero b :=
  by reexport LanglandsSugawaraBridge.central_zero_iff_L_zero B b

/-- Canonical re-export of bulk central-zero iff bulk prime resonance. -/
theorem bulk_central_zero_iff_prime_resonance
    {Bulk Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    {Stress Spectral Scalar : Type*}
    [Zero Scalar]
    {L : CompletedLReadout Boundary Spectral Scalar}
    {S : SugawaraCentralReadout Boundary Stress Scalar}
    (B : LanglandsSugawaraBridge W L S)
    (F : Bulk) :
    HasBulkSugawaraCentralZero W S F ↔
      IsBulkLanglandsPrimeResonance W L F :=
  by reexport LanglandsSugawaraBridge.bulk_central_zero_iff_prime_resonance B F

/-- Canonical re-export of the bulk prime resonance from central-zero. -/
theorem bulk_prime_resonance_of_central_zero
    {Bulk Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    {Stress Spectral Scalar : Type*}
    [Zero Scalar]
    {L : CompletedLReadout Boundary Spectral Scalar}
    {S : SugawaraCentralReadout Boundary Stress Scalar}
    (B : LanglandsSugawaraBridge W L S)
    (F : Bulk)
    (h : HasBulkSugawaraCentralZero W S F) :
    IsBulkLanglandsPrimeResonance W L F :=
  by reexport LanglandsSugawaraBridge.bulk_prime_resonance_of_central_zero B F h

/-- Canonical re-export of the Langlands prime resonance owner target. -/
theorem langlandsPrimeResonanceOwnerTarget :
    LanglandsPrimeResonanceOwnerTarget :=
  by reexport InfoGeometry.Automorphic.LanglandsPrimeResonance.langlandsPrimeResonanceOwnerTarget

end InfoGeometry.Canonical.LanglandsPrimeResonanceCalibration

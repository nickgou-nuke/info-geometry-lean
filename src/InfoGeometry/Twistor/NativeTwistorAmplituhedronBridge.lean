/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.TwoTwistorPluckerKlein
import InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Native twistor / amplituhedron coordinate bridge

Relates the repository's complex-spinor `Twistor4` and native `Plucker6` to
the coordinate realization used by the Zorn/amplituhedron archetype.  The
bridge records the sign/order convention explicitly; it does not identify the
Zorn product with an associative operator product.

## i. Overview

This module transports twistor-pair coordinates and four-brackets to native
Mathlib Plücker and matrix-determinant constructions.

## ii. Key results

- `dot_pluckerPair_eq_kleinQ` matches the electric/magnetic dot product with
  the repository's Klein-quadric equation.
- `native_matrix_det_eq_archetype_twistor_bracket` identifies the native
  determinant with the archetype four-bracket in the declared coordinate order.
- `native_twistor_scattering_anticommutator_eq_matrix_det` transports the
  two-ray Zorn identity to that determinant.

## iii. Table of contents

1. Coordinate adapter and native matrix determinant.
2. Plücker pair convention and Klein-quadric compatibility.
3. Twistor nilpotency and two-ray scattering transport.

## iv. References

- Mathlib's `Matrix.det` over the complex numbers.
- `InfoGeometry.Twistor.TwoTwistorPluckerKlein`.
- `InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon`.

#### BUCKET 1 — Proved Kernel Content
- `native_matrix_det_eq_archetype_twistor_bracket`
- `dot_pluckerPair_eq_kleinQ`
- `twistorPairPlucker_matches_archetype`
- `native_twistor_scattering_anticommutator_eq_matrix_det`

#### BUCKET 2 — Conditional / Interface Boundaries
- None (all coordinate bridge identities hold unconditionally over `ℂ`).

#### BUCKET 3 — Open / Unformalized
- Loop-level momentum-twistor contour integrals remain outside this algebraic coordinate bridge.
-/

namespace InfoGeometry.Twistor.NativeTwistorAmplituhedronBridge

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwoTwistorPluckerKlein
open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon

namespace Archetype

abbrev Vec3 (R : Type*) := InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Vec3 R
abbrev Twistor4 (R : Type*) := InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Twistor4 R
abbrev ZornMatrix (R : Type*) := InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix R

/-- Maps a native complex-spinor `PenroseIncidence.Twistor4` to `Archetype.Twistor4 ℂ`. -/
def ofNative (Z : InfoGeometry.Twistor.PenroseIncidence.Twistor4) : Twistor4 ℂ :=
  ⟨Z.1 0, Z.1 1, Z.2 0, Z.2 1⟩

end Archetype

/-- Native Mathlib matrix whose rows are the four coordinates of four
Penrose-incidence twistors in the same `(ω₀, ω₁, π₀, π₁)` order used by the
repo's Plücker owner. -/
def nativeTwistorMatrix4 (Z₀ Z₁ Z₂ Z₃ : Twistor4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![Z₀.1 0, Z₀.1 1, Z₀.2 0, Z₀.2 1],
    ![Z₁.1 0, Z₁.1 1, Z₁.2 0, Z₁.2 1],
    ![Z₂.1 0, Z₂.1 1, Z₂.2 0, Z₂.2 1],
    ![Z₃.1 0, Z₃.1 1, Z₃.2 0, Z₃.2 1]]

/-- Native `Matrix.det` of the complex-spinor Twistor carrier is the archetype
4-bracket after transport through `Archetype.ofNative`. -/
lemma native_matrix_det_eq_archetype_twistor_bracket
    (Z₀ Z₁ Z₂ Z₃ : Twistor4) :
    Matrix.det (nativeTwistorMatrix4 Z₀ Z₁ Z₂ Z₃) =
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.twistorBracket4
        (Archetype.ofNative Z₀) (Archetype.ofNative Z₁)
        (Archetype.ofNative Z₂) (Archetype.ofNative Z₃) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp [nativeTwistorMatrix4, Matrix.submatrix, Fin.succAbove,
    InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.twistorBracket4,
    InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.det4,
    InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ofTwistors,
    Archetype.ofNative, Matrix.det_fin_three]
  ring

open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6

/-- Read native Plücker coordinates as electric and magnetic 3-vectors.
The magnetic convention is `(p23, -p13, p12)`, matching the cross product
of the last three homogeneous coordinates. -/
def pluckerPair (p : Plucker6 ℂ) : Archetype.Vec3 ℂ × Archetype.Vec3 ℂ :=
  (⟨p.p01, p.p02, p.p03⟩, ⟨p.p23, -p.p13, p.p12⟩)

/-- The Euclidean dot product of the electric/magnetic `pluckerPair` equals the Klein quadric `kleinQ`. -/
lemma dot_pluckerPair_eq_kleinQ (p : Plucker6 ℂ) :
    InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Vec3.dot
      (pluckerPair p).1 (pluckerPair p).2 = kleinQ p := by
  simp [pluckerPair, InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Vec3.dot,
    kleinQ]
  ring

/-- The archetype's electric/magnetic coordinates are precisely the native
Plücker readout of the same complex twistor pair. -/
lemma twistorPairPlucker_matches_archetype
    (Z W : InfoGeometry.Twistor.PenroseIncidence.Twistor4) :
    pluckerPair (twistorPairPlucker Z W) =
      (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Twistor4.pluckerU
          (Archetype.ofNative Z) (Archetype.ofNative W),
       InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Twistor4.pluckerV
          (Archetype.ofNative Z) (Archetype.ofNative W)) := by
  apply Prod.ext
  · apply InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Vec3.ext <;>
      simp [pluckerPair, twistorPairPlucker, twistorVector,
        InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.pluckerLine,
        Archetype.ofNative,
        InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Twistor4.pluckerU]
  · apply InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Vec3.ext <;>
      simp [pluckerPair, twistorPairPlucker, twistorVector,
        InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.pluckerLine,
        Archetype.ofNative,
        InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Twistor4.pluckerV,
        InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Twistor4.spatialVec,
        InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Vec3.cross]

/-- Native decomposability transfers to the archetype's Klein equation. -/
lemma archetype_twistor_pair_on_klein
    (Z W : InfoGeometry.Twistor.PenroseIncidence.Twistor4) :
    InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Vec3.dot
      (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Twistor4.pluckerU
        (Archetype.ofNative Z) (Archetype.ofNative W))
      (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Twistor4.pluckerV
        (Archetype.ofNative Z) (Archetype.ofNative W)) = 0 := by
  have h := twistorPairPlucker_matches_archetype Z W
  calc
    InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Vec3.dot
        (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Twistor4.pluckerU
          (Archetype.ofNative Z) (Archetype.ofNative W))
        (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Twistor4.pluckerV
          (Archetype.ofNative Z) (Archetype.ofNative W)) =
        InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Vec3.dot
          (pluckerPair (twistorPairPlucker Z W)).1
          (pluckerPair (twistorPairPlucker Z W)).2 := by
          have hmapped := congrArg
            (fun uv : Archetype.Vec3 ℂ × Archetype.Vec3 ℂ =>
              InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Vec3.dot uv.1 uv.2) h
          exact hmapped.symm
    _ = kleinQ (twistorPairPlucker Z W) := dot_pluckerPair_eq_kleinQ _
    _ = 0 := twistorPairPlucker_on_klein Z W

/-- Consequently, the archetype's Zorn representative of a native complex
twistor line is square-zero. -/
lemma archetype_zorn_twistor_pair_nilpotent
    (Z W : InfoGeometry.Twistor.PenroseIncidence.Twistor4) :
    InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.zornPhi
      (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Twistor4.pluckerU
        (Archetype.ofNative Z) (Archetype.ofNative W))
      (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Twistor4.pluckerV
        (Archetype.ofNative Z) (Archetype.ofNative W)) *
    InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.zornPhi
      (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Twistor4.pluckerU
        (Archetype.ofNative Z) (Archetype.ofNative W))
      (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.Twistor4.pluckerV
        (Archetype.ofNative Z) (Archetype.ofNative W)) = 0 := by
  ext <;>
  · simp only [ZornMatrix.zornPhi, Twistor4.pluckerU, Twistor4.pluckerV,
      Twistor4.spatialVec,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      ZornMatrix.zero_a, ZornMatrix.zero_u, ZornMatrix.zero_v, ZornMatrix.zero_d,
      Vec3.dot, Vec3.smulLeft, Vec3.smulRight, Vec3.cross,
      Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
      Vec3.add_x, Vec3.add_y, Vec3.add_z,
      Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
    ring

/-- Two native complex-spinor twistor pairs, after the explicit coordinate
map above, satisfy the archetype's Zorn anticommutator/4-bracket identity and
its corresponding projector-defect identity. The bracket and Zorn product
here are the archetype's coordinate definitions. -/
lemma native_twistor_two_ray_scattering_identities
    (Z₀ Z₁ Z₂ Z₃ : InfoGeometry.Twistor.PenroseIncidence.Twistor4) :
    (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.zornPlucker
        (Archetype.ofNative Z₀) (Archetype.ofNative Z₁) *
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.zornPlucker
        (Archetype.ofNative Z₂) (Archetype.ofNative Z₃) +
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.zornPlucker
        (Archetype.ofNative Z₂) (Archetype.ofNative Z₃) *
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.zornPlucker
        (Archetype.ofNative Z₀) (Archetype.ofNative Z₁) =
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.smul
        (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.twistorBracket4
          (Archetype.ofNative Z₀) (Archetype.ofNative Z₁)
          (Archetype.ofNative Z₂) (Archetype.ofNative Z₃))
        (1 : Archetype.ZornMatrix ℂ)) ∧
    ((InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.projP +
        (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.zornPlucker
            (Archetype.ofNative Z₀) (Archetype.ofNative Z₁) +
         InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.zornPlucker
            (Archetype.ofNative Z₂) (Archetype.ofNative Z₃))) *
      (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.projP +
        (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.zornPlucker
            (Archetype.ofNative Z₀) (Archetype.ofNative Z₁) +
         InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.zornPlucker
            (Archetype.ofNative Z₂) (Archetype.ofNative Z₃))) -
      (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.projP +
        (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.zornPlucker
            (Archetype.ofNative Z₀) (Archetype.ofNative Z₁) +
         InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.zornPlucker
            (Archetype.ofNative Z₂) (Archetype.ofNative Z₃))) =
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.smul
        (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.twistorBracket4
          (Archetype.ofNative Z₀) (Archetype.ofNative Z₁)
          (Archetype.ofNative Z₂) (Archetype.ofNative Z₃))
        (1 : Archetype.ZornMatrix ℂ)) := by
  have d := plucker_ray_and_scattering_projector_defects
      (Archetype.ofNative Z₀) (Archetype.ofNative Z₁)
      (Archetype.ofNative Z₂) (Archetype.ofNative Z₃)
  refine ⟨?_, d.2⟩
  ext <;>
  · simp only [zornPlucker, ZornMatrix.zornPhi, Twistor4.pluckerU, Twistor4.pluckerV,
      Twistor4.spatialVec, twistorBracket4, det4, ofTwistors,
      ZornMatrix.smul, ZornMatrix.one_a, ZornMatrix.one_u, ZornMatrix.one_v, ZornMatrix.one_d,
      ZornMatrix.add_a, ZornMatrix.add_u, ZornMatrix.add_v, ZornMatrix.add_d,
      ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
      Vec3.dot, Vec3.smulLeft, Vec3.smulRight, Vec3.cross,
      Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
      Vec3.add_x, Vec3.add_y, Vec3.add_z,
      Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
    ring

/-- The paired-ray Zorn anticommutator is therefore the native Mathlib
`4 × 4` determinant, not only the archetype's hand-expanded bracket. -/
lemma native_twistor_scattering_anticommutator_eq_matrix_det
    (Z₀ Z₁ Z₂ Z₃ : InfoGeometry.Twistor.PenroseIncidence.Twistor4) :
    (InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.zornPlucker
        (Archetype.ofNative Z₀) (Archetype.ofNative Z₁) *
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.zornPlucker
        (Archetype.ofNative Z₂) (Archetype.ofNative Z₃) +
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.zornPlucker
        (Archetype.ofNative Z₂) (Archetype.ofNative Z₃) *
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.zornPlucker
        (Archetype.ofNative Z₀) (Archetype.ofNative Z₁)) =
      InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon.ZornMatrix.smul
        (Matrix.det (nativeTwistorMatrix4 Z₀ Z₁ Z₂ Z₃))
        (1 : Archetype.ZornMatrix ℂ) := by
  rw [native_matrix_det_eq_archetype_twistor_bracket]
  exact (native_twistor_two_ray_scattering_identities Z₀ Z₁ Z₂ Z₃).1

end InfoGeometry.Twistor.NativeTwistorAmplituhedronBridge

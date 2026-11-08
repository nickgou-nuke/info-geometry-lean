/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic
import Mathlib.Tactic.LinearCombination

/-!
# Chiral Anomaly Eikonal Birefringence (Section 117)

Formalizes the axion electrodynamics bridge from the Fujikawa Jacobian
to chiral birefringence in Weyl semimetals:

1. **Poynting–Fujikawa Decomposition**:
   For real vectors `E, B` in `ℝ³`,
   `‖E‖² ‖B‖² = ‖E × B‖² + (E · B)²`.
   The first term is the classical Poynting flux; the second is the
   topological Fujikawa source `(E · B)²`.

2. **Chiral Eikonal Dispersion**:
   `Ω_±(k) = |k| ± b₀` for left/right circular polarizations.

3. **Tachyonic Instability**:
   `Ω_+ · Ω_- = |k|² − b₀²`, which becomes negative when `|k| < |b₀|`.

No positivity, trace-one, or GNS construction is assumed.
-/

noncomputable section

namespace InfoGeometry.Topological.ChiralAnomalyEikonalBirefringence

open Finset

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Three-dimensional vector carrier. -/
abbrev Vec3 (R : Type*) := Fin 3 → R

/-- Dot product of two 3-vectors. -/
def dot (E B : Vec3 R) : R :=
  ∑ i : Fin 3, E i * B i

/-- Cross product of two 3-vectors. -/
def cross (E B : Vec3 R) : Vec3 R :=
  fun i =>
    match i with
    | 0 => E 1 * B 2 - E 2 * B 1
    | 1 => E 2 * B 0 - E 0 * B 2
    | 2 => E 0 * B 1 - E 1 * B 0

/-- Squared norm of a 3-vector. -/
def normSq (V : Vec3 R) : R :=
  ∑ i : Fin 3, V i * V i

/-- Poynting vector magnitude squared: `‖E × B‖²`. -/
def poyntingSq (E B : Vec3 R) : R :=
  normSq (cross E B)

/-- Fujikawa topological source: `(E · B)²`. -/
def fujikawaSource (E B : Vec3 R) : R :=
  dot E B * dot E B

/-- **Poynting–Fujikawa Decomposition**:
    `‖E‖² ‖B‖² = ‖E × B‖² + (E · B)²`. -/
theorem poynting_fujikawa_decomposition (E B : Vec3 R) :
    normSq E * normSq B = poyntingSq E B + fujikawaSource E B := by
  dsimp [normSq, poyntingSq, fujikawaSource, dot, cross]
  simp [Fin.sum_univ_succ]
  ring

/-- Chiral eikonal dispersion: left/right circular polarizations
    `Ω_±(k) = |k| ± b₀`. -/
def omegaPlus (k b0 : R) : R := k + b0
def omegaMinus (k b0 : R) : R := k - b0

/-- **Chiral dispersion product**:
    `Ω_+ · Ω_- = |k|² − b₀²`. -/
theorem chiral_dispersion_product (k b0 : R) :
    omegaPlus k b0 * omegaMinus k b0 = k * k - b0 * b0 := by
  dsimp [omegaPlus, omegaMinus]
  ring

theorem tachyonic_instability (k b0 : R)
    (h_small : k * k < b0 * b0) :
    omegaPlus k b0 * omegaMinus k b0 < 0 := by
  rw [chiral_dispersion_product]
  linarith

end InfoGeometry.Topological.ChiralAnomalyEikonalBirefringence

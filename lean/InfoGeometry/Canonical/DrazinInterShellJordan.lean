/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.DrazinInterShellHodge
import InfoGeometry.Core.JordanSquareZero

/-!
# Normalized Jordan structure of inter-shell Peirce blocks

The inter-shell Hodge--Dirac owner records the associative identities for a
square-zero block `d_{m,r}` and a Moore--Penrose inverse `B`.  This file
transports them to the repository's normalized special Jordan product

`x ∘ y = (1 / 2) • (x * y + y * x)`.

Two points are worth isolating:

* the normalized Jordan associator is `-(1 / 2) • d_{m,r}`, not the
  unnormalized `-2 • d_{m,r}`;
* the chiral grading `Γ = P₊ - P₋` annihilates the normalized local operator
  `d_{m,r} + B` under the normalized Jordan product.

Both statements require an `Algebra ℝ` structure because the normalized
Jordan product uses the real scalar `1 / 2`.  No commutativity, diagonalizability,
or additional Moore--Penrose hypothesis is assumed.
-/

namespace InfoGeometry.Canonical.DrazinNilpotentShell

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Singular.MoorePenrose
  (exactSupport coexactSupport chiralSupport normalizedDirac)
open InfoGeometry.Core.JordanPeirceDecomposition (jordanMul)

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℝ R]
variable {a d : R} {k : ℕ}

/-- The normalized Jordan associator of an inter-shell block and its
Moore--Penrose inverse is `-(1/2) • d_{m,r}`. -/
theorem interShell_jordan_associator (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    {m r : ℕ} (hne : m ≠ r) {B : R}
    (hB : InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse
      (interShellPeirceCorner a d M m r) B) :
    let D := interShellPeirceCorner a d M m r
    jordanMul (jordanMul D D) B - jordanMul D (jordanMul D B) =
      -(1 / 2 : ℝ) • D := by
  intro D
  exact InfoGeometry.Core.JordanAssociator.jordan_associator_square_zero_inner_inverse
    (interShellPeirceCorner_sq_eq_zero hD hM hne) hB.aba_eq_a

/-- The involution also exchanges the local exact and coexact supports when
it reverses the shell corner. -/
theorem interShell_exactSupport_star (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    (h_symm : star (projection a d) = projection a d)
    (ha_star : star a = a) (m r : ℕ) (B : R) :
    star (exactSupport (interShellPeirceCorner a d M m r) B) =
      coexactSupport (interShellPeirceCorner a d M r m) (star B) := by
  have hD_star : star (interShellPeirceCorner a d M m r) =
      interShellPeirceCorner a d M r m :=
    interShellPeirceCorner_star hD hM h_symm ha_star m r
  unfold exactSupport coexactSupport
  rw [star_mul, hD_star]

theorem interShell_coexactSupport_star (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    (h_symm : star (projection a d) = projection a d)
    (ha_star : star a = a) (m r : ℕ) (B : R) :
    star (coexactSupport (interShellPeirceCorner a d M m r) B) =
      exactSupport (interShellPeirceCorner a d M r m) (star B) := by
  have hD_star : star (interShellPeirceCorner a d M m r) =
      interShellPeirceCorner a d M r m :=
    interShellPeirceCorner_star hD hM h_symm ha_star m r
  unfold exactSupport coexactSupport
  rw [star_mul, hD_star]

/-- The chiral grading annihilates the normalized local operator under the
normalized special Jordan product. -/
theorem interShell_jordan_anticommute (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    {m r : ℕ} (hne : m ≠ r) {B : R}
    (hB : InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse
      (interShellPeirceCorner a d M m r) B) :
    let D := interShellPeirceCorner a d M m r
    jordanMul (chiralSupport D B) (normalizedDirac D B) = 0 := by
  intro D
  have hd_sq : D * D = 0 :=
    interShellPeirceCorner_sq_eq_zero hD hM hne
  have hB' : InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse D B :=
    hB.toSingular
  have hanti :=
    InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse.chiralSupport_anticommute_normalizedDirac
      hB' hd_sq
  unfold jordanMul
  rw [hanti]
  simp

end InfoGeometry.Canonical.DrazinNilpotentShell

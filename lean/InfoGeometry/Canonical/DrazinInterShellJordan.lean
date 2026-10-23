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
  (exactSupport coexactSupport harmonicSupport chiralSupport normalizedDirac)
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

theorem interShell_harmonicSupport_star (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    (h_symm : star (projection a d) = projection a d)
    (ha_star : star a = a) (m r : ℕ) (B : R) :
    star (harmonicSupport (interShellPeirceCorner a d M m r) B) =
      harmonicSupport (interShellPeirceCorner a d M r m) (star B) := by
  rw [harmonicSupport, star_sub, star_sub, star_one,
    interShell_coexactSupport_star hD hM h_symm ha_star m r B,
    interShell_exactSupport_star hD hM h_symm ha_star m r B]
  unfold harmonicSupport
  noncomm_ring

theorem interShell_chiralSupport_star (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    (h_symm : star (projection a d) = projection a d)
    (ha_star : star a = a) (m r : ℕ) (B : R) :
    star (chiralSupport (interShellPeirceCorner a d M m r) B) =
      -chiralSupport (interShellPeirceCorner a d M r m) (star B) := by
  rw [chiralSupport, star_sub,
    interShell_exactSupport_star hD hM h_symm ha_star m r B,
    interShell_coexactSupport_star hD hM h_symm ha_star m r B]
  unfold chiralSupport
  abel

theorem interShell_normalizedDirac_star (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    (h_symm : star (projection a d) = projection a d)
    (ha_star : star a = a) (m r : ℕ) (B : R) :
    star (normalizedDirac (interShellPeirceCorner a d M m r) B) =
      normalizedDirac (interShellPeirceCorner a d M r m) (star B) := by
  have hD_star : star (interShellPeirceCorner a d M m r) =
      interShellPeirceCorner a d M r m :=
    interShellPeirceCorner_star hD hM h_symm ha_star m r
  unfold normalizedDirac
  rw [star_add, hD_star]

private theorem star_jordanMul [StarModule ℝ R] (x y : R) :
    star (jordanMul x y) = jordanMul (star x) (star y) := by
  unfold jordanMul
  simp only [star_smul, star_add, star_mul]
  congr 1
  abel

/-- The normalized local Jordan associator transports to the reversed shell
corner under the involution.  The reverse order introduced by `star_mul` is
absorbed by commutativity of the Jordan product. -/
theorem interShell_jordan_associator_star (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    (h_symm : star (projection a d) = projection a d)
    (ha_star : star a = a) (m r : ℕ) (B : R) [StarModule ℝ R] :
    star (jordanMul
      (jordanMul (interShellPeirceCorner a d M m r)
        (interShellPeirceCorner a d M m r)) B -
      jordanMul (interShellPeirceCorner a d M m r)
        (jordanMul (interShellPeirceCorner a d M m r) B)) =
      jordanMul
        (jordanMul (interShellPeirceCorner a d M r m)
          (interShellPeirceCorner a d M r m)) (star B) -
      jordanMul (interShellPeirceCorner a d M r m)
        (jordanMul (interShellPeirceCorner a d M r m) (star B)) := by
  let D := interShellPeirceCorner a d M m r
  let D' := interShellPeirceCorner a d M r m
  have hD_star : star D = D' := by
    exact interShellPeirceCorner_star hD hM h_symm ha_star m r
  rw [star_sub, star_jordanMul, star_jordanMul, star_jordanMul,
    star_jordanMul, hD_star]

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

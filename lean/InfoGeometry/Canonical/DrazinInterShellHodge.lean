/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.DrazinShellCascade
import InfoGeometry.Core.PeirceDecomposition
import InfoGeometry.Singular.SquareZeroChiralHodge
import InfoGeometry.Singular.MoorePenroseCanonicalBridge
import InfoGeometry.Singular.MoorePenroseCornerSupport

/-!
# Inter-shell Peirce blocks and their chiral Hodge--Dirac structure

Given a Drazin inverse `d` of index `k` for `a`, the dressed shell projectors
`S m = E_N * Q_m * E_N` form a mutually orthogonal idempotent family summing to
`E_N`.  The inter-shell Peirce block

`d_{m,r} = S_m * a * S_r`

is strictly lower triangular: it vanishes for `m ≤ r`.  For every distinct pair
`m ≠ r` it is square-zero, because `S_r * S_m = 0`.  If `B` is a Moore--Penrose
inverse of `d_{m,r}`, then the local pair `(d_{m,r}, B)` carries the full
square-zero chiral Hodge--Dirac package of
`InfoGeometry.Singular.SquareZeroChiralHodge`: the two supports are orthogonal
idempotents, the harmonic complement is their kernel, the chiral grading is a
tripotent, and the normalized operator anticommutes with it.

The local supports are absorbed by the shell projectors:
`S_m * P₊ = P₊` and `P₋ * S_r = P₋`.  This is the shell-local form of the
strictly triangular Peirce filtration.
The inverse itself obeys `star S_r * B * star S_m = B`. The adjoints are
essential for oblique shells; the unstarred reverse-corner formula does not
follow from shell idempotence and mutual annihilation.

All statements are over an arbitrary star ring.  No commutativity,
diagonalizability, symmetry of `E_N`, finite dimensionality, or nonzeroness of
a shell is assumed.  The Drazin index is a witness, not a minimality claim.
The normalized local operator `d_{m,r} + B` is not identified with a metric
Hodge--Dirac operator unless `B = star d_{m,r}` is supplied separately.
-/

namespace InfoGeometry.Canonical.DrazinNilpotentShell

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Singular.MoorePenrose
  (exactSupport coexactSupport SquareZeroChiralHodge)

variable {R : Type*} [Ring R] [StarRing R]

section Drazin

variable {a d : R} {k : ℕ}

/-- The inter-shell Peirce block `d_{m,r} = S_m * a * S_r`. -/
def interShellPeirceCorner (a d : R) (M : ℕ → R) (m r : ℕ) : R :=
  drazinShellProj a d M m * a * drazinShellProj a d M r

/-- In the self-adjoint Drazin setting, involution reverses the source and
target shells of an inter-shell Peirce corner. -/
theorem interShellPeirceCorner_star
    (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    (h_symm : star (projection a d) = projection a d)
    (ha_star : star a = a) (m r : ℕ) :
    star (interShellPeirceCorner a d M m r) =
      interShellPeirceCorner a d M r m := by
  have h_complementary_symm :
      star (complementaryProjection a d) = complementaryProjection a d := by
    unfold complementaryProjection
    rw [star_sub, star_one, h_symm]
  unfold interShellPeirceCorner
  rw [star_mul, star_mul,
    drazinShellProj_selfAdjoint hD hM h_complementary_symm r,
    ha_star,
    drazinShellProj_selfAdjoint hD hM h_complementary_symm m]
  noncomm_ring

/-- The inter-shell block is square-zero for every pair of distinct shells. -/
theorem interShellPeirceCorner_sq_eq_zero (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    {m r : ℕ} (hne : m ≠ r) :
    interShellPeirceCorner a d M m r * interShellPeirceCorner a d M m r = 0 := by
  simpa [interShellPeirceCorner, peirceCorner] using
    peirceCorner_sq_eq_zero
      (p := drazinShellProj a d M m)
      (q := drazinShellProj a d M r)
      (x := a)
      (drazinShellProj_orthogonal hD hM hne.symm)

/-- The strictly triangular direction: `d_{m,r} = 0` for `m ≤ r`. -/
theorem interShellPeirceCorner_eq_zero_of_le (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    {m r : ℕ} (hmr : m ≤ r) :
    interShellPeirceCorner a d M m r = 0 :=
  drazinShellProj_mul_a_mul_drazinShellProj_eq_zero_of_le hD hM hmr

/-- The inter-shell block is left-absorbed by `S_m` and right-absorbed by
`S_r`. -/
theorem interShellPeirceCorner_shell_localization (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    (m r : ℕ) :
    drazinShellProj a d M m * interShellPeirceCorner a d M m r =
      interShellPeirceCorner a d M m r ∧
    interShellPeirceCorner a d M m r * drazinShellProj a d M r =
      interShellPeirceCorner a d M m r := by
  constructor
  · simpa [interShellPeirceCorner, peirceCorner] using
      peirceCorner_absorb_left
        (p := drazinShellProj a d M m)
        (q := drazinShellProj a d M r)
        (x := a)
        (drazinShellProj_idem hD hM m)
  · simpa [interShellPeirceCorner, peirceCorner] using
      peirceCorner_absorb_right
        (p := drazinShellProj a d M m)
        (q := drazinShellProj a d M r)
        (x := a)
        (drazinShellProj_idem hD hM r)

/-- The Moore–Penrose inverse is supported in the reverse corner of the
adjoint shells. This remains valid for oblique Drazin shells and for equal
shell indices; no self-adjointness or nonzero-block assumption is needed. -/
theorem interShell_inverse_adjoint_shell_localization
    (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    (m r : ℕ) {B : R}
    (hB : InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse
      (interShellPeirceCorner a d M m r) B) :
    star (drazinShellProj a d M r) * B = B ∧
    B * star (drazinShellProj a d M m) = B ∧
    star (drazinShellProj a d M r) * B *
      star (drazinShellProj a d M m) = B := by
  obtain ⟨hleft, hright⟩ := interShellPeirceCorner_shell_localization hD hM m r
  exact ⟨hB.toSingular.star_left_absorption hright,
    hB.toSingular.star_right_absorption hleft,
    hB.toSingular.adjoint_reverse_corner hleft hright⟩

/-- The exact support of an inter-shell block is left-supported on `S_m`. -/
theorem drazinShellProj_mul_interShellExactSupport
    (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    (m r : ℕ) (B : R) :
    drazinShellProj a d M m *
        exactSupport (interShellPeirceCorner a d M m r) B =
      exactSupport (interShellPeirceCorner a d M m r) B := by
  rw [exactSupport, ← mul_assoc,
    (interShellPeirceCorner_shell_localization hD hM m r).1]

/-- The coexact support of an inter-shell block is right-supported on `S_r`. -/
theorem interShellCoexactSupport_mul_drazinShellProj
    (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    (m r : ℕ) (B : R) :
    coexactSupport (interShellPeirceCorner a d M m r) B *
        drazinShellProj a d M r =
      coexactSupport (interShellPeirceCorner a d M m r) B := by
  rw [coexactSupport, mul_assoc,
    (interShellPeirceCorner_shell_localization hD hM m r).2]

/-- **Double-sum shell reconstruction.**  The core term and the strictly lower
triangular inter-shell blocks reconstruct the full operator. -/
theorem drazin_core_and_double_sum_shell_cascade (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M) :
    a = projection a d * a * projection a d +
        ∑ m ∈ Finset.range k, ∑ r ∈ Finset.range m,
          interShellPeirceCorner a d M m r := by
  calc
    a = projection a d * a * projection a d +
        ∑ m ∈ Finset.range k,
          drazinShellProj a d M m * a *
            (∑ r ∈ Finset.range m, drazinShellProj a d M r) :=
      drazin_core_and_shell_cascade hD hM
    _ = projection a d * a * projection a d +
        ∑ m ∈ Finset.range k, ∑ r ∈ Finset.range m,
          interShellPeirceCorner a d M m r := by
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum]
      rfl

/-- The full triangular Peirce reconstruction, under the descriptive name used
in the canonical matrix formulation.  The core block is `E_C * a * E_C` and the
remaining terms are precisely the strictly lower-triangular inter-shell blocks. -/
theorem full_operator_triangular_peirce_reconstruction
    (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M) :
    a = projection a d * a * projection a d +
        ∑ m ∈ Finset.range k, ∑ r ∈ Finset.range m,
          interShellPeirceCorner a d M m r :=
  drazin_core_and_double_sum_shell_cascade hD hM

/-- **Local inter-shell chiral Hodge--Dirac theorem.**
For a Drazin pair and an inter-shell block `d_{m,r}` with `m ≠ r`, any
Moore--Penrose inverse `B` of `d_{m,r}` yields:
1. `d_{m,r}` and `B` are square-zero;
2. `d_{m,r} = 0` for `m ≤ r`;
3. `S_m` absorbs the exact support and `S_r` absorbs the coexact support;
4. the full square-zero chiral Hodge--Dirac package holds for `(d_{m,r}, B)`.

The last item includes the orthogonal idempotent partition of unity, the
harmonic kernel, the tripotent chiral grading, and the anticommutation with the
normalized local operator. -/
theorem interShell_chiralHodge_decomposition (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    {m r : ℕ} (hne : m ≠ r) {B : R}
    (hB : InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse
      (interShellPeirceCorner a d M m r) B) :
    let D := interShellPeirceCorner a d M m r
    (D * D = 0 ∧ B * B = 0) ∧
    (m ≤ r → D = 0) ∧
    (drazinShellProj a d M m * exactSupport D B = exactSupport D B ∧
      coexactSupport D B * drazinShellProj a d M r = coexactSupport D B) ∧
    SquareZeroChiralHodge D B := by
  intro D
  have hd_sq : D * D = 0 :=
    interShellPeirceCorner_sq_eq_zero hD hM hne
  have hB' : InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse D B :=
    hB.toSingular
  have hB_sq : B * B = 0 := hB'.inverse_sq_eq_zero hd_sq
  refine ⟨⟨hd_sq, hB_sq⟩, ?_, ?_, ?_⟩
  · intro hmr
    exact interShellPeirceCorner_eq_zero_of_le hD hM hmr
  · exact ⟨drazinShellProj_mul_interShellExactSupport hD hM m r B,
      interShellCoexactSupport_mul_drazinShellProj hD hM m r B⟩
  · exact InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse.squareZero_chiralHodge_decomposition
      hB' hd_sq

/-- In the self-adjoint Drazin setting, the complete local Hodge package
transports to the reversed shell corner with inverse `star B`. -/
theorem interShell_chiralHodge_decomposition_star
    (hD : IsDrazinInverse a d k)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a d) M)
    (h_symm : star (projection a d) = projection a d)
    (ha_star : star a = a) (m r : ℕ) (hne : m ≠ r) (B : R)
    (hB : InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse
      (interShellPeirceCorner a d M m r) B) :
    SquareZeroChiralHodge (interShellPeirceCorner a d M r m) (star B) := by
  let D := interShellPeirceCorner a d M m r
  have hD_sq : D * D = 0 := by
    exact interShellPeirceCorner_sq_eq_zero hD hM hne
  have hstarD_sq : star D * star D = 0 := by
    simpa only [star_mul, star_zero] using congrArg star hD_sq
  have hB_singular : InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse D B :=
    hB.toSingular
  have hB_star := hB_singular.star_same_order
  have hcorner_star : star D = interShellPeirceCorner a d M r m := by
    exact interShellPeirceCorner_star hD hM h_symm ha_star m r
  simpa [D, hcorner_star] using
    (InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse.squareZero_chiralHodge_decomposition
      hB_star hstarD_sq)

end Drazin

end InfoGeometry.Canonical.DrazinNilpotentShell

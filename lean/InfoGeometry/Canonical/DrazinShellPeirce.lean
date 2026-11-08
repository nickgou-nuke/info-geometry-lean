/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InfoGeometry.Canonical.DrazinShellCascade
import InfoGeometry.Singular.MoorePenroseSquareZero

/-!
# Local square-zero Moore-Penrose structure of Drazin shell corners

The global shells and the strictly lowering action come from the existing
owners. A corner is square-zero even when the whole nilpotent part is not.
Its MP inverse is an explicit additional hypothesis. One-sided support
localization is valid for oblique shells; no unsupported reverse-corner,
centrality, or self-adjointness claim is made for the shells themselves.
-/
namespace InfoGeometry.Canonical.DrazinShellPeirce

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.DrazinObliqueShellResolution
open InfoGeometry.Canonical.DrazinShellCascade
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.MoorePenroseSquareZero
open InfoGeometry.Algebra.PeirceRegularityIdentities
open scoped BigOperators

variable {R : Type*} [Ring R] {a d : R} {k : ℕ}

/-- The inner regularity defect of a Drazin inverse is exactly its nilpotent part. -/
theorem regularity_defect_eq_nilpotent (hD : IsDrazinInverse a d k) :
    a - a * d * a = nilpotent a d := by
  rw [nilpotent_eq_mul_complementaryProjection]
  unfold complementaryProjection projection
  calc
    a - a * d * a = a - a * (d * a) := by rw [mul_assoc]
    _ = a - a * (a * d) := by rw [← hD.comm]
    _ = a * (1 - a * d) := by noncomm_ring

/-- Uniform exponent bound, also valid at witness exponent zero. -/
theorem regularity_defect_pow_succ (hD : IsDrazinInverse a d k) :
    (a - a * d * a) ^ (k + 1) = 0 := by
  rw [regularity_defect_eq_nilpotent hD, nilpotent_eq_mul_complementaryProjection]
  exact fittingNilpotentPart_pow_succ_eq_zero hD

variable [StarRing R] {g : ℕ → R}

/-- The actual inter-shell Peirce corner, using the existing dressed shells. -/
def shellCorner (a d : R) (g : ℕ → R) (i j : ℕ) : R :=
  dressedShell a d g i * a * dressedShell a d g j

/-- Off-diagonal square-zero needs only the already established shell products. -/
theorem shellCorner_square_zero (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent a d ^ m) (g m))
    {i j : ℕ} (hij : i ≠ j) :
    shellCorner a d g i j * shellCorner a d g i j = 0 :=
  corner_square_zero _ _ _ (dressedShell_mul_eq_zero hD hg hij.symm)

/-- The existing cascade removes every diagonal or upward corner. -/
theorem shellCorner_eq_zero_of_le (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent a d ^ m) (g m))
    {i j : ℕ} (hij : i ≤ j) : shellCorner a d g i j = 0 :=
  shell_step_block_zero hD hg hij

/-- Source and target Peirce absorption, without star assumptions on the shells. -/
theorem shellCorner_localization (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent a d ^ m) (g m)) (i j : ℕ) :
    dressedShell a d g i * shellCorner a d g i j = shellCorner a d g i j ∧
    shellCorner a d g i j * dressedShell a d g j = shellCorner a d g i j := by
  have hi := dressedShell_idempotent hD hg i
  have hj := dressedShell_idempotent hD hg j
  constructor
  · unfold shellCorner
    rw [← mul_assoc, ← mul_assoc, hi]
  · unfold shellCorner
    rw [mul_assoc, hj]

/-- One-sided localization of the MP supports actually needs no inverse law. -/
theorem corner_support_localization (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent a d ^ m) (g m))
    (i j : ℕ) (b : R) :
    dressedShell a d g i * (shellCorner a d g i j * b) = shellCorner a d g i j * b ∧
    (b * shellCorner a d g i j) * dressedShell a d g j = b * shellCorner a d g i j := by
  obtain ⟨hl, hr⟩ := shellCorner_localization hD hg i j
  constructor
  · rw [← mul_assoc, hl]
  · rw [mul_assoc, hr]

/-- Finite triangular reconstruction, derived rather than re-proving the filtration. -/
theorem full_operator_triangular_peirce_reconstruction (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent a d ^ m) (g m)) :
    a = projection a d * a * projection a d +
      ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range i, shellCorner a d g i j := by
  have hc : projection a d * a * projection a d = projection a d * a := by
    rw [mul_assoc, ← projection_comm_self hD, ← mul_assoc, projection_is_idempotent hD]
  simpa only [hc, Finset.mul_sum, shellCorner] using operator_cascade hD hg

/-- The zero Drazin inverse of every off-diagonal corner is an actual witness. -/
theorem shellCorner_drazin_zero (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent a d ^ m) (g m))
    {i j : ℕ} (hij : i ≠ j) : IsDrazinInverse (shellCorner a d g i j) 0 2 := by
  have hz := shellCorner_square_zero hD hg hij
  refine ⟨by simp, by simp, ?_⟩
  simp only [mul_zero, pow_two, hz]

/-- Apply the square-zero theory to each actual inter-shell corner.
The inverse b is supplied by the native MP predicate, not manufactured by a
reverse-order pseudoinverse rule. The final localization remains one-sided. -/
theorem corner_mp_graded_structure (hD : IsDrazinInverse a d k)
    (hg : ∀ m, IsMoorePenroseInverse (nilpotent a d ^ m) (g m))
    {i j : ℕ} (hij : i ≠ j) {b : R}
    (hb : IsMoorePenroseInverse (shellCorner a d g i j) b) :
    let c := shellCorner a d g i j
    (c * c = 0 ∧ b * b = 0) ∧
    (IsStarProjection (c * b) ∧ IsStarProjection (b * c) ∧
      IsStarProjection (1 - (c * b + b * c))) ∧
    ((c * b) * (b * c) = 0 ∧ (b * c) * (c * b) = 0) ∧
    ((c + b) * (c + b) = c * b + b * c) ∧
    ((c * b - b * c) * (c * b - b * c) = c * b + b * c) ∧
    ((c * b - b * c) * (c * b - b * c) * (c * b - b * c) = c * b - b * c) ∧
    ((c * b - b * c) * (c + b) + (c + b) * (c * b - b * c) = 0) ∧
    (dressedShell a d g i * (c * b) = c * b ∧
      (b * c) * dressedShell a d g j = b * c) := by
  dsimp only
  have hc := shellCorner_square_zero hD hg hij
  exact ⟨⟨hc, inverse_square_zero hb hc⟩, three_star_projections hb hc,
    supports_orthogonal hb hc, sum_square hb hc, grading_square hb hc,
    grading_cube hb hc, grading_anticommutes_sum hb hc,
    corner_support_localization hD hg i j b⟩

end InfoGeometry.Canonical.DrazinShellPeirce

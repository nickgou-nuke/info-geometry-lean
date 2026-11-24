/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.HessianThermodynamicManifold

/-!
# Projective incidence defects and three-point holonomy

On a scalar affine chart, the primal--dual incidence pairing is `η * θ`.
The defect is the Fenchel slack
`ψ θ + ψ⋆ η - η θ`.  The identities below are algebraic: they do not turn an
affine chart into a projective quotient, and contact/orthogonality hypotheses
are kept explicit when passing from the cocycle identity to additivity.
-/

namespace InfoGeometry.Projective.ProjectiveIncidenceDefect

open InfoGeometry.Algebra.HessianThermodynamicManifold
open scoped BigOperators

/-- Fenchel/ incidence defect at a primal coordinate and a dual coordinate. -/
def projectiveIncidenceDefect
    (ψ ψStar : ℝ → ℝ) (θ η : ℝ) : ℝ :=
  ψ θ + ψStar η - η * θ

/-- Legendre contact makes the incidence defect vanish. -/
theorem projectiveIncidenceDefect_eq_zero_of_legendre_contact
    (ψ ψStar grad : ℝ → ℝ)
    (pair : FenchelDualPair ψ ψStar grad) (θ : ℝ) :
    projectiveIncidenceDefect ψ ψStar θ (grad θ) = 0 := by
  unfold projectiveIncidenceDefect
  have h := pair.legendre_identity θ
  simpa [InnerSpace.inner] using sub_eq_zero.mpr h

/-- Three-point cocycle identity for incidence defects. -/
theorem projectiveIncidenceDefect_three_point_cocycle
    (ψ ψStar : ℝ → ℝ) (θ₁ θ₂ : ℝ) (η₂ η₃ : ℝ) :
    projectiveIncidenceDefect ψ ψStar θ₁ η₃ =
      projectiveIncidenceDefect ψ ψStar θ₁ η₂ +
        projectiveIncidenceDefect ψ ψStar θ₂ η₃ -
          projectiveIncidenceDefect ψ ψStar θ₂ η₂ +
            (η₂ - η₃) * (θ₁ - θ₂) := by
  unfold projectiveIncidenceDefect
  ring

/-- Additivity follows from contact at the intermediate point and orthogonality
of the intermediate primal/dual displacement. -/
theorem projectiveIncidenceDefect_additive_of_orthogonal
    (ψ ψStar : ℝ → ℝ) (θ₁ θ₂ : ℝ) (η₂ η₃ : ℝ)
    (hcontact : projectiveIncidenceDefect ψ ψStar θ₂ η₂ = 0)
    (horth : (η₂ - η₃) * (θ₁ - θ₂) = 0) :
    projectiveIncidenceDefect ψ ψStar θ₁ η₃ =
      projectiveIncidenceDefect ψ ψStar θ₁ η₂ +
        projectiveIncidenceDefect ψ ψStar θ₂ η₃ := by
  rw [projectiveIncidenceDefect_three_point_cocycle]
  rw [hcontact, horth]
  ring

/-- Triangle holonomy: all potential values cancel, leaving only the
bilinear point--hyperplane pairings. -/
theorem projectiveIncidenceDefect_triangle_holonomy
    (ψ ψStar : ℝ → ℝ)
    (θ₁ θ₂ θ₃ η₁ η₂ η₃ : ℝ) :
    projectiveIncidenceDefect ψ ψStar θ₁ η₂ +
        projectiveIncidenceDefect ψ ψStar θ₂ η₃ +
        projectiveIncidenceDefect ψ ψStar θ₃ η₁ -
      (projectiveIncidenceDefect ψ ψStar θ₁ η₁ +
        projectiveIncidenceDefect ψ ψStar θ₂ η₂ +
        projectiveIncidenceDefect ψ ψStar θ₃ η₃) =
      η₁ * (θ₁ - θ₃) + η₂ * (θ₂ - θ₁) + η₃ * (θ₃ - θ₂) := by
  unfold projectiveIncidenceDefect
  ring

/-- Telescoping multi-state cocycle.  The change of the incidence defect when the dual
coordinate moves from `η 0` to `η n` at the fixed base point `θ 0` is the sum of the
local three-point cocycle increments along the chain `θ 0, θ 1, …, θ n`. -/
theorem projectiveIncidenceDefect_chain_cocycle
    (ψ ψStar : ℝ → ℝ) (n : ℕ) (θ η : ℕ → ℝ) :
    projectiveIncidenceDefect ψ ψStar (θ 0) (η n) -
        projectiveIncidenceDefect ψ ψStar (θ 0) (η 0) =
      ∑ i ∈ Finset.range n,
        (projectiveIncidenceDefect ψ ψStar (θ (i + 1)) (η (i + 1)) -
          projectiveIncidenceDefect ψ ψStar (θ (i + 1)) (η i) +
            (η i - η (i + 1)) * (θ 0 - θ (i + 1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      have h := projectiveIncidenceDefect_three_point_cocycle
        ψ ψStar (θ 0) (θ (n + 1)) (η n) (η (n + 1))
      rw [h]
      ring

/-- Generalized Pythagorean additivity across an arbitrary finite chain.  Contact at
each intermediate state `(θ i, η i)` and orthogonality of each displacement from the
base point make the defect at the final dual point the sum of the successive
off-diagonal defects. -/
theorem projectiveIncidenceDefect_chain_additive_of_orthogonal
    (ψ ψStar : ℝ → ℝ) (n : ℕ) (θ η : ℕ → ℝ)
    (hcontact : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      projectiveIncidenceDefect ψ ψStar (θ i) (η i) = 0)
    (horth : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      (η i - η (i + 1)) * (θ 0 - θ i) = 0) :
    projectiveIncidenceDefect ψ ψStar (θ 0) (η (n + 1)) =
      ∑ i ∈ Finset.range (n + 1),
        projectiveIncidenceDefect ψ ψStar (θ i) (η (i + 1)) := by
  revert hcontact horth
  induction n with
  | zero =>
      intro hcontact horth
      simp
  | succ n ih =>
      intro hcontact horth
      have hct : ∀ i : ℕ, 1 ≤ i → i ≤ n →
          projectiveIncidenceDefect ψ ψStar (θ i) (η i) = 0 :=
        fun i hi hin => hcontact i hi (Nat.le_trans hin (Nat.le_succ n))
      have hort : ∀ i : ℕ, 1 ≤ i → i ≤ n →
          (η i - η (i + 1)) * (θ 0 - θ i) = 0 :=
        fun i hi hin => horth i hi (Nat.le_trans hin (Nat.le_succ n))
      rw [Finset.sum_range_succ, ← ih hct hort]
      have h := projectiveIncidenceDefect_three_point_cocycle
        ψ ψStar (θ 0) (θ (n + 1)) (η (n + 1)) (η (n + 2))
      have hc := hcontact (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) le_rfl
      have ho := horth (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) le_rfl
      rw [h, hc, ho]
      ring

/-- Closed polygonal-loop holonomy.  Around any finite cycle indexed by `Fin n`,
the potentials `ψ` and `ψStar` cancel identically and the circulation of incidence
defects is a sum of bilinear point--hyperplane pairings only. -/
theorem projectiveIncidenceDefect_closed_loop_holonomy
    (ψ ψStar : ℝ → ℝ) (n : ℕ) (θ η : Fin n → ℝ) :
    (∑ i : Fin n, projectiveIncidenceDefect ψ ψStar (θ i) (η (finRotate n i))) -
        (∑ i : Fin n, projectiveIncidenceDefect ψ ψStar (θ i) (η i)) =
      ∑ i : Fin n, η (finRotate n i) * (θ (finRotate n i) - θ i) := by
  classical
  have hψ : (∑ i : Fin n, ψStar (η (finRotate n i))) =
      ∑ i : Fin n, ψStar (η i) := by
    exact Equiv.sum_comp (finRotate n) (fun i : Fin n => ψStar (η i))
  have hηθ : (∑ i : Fin n, η (finRotate n i) * θ (finRotate n i)) =
      ∑ i : Fin n, η i * θ i := by
    exact Equiv.sum_comp (finRotate n) (fun i : Fin n => η i * θ i)
  have hA :
      (∑ i : Fin n, (ψ (θ i) + ψStar (η (finRotate n i)) - η (finRotate n i) * θ i)) -
          (∑ i : Fin n, (ψ (θ i) + ψStar (η i) - η i * θ i)) =
        -((∑ i : Fin n, η (finRotate n i) * θ i) - (∑ i : Fin n, η i * θ i)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hψ]
    ring
  have hB :
      (∑ i : Fin n, η (finRotate n i) * (θ (finRotate n i) - θ i)) =
        (∑ i : Fin n, η i * θ i) - (∑ i : Fin n, η (finRotate n i) * θ i) := by
    calc
      (∑ i : Fin n, η (finRotate n i) * (θ (finRotate n i) - θ i))
          = ∑ i : Fin n, (η (finRotate n i) * θ (finRotate n i) -
              η (finRotate n i) * θ i) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
      _ = (∑ i : Fin n, η (finRotate n i) * θ (finRotate n i)) -
            (∑ i : Fin n, η (finRotate n i) * θ i) := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ i : Fin n, η i * θ i) -
            (∑ i : Fin n, η (finRotate n i) * θ i) := by
              rw [hηθ]
  unfold projectiveIncidenceDefect
  rw [hA, hB]
  ring

/-- Vanishing holonomy of a closed incidence loop.  If each dual hyperplane is incident
with its own primal point and with the preceding primal point of the cycle, the bilinear
pairings collapse to a telescoping difference of the primal potential, so the
diagonal-referenced circulation is zero. -/
theorem projectiveIncidenceDefect_closed_incidence_loop_holonomy_eq_zero
    (ψ ψStar : ℝ → ℝ) (n : ℕ) (θ η : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, projectiveIncidenceDefect ψ ψStar (θ i) (η i) = 0)
    (hprev : ∀ i : Fin n,
      projectiveIncidenceDefect ψ ψStar (θ ((finRotate n).symm i)) (η i) = 0) :
    (∑ i : Fin n, projectiveIncidenceDefect ψ ψStar (θ i) (η (finRotate n i))) -
        (∑ i : Fin n, projectiveIncidenceDefect ψ ψStar (θ i) (η i)) = 0 := by
  classical
  rw [projectiveIncidenceDefect_closed_loop_holonomy]
  have hshift :
      (∑ i : Fin n, η (finRotate n i) * (θ (finRotate n i) - θ i)) =
        ∑ i : Fin n, η i * (θ i - θ ((finRotate n).symm i)) := by
    let σ : Equiv.Perm (Fin n) := finRotate n
    change (∑ i : Fin n, η (σ i) * (θ (σ i) - θ i)) =
      ∑ i : Fin n, η i * (θ i - θ (σ.symm i))
    calc
      (∑ i : Fin n, η (σ i) * (θ (σ i) - θ i))
          = ∑ i : Fin n, η (σ i) * (θ (σ i) - θ (σ.symm (σ i))) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Equiv.symm_apply_apply]
      _ = ∑ i : Fin n, η i * (θ i - θ (σ.symm i)) := by
              exact Equiv.sum_comp σ (fun j : Fin n => η j * (θ j - θ (σ.symm j)))
  rw [hshift]
  have hterm : ∀ i : Fin n,
      η i * (θ i - θ ((finRotate n).symm i)) =
        ψ (θ i) - ψ (θ ((finRotate n).symm i)) := by
    intro i
    have hd := hdiag i
    have hp := hprev i
    unfold projectiveIncidenceDefect at hd hp
    ring_nf at hd hp ⊢
    linarith
  calc
    (∑ i : Fin n, η i * (θ i - θ ((finRotate n).symm i)))
        = ∑ i : Fin n, (ψ (θ i) - ψ (θ ((finRotate n).symm i))) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i
    _ = 0 := by
      have hcomp := Equiv.sum_comp ((finRotate n).symm) (fun i : Fin n => ψ (θ i))
      rw [Finset.sum_sub_distrib, hcomp]
      ring

/-- The general closed-loop holonomy at cycle length three reproduces the
triangle-holonomy identity, up to reordering the three summands. -/
theorem projectiveIncidenceDefect_closed_loop_holonomy_three
    (ψ ψStar : ℝ → ℝ) (θ η : Fin 3 → ℝ) :
    (∑ i : Fin 3, projectiveIncidenceDefect ψ ψStar (θ i) (η (finRotate 3 i))) -
        (∑ i : Fin 3, projectiveIncidenceDefect ψ ψStar (θ i) (η i)) =
      η 0 * (θ 0 - θ 2) + η 1 * (θ 1 - θ 0) + η 2 * (θ 2 - θ 1) := by
  rw [projectiveIncidenceDefect_closed_loop_holonomy]
  norm_num [Fin.sum_univ_three, finRotate_apply]
  ring

end InfoGeometry.Projective.ProjectiveIncidenceDefect

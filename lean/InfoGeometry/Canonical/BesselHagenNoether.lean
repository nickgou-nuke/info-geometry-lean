/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Bessel--Hagen currents for a divergence symmetry

This module proves the algebraic integration-by-parts identity underlying the
first-order Noether theorem with a boundary term. The coefficient carrier is a
commutative real algebra, and all differentiations use Mathlib's `Derivation`.

The inputs `L_u` and `p` are the zeroth- and first-jet variational coefficients.
Their realization as derivatives of a particular Lagrangian is separate from
the algebraic identity proved here. The characteristic `Q` is an evolutionary
variation; any coordinate variation has already been incorporated in `Q` and
the supplied boundary current. No integration theorem or noncommutative
operator-field interpretation is asserted.

Source: E. Bessel-Hagen, *Über die Erhaltungssätze der Elektrodynamik* (1921),
§1, equations (5)--(7), pp. 4--5 of the supplied English translation.
-/

noncomputable section

namespace InfoGeometry.Canonical.BesselHagenNoether

open scoped BigOperators

variable {A ι κ : Type*} [CommRing A] [Algebra ℝ A]
variable [Fintype ι] [Fintype κ]

/-- Divergence with respect to a finite family of real derivations. -/
def divergence (D : ι → Derivation ℝ A A) (J : ι → A) : A :=
  ∑ i, D i (J i)

/-- First variation written in terms of its zeroth- and first-jet coefficients. -/
def firstVariation (D : ι → Derivation ℝ A A)
    (L_u : κ → A) (p : ι → κ → A) (Q : κ → A) : A :=
  (∑ a, L_u a * Q a) + ∑ i, ∑ a, p i a * D i (Q a)

/-- Euler--Lagrange expression associated to the supplied variational coefficients. -/
def eulerLagrange (D : ι → Derivation ℝ A A)
    (L_u : κ → A) (p : ι → κ → A) (a : κ) : A :=
  L_u a - ∑ i, D i (p i a)

/-- Noether current corrected by the divergence-symmetry boundary term. -/
def correctedCurrent (p : ι → κ → A) (Q : κ → A) (B : ι → A) (i : ι) : A :=
  (∑ a, p i a * Q a) - B i

theorem divergence_add (D : ι → Derivation ℝ A A) (J K : ι → A) :
    divergence D (fun i => J i + K i) = divergence D J + divergence D K := by
  simp only [divergence, map_add, Finset.sum_add_distrib]

theorem divergence_sub (D : ι → Derivation ℝ A A) (J K : ι → A) :
    divergence D (fun i => J i - K i) = divergence D J - divergence D K := by
  simp only [divergence, map_sub, Finset.sum_sub_distrib]

/-- The product rule splits the canonical-current divergence into two jet contractions. -/
theorem divergence_correctedCurrent
    (D : ι → Derivation ℝ A A) (p : ι → κ → A) (Q : κ → A) (B : ι → A) :
    divergence D (correctedCurrent p Q B) =
      (∑ i, ∑ a, D i (p i a) * Q a) +
        (∑ i, ∑ a, p i a * D i (Q a)) - divergence D B := by
  have hproduct (i : ι) (a : κ) :
      D i (p i a * Q a) = D i (p i a) * Q a + p i a * D i (Q a) := by
    simp only [Derivation.leibniz, smul_eq_mul]
    ring
  simp only [divergence, correctedCurrent, map_sub, map_sum, hproduct,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Rearrangement of the Euler--Lagrange contraction as a finite double sum. -/
theorem eulerLagrange_contraction
    (D : ι → Derivation ℝ A A) (L_u : κ → A)
    (p : ι → κ → A) (Q : κ → A) :
    (∑ a, eulerLagrange D L_u p a * Q a) =
      (∑ a, L_u a * Q a) - ∑ i, ∑ a, D i (p i a) * Q a := by
  simp only [eulerLagrange, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Off-shell Bessel--Hagen identity, including the exact Euler--Lagrange defect. -/
theorem divergence_correctedCurrent_eq_firstVariation_sub_boundary_sub_euler
    (D : ι → Derivation ℝ A A) (L_u : κ → A)
    (p : ι → κ → A) (Q : κ → A) (B : ι → A) :
    divergence D (correctedCurrent p Q B) =
      firstVariation D L_u p Q - divergence D B -
        ∑ a, eulerLagrange D L_u p a * Q a := by
  rw [divergence_correctedCurrent, eulerLagrange_contraction]
  unfold firstVariation
  ring

/-- A divergence symmetry leaves only the negative Euler--Lagrange contraction. -/
theorem divergence_correctedCurrent_of_divergence_symmetry
    (D : ι → Derivation ℝ A A) (L_u : κ → A)
    (p : ι → κ → A) (Q : κ → A) (B : ι → A)
    (hsym : firstVariation D L_u p Q = divergence D B) :
    divergence D (correctedCurrent p Q B) =
      -∑ a, eulerLagrange D L_u p a * Q a := by
  rw [divergence_correctedCurrent_eq_firstVariation_sub_boundary_sub_euler, hsym]
  simp only [sub_self, zero_sub]

/-- The boundary-corrected current is conserved when the Euler--Lagrange expressions vanish. -/
theorem correctedCurrent_conserved
    (D : ι → Derivation ℝ A A) (L_u : κ → A)
    (p : ι → κ → A) (Q : κ → A) (B : ι → A)
    (hsym : firstVariation D L_u p Q = divergence D B)
    (heuler : ∀ a, eulerLagrange D L_u p a = 0) :
    divergence D (correctedCurrent p Q B) = 0 := by
  rw [divergence_correctedCurrent_of_divergence_symmetry D L_u p Q B hsym]
  simp only [heuler, zero_mul, Finset.sum_const_zero, neg_zero]

/-- The current added by an antisymmetric superpotential `U`. -/
def superpotentialCurrent (D : ι → Derivation ℝ A A) (U : ι → ι → A) (i : ι) : A :=
  ∑ j, D j (U i j)

/-- Commuting differentiations kill the double divergence of an antisymmetric tensor. -/
theorem divergence_superpotentialCurrent
    (D : ι → Derivation ℝ A A) (U : ι → ι → A)
    (hcomm : ∀ i j a, D i (D j a) = D j (D i a))
    (hskew : ∀ i j, U i j = -U j i) :
    divergence D (superpotentialCurrent D U) = 0 := by
  let s : A := ∑ i, ∑ j, D i (D j (U i j))
  have hneg : s = -s := by
    change (∑ i, ∑ j, D i (D j (U i j))) =
      -(∑ i, ∑ j, D i (D j (U i j)))
    calc
      (∑ i, ∑ j, D i (D j (U i j))) =
          ∑ j, ∑ i, D i (D j (U i j)) := Finset.sum_comm
      _ = ∑ i, ∑ j, -D i (D j (U i j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hskew j i, map_neg, map_neg, hcomm j i]
      _ = -(∑ i, ∑ j, D i (D j (U i j))) := by
        simp only [Finset.sum_neg_distrib]
  have hadd : s + s = 0 := by
    calc
      s + s = -s + s := congrArg (fun z => z + s) hneg
      _ = 0 := neg_add_cancel s
  have hzero : s = 0 := by
    calc
      s = (1 : ℝ) • s := (one_smul ℝ s).symm
      _ = (1 / 2 : ℝ) • (s + s) := by
        rw [smul_add, ← add_smul]
        norm_num
      _ = 0 := by rw [hadd, smul_zero]
  simpa only [divergence, superpotentialCurrent, map_sum] using hzero

/-- Antisymmetric superpotentials preserve the exact divergence, including off shell. -/
theorem divergence_add_superpotentialCurrent
    (D : ι → Derivation ℝ A A) (J : ι → A) (U : ι → ι → A)
    (hcomm : ∀ i j a, D i (D j a) = D j (D i a))
    (hskew : ∀ i j, U i j = -U j i) :
    divergence D (fun i => J i + superpotentialCurrent D U i) = divergence D J := by
  rw [divergence_add, divergence_superpotentialCurrent D U hcomm hskew, add_zero]

end InfoGeometry.Canonical.BesselHagenNoether

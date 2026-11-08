/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceExponentialModularSynthesis
import Mathlib.Tactic.NoncommRing

/-!
# Finite products of reversible Peirce gates

This module composes the already-proved square-zero Peirce Gaussian gates over
an arbitrary finite list. It proves algebraic two-sided invertibility of the
finite product. It does not define a Transformer, a tensor-network contraction,
an attention normalization, or an asymptotic runtime bound.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.MultiScalePeirceGateTower

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceExponentialModularSynthesis

variable {B : Type*} [Ring B]

/-- A scale gate formed from the existing upper and lower square-zero corner
unitizations. -/
def scaleGate (P : B) (x : B × B) : B :=
  upperCornerUnit P x.1 * lowerCornerUnit P x.2

/-- The polynomial candidate for the inverse of `scaleGate`. -/
def scaleGateInv (P : B) (x : B × B) : B :=
  lowerCornerUnit P (-x.2) * upperCornerUnit P (-x.1)

/-- The paired Peirce Gaussian and its explicit inverse are two-sided inverses
at each scale. This is the existing one-scale theorem with its factors named
for finite composition. -/
theorem scaleGate_two_sided_inverse {P : B} (hP : P * P = P) (x : B × B) :
    scaleGate P x * scaleGateInv P x = 1 ∧
      scaleGateInv P x * scaleGate P x = 1 := by
  rcases paired_corner_gaussian_and_inverse_laws hP x.1 x.2 with
    ⟨_, _, hRight, hLeft, _, _⟩
  exact ⟨hRight, hLeft⟩

/-- The group commutator of the two opposite Peirce unipotent gates has an
exact finite expansion. The cubic and quartic terms are retained; in general
the commutator is not just `1 + genSig`. -/
theorem peirce_gate_group_commutator_expansion {P A C : B}
    (hP : P * P = P) :
    upperCornerUnit P A * lowerCornerUnit P C *
        upperCornerUnit P (-A) * lowerCornerUnit P (-C) =
      1 + comm (conePlus P A) (coneMinus P C) -
        ((conePlus P A * coneMinus P C + coneMinus P C * conePlus P A) *
          (conePlus P A - coneMinus P C)) +
        (conePlus P A * coneMinus P C) * (conePlus P A * coneMinus P C) := by
  unfold upperCornerUnit lowerCornerUnit
  rw [conePlus_neg, coneMinus_neg]
  unfold comm conePlus coneMinus
  peirce_nf hP

/-- The same exact expansion expressed in the repository's `(Φ,J,V,Σ,Q₊)`
operator vocabulary. This is an algebraic normal form for the gate
commutator, not a conformal-net braiding theorem. -/
theorem peirce_gate_group_commutator_operator_form {P A C : B}
    (hP : P * P = P) :
    upperCornerUnit P A * lowerCornerUnit P C *
        upperCornerUnit P (-A) * lowerCornerUnit P (-C) =
      1 + genSig P A C - genV P A C * genJ P A C +
        qgtPlus P A C * qgtPlus P A C := by
  rw [peirce_gate_group_commutator_expansion hP]
  unfold genSig genV genJ anticomm comm qgtPlus conePlus coneMinus
  noncomm_ring

/-- Reversing the order of the two unipotent wings gives the inverse
commutator, with its own exact operator normal form. -/
theorem peirce_gate_reverse_group_commutator_operator_form {P A C : B}
    (hP : P * P = P) :
    lowerCornerUnit P C * upperCornerUnit P A *
        lowerCornerUnit P (-C) * upperCornerUnit P (-A) =
      1 - genSig P A C + genV P A C * genJ P A C +
        qgtMinus P A C * qgtMinus P A C := by
  unfold lowerCornerUnit upperCornerUnit
  rw [coneMinus_neg, conePlus_neg]
  unfold genSig genV genJ anticomm comm qgtMinus conePlus coneMinus
  peirce_nf hP

/-- Forward and reverse Peirce gate commutators cancel in either order. -/
theorem peirce_gate_group_commutators_are_inverse {P A C : B}
    (hP : P * P = P) :
    (upperCornerUnit P A * lowerCornerUnit P C *
        upperCornerUnit P (-A) * lowerCornerUnit P (-C)) *
        (lowerCornerUnit P C * upperCornerUnit P A *
          lowerCornerUnit P (-C) * upperCornerUnit P (-A)) = 1 ∧
    (lowerCornerUnit P C * upperCornerUnit P A *
        lowerCornerUnit P (-C) * upperCornerUnit P (-A)) *
        (upperCornerUnit P A * lowerCornerUnit P C *
          upperCornerUnit P (-A) * lowerCornerUnit P (-C)) = 1 := by
  let U := upperCornerUnit P A
  let Ui := upperCornerUnit P (-A)
  let L := lowerCornerUnit P C
  let Li := lowerCornerUnit P (-C)
  have hUUi : U * Ui = 1 := by
    dsimp [U, Ui, upperCornerUnit]
    rw [conePlus_neg]
    peirce_nf hP
  have hUiU : Ui * U = 1 := by
    dsimp [U, Ui, upperCornerUnit]
    rw [conePlus_neg]
    peirce_nf hP
  have hLLi : L * Li = 1 := by
    dsimp [L, Li, lowerCornerUnit]
    rw [coneMinus_neg]
    peirce_nf hP
  have hLiL : Li * L = 1 := by
    dsimp [L, Li, lowerCornerUnit]
    rw [coneMinus_neg]
    peirce_nf hP
  constructor
  · change (U * L * Ui * Li) * (L * U * Li * Ui) = 1
    calc
      (U * L * Ui * Li) * (L * U * Li * Ui) =
          U * L * Ui * Li * L * U * Li * Ui := by noncomm_ring
      _ = U * L * Ui * (Li * L) * U * Li * Ui := by noncomm_ring
      _ = U * L * Ui * 1 * U * Li * Ui := by rw [hLiL]
      _ = U * L * (Ui * U) * Li * Ui := by noncomm_ring
      _ = U * L * 1 * Li * Ui := by rw [hUiU]
      _ = U * (L * Li) * Ui := by noncomm_ring
      _ = U * 1 * Ui := by rw [hLLi]
      _ = U * Ui := by simp
      _ = 1 := hUUi
  · change (L * U * Li * Ui) * (U * L * Ui * Li) = 1
    calc
      (L * U * Li * Ui) * (U * L * Ui * Li) =
          L * U * Li * Ui * U * L * Ui * Li := by noncomm_ring
      _ = L * U * Li * (Ui * U) * L * Ui * Li := by noncomm_ring
      _ = L * U * Li * 1 * L * Ui * Li := by rw [hUiU]
      _ = L * U * (Li * L) * Ui * Li := by noncomm_ring
      _ = L * U * 1 * Ui * Li := by rw [hLiL]
      _ = L * (U * Ui) * Li := by noncomm_ring
      _ = L * 1 * Li := by rw [hUUi]
      _ = L * Li := by simp
      _ = 1 := hLLi

/-- Ordered product of the first `n` scale gates. Scale data contains its own
idempotent, so distinct levels may use distinct Peirce cuts. The newest scale
acts on the left. -/
def towerGate (scale : ℕ → B × (B × B)) : ℕ → B
  | 0 => 1
  | n + 1 =>
      scaleGate (scale n).1 (scale n).2 * towerGate scale n

/-- Candidate inverse of `towerGate`, with inverse factors in reverse order. -/
def towerGateInv (scale : ℕ → B × (B × B)) : ℕ → B
  | 0 => 1
  | n + 1 =>
      towerGateInv scale n *
        scaleGateInv (scale n).1 (scale n).2

/-- A finite ordered product of paired Peirce gates has the reversed product
of the polynomial gate inverses as a two-sided inverse. Each scale may use a
different idempotent; no commutation between different scales is assumed. -/
theorem towerGate_two_sided_inverse (scale : ℕ → B × (B × B))
    (hP : ∀ k, (scale k).1 * (scale k).1 = (scale k).1) :
    ∀ n, towerGate scale n * towerGateInv scale n = 1 ∧
      towerGateInv scale n * towerGate scale n = 1 := by
  intro n
  induction n with
  | zero =>
      simp [towerGate, towerGateInv]
  | succ n ih =>
      rcases scaleGate_two_sided_inverse (hP n) (scale n).2 with
        ⟨hGateRight, hGateLeft⟩
      refine ⟨?_, ?_⟩
      · calc
          towerGate scale (n + 1) * towerGateInv scale (n + 1) =
              scaleGate (scale n).1 (scale n).2 *
                (towerGate scale n * towerGateInv scale n) *
                scaleGateInv (scale n).1 (scale n).2 := by
                  simp only [towerGate, towerGateInv]
                  noncomm_ring
          _ = scaleGate (scale n).1 (scale n).2 * 1 *
                scaleGateInv (scale n).1 (scale n).2 := by rw [ih.1]
          _ = 1 := by simp [hGateRight]
      · calc
          towerGateInv scale (n + 1) * towerGate scale (n + 1) =
              towerGateInv scale n *
                (scaleGateInv (scale n).1 (scale n).2 *
                  scaleGate (scale n).1 (scale n).2) *
                towerGate scale n := by
                  simp only [towerGate, towerGateInv]
                  noncomm_ring
          _ = towerGateInv scale n * 1 * towerGate scale n := by rw [hGateLeft]
          _ = 1 := by simp [ih.2]

/-- Product of the `len` forward gates beginning at `start`. The gate at the
largest index in the segment acts outermost (on the left), matching
`towerGate`. -/
def segmentGate (scale : ℕ → B × (B × B)) (start : ℕ) : ℕ → B
  | 0 => 1
  | len + 1 =>
      scaleGate (scale (start + len)).1 (scale (start + len)).2 *
        segmentGate scale start len

/-- Inverse product for `segmentGate`, with inverse factors in the order
required to cancel the forward segment. -/
def segmentGateInv (scale : ℕ → B × (B × B)) (start : ℕ) : ℕ → B
  | 0 => 1
  | len + 1 =>
      segmentGateInv scale start len *
        scaleGateInv (scale (start + len)).1 (scale (start + len)).2

/-- The forward product on any contiguous finite segment has the displayed
two-sided inverse, assuming each scale's Peirce corner is defined by an
idempotent. -/
theorem segmentGate_two_sided_inverse (scale : ℕ → B × (B × B))
    (hP : ∀ k, (scale k).1 * (scale k).1 = (scale k).1)
    (start len : ℕ) :
    segmentGate scale start len * segmentGateInv scale start len = 1 ∧
      segmentGateInv scale start len * segmentGate scale start len = 1 := by
  induction len with
  | zero => simp [segmentGate, segmentGateInv]
  | succ len ih =>
      rcases scaleGate_two_sided_inverse (hP (start + len))
        (scale (start + len)).2 with ⟨hRight, hLeft⟩
      constructor
      · change
          (scaleGate (scale (start + len)).1 (scale (start + len)).2 *
              segmentGate scale start len) *
            (segmentGateInv scale start len *
              scaleGateInv (scale (start + len)).1 (scale (start + len)).2) = 1
        calc
          _ = scaleGate (scale (start + len)).1 (scale (start + len)).2 *
              (segmentGate scale start len * segmentGateInv scale start len) *
              scaleGateInv (scale (start + len)).1 (scale (start + len)).2 := by
                noncomm_ring
          _ = scaleGate (scale (start + len)).1 (scale (start + len)).2 * 1 *
              scaleGateInv (scale (start + len)).1 (scale (start + len)).2 := by
                rw [ih.1]
          _ = 1 := by simp [hRight]
      · change
          (segmentGateInv scale start len *
              scaleGateInv (scale (start + len)).1 (scale (start + len)).2) *
            (scaleGate (scale (start + len)).1 (scale (start + len)).2 *
              segmentGate scale start len) = 1
        calc
          _ = segmentGateInv scale start len *
              (scaleGateInv (scale (start + len)).1 (scale (start + len)).2 *
                scaleGate (scale (start + len)).1 (scale (start + len)).2) *
              segmentGate scale start len := by noncomm_ring
          _ = segmentGateInv scale start len * 1 *
              segmentGate scale start len := by rw [hLeft]
          _ = 1 := by simp [ih.2]

/-- Splitting the finite gate tower at stage `start`: the suffix acts on the
left of the prefix, consistent with the forward convention in `towerGate`. -/
theorem towerGate_add_split (scale : ℕ → B × (B × B)) (start len : ℕ) :
    towerGate scale (start + len) =
      segmentGate scale start len * towerGate scale start := by
  induction len with
  | zero => simp [segmentGate]
  | succ len ih =>
      rw [Nat.add_succ, towerGate, ih, segmentGate]
      noncomm_ring

/-- **Cut-state reconstruction.** If the state after `start + len` scale gates
is known, then the inverse of precisely the `len` gates after the cut recovers
the state after the first `start` gates. -/
theorem suffix_reconstructs_cut_state (scale : ℕ → B × (B × B))
    (hP : ∀ k, (scale k).1 * (scale k).1 = (scale k).1)
    (start len : ℕ) (x : B) :
    segmentGateInv scale start len *
        (towerGate scale (start + len) * x) = towerGate scale start * x := by
  rw [towerGate_add_split]
  calc
    segmentGateInv scale start len *
        (segmentGate scale start len * towerGate scale start * x) =
      segmentGateInv scale start len * segmentGate scale start len *
        towerGate scale start * x := by noncomm_ring
    _ = 1 * towerGate scale start * x := by
      rw [(segmentGate_two_sided_inverse scale hP start len).2]
    _ = towerGate scale start * x := by simp

/-- First variation of a single `scaleGate` with respect to `(dA, dC)`. -/
def scaleGateDiff (P : B) (x dx : B × B) : B :=
  conePlus P dx.1 * lowerCornerUnit P x.2 +
    upperCornerUnit P x.1 * coneMinus P dx.2

/-- **Single-scale nilpotent Maurer–Cartan reduction**:
the right-invariant differential `(dG) G⁻¹` of `scaleGate P (A, C)` eliminates
all lower-corner `C` dependence and reduces to quadratic conjugation by the
upper corner `conePlus P A`. -/
theorem scaleGate_maurer_cartan_right_log_diff {P : B} (hP : P * P = P)
    (x dx : B × B) :
    scaleGateDiff P x dx * scaleGateInv P x =
      conePlus P dx.1 +
        upperCornerUnit P x.1 * coneMinus P dx.2 *
          upperCornerUnit P (-x.1) := by
  dsimp [scaleGateDiff, scaleGateInv, upperCornerUnit, lowerCornerUnit]
  rw [conePlus_neg, coneMinus_neg]
  unfold conePlus coneMinus
  peirce_nf hP

/-- **Two-layer Maurer–Cartan adjoint telescoping law**:
for any outer reversible gate `G₂` (`G₂ * G₂_inv = 1`) and inner reversible gate
`G₁` (`G₁ * G₁_inv = 1`), the right-invariant variation of `G₂ * G₁` is the sum
of the outer right-invariant variation and the `G₂`-adjoint transport of the
inner right-invariant variation. -/
theorem two_layer_maurer_cartan_right_log_diff
    {G₂ G₂_inv dG₂ G₁ G₁_inv dG₁ : B}
    (hG₁ : G₁ * G₁_inv = 1) :
    (dG₂ * G₁ + G₂ * dG₁) * (G₁_inv * G₂_inv) =
      dG₂ * G₂_inv + G₂ * (dG₁ * G₁_inv) * G₂_inv := by
  calc
    (dG₂ * G₁ + G₂ * dG₁) * (G₁_inv * G₂_inv) =
        dG₂ * (G₁ * G₁_inv) * G₂_inv + G₂ * (dG₁ * G₁_inv) * G₂_inv := by
          noncomm_ring
    _ = dG₂ * 1 * G₂_inv + G₂ * (dG₁ * G₁_inv) * G₂_inv := by rw [hG₁]
    _ = dG₂ * G₂_inv + G₂ * (dG₁ * G₁_inv) * G₂_inv := by simp

/-- **Multi-scale step Maurer–Cartan telescoping law**:
at depth `n + 1`, the right-invariant variation of `towerGate scale (n + 1)`
decomposes into the top-scale nilpotent Maurer–Cartan differential plus the
`scaleGate (scale n)`-conjugated right-invariant variation of the `n`-layer
prefix tower. -/
theorem towerGate_succ_maurer_cartan_telescoping
    (scale : ℕ → B × (B × B))
    (hP : ∀ k, (scale k).1 * (scale k).1 = (scale k).1)
    (n : ℕ) (dx : B × B) (dT : B) :
    (scaleGateDiff (scale n).1 (scale n).2 dx * towerGate scale n +
        scaleGate (scale n).1 (scale n).2 * dT) *
      towerGateInv scale (n + 1) =
      (conePlus (scale n).1 dx.1 +
        upperCornerUnit (scale n).1 (scale n).2.1 *
          coneMinus (scale n).1 dx.2 *
          upperCornerUnit (scale n).1 (-(scale n).2.1)) +
      scaleGate (scale n).1 (scale n).2 *
        (dT * towerGateInv scale n) *
        scaleGateInv (scale n).1 (scale n).2 := by
  rw [towerGateInv]
  rw [two_layer_maurer_cartan_right_log_diff (towerGate_two_sided_inverse scale hP n).1]
  rw [scaleGate_maurer_cartan_right_log_diff (hP n) (scale n).2 dx]

end InfoGeometry.OperatorAlgebra.PeirceSpine.MultiScalePeirceGateTower

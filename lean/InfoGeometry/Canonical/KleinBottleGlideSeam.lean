/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Klein Bottle Glide Reflection and the Real Seam Fixed Locus

This module formalizes:
1. Para-complex coordinates `z = x + τ t` with `τ² = +1`.
2. Para-complex conjugation `conj z = x - τ t` swapping chiral sectors.
3. The real seam predicate `z = conj z` and its equivalence to `t = 0`.
4. The Klein glide reflection `T_a(z, w) = (w + L/2, z + L/2)`.
5. The single-coordinate reduction `glideZ L z = conj z + L/2`.
6. Stability: the real seam maps into itself under `T_a`.
7. Transverse fixed locus: `t = 0` is the exact fixed point of `t ↦ -t`.
8. Action on the seam: reduction to a pure 1D spatial translation `x ↦ x + L/2`.
9. The Klein periodicity theorem: `(T_a)²` is a pure translation by `L`.
-/

noncomputable section

namespace InfoGeometry.Canonical.KleinBottleGlideSeam

/-- Para-complex coordinate `z = x + τ t` where `re = x` and `tau = t`. -/
structure ParaComplex where
  re : ℝ
  tau : ℝ

namespace ParaComplex

@[ext]
theorem ext {z w : ParaComplex} (h_re : z.re = w.re) (h_tau : z.tau = w.tau) : z = w := by
  cases z
  cases w
  dsimp at h_re h_tau
  rw [h_re, h_tau]

/-- Para-complex conjugation swapping the holomorphic and antiholomorphic sectors:
    `conj(x + τ t) = x - τ t`. -/
def conj (z : ParaComplex) : ParaComplex :=
  ⟨z.re, -z.tau⟩

/-- Real horizontal translation along the spatial direction: `z + c = (x + c) + τ t`. -/
def addReal (z : ParaComplex) (c : ℝ) : ParaComplex :=
  ⟨z.re + c, z.tau⟩

@[simp] lemma conj_re (z : ParaComplex) : (conj z).re = z.re := rfl
@[simp] lemma conj_tau (z : ParaComplex) : (conj z).tau = -z.tau := rfl
@[simp] lemma addReal_re (z : ParaComplex) (c : ℝ) : (addReal z c).re = z.re + c := rfl
@[simp] lemma addReal_tau (z : ParaComplex) (c : ℝ) : (addReal z c).tau = z.tau := rfl

@[simp]
lemma conj_conj (z : ParaComplex) : conj (conj z) = z := by
  ext
  · rfl
  · simp [conj]

/-!
### 1. The Real Seam Locus
-/

/-- The Real Seam condition: the holomorphic and antiholomorphic components coincide. -/
def IsOnRealSeam (z : ParaComplex) : Prop :=
  z = conj z

/-- **Theorem (Real Seam Characterization)**:
    A state lies on the real seam (`z = conj z`) if and only if
    its hyperbolic modular time vanishes identically (`t = 0`). -/
theorem is_on_real_seam_iff_tau_zero (z : ParaComplex) :
    IsOnRealSeam z ↔ z.tau = 0 := by
  dsimp [IsOnRealSeam]
  constructor
  · intro h
    have h_tau := congr_arg tau h
    dsimp [conj] at h_tau
    linarith
  · intro h
    ext
    · rfl
    · dsimp [conj]
      rw [h, neg_zero]

/-!
### 2. The Klein Bottle Glide Reflection Operator
-/

/-- The bivariate glide reflection acting on the chiral pair `(z, w)`:
    `T_a(z, w) = (w + L/2, z + L/2)`. -/
def glide (L : ℝ) (p : ParaComplex × ParaComplex) : ParaComplex × ParaComplex :=
  (addReal p.2 (L / 2), addReal p.1 (L / 2))

/-- The induced action on a single para-complex coordinate `z`:
    `glideZ L z = conj z + L/2`. -/
def glideZ (L : ℝ) (z : ParaComplex) : ParaComplex :=
  addReal (conj z) (L / 2)

@[simp] lemma glideZ_re (L : ℝ) (z : ParaComplex) : (glideZ L z).re = z.re + L / 2 := rfl
@[simp] lemma glideZ_tau (L : ℝ) (z : ParaComplex) : (glideZ L z).tau = -z.tau := rfl

/-- Equivalence between the pair glide on `(z, conj z)` and `(glideZ z, conj (glideZ z))`. -/
theorem glide_pair_eq (L : ℝ) (z : ParaComplex) :
    glide L (z, conj z) = (glideZ L z, conj (glideZ L z)) := by
  dsimp [glide, glideZ, addReal, conj]
  apply Prod.ext
  · ext <;> rfl
  · ext
    · rfl
    · simp

/-!
### 3. Fixed Locus and Seam Invariance
-/

/-- **Theorem (Seam Stability under Glide Reflection)**:
    If `z` is on the real seam, its image under the Klein glide reflection
    also lies strictly on the real seam. -/
theorem glide_preserves_real_seam (L : ℝ) (z : ParaComplex) (hz : IsOnRealSeam z) :
    IsOnRealSeam (glideZ L z) := by
  rw [is_on_real_seam_iff_tau_zero] at hz ⊢
  dsimp [glideZ, addReal, conj]
  rw [hz, neg_zero]

/-- **Theorem (Transverse Fixed Locus)**:
    The transverse reflection `t ↦ -t` fixing the spatial coordinate
    has the real seam `t = 0` as its UNIQUE fixed-point set. -/
theorem transverse_fixed_locus (z : ParaComplex) :
    (conj z).tau = z.tau ↔ z.tau = 0 := by
  dsimp [conj]
  constructor
  · intro h; linarith
  · intro h; rw [h, neg_zero]

/-- **Theorem (Pure Spatial Translation on the Seam)**:
    On the real seam (`t = 0`), the glide reflection reduces strictly
    to the 1D spatial translation `x ↦ x + L/2`. -/
theorem glide_on_seam_is_pure_translation (L : ℝ) (z : ParaComplex) (hz : IsOnRealSeam z) :
    glideZ L z = ⟨z.re + L / 2, 0⟩ := by
  rw [is_on_real_seam_iff_tau_zero] at hz
  ext
  · rfl
  · dsimp [glideZ, addReal, conj]
    rw [hz, neg_zero]

/-!
### 4. Periodicity: The Klein Bottle Fundamental Group
-/

/-- **Theorem (Klein Periodicity / Translation Invariance)**:
    Applying the glide reflection twice recovers the pure period translation by `L`:
    `(T_a)² (z, w) = (z + L, w + L)`. -/
theorem glide_iter_two (L : ℝ) (p : ParaComplex × ParaComplex) :
    glide L (glide L p) = (addReal p.1 L, addReal p.2 L) := by
  dsimp [glide, addReal]
  apply Prod.ext
  · ext
    · dsimp; ring
    · rfl
  · ext
    · dsimp; ring
    · rfl

/-- Single coordinate iteration: `(T_a)²(z) = z + L`. -/
theorem glideZ_iter_two (L : ℝ) (z : ParaComplex) :
    glideZ L (glideZ L z) = addReal z L := by
  ext
  · dsimp [glideZ, addReal, conj]
    ring
  · dsimp [glideZ, addReal, conj]
    rw [neg_neg]

end ParaComplex

end InfoGeometry.Canonical.KleinBottleGlideSeam

end

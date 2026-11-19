/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.KreinSpace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A fixed Krein-skew flow preserves its quadratic form

The conservation law follows by differentiation using the existing Krein
adjoint. A differentiable orbit of such a generator cannot enter the null cone
from a non-null initial state. This asserts no existence of an orbit or
equivalence with the Navier--Stokes equation.
-/

noncomputable section

namespace InfoGeometry.Canonical.KreinFlowConservation

open InfoGeometry.Krein InfoGeometry.Krein.KreinSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [KreinSpace H]

theorem hasDerivAt_krein_square {x : ℝ → H} {A : H →L[ℝ] H} {t : ℝ}
    (hx : HasDerivAt x (A (x t)) t) (hA : IsKreinSkewAdjoint A) :
    HasDerivAt (fun r => kreinInner (x r) (x r)) 0 t := by
  have hJ := (jCLM (H := H)).hasFDerivAt.comp_hasDerivAt t hx
  have h := hJ.inner ℝ hx
  have hz := (isKreinSkewAdjoint_iff A).mp hA (x t) (x t)
  change kreinInner (A (x t)) (x t) + kreinInner (x t) (A (x t)) = 0 at hz
  have h_deriv_eq :
      inner ℝ ((⇑jCLM ∘ x) t) (A (x t)) + inner ℝ (jCLM (A (x t))) (x t) = 0 := by
    have h1 : inner ℝ ((⇑jCLM ∘ x) t) (A (x t)) = kreinInner (x t) (A (x t)) := rfl
    have h2 : inner ℝ (jCLM (A (x t))) (x t) = kreinInner (A (x t)) (x t) := rfl
    rw [h1, h2, add_comm, hz]
  rw [h_deriv_eq] at h
  exact h

/-- The derivative of the Krein pairing of two differentiable orbits under
the same bounded operator. The fundamental symmetry is applied to the first
slot, so the formula uses the actual Krein metric rather than the ambient
positive Hilbert product. -/
theorem hasDerivAt_krein_pairing {x y : ℝ → H} {A : H →L[ℝ] H} {t : ℝ}
    (hx : HasDerivAt x (A (x t)) t)
    (hy : HasDerivAt y (A (y t)) t) :
    HasDerivAt (fun r => kreinInner (x r) (y r))
      (kreinInner (A (x t)) (y t) + kreinInner (x t) (A (y t))) t := by
  have hJ := (jCLM (H := H)).hasFDerivAt.comp_hasDerivAt t hx
  have h := hJ.inner ℝ hy
  simpa [kreinInner_def, add_comm] using h

/-- A real-linear generator is Krein-skew-adjoint exactly when the
infinitesimal derivative of the Krein quadratic form vanishes on every
vector. The reverse implication is polarization for the symmetric
fundamental-symmetry pairing. -/
theorem isKreinSkewAdjoint_iff_quadratic_derivative_zero
    (A : H →L[ℝ] H) :
    IsKreinSkewAdjoint A ↔
      ∀ x : H, kreinInner (A x) x + kreinInner x (A x) = 0 := by
  rw [isKreinSkewAdjoint_iff]
  constructor
  · intro h x
    exact h x x
  · intro h u v
    have huv := h (u + v)
    have hu := h u
    have hv := h v
    simp only [map_add, kreinInner_add_left, kreinInner_add_right] at huv
    rw [kreinInner_symm (A v) u, kreinInner_symm v (A u)] at huv
    linarith

/-- Time dependence of the generator is allowed; the Krein metric is fixed. -/
theorem krein_square_conserved {x : ℝ → H} {A : ℝ → H →L[ℝ] H}
    (hx : ∀ t, HasDerivAt x (A t (x t)) t)
    (hA : ∀ t, IsKreinSkewAdjoint (A t)) (t s : ℝ) :
    kreinInner (x t) (x t) = kreinInner (x s) (x s) := by
  have hd := fun r => hasDerivAt_krein_square (hx r) (hA r)
  exact is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t s

/-- A preserved nonzero quadratic value cannot become zero at a later time. -/
theorem nonnull_preserved {x : ℝ → H} {A : ℝ → H →L[ℝ] H}
    (hx : ∀ t, HasDerivAt x (A t (x t)) t)
    (hA : ∀ t, IsKreinSkewAdjoint (A t)) {s : ℝ}
    (hs : kreinInner (x s) (x s) ≠ 0) (t : ℝ) :
    kreinInner (x t) (x t) ≠ 0 := by
  rwa [krein_square_conserved hx hA t s]

end InfoGeometry.Canonical.KreinFlowConservation

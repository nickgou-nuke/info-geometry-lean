/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.ChiralBoundarySymplecticBridge
import InfoGeometry.Geometry.QuadraticPotentialCalculus

/-!
# A real quadratic moment map on the canonical doubled space

This owner isolates the first genuine bridge from a linear symplectic generator
on `DoubledSpace E` to a real Hamiltonian.  The carrier is the existing
`WithLp 2 (E × E)` doubled space, and the symplectic form is the existing
coordinate form transported through its `WithLp` projections.

For a continuous linear generator `G` satisfying the infinitesimal symplectic
identity, the quadratic function
`z ↦ Ω (G z) z / 2` has derivative `v ↦ Ω (G z) v`.  No manifold,
probability, or Lipschitz--Killing curvature claim is made here.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap

open InfoGeometry.Krein
open InfoGeometry.Geometry.QuadraticPotentialCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Doubled (E : Type*) := DoubledSpace E

/-- The canonical real symplectic form on the doubled `WithLp` carrier. -/
noncomputable def symplecticForm : Doubled E →L[ℝ] Doubled E →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (fst_L (E := E)) (snd_L (E := E)) -
    (innerSL ℝ).bilinearComp (snd_L (E := E)) (fst_L (E := E))

@[simp] lemma symplecticForm_apply (u v : Doubled E) :
    symplecticForm u v =
      inner ℝ (WithLp.fst u) (WithLp.snd v) -
        inner ℝ (WithLp.snd u) (WithLp.fst v) :=
  rfl

/-- This is the existing chiral boundary form after `WithLp` readback. -/
lemma symplecticForm_eq_chiral (u v : Doubled E) :
    symplecticForm u v =
      InfoGeometry.Canonical.ChiralBoundarySymplectic.ChiralDoubled.symplecticForm
        (WithLp.ofLp u) (WithLp.ofLp v) := by
  simp [symplecticForm,
    InfoGeometry.Canonical.ChiralBoundarySymplectic.ChiralDoubled.symplecticForm,
    real_inner_comm]

lemma symplecticForm_skew (u v : Doubled E) :
    symplecticForm u v = -symplecticForm v u := by
  rw [symplecticForm_apply, symplecticForm_apply]
  rw [real_inner_comm (WithLp.fst v) (WithLp.snd u),
    real_inner_comm (WithLp.fst u) (WithLp.snd v)]
  ring

/-- Infinitesimal preservation of the canonical doubled symplectic form. -/
def IsSymplecticGenerator (G : Doubled E →L[ℝ] Doubled E) : Prop :=
  ∀ u v, symplecticForm (G u) v + symplecticForm u (G v) = 0

lemma symplecticForm_comp_generator_symmetric
    (G : Doubled E →L[ℝ] Doubled E) (hG : IsSymplecticGenerator G)
    (u v : Doubled E) :
    symplecticForm (G u) v = symplecticForm (G v) u := by
  have hskew := symplecticForm_skew u (G v)
  linarith [hG u v]

/-- The quadratic Souriau Hamiltonian attached to a linear symplectic generator. -/
noncomputable def quadraticMoment
    (G : Doubled E →L[ℝ] Doubled E) (z : Doubled E) : ℝ :=
  potential (symplecticForm.comp G) z

@[simp] lemma quadraticMoment_apply
    (G : Doubled E →L[ℝ] Doubled E) (z : Doubled E) :
    quadraticMoment G z = symplecticForm (G z) z / 2 :=
  rfl

/-- The genuine real Fréchet derivative of the quadratic moment map. -/
theorem hasFDerivAt_quadraticMoment
    (G : Doubled E →L[ℝ] Doubled E) (hG : IsSymplecticGenerator G)
    (z : Doubled E) :
    HasFDerivAt (quadraticMoment G) (symplecticForm (G z)) z := by
  exact hasFDerivAt_potential (symplecticForm.comp G)
    (fun u v => symplecticForm_comp_generator_symmetric G hG u v) z

/-- Pointwise form of the Hamiltonian identity `dH = ι_(Gz) Ω`. -/
theorem fderiv_quadraticMoment
    (G : Doubled E →L[ℝ] Doubled E) (hG : IsSymplecticGenerator G)
    (z v : Doubled E) :
    fderiv ℝ (quadraticMoment G) z v = symplecticForm (G z) v := by
  rw [(hasFDerivAt_quadraticMoment G hG z).fderiv]

end InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap

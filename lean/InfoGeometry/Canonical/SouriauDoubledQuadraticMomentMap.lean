/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.ChiralBoundarySymplecticBridge
import InfoGeometry.Canonical.SouriauKKSForm
import InfoGeometry.Physics.SouriauLieThermodynamics
import InfoGeometry.Thermo.OnsagerOperatorClosure
import InfoGeometry.Geometry.RealHamiltonianMoment
import InfoGeometry.Geometry.QuadraticPotentialCalculus
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Normed.Algebra.Exponential

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

local instance : LieRing (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  LieRing.ofAssociativeRing
local instance : LieAlgebra ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  LieAlgebra.ofAssociativeAlgebra
abbrev Doubled (E : Type*) := DoubledSpace E

local notation "EndD" => Doubled E →L[ℝ] Doubled E

local instance [CompleteSpace E] : NormedRing EndD := inferInstance
local instance [CompleteSpace E] : NormedAlgebra ℝ EndD := inferInstance
local instance [CompleteSpace E] : NormedSpace ℝ EndD := inferInstance
local instance [CompleteSpace E] : NormedAlgebra ℚ EndD :=
  NormedAlgebra.restrictScalars ℚ ℝ EndD

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

/-- The symplectic form is represented by the canonical real clock axis and
the positive doubled Hilbert product. -/
lemma symplecticForm_eq_inner_clockAxis (u v : Doubled E) :
    symplecticForm u v = inner ℝ (clockAxis u) v := by
  rw [symplecticForm_apply, clockAxis_apply]
  simp only [WithLp.prod_inner_apply]
  rw [inner_neg_left]
  simp only [WithLp.fst, WithLp.snd]
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

/-- The positive-Hilbert Riesz gradient of the quadratic Souriau moment.
The carrier remains the real doubled space; this is the vector representing
the derivative through its positive inner product, not through the indefinite
Krein pairing. -/
noncomputable def quadraticMomentGradient
    (G : Doubled E →L[ℝ] Doubled E) (z : Doubled E) : Doubled E :=
  clockAxis (G z)

/-- The Fréchet derivative of a symplectic quadratic moment is represented by
`quadraticMomentGradient` under the positive doubled Hilbert product. -/
theorem fderiv_quadraticMoment_eq_inner_gradient
    (G : Doubled E →L[ℝ] Doubled E) (hG : IsSymplecticGenerator G)
    (z v : Doubled E) :
    fderiv ℝ (quadraticMoment G) z v =
      inner ℝ (quadraticMomentGradient G z) v := by
  rw [fderiv_quadraticMoment G hG, symplecticForm_eq_inner_clockAxis]
  rfl

/-- The Riesz gradient of the quadratic moment is globally Lipschitz in the
positive doubled Hilbert norm, with the generator's operator norm as constant.
This is an exact gradient estimate, unlike the state-value estimate, which is
only Lipschitz on bounded balls. -/
theorem quadraticMomentGradient_lipschitz
    (G : Doubled E →L[ℝ] Doubled E) :
    LipschitzWith ⟨‖G‖, norm_nonneg G⟩ (quadraticMomentGradient G) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [dist_eq_norm, dist_eq_norm]
  change ‖clockAxis (G z) - clockAxis (G w)‖ ≤ ‖G‖ * ‖z - w‖
  calc
    ‖clockAxis (G z) - clockAxis (G w)‖ =
        ‖clockAxis (G z - G w)‖ := by rw [← map_sub]
    _ = ‖G z - G w‖ := clockAxis_norm _
    _ = ‖G (z - w)‖ := by rw [map_sub]
    _ ≤ ‖G‖ * ‖z - w‖ := G.le_opNorm (z - w)

/-- The canonical symplectic pairing is bounded by the positive doubled
Hilbert norm. This uses the real clock-axis isometry, not the indefinite
Krein quadratic form. -/
lemma abs_symplecticForm_le_norm (u v : Doubled E) :
    |symplecticForm u v| ≤ ‖u‖ * ‖v‖ := by
  rw [symplecticForm_eq_inner_clockAxis]
  calc
    |inner ℝ (clockAxis u) v| ≤ ‖clockAxis u‖ * ‖v‖ :=
      abs_real_inner_le_norm _ _
    _ = ‖u‖ * ‖v‖ := by rw [clockAxis_norm]

/-- Boundedness of a symplectic-generator readout in its vector argument. -/
lemma abs_symplecticForm_generator_le_norm
    (G : Doubled E →L[ℝ] Doubled E) (u v : Doubled E) :
    |symplecticForm (G u) v| ≤ ‖G‖ * ‖u‖ * ‖v‖ := by
  calc
    |symplecticForm (G u) v| ≤ ‖G u‖ * ‖v‖ := abs_symplecticForm_le_norm _ _
    _ ≤ (‖G‖ * ‖u‖) * ‖v‖ := by gcongr; exact G.le_opNorm u

/-- Exact polarization identity for the difference of two quadratic Souriau
moments. It is the algebraic step behind the local Lipschitz estimate below. -/
lemma quadraticMoment_sub_eq_polarized
    (G : Doubled E →L[ℝ] Doubled E →L[ℝ] ℝ)
    (z w : Doubled E) :
    (G z z / 2) - (G w w / 2) =
      (G (z - w) z + G w (z - w)) / 2 := by
  simp only [map_sub, sub_apply]
  ring

/-- A bilinear quadratic form with first-slot operator bound `C` is Lipschitz
on every Hilbert ball of radius `R`, with constant `R * C`. The estimate is
local because a nonzero quadratic map is not globally Lipschitz on an
unbounded vector space. -/
theorem quadraticMoment_lipschitzOn_ball
    (G : Doubled E →L[ℝ] Doubled E →L[ℝ] ℝ)
    (C R : ℝ)
    (hC : ∀ u, ‖G u‖ ≤ C * ‖u‖) (hC0 : 0 ≤ C)
    (z w : Doubled E) (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    |(G z z / 2) - (G w w / 2)| ≤ R * C * ‖z - w‖ := by
  rw [quadraticMoment_sub_eq_polarized G z w]
  have hbound₁ : |G (z - w) z| ≤ C * ‖z - w‖ * ‖z‖ := by
    calc
      |G (z - w) z| ≤ ‖G (z - w)‖ * ‖z‖ := (G (z - w)).le_opNorm z
      _ ≤ (C * ‖z - w‖) * ‖z‖ :=
        mul_le_mul_of_nonneg_right (hC (z - w)) (norm_nonneg _)
  have hbound₂ : |G w (z - w)| ≤ C * ‖w‖ * ‖z - w‖ := by
    calc
      |G w (z - w)| ≤ ‖G w‖ * ‖z - w‖ := (G w).le_opNorm (z - w)
      _ ≤ (C * ‖w‖) * ‖z - w‖ :=
        mul_le_mul_of_nonneg_right (hC w) (norm_nonneg _)
  have hdist : ‖z - w‖ ≤ ‖z‖ + ‖w‖ := by
    calc
      ‖z - w‖ = ‖z + -w‖ := by rw [sub_eq_add_neg]
      _ ≤ ‖z‖ + ‖-w‖ := norm_add_le _ _
      _ = ‖z‖ + ‖w‖ := by rw [norm_neg]
  have hsum : |G (z - w) z + G w (z - w)| ≤
      C * ‖z - w‖ * (‖z‖ + ‖w‖) := by
    calc
      |G (z - w) z + G w (z - w)| ≤
          |G (z - w) z| + |G w (z - w)| := abs_add_le _ _
      _ ≤ C * ‖z - w‖ * ‖z‖ +
          C * ‖w‖ * ‖z - w‖ := add_le_add hbound₁ hbound₂
      _ = C * ‖z - w‖ * (‖z‖ + ‖w‖) := by ring
  have hrad : ‖z‖ + ‖w‖ ≤ 2 * R := by linarith
  have hfinal : (|G (z - w) z + G w (z - w)|) / 2 ≤
      R * C * ‖z - w‖ := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    calc
      |G (z - w) z + G w (z - w)| ≤
          C * ‖z - w‖ * (‖z‖ + ‖w‖) := hsum
      _ ≤ C * ‖z - w‖ * (2 * R) := by
        exact mul_le_mul_of_nonneg_left hrad
          (mul_nonneg hC0 (norm_nonneg _))
      _ = R * C * ‖z - w‖ * 2 := by ring
  have habs : |(G (z - w) z + G w (z - w)) / 2| =
      |G (z - w) z + G w (z - w)| / 2 := by norm_num [abs_div]
  rw [habs]
  exact hfinal

/-- The Souriau quadratic moment inherits the preceding ball-Lipschitz
estimate with the operator-norm constant of its generator. The estimate
itself does not require infinitesimal symplecticity; that hypothesis is
required for the Hamiltonian derivative theorem above. -/
theorem souriauMoment_lipschitzOn_ball
    (G : Doubled E →L[ℝ] Doubled E)
    (R : ℝ)
    (z w : Doubled E) (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    |quadraticMoment G z - quadraticMoment G w| ≤ R * ‖G‖ * ‖z - w‖ := by
  have hbound : ∀ u, ‖symplecticForm (G u)‖ ≤ ‖G‖ * ‖u‖ := by
    intro u
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (norm_nonneg G) (norm_nonneg u)) fun v => ?_
    rw [Real.norm_eq_abs]
    exact abs_symplecticForm_generator_le_norm G u v
  simpa [quadraticMoment_apply] using
    quadraticMoment_lipschitzOn_ball (symplecticForm.comp G) ‖G‖ R hbound
      (norm_nonneg G)
      z w hz hw

/-- At a fixed state, the quadratic moment is globally Lipschitz in the
generator for the operator norm. This is the parameter-direction estimate:
unlike `souriauMoment_lipschitzOn_ball`, it varies the generator and keeps the
state fixed. No infinitesimal symplecticity hypothesis is needed for this
bound. -/
theorem quadraticMoment_generator_lipschitz
    (z : Doubled E) :
    LipschitzWith ⟨‖z‖ ^ 2, sq_nonneg _⟩
      (fun G : Doubled E →L[ℝ] Doubled E => quadraticMoment G z) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  rw [dist_eq_norm, dist_eq_norm]
  have hdiff : quadraticMoment A z - quadraticMoment B z =
      quadraticMoment (A - B) z := by
    simp [quadraticMoment_apply]
    ring
  rw [hdiff, quadraticMoment_apply]
  change |symplecticForm ((A - B) z) z / 2| ≤ _
  have hpair := abs_symplecticForm_generator_le_norm (A - B) z z
  have hden : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  rw [abs_div, hden]
  calc
    |symplecticForm ((A - B) z) z| / 2 ≤
        |symplecticForm ((A - B) z) z| := by
          exact div_le_self (abs_nonneg _) (by norm_num)
    _ ≤ ‖A - B‖ * ‖z‖ * ‖z‖ := hpair
    _ = (‖z‖ ^ 2) * ‖A - B‖ := by ring

/-- The linear moment-map component is bounded by half the squared state norm
times the operator norm of the generator. This is the pointwise estimate from
which `quadraticMoment_generator_lipschitz` follows. -/
theorem abs_quadraticMoment_le_generator_norm
    (G : Doubled E →L[ℝ] Doubled E) (z : Doubled E) :
    |quadraticMoment G z| ≤ (‖G‖ * ‖z‖ ^ 2) / 2 := by
  rw [quadraticMoment_apply]
  have hpair := abs_symplecticForm_generator_le_norm G z z
  have hnonneg : 0 ≤ ‖G‖ * ‖z‖ := by positivity
  calc
    |symplecticForm (G z) z / 2| =
        |symplecticForm (G z) z| / 2 := by rw [abs_div]; norm_num
    _ ≤ (‖G‖ * ‖z‖ * ‖z‖) / 2 := by
        exact div_le_div_of_nonneg_right hpair (by norm_num : (0 : ℝ) ≤ 2)
    _ = (‖G‖ * ‖z‖ ^ 2) / 2 := by ring

/-- The general real Hamiltonian owner uses the normalized form
`omega K = -2 Ω`, while this owner uses the canonical doubled form `Ω`.
Consequently its quadratic Hamiltonian is `-2` times the Souriau moment.
This explicit comparison prevents silently identifying the two conventions. -/
theorem realHamiltonian_quadraticHamiltonian_eq_neg_two_quadraticMoment
    [CompleteSpace E]
    (G : Doubled E →L[ℝ] Doubled E) (z : Doubled E) :
    InfoGeometry.Geometry.RealHamiltonianMoment.quadraticHamiltonian
        (clockAxis (E := E)) G z = -2 * quadraticMoment G z := by
  calc
    InfoGeometry.Geometry.RealHamiltonianMoment.quadraticHamiltonian
        (clockAxis (E := E)) G z =
      (1 / 2 : ℝ) * (-2 * symplecticForm (G z) z) := by
        rw [InfoGeometry.Geometry.RealHamiltonianMoment.quadraticHamiltonian,
          InfoGeometry.Geometry.RealHamiltonianMoment.omega_apply,
          ← symplecticForm_eq_inner_clockAxis]
    _ = -2 * quadraticMoment G z := by
      rw [quadraticMoment_apply]
      ring

/-- Infinitesimal symplecticity for the canonical doubled form is equivalent
to infinitesimal symplecticity for the normalized real Hamiltonian form
`omega clockAxis = -2 Ω`. -/
theorem isSymplecticGenerator_iff_isOmegaGenerator
    [CompleteSpace E]
    (G : Doubled E →L[ℝ] Doubled E) :
    IsSymplecticGenerator G ↔
      InfoGeometry.Geometry.RealHamiltonianMoment.IsOmegaGenerator
        (clockAxis (E := E)) G := by
  constructor
  · intro h u v
    change InfoGeometry.Geometry.RealHamiltonianMoment.omega
        (clockAxis (E := E)) (G u) v +
      InfoGeometry.Geometry.RealHamiltonianMoment.omega
        (clockAxis (E := E)) u (G v) = 0
    simp only [InfoGeometry.Geometry.RealHamiltonianMoment.omega_apply,
      ← symplecticForm_eq_inner_clockAxis]
    have hh := h u v
    linarith
  · intro h u v
    have hh := h u v
    change InfoGeometry.Geometry.RealHamiltonianMoment.omega
        (clockAxis (E := E)) (G u) v +
      InfoGeometry.Geometry.RealHamiltonianMoment.omega
        (clockAxis (E := E)) u (G v) = 0 at hh
    simp only [InfoGeometry.Geometry.RealHamiltonianMoment.omega_apply,
      ← symplecticForm_eq_inner_clockAxis] at hh
    linarith

/-- The canonical modular swap is a Hamiltonian generator for the doubled
symplectic form. Its finite map is anti-symplectic, but its infinitesimal
action satisfies the generator equation required here. -/
theorem modularSwap_isSymplecticGenerator [CompleteSpace E] :
    IsSymplecticGenerator (InfoGeometry.Krein.modular_j (E := E)) := by
  intro u v
  rw [symplecticForm_apply, symplecticForm_apply]
  simp only [InfoGeometry.Krein.modular_j_apply]
  simp only [WithLp.fst, WithLp.snd]
  ring

/-- The quadratic Souriau Hamiltonian for the doubled boost generator is the
real hyperbolic energy `(|xi|² - |x|²)/2`. This is the explicit finite real
model behind the hyperbolic flow, without introducing complex scalars. -/
theorem quadraticMoment_modularSwap [CompleteSpace E] (z : Doubled E) :
    quadraticMoment (InfoGeometry.Krein.modular_j (E := E)) z =
      (‖WithLp.snd z‖ ^ 2 - ‖WithLp.fst z‖ ^ 2) / 2 := by
  rw [quadraticMoment_apply, symplecticForm_apply,
    InfoGeometry.Krein.modular_j_apply]
  simp only [WithLp.fst, WithLp.snd]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- The second Fréchet derivative of the quadratic Hamiltonian is the
constant bilinear form `(u,v) ↦ Ω (G u) v`. In particular, the Hessian is
independent of the base point; this is the precise finite-dimensional-style
differential datum required before comparing it with a statistical BKM
Hessian. -/
theorem hessian_quadraticMoment
    (G : Doubled E →L[ℝ] Doubled E) (hG : IsSymplecticGenerator G)
    (z : Doubled E) :
    fderiv ℝ (fderiv ℝ (quadraticMoment G)) z = symplecticForm.comp G := by
  exact hessian_potential (symplecticForm.comp G)
    (fun u v => symplecticForm_comp_generator_symmetric G hG u v) z

/-- Polarized Hessian of the real modular-swap moment is the negative of the
repository's canonical Krein pairing on the doubled carrier. The sign records
that this Hamiltonian is `-1/2` times the Krein quadratic form. -/
theorem hessian_quadraticMoment_modularSwap_eq_neg_kreinPairing
    [CompleteSpace E] (z u v : Doubled E) :
    (fderiv ℝ (fderiv ℝ
      (quadraticMoment (InfoGeometry.Krein.modular_j (E := E)))) z) u v =
      -InfoGeometry.Krein.hessian_indefinite_form u v := by
  rw [hessian_quadraticMoment
    (InfoGeometry.Krein.modular_j (E := E)) modularSwap_isSymplecticGenerator z]
  rw [InfoGeometry.Krein.hessian_indefinite_form_eq_doubledHilbertBilin_spectral_epsilon]
  change symplecticForm (InfoGeometry.Krein.modular_j u) v =
    -doubledHilbertBilin u (InfoGeometry.Krein.spectral_epsilon v)
  simp [symplecticForm_apply, InfoGeometry.Krein.modular_j_apply,
    doubledHilbertBilin, InfoGeometry.Krein.spectral_epsilon,
    WithLp.prod_inner_apply]
  ring

/-- The modular swap is anti-isometric for the Krein pairing, so its action on
both tangent arguments reverses the polarized Hessian of the quadratic moment.
This is the exact sign obstruction to transporting the positive-sheet Hessian
as a positive metric through the swap. -/
theorem hessian_quadraticMoment_modularSwap_conjugation
    [CompleteSpace E] (z u v : Doubled E) :
    (fderiv ℝ (fderiv ℝ
      (quadraticMoment (InfoGeometry.Krein.modular_j (E := E)))) z)
        (InfoGeometry.Krein.modular_j u) (InfoGeometry.Krein.modular_j v) =
      -((fderiv ℝ (fderiv ℝ
      (quadraticMoment (InfoGeometry.Krein.modular_j (E := E)))) z) u v) := by
  rw [hessian_quadraticMoment_modularSwap_eq_neg_kreinPairing,
    hessian_quadraticMoment_modularSwap_eq_neg_kreinPairing]
  unfold InfoGeometry.Krein.hessian_indefinite_form
  rw [InfoGeometry.Krein.kreinInner_modular_j]

/-- The Hessian of the modular-swap quadratic moment has the exact split
signature on every doubled tangent vector: `‖ξ‖² - ‖x‖²`. It is independent
of the base point, and exposes the obstruction to identifying the whole
doubled Hessian with a positive BKM covariance metric. -/
theorem hessian_quadraticMoment_modularSwap
    [CompleteSpace E] (z u : Doubled E) :
    (fderiv ℝ (fderiv ℝ
      (quadraticMoment (InfoGeometry.Krein.modular_j (E := E)))) z)
        u u = ‖WithLp.snd u‖ ^ 2 - ‖WithLp.fst u‖ ^ 2 := by
  have h := congrArg
    (fun H : Doubled E →L[ℝ] Doubled E →L[ℝ] ℝ => H u u)
    (hessian_quadraticMoment (InfoGeometry.Krein.modular_j (E := E))
      modularSwap_isSymplecticGenerator z)
  change (fderiv ℝ (fderiv ℝ
      (quadraticMoment (InfoGeometry.Krein.modular_j (E := E)))) z) u u =
    (symplecticForm.comp (InfoGeometry.Krein.modular_j (E := E))) u u at h
  rw [h]
  change symplecticForm (InfoGeometry.Krein.modular_j u) u = _
  rw [symplecticForm_apply, InfoGeometry.Krein.modular_j_apply]
  simp only [WithLp.fst, WithLp.snd]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- On the first sheet, the Hessian is negative definite: it evaluates to
`-‖x‖²`. -/
theorem hessian_quadraticMoment_modularSwap_firstSheet
    [CompleteSpace E] (z : Doubled E) (x : E) :
    (fderiv ℝ (fderiv ℝ
      (quadraticMoment (InfoGeometry.Krein.modular_j (E := E)))) z)
        (WithLp.toLp (2 : ENNReal) (x, 0))
        (WithLp.toLp (2 : ENNReal) (x, 0)) = -‖x‖ ^ 2 := by
  simpa using hessian_quadraticMoment_modularSwap z
    (WithLp.toLp (2 : ENNReal) (x, 0))

/-- On the second sheet, the same Hessian is positive definite and evaluates
to the squared Hilbert norm. Thus the full doubled Hessian has a genuine
positive sector even though it is indefinite on the whole carrier. -/
theorem hessian_quadraticMoment_modularSwap_secondSheet
    [CompleteSpace E] (z : Doubled E) (xi : E) :
    (fderiv ℝ (fderiv ℝ
      (quadraticMoment (InfoGeometry.Krein.modular_j (E := E)))) z)
        (WithLp.toLp (2 : ENNReal) (0, xi))
        (WithLp.toLp (2 : ENNReal) (0, xi)) = ‖xi‖ ^ 2 := by
  rw [hessian_quadraticMoment_modularSwap]
  simp

/-- The polarized modular-swap Hessian restricts on the second coordinate
sheet to the original positive real Hilbert inner product. This is the
bilinear pullback, rather than only its diagonal norm formula. -/
theorem hessian_quadraticMoment_modularSwap_secondSheet_bilinear
    [CompleteSpace E] (z : Doubled E) (xi eta : E) :
    (fderiv ℝ (fderiv ℝ
      (quadraticMoment (InfoGeometry.Krein.modular_j (E := E)))) z)
        (WithLp.toLp (2 : ENNReal) (0, xi))
        (WithLp.toLp (2 : ENNReal) (0, eta)) = inner ℝ xi eta := by
  rw [hessian_quadraticMoment_modularSwap_eq_neg_kreinPairing]
  rw [InfoGeometry.Krein.hessian_indefinite_form_eq_doubledHilbertBilin_spectral_epsilon]
  simp [doubledHilbertBilin, InfoGeometry.Krein.spectral_epsilon,
    WithLp.prod_inner_apply]

/-- The restricted second-sheet Hessian is positive definite: its diagonal
vanishes exactly at the zero tangent vector. -/
theorem hessian_quadraticMoment_modularSwap_secondSheet_pos_iff
    [CompleteSpace E] (z : Doubled E) (xi : E) :
    0 < (fderiv ℝ (fderiv ℝ
      (quadraticMoment (InfoGeometry.Krein.modular_j (E := E)))) z)
        (WithLp.toLp (2 : ENNReal) (0, xi))
        (WithLp.toLp (2 : ENNReal) (0, xi)) ↔ xi ≠ 0 := by
  rw [hessian_quadraticMoment_modularSwap_secondSheet]
  constructor
  · intro h hx
    subst xi
    simp at h
  · intro h
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr h)

/-- The modular-swap Hessian has no mixed term between the two coordinate
sheets. It is therefore exactly the orthogonal difference of its positive
and negative sheet Hessians. -/
theorem hessian_quadraticMoment_modularSwap_mixedSheets
    [CompleteSpace E] (z : Doubled E) (x xi : E) :
    (fderiv ℝ (fderiv ℝ
      (quadraticMoment (InfoGeometry.Krein.modular_j (E := E)))) z)
        (WithLp.toLp (2 : ENNReal) (x, 0))
        (WithLp.toLp (2 : ENNReal) (0, xi)) = 0 := by
  rw [hessian_quadraticMoment
    (InfoGeometry.Krein.modular_j (E := E)) modularSwap_isSymplecticGenerator z]
  simp [symplecticForm_apply, InfoGeometry.Krein.modular_j_apply]

/-- The modular-swap moment Hessian is not positive semidefinite on the whole
doubled carrier whenever the underlying real Hilbert space is nontrivial. -/
theorem modularSwap_quadraticMoment_hessian_not_positiveSemidefinite
    [CompleteSpace E] [Nontrivial E] :
    ¬ ∀ z u : Doubled E,
      0 ≤ (fderiv ℝ (fderiv ℝ
        (quadraticMoment (InfoGeometry.Krein.modular_j (E := E)))) z) u u := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  let u : Doubled E := WithLp.toLp (2 : ENNReal) (x, 0)
  intro hpositive
  have hneg := hessian_quadraticMoment_modularSwap_firstSheet (0 : Doubled E) x
  have hnonneg := hpositive 0 u
  have hnorm : 0 < ‖x‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx)
  rw [hneg] at hnonneg
  linarith

/-- The infinitesimal symplectic identity is the operator equation
`K G + G† K = 0`, where `K` is the canonical real clock axis and `†` is the
positive doubled Hilbert adjoint. -/
theorem symplecticGenerator_adjoint_identity
    [CompleteSpace E] (G : Doubled E →L[ℝ] Doubled E)
    (hG : IsSymplecticGenerator G) :
    clockAxis.comp G + (ContinuousLinearMap.adjoint G).comp clockAxis = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  let w : Doubled E := (clockAxis.comp G + (ContinuousLinearMap.adjoint G).comp clockAxis) u
  change w = 0
  apply (inner_self_eq_zero (𝕜 := ℝ) (x := w)).mp
  have h := hG u w
  rw [symplecticForm_eq_inner_clockAxis, symplecticForm_eq_inner_clockAxis] at h
  rw [← ContinuousLinearMap.adjoint_inner_left G w (clockAxis u)] at h
  rw [← inner_add_left] at h
  simpa [w, add_apply, ContinuousLinearMap.comp_apply] using h

/-- Solving the infinitesimal identity for the Hilbert adjoint uses the
real clock-axis square `K² = -1`: `G† = K G K`. -/
theorem adjoint_eq_clockAxis_comp_generator_comp_clockAxis
    [CompleteSpace E] (G : Doubled E →L[ℝ] Doubled E)
    (hG : IsSymplecticGenerator G) :
    ContinuousLinearMap.adjoint G =
      clockAxis.comp (G.comp clockAxis) := by
  apply ContinuousLinearMap.ext
  intro u
  have hsq : clockAxis (clockAxis u) = -u := by
    have h := congrArg (fun T : Doubled E →L[ℝ] Doubled E => T u) (clockAxis_sq E)
    simpa [ContinuousLinearMap.comp_apply] using h
  have h := congrArg (fun T : Doubled E →L[ℝ] Doubled E => T (clockAxis u))
    (symplecticGenerator_adjoint_identity G hG)
  simp only [add_apply, ContinuousLinearMap.comp_apply] at h
  rw [hsq, map_neg] at h
  have h' : clockAxis (G (clockAxis u)) - ContinuousLinearMap.adjoint G u = 0 := by
    simpa [sub_eq_add_neg] using h
  exact (sub_eq_zero.mp h').symm

/-- The real clock axis is a unit in the bounded-operator algebra, with
inverse `-K`; this is the algebraic datum needed for conjugating exponentials. -/
noncomputable def clockAxisUnit [CompleteSpace E] :
    (Doubled E →L[ℝ] Doubled E)ˣ where
  val := clockAxis
  inv := -clockAxis
  val_inv := by
    apply ContinuousLinearMap.ext
    intro u
    change clockAxis (-clockAxis u) = u
    rw [map_neg]
    have hsq := congrArg (fun T : Doubled E →L[ℝ] Doubled E => T u) (clockAxis_sq E)
    simpa [ContinuousLinearMap.comp_apply] using congrArg Neg.neg hsq
  inv_val := by
    apply ContinuousLinearMap.ext
    intro u
    change -clockAxis (clockAxis u) = u
    have hsq := congrArg (fun T : Doubled E →L[ℝ] Doubled E => T u) (clockAxis_sq E)
    simpa [ContinuousLinearMap.comp_apply] using congrArg Neg.neg hsq

/-- Exponentiating an infinitesimal symplectic generator preserves the actual
bilinear form on the completed real doubled carrier. -/
theorem exp_preserves_symplecticForm
    [CompleteSpace E] (G : Doubled E →L[ℝ] Doubled E)
    (hG : IsSymplecticGenerator G) (t : ℝ) (u v : Doubled E) :
    symplecticForm (NormedSpace.exp (t • G) u)
        (NormedSpace.exp (t • G) v) = symplecticForm u v := by
  let U : Doubled E →L[ℝ] Doubled E := NormedSpace.exp (t • G)
  let Kunit := clockAxisUnit (E := E)
  have hscale : ContinuousLinearMap.adjoint (t • G) =
      t • ContinuousLinearMap.adjoint G := by
    simp
  have hconj : (Kunit : Doubled E →L[ℝ] Doubled E) * (-(t • G)) *
      ↑(Kunit⁻¹) = ContinuousLinearMap.adjoint (t • G) := by
    rw [hscale, adjoint_eq_clockAxis_comp_generator_comp_clockAxis G hG]
    change clockAxis * (-(t • G)) * (-clockAxis) =
      t • (clockAxis * G * clockAxis)
    noncomm_ring
  have hstar : star (t • G) = ContinuousLinearMap.adjoint (t • G) := by
    exact ContinuousLinearMap.star_eq_adjoint (t • G)
  have hAdjU : ContinuousLinearMap.adjoint U =
      (Kunit : Doubled E →L[ℝ] Doubled E) *
        NormedSpace.exp (-(t • G)) * ↑(Kunit⁻¹) := by
    calc
      ContinuousLinearMap.adjoint U =
          NormedSpace.exp (ContinuousLinearMap.adjoint (t • G)) := by
            calc
              ContinuousLinearMap.adjoint U = star U := rfl
              _ = NormedSpace.exp (star (t • G)) := by
                change star (NormedSpace.exp (t • G)) = _
                rw [NormedSpace.star_exp]
              _ = NormedSpace.exp (ContinuousLinearMap.adjoint (t • G)) :=
                congrArg NormedSpace.exp hstar
      _ = NormedSpace.exp ((Kunit : Doubled E →L[ℝ] Doubled E) *
            (-(t • G)) * ↑(Kunit⁻¹)) := by rw [← hconj]
      _ = (Kunit : Doubled E →L[ℝ] Doubled E) *
            NormedSpace.exp (-(t • G)) * ↑(Kunit⁻¹) :=
          NormedSpace.exp_units_conj Kunit (-(t • G))
  have hcancel : NormedSpace.exp (-(t • G)) * NormedSpace.exp (t • G) =
      (1 : Doubled E →L[ℝ] Doubled E) := by
    have hcomm : Commute (-(t • G)) (t • G) :=
      (Commute.refl (t • G)).neg_left
    rw [← NormedSpace.exp_add_of_commute hcomm]
    simp
  have hProduct : ContinuousLinearMap.adjoint U * clockAxis * U = clockAxis := by
    rw [hAdjU]
    have hUnitInv : (↑(Kunit⁻¹) : EndD) * (↑Kunit : EndD) = 1 :=
      Units.inv_val Kunit
    calc
      ((Kunit : EndD) * NormedSpace.exp (-(t • G)) * ↑(Kunit⁻¹)) *
          clockAxis * U =
        (Kunit : EndD) * (NormedSpace.exp (-(t • G)) *
          (↑(Kunit⁻¹) * (Kunit : EndD)) * U) := by noncomm_ring
      _ = (Kunit : EndD) * (NormedSpace.exp (-(t • G)) * U) := by
        rw [hUnitInv]
        simp
      _ = (Kunit : EndD) := by
        change (Kunit : EndD) *
          (NormedSpace.exp (-(t • G)) * NormedSpace.exp (t • G)) = Kunit
        rw [hcancel, mul_one]
      _ = clockAxis := by rfl
  have hpoint : ContinuousLinearMap.adjoint U (clockAxis (U u)) = clockAxis u := by
    have h := congrArg (fun T : Doubled E →L[ℝ] Doubled E => T u) hProduct
    simpa [_root_.mul_apply_eq_comp, ContinuousLinearMap.comp_apply] using h
  rw [symplecticForm_eq_inner_clockAxis, symplecticForm_eq_inner_clockAxis]
  calc
    inner ℝ (clockAxis (U u)) (U v) =
        inner ℝ (ContinuousLinearMap.adjoint U (clockAxis (U u))) v := by
          symm
          exact ContinuousLinearMap.adjoint_inner_left U v (clockAxis (U u))
    _ = inner ℝ (clockAxis u) v := by rw [hpoint]

/-- At every time, the derivative of the pairing along two exponential
trajectories is the infinitesimal symplectic defect evaluated at the flowed
vectors. -/
theorem hasDerivAt_symplecticForm_exp_flow_pair
    [CompleteSpace E] (G : Doubled E →L[ℝ] Doubled E)
    (u v : Doubled E) (t : ℝ) :
    HasDerivAt
      (fun t : ℝ => symplecticForm (NormedSpace.exp (t • G) u)
        (NormedSpace.exp (t • G) v))
      (symplecticForm (G (NormedSpace.exp (t • G) u))
        (NormedSpace.exp (t • G) v) +
       symplecticForm (NormedSpace.exp (t • G) u)
        (G (NormedSpace.exp (t • G) v))) t := by
  let path : ℝ → Doubled E := fun s => NormedSpace.exp (s • G) u
  let path' : ℝ → Doubled E := fun s => NormedSpace.exp (s • G) v
  have hexp : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • G))
      (NormedSpace.exp (t • G) * G) t :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) G t
  have hconstU : HasDerivAt (fun _ : ℝ => u) (0 : Doubled E) t :=
    hasDerivAt_const t u
  have hconstV : HasDerivAt (fun _ : ℝ => v) (0 : Doubled E) t :=
    hasDerivAt_const t v
  have hu₀ := hexp.clm_apply hconstU
  have hv₀ := hexp.clm_apply hconstV
  have hflowCommute : Commute G (NormedSpace.exp (t • G)) := by
    simpa using ((Commute.refl G).smul_right t).exp_right
  have hcommPoint (x : Doubled E) :
      (NormedSpace.exp (t • G)) (G x) = G ((NormedSpace.exp (t • G)) x) := by
    have hcomm := congrArg (fun T : EndD => T x) hflowCommute.eq.symm
    simpa [_root_.mul_apply_eq_comp, ContinuousLinearMap.comp_apply] using hcomm
  have hu : HasDerivAt path (G (path t)) t := by
    convert hu₀ using 1
    simpa [path] using (hcommPoint u).symm
  have hv : HasDerivAt path' (G (path' t)) t := by
    convert hv₀ using 1
    simpa [path'] using (hcommPoint v).symm
  have hpair := symplecticForm.hasFDerivAt_of_bilinear hu.hasFDerivAt hv.hasFDerivAt
  apply (hasFDerivAt_iff_hasDerivAt.mp hpair).congr_deriv
  simp [ContinuousLinearMap.precompL_apply, path, path', symplecticForm_apply]
  ring

/-- At the identity time, the arbitrary-time formula reduces to the
infinitesimal symplectic defect. -/
theorem hasDerivAt_symplecticForm_exp_flow_pair_zero
    [CompleteSpace E] (G : Doubled E →L[ℝ] Doubled E)
    (u v : Doubled E) :
    HasDerivAt
      (fun t : ℝ => symplecticForm (NormedSpace.exp (t • G) u)
        (NormedSpace.exp (t • G) v))
      (symplecticForm (G u) v + symplecticForm u (G v)) 0 := by
  simpa using hasDerivAt_symplecticForm_exp_flow_pair G u v 0

/-- An operator is an infinitesimal symplectic generator exactly when every
pairing has zero first variation along its exponential flow at the identity. -/
theorem isSymplecticGenerator_iff_exp_flow_pair_deriv_zero
    [CompleteSpace E] (G : Doubled E →L[ℝ] Doubled E) :
    IsSymplecticGenerator G ↔
      ∀ u v : Doubled E,
        deriv (fun t : ℝ => symplecticForm (NormedSpace.exp (t • G) u)
          (NormedSpace.exp (t • G) v)) 0 = 0 := by
  constructor
  · intro hG u v
    rw [(hasDerivAt_symplecticForm_exp_flow_pair_zero G u v).deriv]
    exact hG u v
  · intro h u v
    have hd := h u v
    rw [(hasDerivAt_symplecticForm_exp_flow_pair_zero G u v).deriv] at hd
    exact hd

/-- Infinitesimal symplecticity is equivalent to preservation of the canonical
pairing by the entire one-parameter exponential flow. The reverse direction
recovers the infinitesimal identity by differentiating the constant pairing
at time zero. -/
theorem isSymplecticGenerator_iff_exp_flow_preserves_pairing
    [CompleteSpace E] (G : Doubled E →L[ℝ] Doubled E) :
    IsSymplecticGenerator G ↔
      ∀ t : ℝ, ∀ u v : Doubled E,
        symplecticForm (NormedSpace.exp (t • G) u)
          (NormedSpace.exp (t • G) v) = symplecticForm u v := by
  constructor
  · intro hG t u v
    exact exp_preserves_symplecticForm G hG t u v
  · intro h u v
    let pairing : ℝ → ℝ := fun t =>
      symplecticForm (NormedSpace.exp (t • G) u)
        (NormedSpace.exp (t • G) v)
    have hconst : pairing = fun _ => symplecticForm u v := by
      funext t
      exact h t u v
    have hderiv : deriv pairing 0 = 0 := by
      rw [hconst]
      simp
    rw [(hasDerivAt_symplecticForm_exp_flow_pair_zero G u v).deriv] at hderiv
    exact hderiv

/-- The quadratic Hamiltonian of a linear symplectic generator is conserved by
its own exponential flow. The proof uses commutation of the generator with its
exponential and preservation of the canonical doubled symplectic form. -/
theorem quadraticMoment_exp_flow_invariant
    [CompleteSpace E] (G : Doubled E →L[ℝ] Doubled E)
    (hG : IsSymplecticGenerator G) (t : ℝ) (z : Doubled E) :
    quadraticMoment G (NormedSpace.exp (t • G) z) = quadraticMoment G z := by
  let U : EndD := NormedSpace.exp (t • G)
  have hcomm : Commute G U := by
    simpa [U] using ((Commute.refl G).smul_right t).exp_right
  have hGU : G (U z) = U (G z) := by
    have h := congrArg (fun A : EndD => A z) hcomm.eq
    simpa [_root_.mul_apply_eq_comp, ContinuousLinearMap.comp_apply] using h
  rw [quadraticMoment_apply, quadraticMoment_apply, hGU]
  congr 1
  exact exp_preserves_symplecticForm G hG t (G z) z

/-- The canonical doubled symplectic form is nondegenerate, transported from
the existing chiral product-space proof through `WithLp.ofLp`. -/
theorem symplecticForm_nondegenerate (u : Doubled E)
    (h : ∀ v, symplecticForm u v = 0) :
    u = 0 := by
  apply WithLp.ofLp_injective (p := (2 : ENNReal))
  apply InfoGeometry.Canonical.ChiralBoundarySymplectic.ChiralDoubled.symplectic_nondegenerate
    (WithLp.ofLp u)
  intro v
  have hv := h (WithLp.toLp (2 : ENNReal) v)
  simpa [symplecticForm_eq_chiral,
    InfoGeometry.Canonical.ChiralBoundarySymplectic.ChiralDoubled.symplecticForm,
    real_inner_comm] using hv

/-- The quadratic moment separates infinitesimal symplectic generators: if
their Hamiltonians agree at every doubled state, then the generators agree. -/
theorem quadraticMoment_injective_on_symplecticGenerators
    {A B : Doubled E →L[ℝ] Doubled E}
    (hA : IsSymplecticGenerator A) (hB : IsSymplecticGenerator B)
    (h : quadraticMoment A = quadraticMoment B) :
    A = B := by
  apply ContinuousLinearMap.ext
  intro z
  apply sub_eq_zero.mp
  apply symplecticForm_nondegenerate
  intro v
  have hd := congrArg (fun f : Doubled E → ℝ => fderiv ℝ f z v) h
  rw [fderiv_quadraticMoment A hA, fderiv_quadraticMoment B hB] at hd
  rw [map_sub, sub_apply]
  linarith

/-- The commutator of two infinitesimal symplectic generators is again
infinitesimally symplectic. This makes the generator carrier a Lie subalgebra. -/
theorem lie_isSymplecticGenerator
    {A B : Doubled E →L[ℝ] Doubled E}
    (hA : IsSymplecticGenerator A) (hB : IsSymplecticGenerator B) :
    IsSymplecticGenerator ⁅A, B⁆ := by
  intro u v
  change symplecticForm (A (B u) - B (A u)) v +
      symplecticForm u (A (B v) - B (A v)) = 0
  simp only [map_sub, sub_apply]
  have hA₁ := hA (B u) v
  have hA₂ := hA u (B v)
  have hB₁ := hB (A u) v
  have hB₂ := hB u (A v)
  linear_combination hA₁ - hB₁ + hA₂ - hB₂

/-- The real Lie algebra of continuous infinitesimal symplectic operators on
the canonical doubled carrier. -/
def symplecticGeneratorLieSubalgebra :
    LieSubalgebra ℝ (Doubled E →L[ℝ] Doubled E) where
  carrier := {G | IsSymplecticGenerator G}
  zero_mem' := by
    intro u v
    simp
  add_mem' := by
    intro A B hA hB u v
    change IsSymplecticGenerator A at hA
    change IsSymplecticGenerator B at hB
    simp only [add_apply, map_add]
    linear_combination hA u v + hB u v
  smul_mem' := by
    intro c A hA u v
    change IsSymplecticGenerator A at hA
    simp only [smul_apply, map_smul, smul_eq_mul]
    linear_combination c * hA u v
  lie_mem' := by
    intro A B hA hB
    exact lie_isSymplecticGenerator hA hB

/-- The Hamiltonian bracket of two linear moment-map components, in the
convention `{H_A,H_B}(z) = Ω(Az,Bz)`, is the component for the commutator
generator. Thus the quadratic map respects the generator Lie bracket. -/
def quadraticMomentBracket
    (A B : Doubled E →L[ℝ] Doubled E) (z : Doubled E) : ℝ :=
  symplecticForm (A z) (B z)

theorem quadraticMomentBracket_eq_commutatorMoment
    (A B : Doubled E →L[ℝ] Doubled E)
    (hA : IsSymplecticGenerator A) (hB : IsSymplecticGenerator B)
    (z : Doubled E) :
    quadraticMomentBracket A B z = quadraticMoment ⁅A, B⁆ z := by
  rw [quadraticMoment_apply]
  change symplecticForm (A z) (B z) =
    symplecticForm (A (B z) - B (A z)) z / 2
  rw [map_sub]
  have hA' := hA (B z) z
  have hB' := hB (A z) z
  have hskew := symplecticForm_skew (B z) (A z)
  have hAB : symplecticForm (A (B z)) z = symplecticForm (A z) (B z) := by
    linarith
  have hBA : symplecticForm (B (A z)) z = -symplecticForm (A z) (B z) := by
    linarith
  rw [sub_apply, hAB, hBA]
  ring

/-- Evaluation of the real doubled moment map at a fixed state is a genuine
linear functional on the infinitesimal symplectic-generator Lie algebra. -/
noncomputable def quadraticMomentFunctional (z : Doubled E) :
    Module.Dual ℝ (Doubled E →L[ℝ] Doubled E) where
  toFun G := quadraticMoment G z
  map_add' A B := by
    simp [quadraticMoment_apply]
    ring
  map_smul' r A := by
    simp [quadraticMoment_apply]
    ring

/-- The Poisson bracket of two quadratic Hamiltonians is exactly the KKS
form of the evaluation functional `G ↦ H_G(z)` on the commutator of their
infinitesimal symplectic generators. -/
theorem quadraticMomentBracket_eq_kksForm
    (A B : Doubled E →L[ℝ] Doubled E)
    (hA : IsSymplecticGenerator A) (hB : IsSymplecticGenerator B)
    (z : Doubled E) :
    quadraticMomentBracket A B z =
      SouriauKKS.kksForm (quadraticMomentFunctional z) A B := by
  rw [quadraticMomentBracket_eq_commutatorMoment A B hA hB z]
  rfl

/-- The KKS form induced by the doubled quadratic moment map is closed in the
Chevalley--Eilenberg cyclic sense. This is an actual consequence of the
generator Lie algebra and Jacobi, not a cocycle field supplied as data. -/
theorem quadraticMomentBracket_cyclic_closed
    (A B C : Doubled E →L[ℝ] Doubled E)
    (hA : IsSymplecticGenerator A) (hB : IsSymplecticGenerator B)
    (hC : IsSymplecticGenerator C) (z : Doubled E) :
    quadraticMomentBracket A (⁅B, C⁆) z +
      quadraticMomentBracket B (⁅C, A⁆) z +
      quadraticMomentBracket C (⁅A, B⁆) z = 0 := by
  have hBC := lie_isSymplecticGenerator hB hC
  have hCA := lie_isSymplecticGenerator hC hA
  have hAB := lie_isSymplecticGenerator hA hB
  calc
    quadraticMomentBracket A (⁅B, C⁆) z +
        quadraticMomentBracket B (⁅C, A⁆) z +
        quadraticMomentBracket C (⁅A, B⁆) z =
      SouriauKKS.kksForm (quadraticMomentFunctional z) A ⁅B, C⁆ +
        SouriauKKS.kksForm (quadraticMomentFunctional z) B ⁅C, A⁆ +
        SouriauKKS.kksForm (quadraticMomentFunctional z) C ⁅A, B⁆ := by
          rw [quadraticMomentBracket_eq_kksForm A ⁅B, C⁆ hA hBC z,
            quadraticMomentBracket_eq_kksForm B ⁅C, A⁆ hB hCA z,
            quadraticMomentBracket_eq_kksForm C ⁅A, B⁆ hC hAB z]
    _ = 0 := SouriauKKS.kksForm_jacobi (quadraticMomentFunctional z) A B C

/-- The type of actual infinitesimal symplectic generators, with the Lie
bracket inherited from continuous endomorphisms of the real doubled carrier. -/
abbrev SymplecticGenerators := symplecticGeneratorLieSubalgebra (E := E)

/-- The symplectic-generator Lie algebra acts on the doubled real carrier by
its defining bounded endomorphisms. This is the repository's `QuantumMomentMap`
interface with observable algebra `EndD`: the map is the actual inclusion,
and Lie compatibility is the commutator law inherited from the associative
endomorphism algebra. -/
noncomputable def souriauQuantumMomentMapRepresentation [CompleteSpace E] :
    InfoGeometry.Physics.SouriauLieThermodynamics.QuantumMomentMap
      (R := ℝ) (g := SymplecticGenerators (E := E)) (A := EndD) where
  toLinearMap :=
    { toFun := fun A => (A : EndD)
      map_add' := by intro A B; rfl
      map_smul' := by intro r A; rfl }
  lie_compat := by
    intro A B
    change (⁅(A : EndD), (B : EndD)⁆) =
      (A : EndD) * (B : EndD) - (B : EndD) * (A : EndD)
    simp only [Ring.lie_def]

/-- Evaluating the Souriau representation at a generator returns its bounded
real endomorphism, so the representation uses precisely the operator already
driving the doubled Hamiltonian. -/
@[simp] theorem souriauQuantumMomentMapRepresentation_apply
    [CompleteSpace E] (A : SymplecticGenerators (E := E)) :
    (souriauQuantumMomentMapRepresentation (E := E)).toLinearMap A =
      (A : EndD) := rfl

/-- The genuine Souriau moment map takes values in the dual of the Lie algebra
of infinitesimal symplectic generators, rather than the dual of the ambient
endomorphism space. -/
noncomputable def souriauMomentMap (z : Doubled E) :
    Module.Dual ℝ (SymplecticGenerators (E := E)) where
  toFun A := quadraticMoment (A : EndD) z
  map_add' A B := by
    simp [quadraticMoment_apply]
    ring
  map_smul' r A := by
    simp [quadraticMoment_apply]
    ring

/-- The algebraic evaluation functional on ambient bounded real generators is
continuous in operator norm. Its bound is derived from the doubled
symplectic-pairing estimate, not supplied as moment-map data. -/
noncomputable def quadraticMomentFunctionalContinuous [CompleteSpace E] (z : Doubled E) :
    (Doubled E →L[ℝ] Doubled E) →L[ℝ] ℝ :=
  (quadraticMomentFunctional z).mkContinuous (‖z‖ ^ 2 / 2) (by
    intro G
    rw [Real.norm_eq_abs]
    have h := abs_quadraticMoment_le_generator_norm G z
    calc
      |quadraticMoment G z| ≤ (‖G‖ * ‖z‖ ^ 2) / 2 := h
      _ = (‖z‖ ^ 2 / 2) * ‖G‖ := by ring)

/-- The ambient continuous evaluation functional has operator norm at most
the quadratic state scale. -/
theorem quadraticMomentFunctionalContinuous_norm_le [CompleteSpace E] (z : Doubled E) :
    ‖quadraticMomentFunctionalContinuous z‖ ≤ ‖z‖ ^ 2 / 2 := by
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- As a map into the continuous dual of ambient bounded generators, the
quadratic moment is Lipschitz on every positive-Hilbert ball. This upgrades
the componentwise estimate to the operator norm of the full dual-valued
moment map. -/
theorem quadraticMomentFunctionalContinuous_lipschitzOn_ball [CompleteSpace E]
    (R : ℝ) (z w : Doubled E) (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖quadraticMomentFunctionalContinuous z - quadraticMomentFunctionalContinuous w‖ ≤
      R * ‖z - w‖ := by
  have hR : 0 ≤ R := le_trans (norm_nonneg z) hz
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hR (norm_nonneg (z - w))) ?_
  intro G
  rw [Real.norm_eq_abs]
  have h := souriauMoment_lipschitzOn_ball G R z w hz hw
  change |quadraticMoment G z - quadraticMoment G w| ≤
    (R * ‖z - w‖) * ‖G‖
  calc
    |quadraticMoment G z - quadraticMoment G w| ≤ R * ‖G‖ * ‖z - w‖ := h
    _ = (R * ‖z - w‖) * ‖G‖ := by ring

/-- Restricting the continuous ambient functional to an infinitesimal
symplectic generator recovers the Souriau moment-map component. -/
@[simp] theorem quadraticMomentFunctionalContinuous_apply_generator
    [CompleteSpace E] (z : Doubled E) (A : SymplecticGenerators (E := E)) :
    quadraticMomentFunctionalContinuous z (A : EndD) = souriauMomentMap z A := rfl

/-- The Souriau component is continuous as a function of the generator on the
Lie-subalgebra subtype, by restriction of the ambient operator-norm
functional. -/
theorem continuous_souriauMomentMap_component [CompleteSpace E] (z : Doubled E) :
    Continuous (fun A : SymplecticGenerators (E := E) => souriauMomentMap z A) := by
  exact (quadraticMomentFunctionalContinuous z).continuous.comp continuous_subtype_val

/-- The Souriau moment at a fixed doubled state is a bounded functional on
the actual infinitesimal symplectic Lie algebra. It is obtained by restricting
the ambient operator-norm continuous functional, so continuity is proved from
the quadratic estimate rather than assumed as part of the moment-map data. -/
noncomputable def souriauMomentMapContinuous [CompleteSpace E] (z : Doubled E) :
    SymplecticGenerators (E := E) →L[ℝ] ℝ :=
  (quadraticMomentFunctionalContinuous z).comp
    (symplecticGeneratorLieSubalgebra (E := E)).toSubmodule.subtypeL

/-- The continuous dual-valued representative agrees with the algebraic
Souriau moment map on every symplectic generator. -/
@[simp] theorem souriauMomentMapContinuous_apply [CompleteSpace E]
    (z : Doubled E) (A : SymplecticGenerators (E := E)) :
    souriauMomentMapContinuous z A = souriauMomentMap z A := rfl

/-- The full moment functional, measured in the operator norm of the
continuous dual of the symplectic-generator Lie algebra, is Lipschitz on
positive-Hilbert balls. This is the dual-valued estimate, not merely
continuity of each scalar component. -/
theorem souriauMomentMapContinuous_lipschitzOn_ball [CompleteSpace E]
    (R : ℝ) (z w : Doubled E) (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖souriauMomentMapContinuous z - souriauMomentMapContinuous w‖ ≤
      R * ‖z - w‖ := by
  have hR : 0 ≤ R := le_trans (norm_nonneg z) hz
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hR (norm_nonneg (z - w))) ?_
  intro A
  rw [Real.norm_eq_abs]
  have h := souriauMoment_lipschitzOn_ball (A : EndD) R z w hz hw
  change |quadraticMoment (A : EndD) z - quadraticMoment (A : EndD) w| ≤
    (R * ‖z - w‖) * ‖A‖
  calc
    |quadraticMoment (A : EndD) z - quadraticMoment (A : EndD) w| ≤
        R * ‖(A : EndD)‖ * ‖z - w‖ := h
    _ = (R * ‖z - w‖) * ‖A‖ := by simp [mul_comm, mul_left_comm, mul_assoc]

/-- Pairing the Souriau moment map with a generator has the Hamiltonian
Fréchet derivative prescribed by the real doubled symplectic form. -/
theorem hasFDerivAt_souriauMoment_component
    (A : SymplecticGenerators (E := E)) (z : Doubled E) :
    HasFDerivAt (fun w => souriauMomentMap w A)
      (symplecticForm ((A : EndD) z)) z := by
  have hfun : (fun w => souriauMomentMap w A) =
      quadraticMoment (A : EndD) := by
    funext w
    rfl
  rw [hfun]
  exact hasFDerivAt_quadraticMoment (A : EndD) A.property z

/-- Infinitesimal equivariance of the doubled Souriau moment map: the
derivative of the `A`-component along the linear vector field generated by
`B` is the moment-map component of the Lie bracket `[A,B]`. This is the
Hamiltonian infinitesimal-action law on the actual real doubled carrier. -/
theorem fderiv_souriauMoment_component_along_generator
    (A B : SymplecticGenerators (E := E)) (z : Doubled E) :
    fderiv ℝ (fun w => souriauMomentMap w A) z ((B : EndD) z) =
      souriauMomentMap z ⁅A, B⁆ := by
  have hfun : (fun w => souriauMomentMap w A) =
      quadraticMoment (A : EndD) := by
    funext w
    rfl
  rw [hfun]
  rw [fderiv_quadraticMoment (A : EndD) A.property z ((B : EndD) z)]
  calc
    symplecticForm ((A : EndD) z) ((B : EndD) z) =
        quadraticMomentBracket (A : EndD) (B : EndD) z := rfl
    _ = quadraticMoment ⁅(A : EndD), (B : EndD)⁆ z :=
      quadraticMomentBracket_eq_commutatorMoment
        (A : EndD) (B : EndD) A.property B.property z
    _ = souriauMomentMap z ⁅A, B⁆ := rfl

/-- The Souriau reversible pairing on the genuine Lie subalgebra of
infinitesimal symplectic generators. -/
noncomputable def souriauReversibleForm (z : Doubled E) :
    LinearMap.BilinForm ℝ (SymplecticGenerators (E := E)) :=
  LinearMap.mk₂ ℝ
    (fun A B => quadraticMomentBracket (A : EndD) (B : EndD) z)
    (by
      intro A₁ A₂ B
      change quadraticMomentBracket ((A₁ : EndD) + (A₂ : EndD)) (B : EndD) z = _
      simp [quadraticMomentBracket, add_apply, map_add])
    (by
      intro r A B
      change quadraticMomentBracket (r • (A : EndD)) (B : EndD) z = _
      simp [quadraticMomentBracket, smul_apply, map_smul])
    (by
      intro A B₁ B₂
      change quadraticMomentBracket (A : EndD) ((B₁ : EndD) + (B₂ : EndD)) z = _
      simp [quadraticMomentBracket, add_apply, map_add])
    (by
      intro r A B
      change quadraticMomentBracket (A : EndD) (r • (B : EndD)) z = _
      simp [quadraticMomentBracket, smul_apply, map_smul])

/-- This doubled Souriau pairing is skew-symmetric, so it is a genuine
reversible Onsager form on the symplectic-generator sector. -/
theorem souriauReversibleForm_skew (z : Doubled E)
    (A B : SymplecticGenerators (E := E)) :
    souriauReversibleForm z A B = -souriauReversibleForm z B A := by
  exact symplecticForm_skew ((A : EndD) z) ((B : EndD) z)

/-- The reversible Souriau sector is Chevalley--Eilenberg closed on the
symplectic-generator Lie algebra. The closure follows from Jacobi via the
derived KKS identification above. -/
theorem souriauReversibleForm_cyclic_closed (z : Doubled E)
    (A B C : SymplecticGenerators (E := E)) :
    souriauReversibleForm z A ⁅B, C⁆ +
      souriauReversibleForm z B ⁅C, A⁆ +
      souriauReversibleForm z C ⁅A, B⁆ = 0 := by
  exact quadraticMomentBracket_cyclic_closed
    (A : EndD) (B : EndD) (C : EndD) A.property B.property C.property z

/-- A concrete reversible Onsager--Casimir system built from the doubled
Souriau moment. Its dissipative part is explicitly zero; this construction
identifies the reversible/KKS curvature only and makes no claim that it
provides a nontrivial dissipative BKM metric. -/
noncomputable def souriauReversibleOnsagerSystem (z : Doubled E) :
    InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem
      (SymplecticGenerators (E := E)) where
  dissipative := 0
  reversible := souriauReversibleForm z
  dissipative_symm := by simp
  reversible_skew := souriauReversibleForm_skew z
  dissipative_nonneg := by simp

/-- The constructed Onsager system has zero entropy production because it is
the purely reversible Souriau/KKS sector. -/
theorem souriauReversibleOnsagerSystem_entropy_production_zero
    (z : Doubled E) (A : SymplecticGenerators (E := E)) :
    (souriauReversibleOnsagerSystem z).totalGenerator A A = 0 := by
  rw [(souriauReversibleOnsagerSystem z).entropy_production_eq A]
  simp [souriauReversibleOnsagerSystem]

/-- A continuous linear equivalence preserving the doubled symplectic form. -/
def IsSymplecticEquiv (S : Doubled E ≃L[ℝ] Doubled E) : Prop :=
  ∀ u v, symplecticForm (S u) (S v) = symplecticForm u v

/-- Conjugation of a generator by a continuous linear equivalence. -/
noncomputable def conjugateGenerator
    (S : Doubled E ≃L[ℝ] Doubled E) (G : Doubled E →L[ℝ] Doubled E) :
    Doubled E →L[ℝ] Doubled E :=
  S.symm.toContinuousLinearMap.comp (G.comp S.toContinuousLinearMap)

/-- Conjugation by a continuous linear equivalence preserves the commutator
Lie bracket on bounded endomorphisms. -/
theorem conjugateGenerator_lie
    (S : Doubled E ≃L[ℝ] Doubled E)
    (A B : Doubled E →L[ℝ] Doubled E) :
    conjugateGenerator S ⁅A, B⁆ =
      ⁅conjugateGenerator S A, conjugateGenerator S B⁆ := by
  apply ContinuousLinearMap.ext
  intro u
  simp [conjugateGenerator, ContinuousLinearMap.comp_apply,
    Ring.lie_def]

/-- Symplectic conjugation preserves the infinitesimal generator identity. -/
theorem conjugateGenerator_isSymplecticGenerator
    (S : Doubled E ≃L[ℝ] Doubled E) (hS : IsSymplecticEquiv S)
    (G : Doubled E →L[ℝ] Doubled E) (hG : IsSymplecticGenerator G) :
    IsSymplecticGenerator (conjugateGenerator S G) := by
  intro u v
  calc
    symplecticForm (conjugateGenerator S G u) v +
        symplecticForm u (conjugateGenerator S G v) =
        symplecticForm (S (conjugateGenerator S G u)) (S v) +
          symplecticForm (S u) (S (conjugateGenerator S G v)) := by
            rw [hS, hS]
    _ = symplecticForm (G (S u)) (S v) +
          symplecticForm (S u) (G (S v)) := by
            simp [conjugateGenerator]
    _ = 0 := hG (S u) (S v)

/-- Symplectic conjugation acts on the generator Lie algebra by the actual
conjugated continuous operator. -/
noncomputable def conjugateSymplecticGenerator
    (S : Doubled E ≃L[ℝ] Doubled E) (hS : IsSymplecticEquiv S)
    (A : SymplecticGenerators (E := E)) :
    SymplecticGenerators (E := E) where
  val := conjugateGenerator S (A : EndD)
  property := conjugateGenerator_isSymplecticGenerator S hS
    (A : EndD) A.property

/-- The quadratic moment is equivariant under symplectic conjugation. -/
theorem quadraticMoment_equivariant
    (S : Doubled E ≃L[ℝ] Doubled E) (hS : IsSymplecticEquiv S)
    (G : Doubled E →L[ℝ] Doubled E) (z : Doubled E) :
    quadraticMoment G (S z) =
      quadraticMoment (conjugateGenerator S G) z := by
  rw [quadraticMoment_apply, quadraticMoment_apply]
  have hconj : S (conjugateGenerator S G z) = G (S z) := by
    simp [conjugateGenerator]
  rw [← hconj, hS]

/-- The dual-valued Souriau map is equivariant under symplectic changes of
frame: evaluating at `A` after transporting the state equals evaluating at
the conjugated generator `S⁻¹ A S` before transport. -/
theorem souriauMomentMap_equivariant
    (S : Doubled E ≃L[ℝ] Doubled E) (hS : IsSymplecticEquiv S)
    (A : SymplecticGenerators (E := E)) (z : Doubled E) :
    souriauMomentMap (S z) A =
      souriauMomentMap z (conjugateSymplecticGenerator S hS A) := by
  exact quadraticMoment_equivariant S hS (A : EndD) z

/-- The concrete doubled Souriau moment map transports the KKS pairing under
the induced conjugation action on its actual symplectic-generator Lie algebra.
This specializes the repository's abstract contragredient KKS invariance to
the real doubled carrier and its quadratic moment map. -/
theorem souriauKKS_pairing_equivariant
    (S : Doubled E ≃L[ℝ] Doubled E) (hS : IsSymplecticEquiv S)
    (A B : SymplecticGenerators (E := E)) (z : Doubled E) :
    SouriauKKS.kksForm (souriauMomentMap (S z))
        (conjugateSymplecticGenerator S.symm
          (by
            intro u v
            have h := hS (S.symm u) (S.symm v)
            simpa using h.symm) A)
        (conjugateSymplecticGenerator S.symm
          (by
            intro u v
            have h := hS (S.symm u) (S.symm v)
            simpa using h.symm) B) =
      SouriauKKS.kksForm (souriauMomentMap z) A B := by
  rw [SouriauKKS.kksForm, SouriauKKS.kksForm]
  let hSinv : IsSymplecticEquiv S.symm := by
    intro u v
    have h := hS (S.symm u) (S.symm v)
    simpa using h.symm
  have hbracket :
      ⁅conjugateSymplecticGenerator S.symm hSinv A,
        conjugateSymplecticGenerator S.symm hSinv B⁆ =
        conjugateSymplecticGenerator S.symm hSinv ⁅A, B⁆ := by
    apply Subtype.ext
    exact (conjugateGenerator_lie S.symm (A : EndD) (B : EndD)).symm
  rw [hbracket]
  change quadraticMoment
    (conjugateGenerator S.symm
      (⁅(A : EndD), (B : EndD)⁆)) (S z) = quadraticMoment ⁅(A : EndD), (B : EndD)⁆ z
  simpa using (quadraticMoment_equivariant S.symm hSinv
    ⁅(A : EndD), (B : EndD)⁆ (S z)).symm

/-- The exponential of a completed infinitesimal symplectic generator is an
actual continuous linear equivalence. Its inverse is the exponential of the
negative generator; this records the finite-time flow on the same doubled
carrier rather than merely a pointwise preservation identity. -/
noncomputable def symplecticFlowEquiv [CompleteSpace E]
    (G : Doubled E →L[ℝ] Doubled E) (t : ℝ) :
    Doubled E ≃L[ℝ] Doubled E := by
  let U : EndD := NormedSpace.exp (t • G)
  let V : EndD := NormedSpace.exp (-(t • G))
  have hcomm : Commute (-(t • G)) (t • G) := (Commute.refl (t • G)).neg_left
  have hVU : V * U = 1 := by
    change NormedSpace.exp (-(t • G)) * NormedSpace.exp (t • G) = 1
    rw [← NormedSpace.exp_add_of_commute hcomm]
    simp
  have hUV : U * V = 1 := by
    change NormedSpace.exp (t • G) * NormedSpace.exp (-(t • G)) = 1
    rw [← NormedSpace.exp_add_of_commute hcomm.symm]
    simp
  have hVU_apply : ∀ x, V (U x) = x := by
    intro x
    have h := congrArg (fun T : EndD => T x) hVU
    simpa [_root_.mul_apply_eq_comp, ContinuousLinearMap.comp_apply] using h
  have hUV_apply : ∀ x, U (V x) = x := by
    intro x
    have h := congrArg (fun T : EndD => T x) hUV
    simpa [_root_.mul_apply_eq_comp, ContinuousLinearMap.comp_apply] using h
  have hinj : Function.Injective U := by
    intro x y hxy
    calc
      x = V (U x) := (hVU_apply x).symm
      _ = V (U y) := congrArg V hxy
      _ = y := hVU_apply y
  have hsurj : Function.Surjective U := by
    intro y
    exact ⟨V y, hUV_apply y⟩
  exact ContinuousLinearEquiv.ofBijective U
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)

/-- The finite-time exponential flow acts on the doubled Souriau moment map
by the corresponding conjugation action on the symplectic-generator dual.
Thus the componentwise infinitesimal equivariance integrates to an actual
coadjoint transport identity for every real time. -/
theorem souriauMomentMap_exp_flow_equivariant [CompleteSpace E]
    (G : Doubled E →L[ℝ] Doubled E) (hG : IsSymplecticGenerator G)
    (t : ℝ) (A : SymplecticGenerators (E := E)) (z : Doubled E) :
    souriauMomentMap (NormedSpace.exp (t • G) z) A =
      souriauMomentMap z
        (conjugateSymplecticGenerator (symplecticFlowEquiv G t)
          (fun u v => exp_preserves_symplecticForm G hG t u v) A) := by
  exact souriauMomentMap_equivariant (symplecticFlowEquiv G t)
    (fun u v => exp_preserves_symplecticForm G hG t u v) A z

/-- The finite exponential flow transports the concrete KKS pairing on the
symplectic-generator subalgebra without changing its value. -/
theorem souriauKKS_pairing_exp_flow_equivariant [CompleteSpace E]
    (G : Doubled E →L[ℝ] Doubled E) (hG : IsSymplecticGenerator G)
    (t : ℝ) (A B : SymplecticGenerators (E := E)) (z : Doubled E) :
    SouriauKKS.kksForm
        (souriauMomentMap (NormedSpace.exp (t • G) z))
        (conjugateSymplecticGenerator (symplecticFlowEquiv G t).symm
          (by
            intro u v
            have h := exp_preserves_symplecticForm G hG t
              ((symplecticFlowEquiv G t).symm u) ((symplecticFlowEquiv G t).symm v)
            have hu : NormedSpace.exp (t • G)
                ((symplecticFlowEquiv G t).symm u) = u :=
              (symplecticFlowEquiv G t).apply_symm_apply u
            have hv : NormedSpace.exp (t • G)
                ((symplecticFlowEquiv G t).symm v) = v :=
              (symplecticFlowEquiv G t).apply_symm_apply v
            rw [hu, hv] at h
            exact h.symm) A)
        (conjugateSymplecticGenerator (symplecticFlowEquiv G t).symm
          (by
            intro u v
            have h := exp_preserves_symplecticForm G hG t
              ((symplecticFlowEquiv G t).symm u) ((symplecticFlowEquiv G t).symm v)
            have hu : NormedSpace.exp (t • G)
                ((symplecticFlowEquiv G t).symm u) = u :=
              (symplecticFlowEquiv G t).apply_symm_apply u
            have hv : NormedSpace.exp (t • G)
                ((symplecticFlowEquiv G t).symm v) = v :=
              (symplecticFlowEquiv G t).apply_symm_apply v
            rw [hu, hv] at h
            exact h.symm) B) =
      SouriauKKS.kksForm (souriauMomentMap z) A B := by
  exact souriauKKS_pairing_equivariant (symplecticFlowEquiv G t)
    (fun u v => exp_preserves_symplecticForm G hG t u v) A B z

/-- At every time, the derivative of the finite-time Souriau transport is the
coadjoint Lie-bracket component evaluated at the transported state. The
trajectory derivative is computed from the exponential and its commutation
with its generator; the final identity is the already-proved Hamiltonian
infinitesimal-action law. -/
theorem hasDerivAt_souriauMomentMap_exp_flow_component
    [CompleteSpace E]
    (B : SymplecticGenerators (E := E))
    (A : SymplecticGenerators (E := E)) (z : Doubled E) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => souriauMomentMap (NormedSpace.exp (s • (B : EndD)) z) A)
      (souriauMomentMap (NormedSpace.exp (t • (B : EndD)) z) ⁅A, B⁆) t := by
  let path : ℝ → Doubled E := fun s => NormedSpace.exp (s • (B : EndD)) z
  have hexp : HasDerivAt
      (fun s : ℝ => NormedSpace.exp (s • (B : EndD)))
      (NormedSpace.exp (t • (B : EndD)) * (B : EndD)) t :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) (B : EndD) t
  have hconst : HasDerivAt (fun _ : ℝ => z) (0 : Doubled E) t :=
    hasDerivAt_const t z
  have hpath₀ := hexp.clm_apply hconst
  have hflowCommute : Commute (B : EndD) (NormedSpace.exp (t • (B : EndD))) := by
    simpa using ((Commute.refl (B : EndD)).smul_right t).exp_right
  have hcommPoint :
      (NormedSpace.exp (t • (B : EndD))) ((B : EndD) z) =
        (B : EndD) ((NormedSpace.exp (t • (B : EndD))) z) := by
    have hcomm := congrArg (fun T : EndD => T z) hflowCommute.eq.symm
    simpa [_root_.mul_apply_eq_comp, ContinuousLinearMap.comp_apply] using hcomm
  have hpath : HasDerivAt path ((B : EndD) (path t)) t := by
    convert hpath₀ using 1
    · simpa [path] using hcommPoint.symm
  have hcomp := (hasFDerivAt_souriauMoment_component A (path t)).comp_hasDerivAt
    t hpath
  convert hcomp using 1
  · ext s
    rfl
  · calc
      souriauMomentMap (path t) ⁅A, B⁆ =
          fderiv ℝ (fun w => souriauMomentMap w A) (path t)
            ((B : EndD) (path t)) :=
              (fderiv_souriauMoment_component_along_generator A B (path t)).symm
      _ = symplecticForm ((A : EndD) (path t)) ((B : EndD) (path t)) := by
        rw [(hasFDerivAt_souriauMoment_component A (path t)).fderiv]

/-- The zero-time derivative is the coadjoint Lie-bracket component at the
initial state. -/
theorem hasDerivAt_souriauMomentMap_exp_flow_component_zero
    [CompleteSpace E]
    (B : SymplecticGenerators (E := E))
    (A : SymplecticGenerators (E := E)) (z : Doubled E) :
    HasDerivAt
      (fun t : ℝ => souriauMomentMap (NormedSpace.exp (t • (B : EndD)) z) A)
      (souriauMomentMap z ⁅A, B⁆) 0 := by
  simpa using hasDerivAt_souriauMomentMap_exp_flow_component B A z 0

end InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap

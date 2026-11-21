/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.ChiralBoundarySymplecticBridge
import InfoGeometry.Canonical.SouriauKKSForm
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

end InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap

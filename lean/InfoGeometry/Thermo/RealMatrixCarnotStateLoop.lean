/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Thermo.RealMatrixCarnot
import Mathlib.Topology.Path

/-! # The density path of the real matrix Carnot cycle

The carrier is the full real matrix algebra. The hot and cold isotherms use
the actual Gibbs states of `RealMatrixCarnot.affineHamiltonian`; neither the
Hamiltonians nor the transported group elements are assumed to commute.
The cold density path is exactly the reverse of the hot density path. Each
reciprocal-scale stroke is a path built from its changing controls, and the
Gibbs scaling identity proves that its density is constant.

The resulting four-stroke native `Path` therefore has identity transport for
any group-valued path transport satisfying constant-path, reversal, and
chronological concatenation laws. The convention is
`transport (p.trans q) = transport p * transport q`. No homotopy-invariance
or flatness hypothesis is used, and the loop is not asserted to be equal to
a constant parametrized path.

This is a conditional cancellation theorem for transport on density space.
It does not construct an operator or Uhlmann connection, solve a parallel
transport ODE, or identify a Souriau symmetry cocycle with geometric holonomy.
The nonzero work integral of the cycle also depends on the Hamiltonian
control, which the density projection forgets.
-/

noncomputable section

namespace InfoGeometry.Thermo.RealMatrixCarnotStateLoop

open RealMatrixCarnot
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℝ

/-! ## Exact identities on the Hamiltonian and density curves -/

omit [Fintype n] [DecidableEq n] in
/-- Reversing the affine control interchanges its endpoints. -/
theorem affineHamiltonian_reverse (H₀ H₁ : Mat) (t : ℝ) :
    affineHamiltonian H₁ H₀ t = affineHamiltonian H₀ H₁ (1 - t) := by
  simp only [affineHamiltonian, sub_smul, one_smul, smul_sub]
  abel

omit [Fintype n] [DecidableEq n] in
/-- Simultaneous scalar rescaling preserves the full affine matrix curve. -/
theorem affineHamiltonian_smul (c : ℝ) (H₀ H₁ : Mat) (t : ℝ) :
    affineHamiltonian (c • H₀) (c • H₁) t =
      c • affineHamiltonian H₀ H₁ t := by
  simp only [affineHamiltonian, smul_add, smul_sub, smul_smul, mul_comm]

/-- The scaled cold isotherm retraces the hot density curve pointwise.
This equality needs no positivity, self-adjointness, or commutation premise;
those analytic premises enter only when constructing the native paths. -/
theorem coldState_eq_hotState_reverse (β c : ℝ) (H₀ H₁ : Mat)
    (hc : c ≠ 0) (t : ℝ) :
    state (β / c) (affineHamiltonian (c • H₁) (c • H₀) t) =
      state β (affineHamiltonian H₀ H₁ (1 - t)) := by
  rw [affineHamiltonian_smul, state_cold_corner β c _ hc,
    affineHamiltonian_reverse]

/-! ## Native paths made from the actual Gibbs curves -/

/-- The hot Gibbs curve as a native path. Continuity is supplied by the
proved continuously differentiable full matrix Gibbs construction. -/
def hotStatePath [Nonempty n] (β : ℝ) (H₀ H₁ : Mat)
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) :
    Path (state β H₀) (state β H₁) where
  toFun t := state β (affineHamiltonian H₀ H₁ (t : ℝ))
  continuous_toFun :=
    (contDiff_state_affine β H₀ H₁ h₀ h₁).continuous.comp continuous_subtype_val
  source' := by simp
  target' := by simp

@[simp] theorem hotStatePath_apply [Nonempty n] (β : ℝ) (H₀ H₁ : Mat)
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) (t : unitInterval) :
    hotStatePath β H₀ H₁ h₀ h₁ t =
      state β (affineHamiltonian H₀ H₁ (t : ℝ)) := rfl

/-- The reciprocal-scale stroke is defined from its actual changing inverse
temperature and Hamiltonian. Positivity of both scale endpoints prevents
division by zero throughout the unit interval. -/
def scalingStatePath (β a b : ℝ) (H : Mat) (ha : 0 < a) (hb : 0 < b) :
    Path (state β H) (state β H) where
  toFun t := state (β / scaleSegment a b (t : ℝ))
    (scaleSegment a b (t : ℝ) • H)
  continuous_toFun :=
    continuous_const.congr (fun t =>
      (state_scaling_segment H β a b (t : ℝ) ha hb t.property).symm)
  source' := state_scaling_segment H β a b 0 ha hb ⟨le_rfl, zero_le_one⟩
  target' := state_scaling_segment H β a b 1 ha hb ⟨zero_le_one, le_rfl⟩

@[simp] theorem scalingStatePath_apply (β a b : ℝ) (H : Mat)
    (ha : 0 < a) (hb : 0 < b) (t : unitInterval) :
    scalingStatePath β a b H ha hb t =
      state (β / scaleSegment a b (t : ℝ))
        (scaleSegment a b (t : ℝ) • H) := rfl

/-- The native path built from the reciprocal controls is exactly constant
after projection to density space. -/
theorem scalingStatePath_eq_refl (β a b : ℝ) (H : Mat)
    (ha : 0 < a) (hb : 0 < b) :
    scalingStatePath β a b H ha hb = Path.refl (state β H) := by
  apply Path.ext
  funext t
  exact state_scaling_segment H β a b (t : ℝ) ha hb t.property

/-- The actual cold Gibbs curve, with its endpoint types normalized using
the reciprocal-scale corner identity. -/
def coldStatePath [Nonempty n] (β c : ℝ) (H₀ H₁ : Mat)
    (hc : c ≠ 0) (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) :
    Path (state β H₁) (state β H₀) where
  toFun t := state (β / c)
    (affineHamiltonian (c • H₁) (c • H₀) (t : ℝ))
  continuous_toFun := by
    have h₀c : IsSelfAdjoint (c • H₀) := by
      rw [isSelfAdjoint_iff]
      simp [star_smul, h₀.star_eq]
    have h₁c : IsSelfAdjoint (c • H₁) := by
      rw [isSelfAdjoint_iff]
      simp [star_smul, h₁.star_eq]
    exact (contDiff_state_affine (β / c) (c • H₁) (c • H₀) h₁c h₀c).continuous.comp
      continuous_subtype_val
  source' := by simpa using state_cold_corner β c H₁ hc
  target' := by simpa using state_cold_corner β c H₀ hc

@[simp] theorem coldStatePath_apply [Nonempty n] (β c : ℝ) (H₀ H₁ : Mat)
    (hc : c ≠ 0) (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁)
    (t : unitInterval) :
    coldStatePath β c H₀ H₁ hc h₀ h₁ t =
      state (β / c) (affineHamiltonian (c • H₁) (c • H₀) (t : ℝ)) := rfl

/-- The cold and reversed hot paths are equal as native paths, not merely
homotopic or equal at their endpoints. -/
theorem coldStatePath_eq_symm [Nonempty n] (β c : ℝ) (H₀ H₁ : Mat)
    (hc : c ≠ 0) (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) :
    coldStatePath β c H₀ H₁ hc h₀ h₁ =
      (hotStatePath β H₀ H₁ h₀ h₁).symm := by
  apply Path.ext
  funext t
  change state (β / c) (affineHamiltonian (c • H₁) (c • H₀) (t : ℝ)) =
    state β (affineHamiltonian H₀ H₁ (1 - (t : ℝ)))
  exact coldState_eq_hotState_reverse β c H₀ H₁ hc (t : ℝ)

/-- The four real Carnot strokes in chronological order, projected to the
full density-matrix carrier. The scale `c` is positive; no engine sign or
temperature-order premise is needed for this state-space cancellation. -/
def stateCycle [Nonempty n] (β c : ℝ) (H₀ H₁ : Mat)
    (hc : 0 < c) (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) :
    Path (state β H₀) (state β H₀) :=
  (((hotStatePath β H₀ H₁ h₀ h₁).trans
      (scalingStatePath β 1 c H₁ zero_lt_one hc)).trans
      (coldStatePath β c H₀ H₁ hc.ne' h₀ h₁)).trans
      (scalingStatePath β c 1 H₀ hc zero_lt_one)

/-- The actual density cycle consists of the hot path, a constant stroke,
the reversed hot path, and another constant stroke. -/
theorem stateCycle_eq_retrace [Nonempty n] (β c : ℝ) (H₀ H₁ : Mat)
    (hc : 0 < c) (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) :
    stateCycle β c H₀ H₁ hc h₀ h₁ =
      (((hotStatePath β H₀ H₁ h₀ h₁).trans
        (Path.refl (state β H₁))).trans
        (hotStatePath β H₀ H₁ h₀ h₁).symm).trans
        (Path.refl (state β H₀)) := by
  rw [stateCycle, scalingStatePath_eq_refl, scalingStatePath_eq_refl,
    coldStatePath_eq_symm]

/-! ## Cancellation for path-sensitive group-valued transport -/

/-- Retracing cancellation uses only the three stated transport laws.
The transport may depend on the whole path and need not be invariant under
arbitrary homotopies. The target group need not be commutative. -/
theorem transport_retrace_eq_one {X G : Type*} [TopologicalSpace X] [Group G]
    (τ : ∀ {a b : X}, Path a b → G)
    (hconst : ∀ a : X, τ (Path.refl a) = 1)
    (hrev : ∀ {a b : X} (p : Path a b), τ p.symm = (τ p)⁻¹)
    (hcomp : ∀ {a b d : X} (p : Path a b) (q : Path b d),
      τ (p.trans q) = τ p * τ q)
    {a b : X} (p : Path a b) :
    τ (((p.trans (Path.refl b)).trans p.symm).trans (Path.refl a)) = 1 := by
  rw [hcomp, hcomp, hcomp, hconst, hconst, hrev]
  simp

/-- Any transport with the stated native path laws has identity holonomy
around this actual Carnot density cycle. This theorem does not supply the
analytic construction of a particular operator or Uhlmann transport. -/
theorem stateCycle_transport_eq_one [Nonempty n] {G : Type*} [Group G]
    (β c : ℝ) (H₀ H₁ : Mat)
    (hc : 0 < c) (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁)
    (τ : ∀ {a b : Mat}, Path a b → G)
    (hconst : ∀ a : Mat, τ (Path.refl a) = 1)
    (hrev : ∀ {a b : Mat} (p : Path a b), τ p.symm = (τ p)⁻¹)
    (hcomp : ∀ {a b d : Mat} (p : Path a b) (q : Path b d),
      τ (p.trans q) = τ p * τ q) :
    τ (stateCycle β c H₀ H₁ hc h₀ h₁) = 1 := by
  rw [stateCycle_eq_retrace]
  exact transport_retrace_eq_one τ hconst hrev hcomp
    (hotStatePath β H₀ H₁ h₀ h₁)

end InfoGeometry.Thermo.RealMatrixCarnotStateLoop

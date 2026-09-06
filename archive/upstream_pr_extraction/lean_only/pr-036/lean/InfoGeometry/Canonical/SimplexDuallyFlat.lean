import Mathlib.Tactic
import InfoGeometry.Canonical.SimplexSurprisalMetriplectic
import InfoGeometry.Convex.Bregman

/-!
# Simplex Dually Flat Geometry

Finite algebraic core of Amari's dually flat structure on the 1-simplex:

* mixture coordinate `η = s` (m-flat, affine combinations);
* exponential coordinate `θ = ln(s/(1-s))` (e-flat, log-odds);
* Legendre-dual convex potentials `φ(η)` and `ψ(θ)`;
* self-dual seam `s = 1/2` ↔ `θ = 0`;
* reflection symmetry `η ↦ 1-η` ↔ `θ ↦ -θ`;
* Bregman divergence to the symmetric center.

No infinities, no analytic continuation, no measure-theoretic debt.
-/

noncomputable section

namespace InfoGeometry.Canonical.SimplexDuallyFlat

open SimplexState
open InfoGeometry

variable {S : SimplexState}

/-! ## 1. Mixture and exponential coordinates -/

/-- Mixture coordinate (affine parameter) `η = s`. -/
def mixtureCoord (S : SimplexState) : ℝ :=
  S.s

/-- Exponential coordinate (natural parameter) `θ = ln(s/(1-s))`. -/
def expCoord (S : SimplexState) : ℝ :=
  S.W

/-- The exponential coordinate equals the logit. -/
theorem expCoord_eq_W (S : SimplexState) :
    expCoord S = S.W := rfl

/-- The mixture coordinate of the complement is `1 - s`. -/
theorem mixtureCoord_complement (S : SimplexState) :
    mixtureCoord S.complement = 1 - mixtureCoord S := by
  simp [mixtureCoord, SimplexState.complement]

/-- The exponential coordinate of the complement is `-W`. -/
theorem expCoord_complement (S : SimplexState) :
    expCoord S.complement = -expCoord S := by
  simp [expCoord, S.W_complement]

/-! ## 2. Legendre-dual convex potentials -/

/-- Shannon negative-entropy potential (dual potential, m-flat):
    `φ(η) = η log η + (1-η) log(1-η)`. -/
def shannonPotential (η : ℝ) : ℝ :=
  η * Real.log η + (1 - η) * Real.log (1 - η)

/-- Massieu free-energy potential (primal potential, e-flat):
    `ψ(θ) = log(1 + e^θ) = -log(1-s)`. -/
def massieuPotential (θ : ℝ) : ℝ :=
  Real.log (1 + Real.exp θ)

/-- The massieu potential in terms of the mixture coordinate. -/
theorem massieuPotential_eq_neg_log_one_sub_s (S : SimplexState)
    (hs0 : 0 < S.s) (hs1 : S.s < 1) :
    massieuPotential S.W = -Real.log (1 - S.s) := by
  unfold massieuPotential W tau
  have htau_pos : 0 < S.tau := by
    unfold tau
    apply div_pos hs0
    linarith [hs1]
  have htau_pos' : 0 < S.s / (1 - S.s) := by
    exact htau_pos
  rw [Real.exp_log htau_pos']
  have hsub : 0 < 1 - S.s := by linarith [hs1]
  have harg : 1 + S.s / (1 - S.s) = 1 / (1 - S.s) := by
    field_simp [ne_of_gt hsub]
    ring
  rw [harg]
  rw [Real.log_div (by norm_num) (by linarith [hs1])]
  simp [Real.log_one]

/-- The Shannon potential of the complement equals the Shannon potential. -/
theorem shannonPotential_complement (S : SimplexState) :
    shannonPotential (mixtureCoord S.complement) = shannonPotential (mixtureCoord S) := by
  simp [mixtureCoord, shannonPotential, SimplexState.complement]
  ring_nf

/-! ## 3. Self-dual midpoint -/

/-- The center state `s = 1/2` is the unique self-dual point. -/
theorem centerState_self_dual :
    mixtureCoord centerState = 1 / 2 ∧ expCoord centerState = 0 := by
  constructor
  · simp [mixtureCoord, centerState]
  · simp [expCoord, centerState_W]

/-- The mixture coordinate of the center is `1/2`. -/
theorem mixtureCoord_center : mixtureCoord centerState = 1 / 2 := by
  simp [mixtureCoord, centerState]

/-- The exponential coordinate of the center is `0`. -/
theorem expCoord_center : expCoord centerState = 0 := by
  simp [expCoord, centerState_W]

/-- The Shannon potential at the center equals `-ln 2`. -/
theorem shannonPotential_center :
    shannonPotential (mixtureCoord centerState) = -Real.log 2 := by
  simp [mixtureCoord, centerState, shannonPotential]
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  have hhalf : 1 - (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  rw [hhalf]
  rw [hlog]
  ring

/-- The Massieu potential at the center equals `ln 2`. -/
theorem massieuPotential_center :
    massieuPotential (expCoord centerState) = Real.log 2 := by
  simp [expCoord, centerState_W, massieuPotential]
  norm_num

/-! ## 4. Bregman divergence to the symmetric center -/

/-- The Bregman divergence of the Shannon potential from `s` to `1/2`. -/
def bregmanShannonToCenter (S : SimplexState) : ℝ :=
  bregmanDiv shannonPotential S.s (1 / 2)

/-- The Bregman divergence vanishes at the center. -/
theorem bregmanShannonToCenter_center_zero :
    bregmanShannonToCenter centerState = 0 := by
  simp [bregmanShannonToCenter, centerState, bregmanDiv_self]

/-- The Bregman divergence is zero when `s = 1/2`. -/
theorem bregmanShannonToCenter_eq_zero_of_s_eq_one_half (S : SimplexState)
    (hs : S.s = 1 / 2) :
    bregmanShannonToCenter S = 0 := by
  unfold bregmanShannonToCenter
  rw [hs]
  exact bregmanDiv_self _ _

/-! ## 5. Critical line complexification -/

/-- The critical line `Re(s) = 1/2` in the mixture plane. -/
def onCriticalLineMixture (s : ℂ) : Prop :=
  s.re = 1 / 2

/-- The critical line `Re(θ) = 0` in the exponential plane. -/
def onCriticalLineExp (θ : ℂ) : Prop :=
  θ.re = 0

end InfoGeometry.Canonical.SimplexDuallyFlat

end noncomputable section

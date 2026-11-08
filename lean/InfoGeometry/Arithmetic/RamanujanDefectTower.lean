import InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Ramanujan Defect Tower Interface

This module exposes a compact interface for the finite Ramanujan/Bernoulli
defect tower in the centered zeta chart.

The verified layer is finite algebra:
* centered-coordinate readout and Dirichlet channel split,
* finite `ζ(3)` and `ζ(5)` tau defects,
* finite swap/tau parity through `ζ(9)`.

The analytic Ramanujan odd-zeta identity remains a transparent side-supplied
`Prop` target; no axiom, placeholder, or analytic proof is introduced here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.RamanujanDefectTower

open InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions

/-! ## Centered chart and Dirichlet mode split -/

/-- Local alias for the repository-owned centered zeta chart. -/
abbrev CenteredChart :=
  InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions.CenteredChart

/-- The centered chart read as `s = 1/2 + u + iv`. -/
def CenteredChart.toComplex (z : CenteredChart) : ℂ :=
  centeredParameter z

/--
Three-channel factorization data for a Dirichlet mode with logarithmic weight
`log n`: critical-line ground envelope, scale-normal dissipation, and tangential
phase.
-/
structure DirichletChannelSplit (n : ℕ) (z : CenteredChart) where
  ground : ℝ
  dissipation : ℝ
  phase : ℂ

/-- The canonical three-channel split, expressed through the existing owner functions. -/
def dirichletChannelSplit (n : ℕ) (z : CenteredChart) : DirichletChannelSplit n z where
  ground := Real.exp (-(1 / 2 : ℝ) * Real.log n)
  dissipation := Real.exp (-z.u * Real.log n)
  phase := Complex.exp (-(z.v * Real.log n : ℝ) * Complex.I)

/-- The three channels multiply back to the repository-owned centered Dirichlet mode. -/
theorem dirichletChannelSplit_product (n : ℕ) (z : CenteredChart) :
    ((dirichletChannelSplit n z).ground : ℂ) *
        ((dirichletChannelSplit n z).dissipation : ℂ) *
        (dirichletChannelSplit n z).phase =
      centeredDirichletMode (Real.log n) z := by
  rfl

/-! ## Finite Bernoulli defect cores -/

/-- Finite `ζ(3)` tau-defect core, delegated to the existing owner readout. -/
def BernoulliDefect3Core (τ : ℝ) : ℝ :=
  aperyBernoulliDefectTau τ

/-- Finite `ζ(5)` tau-defect core, delegated to the existing owner readout. -/
def BernoulliDefect5Core (τ : ℝ) : ℝ :=
  zetaFiveBernoulliDefectTau τ

/-- Positive-parameter interface for the finite `ζ(3)` Bernoulli defect. -/
def BernoulliDefect3 (τ : ℝ) (_hτ : 0 < τ) : ℝ :=
  BernoulliDefect3Core τ

/-- Positive-parameter interface for the finite `ζ(5)` Bernoulli defect. -/
def BernoulliDefect5 (τ : ℝ) (_hτ : 0 < τ) : ℝ :=
  BernoulliDefect5Core τ

/-- The finite `ζ(3)` defect is invariant under positive real modular inversion. -/
theorem bernoulli_defect_3_invariant (τ : ℝ) (hτ : 0 < τ) :
    BernoulliDefect3 (1 / τ) (one_div_pos.mpr hτ) = BernoulliDefect3 τ hτ := by
  simpa [BernoulliDefect3, BernoulliDefect3Core, one_div] using
    (aperyBernoulliDefectTau_inv hτ.ne').symm

/-- The finite `ζ(5)` defect is anti-invariant under positive real modular inversion. -/
theorem bernoulli_defect_5_anti_invariant (τ : ℝ) (hτ : 0 < τ) :
    BernoulliDefect5 (1 / τ) (one_div_pos.mpr hτ) = -BernoulliDefect5 τ hτ := by
  have h := zetaFiveBernoulliDefectTau_inv hτ.ne'
  simp [BernoulliDefect5, BernoulliDefect5Core, one_div] at h ⊢
  linarith

/-! ## Transparent analytic and parity targets -/

/--
Transparent target for the full Ramanujan odd-zeta identity at a supplied
finite/analytic readout triple.

`positiveSide`, `reflectedSide`, and `finiteDefect` are deliberately supplied
arguments.  This prevents the interface from hiding an unproved convergence or
Lambert-series construction behind an existential placeholder.
-/
def IsRamanujanOddZetaFormula
    (α β : ℝ) (n : ℕ) (positiveSide reflectedSide finiteDefect : ℝ) : Prop :=
  0 < n ∧ 0 < α ∧ 0 < β ∧ α * β = Real.pi ^ 2 ∧
    positiveSide = reflectedSide - finiteDefect

/-- Uniform S-duality parity target for a finite defect core. -/
def TowerParityPattern (n : ℕ) (τ : ℝ) (_hτ : 0 < τ) (defect : ℝ → ℝ) : Prop :=
  defect τ⁻¹ = (-1 : ℝ) ^ (n + 1) * defect τ

/-- The finite `ζ(3)` tau-defect satisfies the tower parity target. -/
theorem bernoulli_defect_3_tower_parity (τ : ℝ) (hτ : 0 < τ) :
    TowerParityPattern 1 τ hτ BernoulliDefect3Core := by
  unfold TowerParityPattern BernoulliDefect3Core
  rw [(aperyBernoulliDefectTau_inv hτ.ne').symm]
  norm_num

/-- The finite `ζ(5)` tau-defect satisfies the tower parity target. -/
theorem bernoulli_defect_5_tower_parity (τ : ℝ) (hτ : 0 < τ) :
    TowerParityPattern 2 τ hτ BernoulliDefect5Core := by
  unfold TowerParityPattern BernoulliDefect5Core
  have h := zetaFiveBernoulliDefectTau_inv hτ.ne'
  norm_num
  linarith

/-! ## Swap parity in alpha/beta coordinates for verified finite layers -/

/-- A finite defect polynomial has Ramanujan parity `(-1)^(n+1)` if swapping
`alpha` and `beta` multiplies the polynomial by that sign. -/
def DefectParityTarget (n : ℕ) (D : ℝ → ℝ → ℝ) : Prop :=
  ∀ alpha beta : ℝ, D beta alpha = (-1 : ℝ) ^ (n + 1) * D alpha beta

/-- The finite `ζ(3)` Bernoulli defect is invariant under `alpha ↔ beta`. -/
theorem zeta3_defect_swap_even (alpha beta : ℝ) :
    ramanujanBernoulliSide aperyBernoulliReadout 1 beta alpha =
      ramanujanBernoulliSide aperyBernoulliReadout 1 alpha beta := by
  rw [ramanujanBernoulliSide_apery_n1_explicit,
    ramanujanBernoulliSide_apery_n1_explicit]
  ring

/-- The finite `ζ(5)` Bernoulli defect is anti-invariant under `alpha ↔ beta`. -/
theorem zeta5_defect_swap_odd (alpha beta : ℝ) :
    ramanujanBernoulliSide zetaFiveBernoulliReadout 2 beta alpha =
      -ramanujanBernoulliSide zetaFiveBernoulliReadout 2 alpha beta := by
  rw [ramanujanBernoulliSide_zeta5_n2_explicit,
    ramanujanBernoulliSide_zeta5_n2_explicit]
  ring

/-- The finite `ζ(7)` Bernoulli defect is invariant under `alpha ↔ beta`. -/
theorem zeta7_defect_swap_even (alpha beta : ℝ) :
    ramanujanBernoulliSide zetaSevenBernoulliReadout 3 beta alpha =
      ramanujanBernoulliSide zetaSevenBernoulliReadout 3 alpha beta := by
  rw [ramanujanBernoulliSide_zeta7_n3_explicit,
    ramanujanBernoulliSide_zeta7_n3_explicit]
  ring

/-- The finite `ζ(9)` Bernoulli defect is anti-invariant under `alpha ↔ beta`. -/
theorem zeta9_defect_swap_odd (alpha beta : ℝ) :
    ramanujanBernoulliSide zetaNineBernoulliReadout 4 beta alpha =
      -ramanujanBernoulliSide zetaNineBernoulliReadout 4 alpha beta := by
  rw [ramanujanBernoulliSide_zeta9_n4_explicit,
    ramanujanBernoulliSide_zeta9_n4_explicit]
  ring

theorem zeta3_defect_parity :
    DefectParityTarget 1 (ramanujanBernoulliSide aperyBernoulliReadout 1) := by
  intro alpha beta
  rw [zeta3_defect_swap_even]
  norm_num

theorem zeta5_defect_parity :
    DefectParityTarget 2 (ramanujanBernoulliSide zetaFiveBernoulliReadout 2) := by
  intro alpha beta
  rw [zeta5_defect_swap_odd]
  norm_num

theorem zeta7_defect_parity :
    DefectParityTarget 3 (ramanujanBernoulliSide zetaSevenBernoulliReadout 3) := by
  intro alpha beta
  rw [zeta7_defect_swap_even]
  norm_num

theorem zeta9_defect_parity :
    DefectParityTarget 4 (ramanujanBernoulliSide zetaNineBernoulliReadout 4) := by
  intro alpha beta
  rw [zeta9_defect_swap_odd]
  norm_num

theorem zeta3_defect_parity_swap_eq (alpha beta : ℝ) :
    ramanujanBernoulliSide aperyBernoulliReadout 1 beta alpha =
      (-1 : ℝ) ^ (1 + 1) *
        ramanujanBernoulliSide aperyBernoulliReadout 1 alpha beta :=
  zeta3_defect_parity alpha beta

theorem zeta5_defect_parity_swap_eq (alpha beta : ℝ) :
    ramanujanBernoulliSide zetaFiveBernoulliReadout 2 beta alpha =
      (-1 : ℝ) ^ (2 + 1) *
        ramanujanBernoulliSide zetaFiveBernoulliReadout 2 alpha beta :=
  zeta5_defect_parity alpha beta

theorem zeta7_defect_parity_swap_eq (alpha beta : ℝ) :
    ramanujanBernoulliSide zetaSevenBernoulliReadout 3 beta alpha =
      (-1 : ℝ) ^ (3 + 1) *
        ramanujanBernoulliSide zetaSevenBernoulliReadout 3 alpha beta :=
  zeta7_defect_parity alpha beta

theorem zeta9_defect_parity_swap_eq (alpha beta : ℝ) :
    ramanujanBernoulliSide zetaNineBernoulliReadout 4 beta alpha =
      (-1 : ℝ) ^ (4 + 1) *
        ramanujanBernoulliSide zetaNineBernoulliReadout 4 alpha beta :=
  zeta9_defect_parity alpha beta

/-- The finite `ζ(7)` tau-defect is invariant under `tau ↦ tau⁻¹`. -/
theorem zeta7_tau_defect_even {tau : ℝ} (hτ : tau ≠ 0) :
    zetaSevenBernoulliDefectTau tau = zetaSevenBernoulliDefectTau tau⁻¹ :=
  zetaSevenBernoulliDefectTau_inv hτ

/-- The finite `ζ(9)` tau-defect is anti-invariant under `tau ↦ tau⁻¹`. -/
theorem zeta9_tau_defect_odd {tau : ℝ} (hτ : tau ≠ 0) :
    zetaNineBernoulliDefectTau tau = -zetaNineBernoulliDefectTau tau⁻¹ :=
  zetaNineBernoulliDefectTau_inv hτ

end InfoGeometry.Arithmetic.RamanujanDefectTower

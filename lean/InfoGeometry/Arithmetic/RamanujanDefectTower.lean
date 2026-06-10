import InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions

/-!
# Ramanujan finite defect parity tower

This module is a theorem bridge over the finite Bernoulli readouts already
owned by `ZetaSymmetryAdaptedDefinitions`.

It does not assert Ramanujan's analytic odd-zeta transformation.  It only
records exact finite polynomial parity under the algebraic swap `alpha ↔ beta`
for the verified layers `ζ(3)`, `ζ(5)`, `ζ(7)`, and `ζ(9)`.

#### BUCKET 1: CLOSED FINITE THEOREMS
Swap parity and `(-1)^(n+1)` parity for the finite `ζ(3)`, `ζ(5)`, `ζ(7)`,
and `ζ(9)` Bernoulli readouts; tau-coordinate parity for `ζ(7)` and `ζ(9)`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The tau-coordinate readouts require the explicit premise `tau ≠ 0`.

#### BUCKET 3: OPEN CLOSURE DEBT
The analytic Ramanujan odd-zeta transformation and all convergence statements.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.RamanujanDefectTower

open InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions

/-- A finite defect polynomial has Ramanujan parity `(-1)^(n+1)` if swapping
`alpha` and `beta` multiplies the polynomial by that sign. -/
def DefectParityTarget (n : ℕ) (D : ℝ → ℝ → ℝ) : Prop :=
  ∀ alpha beta : ℝ, D beta alpha = (-1 : ℝ) ^ (n + 1) * D alpha beta

/-! ## Swap parity in alpha/beta coordinates -/

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

/-! ## Uniform `(-1)^(n+1)` readout for the verified layers -/

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

/-! ## S-dual tau-coordinate readouts for `ζ(7)` and `ζ(9)` -/

/-- The finite `ζ(7)` tau-defect is invariant under `tau ↦ tau⁻¹`. -/
theorem zeta7_tau_defect_even {tau : ℝ} (hτ : tau ≠ 0) :
    zetaSevenBernoulliDefectTau tau = zetaSevenBernoulliDefectTau tau⁻¹ :=
  zetaSevenBernoulliDefectTau_inv hτ

/-- The finite `ζ(9)` tau-defect is anti-invariant under `tau ↦ tau⁻¹`. -/
theorem zeta9_tau_defect_odd {tau : ℝ} (hτ : tau ≠ 0) :
    zetaNineBernoulliDefectTau tau = -zetaNineBernoulliDefectTau tau⁻¹ :=
  zetaNineBernoulliDefectTau_inv hτ

end InfoGeometry.Arithmetic.RamanujanDefectTower


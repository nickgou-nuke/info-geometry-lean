import Mathlib
import InfoGeometry.Arithmetic.PrimonMajoranaWittenCharacter
import InfoGeometry.Arithmetic.PrimitiveSetsAbove
import InfoGeometry.Probability.HomologicalProbability

/-!
# InfoGeometry.Arithmetic.PrimonFreeEnergyRelativeTrace

Witness-gated free-energy and relative-trace socket for the MBK/primon program.

This file records the theorem-safe version of the conceptual passage

`Majorana Witten character 1 / ζ  →  free energy log ζ  →  relative trace`.

It deliberately does **not** assert convexity of a zeta potential, identify
Riemann zeros with minima, prove Connes' trace formula, or prove RH.  Those are
separate analytic/spectral witnesses.
-/

noncomputable section

namespace PrimonFreeEnergyRelativeTrace

open InfoGeometry.Arithmetic.PrimonMajoranaWittenCharacter

/-! ## 1. Finite positive free-energy lane -/

/-- Free energy of a positive partition readout. -/
def freeEnergy (Z : ℝ) : ℝ :=
  -Real.log Z

/--
Finite inversion identity for the free energy.

If `ZF * ZB = 1` and both readouts are positive, then the fermionic free
energy `-log ZF` is `log ZB`.
-/
theorem freeEnergy_eq_log_dual_of_mul_eq_one
    {ZF ZB : ℝ}
    (hZF : 0 < ZF)
    (hZB : 0 < ZB)
    (hmul : ZF * ZB = 1) :
    freeEnergy ZF = Real.log ZB := by
  unfold freeEnergy
  have hlog_mul :
      Real.log (ZF * ZB) = Real.log ZF + Real.log ZB :=
    Real.log_mul (ne_of_gt hZF) (ne_of_gt hZB)
  rw [hmul] at hlog_mul
  simp only [Real.log_one] at hlog_mul
  linarith

/--
Finite product free energy for a finite primon Majorana character.

This is only defined as a real log readout; positivity must be supplied when
using analytic log identities.
-/
def finiteMajoranaFreeEnergy (P : Finset ℕ) (s : ℝ) : ℝ :=
  freeEnergy (finiteWittenCharacter P s)

/-! ## 2. Determinant-line inversion lane -/

/--
Determinant-line inversion.

This is the finite real shadow of the passage

`Z ↦ Z⁻¹`.

It is not an analytic continuation theorem and it does not identify the
resulting inverse with an infinite Euler product.
-/
def determinantLineInversion (Z : ℝ) : ℝ :=
  Z⁻¹

/--
The determinant-line inversion is involutive.
-/
theorem determinantLineInversion_involutive
    (Z : ℝ) :
    determinantLineInversion (determinantLineInversion Z) = Z := by
  simp [determinantLineInversion]

/--
Positive determinant-line inversion turns free energy into the logarithm of the
dual determinant.

This is the precise finite real form of

`-log (Z⁻¹) = log Z`.
-/
theorem freeEnergy_determinantLineInversion_eq_log
    {Z : ℝ}
    (hZ : 0 < Z) :
    freeEnergy (determinantLineInversion Z) = Real.log Z := by
  unfold determinantLineInversion
  exact freeEnergy_eq_log_dual_of_mul_eq_one (inv_pos.mpr hZ) hZ (inv_mul_cancel₀ (ne_of_gt hZ))

/-! ## 8. Gibbs/KMS equilibrium lane -/

/-- The Gibbs/KMS free-energy gap is nonnegative in the concrete packet. -/
theorem GibbsKMS_freeEnergy_gap_nonneg
    (gk : InfoGeometry.Probability.Homological.GibbsKMSPacket)
    (ρ : gk.ObservableAlgebra)
    (hrel : 0 ≤ gk.relativeEntropyToGibbs ρ)
    (hβ : 0 < gk.beta) :
    0 ≤ gk.freeEnergy ρ - gk.freeEnergy gk.gibbsState :=
  gk.freeEnergy_gap_nonneg_of_relativeEntropy_nonneg ρ hrel hβ

/-- The Gibbs state minimizes free energy in the concrete packet. -/
theorem GibbsKMS_freeEnergy_ge_gibbs
    (gk : InfoGeometry.Probability.Homological.GibbsKMSPacket)
    (ρ : gk.ObservableAlgebra)
    (hrel : 0 ≤ gk.relativeEntropyToGibbs ρ)
    (hβ : 0 < gk.beta) :
    gk.freeEnergy gk.gibbsState ≤ gk.freeEnergy ρ := by
  have hgap := GibbsKMS_freeEnergy_gap_nonneg gk ρ hrel hβ
  linarith

/--
Root-corridor identification of the primitive-set analytic-input lane.

This is only the definitional owner surface currently available in
`PrimitiveSetsAbove`: the analytic input implies the finite primitive-set
statement. It does not assert a Mellin functional equation or critical-axis
theorem.
-/
theorem primitiveMellinParityIdentification :
    InfoGeometry.Arithmetic.PrimitiveWeightSumAssemblyFromAnalyticInput =
      (InfoGeometry.Arithmetic.PrimitiveLargeDivisorAnalyticInput →
        InfoGeometry.Arithmetic.PrimitiveSetsAboveFiniteStatement) :=
  rfl

/-! ## 8b. Mathlib-backed completed-zeta parity lane -/

/--
Completed-zeta parity identification.

This is the concrete theorem-backed version of the Mellin inversion/parity
lane, obtained by reusing mathlib's `completedRiemannZeta_one_sub` theorem:
the completed zeta function is symmetric under `s ↦ 1 - s`, and the critical
axis `Re(s) = 1/2` is fixed by that involution.
-/
theorem completedRiemannZeta_parity_identification (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s ∧
      (Complex.re s = (1 : ℝ) / 2 → Complex.re (1 - s) = (1 : ℝ) / 2) := by
  constructor
  · exact completedRiemannZeta_one_sub s
  · intro hs
    have hre : Complex.re (1 - s) = 1 - Complex.re s := by
      simp
    rw [hre, hs]
    nlinarith

/--
The uncompleted zeta functional equation, reexported from mathlib.

This is the Mellin/Dirichlet symmetry lane in explicit form. The additional
non-pole hypothesis is exactly the one required by mathlib's theorem, so this
file reexports `riemannZeta_one_sub` rather than proving a fresh variant.
-/
theorem riemannZeta_functionalEquation_symmetry
    {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) =
      2 * (2 * Real.pi) ^ (-s) * Complex.Gamma s *
        Complex.cos (Real.pi * s / 2) * riemannZeta s := by
  simpa using (riemannZeta_one_sub (s := s) hs hs')

end PrimonFreeEnergyRelativeTrace

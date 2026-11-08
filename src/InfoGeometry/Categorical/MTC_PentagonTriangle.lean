import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.FibonacciFusionCategoryData
import InfoGeometry.Topology.RohozhkinProjectiveCrossRatio
import InfoGeometry.Projective.SplitOctonions.ProjectiveLine

/-!
# MTC_PentagonTriangle

A conservative skeleton that records the finite MTC-shaped coherence packets we can
prove today from currently owned facts:

* `FMatrix`, `RMatrix`, and `BMatrix` aliases for the finite Fibonacci matrices;
* a finite-matrix shadow theorem for `F² = 1`, `det F = -1`, `B = F R F`, and a
  supplied Artin relation;
* a diagonal-associativity triangle law in the reduced Zorn `OP1` shell;
* a Rohozhkin five-flip cocycle law for the pentagon chart.

No full categorical instance (`BraidedCategory`), WRT invariant functor, or spin/
Rokhlin theorem is introduced here. Those belong to the follow-on `RokhlinBraidInvariant`
module.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Categorical.MTC_PentagonTriangle

open Matrix
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
open InfoGeometry.Categorical.FibonacciFusionCategoryData
open InfoGeometry.Categorical.FibonacciBraiding
open InfoGeometry.Projective.SplitOctonions
open InfoGeometry.Projective.SplitOctonions.ZornMatrix
open InfoGeometry.Topology.Delaunay

/-- Finite Fibonacci data needed for the MTC packet. -/
def MTC_FusionMatrix (τ s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fibonacciFusionMatrix τ s

/-- Finite diagonal `R` generator for Artin/braid readout. -/
def MTC_RMatrix (q : Units ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fibonacciRMatrix q

/-- Finite middle generator `B = F R F`. -/
def MTC_BMatrix (q : Units ℂ) (τ s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fibonacciBMatrix q τ s

/--
Bundled finite hypotheses for the finite Fibonacci shadow.

This restores the historical input owner as a subtype: its certificate is the
actual square-root, fusion, and Artin equality, not a separate evidence field.
-/
def MTC_FiniteInput : Type _ :=
  {q : Units ℂ //
    ∃ τ s : ℂ,
      s ^ 2 = τ ∧
        τ ^ 2 + τ = 1 ∧
          fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q =
            fibonacciBMatrix q τ s * fibonacciRMatrix q * fibonacciBMatrix q τ s}

/--
Finite matrix shadow theorem with all mathematical inputs explicit.

The statement is exactly the finite owner-backed shadow from
`FibonacciFusionCategoryData.finite_braiding_input_readout`.
-/
theorem MTC_FiniteShadow
    (q : Units ℂ) (τ s : ℂ)
    (hsq : s ^ 2 = τ)
    (hTau : τ ^ 2 + τ = 1)
    (hArtin :
      fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q =
        fibonacciBMatrix q τ s * fibonacciRMatrix q * fibonacciBMatrix q τ s) :
      MTC_FusionMatrix τ s * MTC_FusionMatrix τ s = 1 ∧
      (MTC_FusionMatrix τ s).det = -1 ∧
      MTC_BMatrix q τ s =
        MTC_FusionMatrix τ s * MTC_RMatrix q * MTC_FusionMatrix τ s ∧
      MTC_RMatrix q * MTC_BMatrix q τ s * MTC_RMatrix q =
        MTC_BMatrix q τ s * MTC_RMatrix q * MTC_BMatrix q τ s := by
  rcases finite_braiding_input_readout q τ s hsq hTau hArtin with
    ⟨hF2, hdet, hB, hArtin'⟩
  exact ⟨hF2, hdet, hB, hArtin'⟩

/-- Every bundled finite input exposes the complete owner-backed shadow. -/
theorem MTC_FiniteInput.shadow (data : MTC_FiniteInput) :
    ∃ τ s : ℂ,
      s ^ 2 = τ ∧
        τ ^ 2 + τ = 1 ∧
          MTC_FusionMatrix τ s * MTC_FusionMatrix τ s = 1 ∧
          (MTC_FusionMatrix τ s).det = -1 ∧
          MTC_BMatrix data.1 τ s =
            MTC_FusionMatrix τ s * MTC_RMatrix data.1 * MTC_FusionMatrix τ s ∧
          MTC_RMatrix data.1 * MTC_BMatrix data.1 τ s * MTC_RMatrix data.1 =
            MTC_BMatrix data.1 τ s * MTC_RMatrix data.1 * MTC_BMatrix data.1 τ s := by
  rcases data with ⟨q, τ, s, hsq, hTau, hArtin⟩
  exact ⟨τ, s, hsq, hTau, MTC_FiniteShadow q τ s hsq hTau hArtin⟩

/--
Mac Lane triangle-style graph law on the Zorn diagonal shell.

Interpreting the first leg as a diagonal source factor matches the local
associator-vanishing branch recorded in `ProjectiveLine.lean`.
-/
theorem MacLane_Triangle_Equation
    {R : Type*} [CommRing R]
    {V : Type*} [AddCommGroup V] [Module R V]
    (B : V →ₗ[R] V →ₗ[R] R)
    (_v_i : ZornMatrix R V)
    (v_j x : ZornMatrix R V)
    (z : R)
    (_hx : half_eq_e1 x) :
    associator B (ZornMatrix.diag (1 : R) z) x (star (mul B v_j x)) = ZornMatrix.diag 0 0 := by
  exact op1_associator_vanishes_of_diag_left (B := B) v_j x z

/--
Diagonal half-or-projector branch from the local `OP1` shell for the same Mac Lane
triangle graph shape.
-/
theorem MTC_DiagonalTriangle_from_half_or_diag
    {R : Type*} [CommRing R]
    {V : Type*} [AddCommGroup V] [Module R V]
    (B : V →ₗ[R] V →ₗ[R] R)
    (v_i v_j x : ZornMatrix R V)
    (hx : half_eq_e1 x)
    (h_left : half_eq_e1 v_i ∨ ∃ z : R, v_i = ZornMatrix.diag (1 : R) z) :
    associator B v_i x (star (mul B v_j x)) = ZornMatrix.diag 0 0 := by
  rcases h_left with hvi | ⟨z, rfl⟩
  · exact op1_associator_vanishes_of_half_projector (B := B) v_i v_j x hx (Or.inl hvi)
  · exact op1_associator_vanishes_of_diag_left (B := B) v_j x z

/--
`pentagonGamma` cocycle closure for Rohozhkin flips (five-flip chart identity).
-/
theorem MacLane_Pentagon_Equation
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0)
    (h_ik : zi - zk ≠ 0)
    (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0)
    (h_jl : zj - zl ≠ 0) :
    pentagonGamma5 zi zj zk zl zm *
      pentagonGamma4 zi zj zk zl zm *
      pentagonGamma3 zi zj zk zl zm *
      pentagonGamma2 zi zj zk zl zm *
      pentagonGamma1 zi zj zk zl zm = 1 :=
  pentagon_chart_cocycle_identity zi zj zk zl zm h_il h_ik h_km h_jm h_jl

end InfoGeometry.Categorical.MTC_PentagonTriangle

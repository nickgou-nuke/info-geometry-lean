/-
InfoGeometry/OperatorAlgebra/ConstructiveCayley.lean

Constructive elimination of Cayley hypotheses.

This module proves the phase-linearity of the bounded Cayley transform from
the phase-linearity of `D` and the explicit two-sided inverse of `D + K`.

No independent `cayley_phase_linear` or `denomInv_phase_linear` hypothesis is
kept.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ConstructiveCayley

universe u

/-- Bounded real-linear endomorphisms. -/
abbrev EndR
    (H : Type u) [NormedAddCommGroup H] [NormedSpace ℝ H] : Type u :=
  H →L[ℝ] H

/-! ## 1. Base PhaseLinear API -/

/-- `T` is phase-linear relative to `K` when it commutes with `K`. -/
def PhaseLinear
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K T : EndR H) : Prop :=
  T.comp K = K.comp T

namespace PhaseLinear

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : EndR H}

/-- Pointwise form of phase-linearity. -/
theorem apply
    {T : EndR H}
    (hT : PhaseLinear K T)
    (x : H) :
    T (K x) = K (T x) := by
  change (T.comp K) x = (K.comp T) x
  rw [hT]

/-- The phase axis is phase-linear relative to itself. -/
theorem self :
    PhaseLinear K K :=
  rfl

/-- The identity is phase-linear. -/
theorem id_map :
    PhaseLinear K (ContinuousLinearMap.id ℝ H) := by
  ext x
  rfl

/-- Sums of phase-linear operators are phase-linear. -/
theorem add
    {T S : EndR H}
    (hT : PhaseLinear K T)
    (hS : PhaseLinear K S) :
    PhaseLinear K (T + S) := by
  ext x
  change T (K x) + S (K x) = K (T x + S x)
  rw [apply hT x, apply hS x]
  simp

/-- Negatives of phase-linear operators are phase-linear. -/
theorem neg
    {T : EndR H}
    (hT : PhaseLinear K T) :
    PhaseLinear K (-T) := by
  ext x
  change -T (K x) = K (-T x)
  rw [apply hT x]
  simp

/-- Differences of phase-linear operators are phase-linear. -/
theorem sub
    {T S : EndR H}
    (hT : PhaseLinear K T)
    (hS : PhaseLinear K S) :
    PhaseLinear K (T - S) := by
  simpa [sub_eq_add_neg] using add hT (neg hS)

/-- Composites of phase-linear operators are phase-linear. -/
theorem comp
    {T S : EndR H}
    (hT : PhaseLinear K T)
    (hS : PhaseLinear K S) :
    PhaseLinear K (T.comp S) := by
  ext x
  change T (S (K x)) = K (T (S x))
  rw [apply hS x, apply hT (S x)]

end PhaseLinear

/-! ## 2. General inverse-commutation lemma -/

/--
If `B` is invertible with inverse `Binv`, and `A` commutes with `B`, then
`A` commutes with `Binv`.

This is the algebraic core that eliminates phase-linearity hypotheses for
resolvent inverses.
-/
theorem inverse_commutes_of_commutes
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A B Binv : EndR H}
    (h_right : B.comp Binv = ContinuousLinearMap.id ℝ H)
    (h_left : Binv.comp B = ContinuousLinearMap.id ℝ H)
    (hAB : A.comp B = B.comp A) :
    A.comp Binv = Binv.comp A := by
  ext x
  change A (Binv x) = Binv (A x)
  have hLeftApply :
      Binv (B (A (Binv x))) = A (Binv x) := by
    have h :=
      congrArg
        (fun T : EndR H => T (A (Binv x)))
        h_left
    simpa [ContinuousLinearMap.comp_apply] using h
  have hABApply :
      A (B (Binv x)) = B (A (Binv x)) := by
    have h :=
      congrArg
        (fun T : EndR H => T (Binv x))
        hAB
    simpa [ContinuousLinearMap.comp_apply] using h
  have hRightApply :
      B (Binv x) = x := by
    have h :=
      congrArg
        (fun T : EndR H => T x)
        h_right
    simpa [ContinuousLinearMap.comp_apply] using h
  calc
    A (Binv x)
        = Binv (B (A (Binv x))) := hLeftApply.symm
    _ = Binv (A (B (Binv x))) := by
          rw [← hABApply]
    _ = Binv (A x) := by
          rw [hRightApply]

/--
If `B` is phase-linear and invertible, then its inverse is phase-linear.
-/
theorem inverse_phaseLinear
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K B Binv : EndR H}
    (hB : PhaseLinear K B)
    (h_right : B.comp Binv = ContinuousLinearMap.id ℝ H)
    (h_left : Binv.comp B = ContinuousLinearMap.id ℝ H) :
    PhaseLinear K Binv := by
  exact
    (inverse_commutes_of_commutes
      (A := K)
      (B := B)
      (Binv := Binv)
      h_right
      h_left
      hB.symm).symm

/-! ## 3. Phase resolvent without inverse phase-linearity hypothesis -/

/--
A verified phase resolvent.

Only `D_phase_linear` is supplied.  Phase-linearity of the inverse of `D + K`
is derived constructively.
-/
structure VerifiedPhaseResolvent
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H)
    (D : EndR H) where
  /-- Bounded inverse of `D + K`. -/
  denomInv : EndR H

  /-- Right inverse law. -/
  denom_right :
    (D + K).comp denomInv = ContinuousLinearMap.id ℝ H

  /-- Left inverse law. -/
  denom_left :
    denomInv.comp (D + K) = ContinuousLinearMap.id ℝ H

  /-- `D` commutes with the phase axis. -/
  D_phase_linear :
    PhaseLinear K D

namespace VerifiedPhaseResolvent

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K D : EndR H}

variable (R : VerifiedPhaseResolvent H K D)

/-- The denominator `D + K` is phase-linear. -/
theorem denom_phase_linear
    (R : VerifiedPhaseResolvent H K D) :
    PhaseLinear K (D + K) :=
  PhaseLinear.add (VerifiedPhaseResolvent.D_phase_linear R) PhaseLinear.self

/--
The denominator inverse is phase-linear.

This is proved from `denom_phase_linear` and the two inverse laws.
-/
theorem denomInv_phase_linear :
    PhaseLinear K R.denomInv :=
  inverse_phaseLinear
    (denom_phase_linear R)
    R.denom_right
    R.denom_left

/-- `D + K` commutes with its inverse. -/
theorem denom_commutes_inverse :
    (D + K).comp R.denomInv =
      R.denomInv.comp (D + K) := by
  rw [R.denom_right, R.denom_left]

end VerifiedPhaseResolvent

/-! ## 4. Constructive Cayley transform -/

/-- The bounded Cayley transform: `U = (D - K)(D + K)⁻¹`. -/
def boundedCayley
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K D : EndR H}
    (R : VerifiedPhaseResolvent H K D) : EndR H :=
  (D - K).comp R.denomInv

/--
Constructive proof: the Cayley transform is phase-linear.

No independent `cayley_phase_linear` hypothesis is needed.
-/
theorem boundedCayley_is_phase_linear
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K D : EndR H}
    (R : VerifiedPhaseResolvent H K D) :
    PhaseLinear K (boundedCayley R) := by
  dsimp [boundedCayley]
  exact
    PhaseLinear.comp
      (PhaseLinear.sub R.D_phase_linear PhaseLinear.self)
      R.denomInv_phase_linear

/-! ## 5. Commutation of Cayley factors -/

/--
If `D` commutes with `K`, then `D - K` commutes with `D + K`.
-/
theorem D_sub_K_commutes_D_add_K
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K D : EndR H}
    (hD : PhaseLinear K D) :
    (D - K).comp (D + K) =
      (D + K).comp (D - K) := by
  ext x
  change (D - K) ((D + K) x) = (D + K) ((D - K) x)
  have hDKx : D (K x) = K (D x) :=
    PhaseLinear.apply hD x
  simp [hDKx]
  abel

/--
Constructive proof: `(D - K)` commutes with `(D + K)⁻¹`.
-/
theorem cayley_factors_commute
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K D : EndR H}
    (R : VerifiedPhaseResolvent H K D) :
    (D - K).comp R.denomInv =
      R.denomInv.comp (D - K) := by
  have hAB :
      (D - K).comp (D + K) =
        (D + K).comp (D - K) :=
    D_sub_K_commutes_D_add_K R.D_phase_linear
  exact
    inverse_commutes_of_commutes
      (A := D - K)
      (B := D + K)
      (Binv := R.denomInv)
      R.denom_right
      R.denom_left
      hAB

attribute [rep_depth operator]
  EndR
  PhaseLinear
  PhaseLinear.apply
  PhaseLinear.self
  PhaseLinear.id_map
  PhaseLinear.add
  PhaseLinear.neg
  PhaseLinear.sub
  PhaseLinear.comp
  inverse_commutes_of_commutes
  inverse_phaseLinear
  VerifiedPhaseResolvent
  VerifiedPhaseResolvent.denom_phase_linear
  VerifiedPhaseResolvent.denomInv_phase_linear
  VerifiedPhaseResolvent.denom_commutes_inverse
  boundedCayley
  boundedCayley_is_phase_linear
  D_sub_K_commutes_D_add_K
  cayley_factors_commute

end InfoGeometry.OperatorAlgebra.ConstructiveCayley

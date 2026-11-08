/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.MatrixOperatorIdentities
import InfoGeometry.Core.JordanMultiplicationClosure
import InfoGeometry.OperatorAlgebra.PeirceKrausGeometry

/-!
# Lie and Jordan multiplication on the full matrix algebra

The Lie action is the native `LieAlgebra.ad`; the unnormalized Jordan action
is the existing `jordanLeft`. Sandwich terms use `LinearMap.mulLeftRight`.
All compositions below are equalities of native complex-linear endomorphisms.
The two-sided positive transport at the end requires the reverse coefficient
to be the adjoint; the preceding polynomial and trace identities do not.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.MatrixLieJordanOperators

open Matrix
open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.Quantum.Choi InfoGeometry.Quantum.KrausAmplification
open scoped ComplexOrder

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The existing associative-envelope identity as a native operator equality. -/
theorem ad_jordan_commutator (U V : Matrix n n ℂ) :
    LieAlgebra.ad ℂ (Matrix n n ℂ) U * jordanLeft (R := ℂ) V -
        jordanLeft (R := ℂ) V * LieAlgebra.ad ℂ (Matrix n n ℂ) U =
      jordanLeft (R := ℂ) ⁅U, V⁆ := by
  apply LinearMap.ext
  intro X
  change (U * (V * X + X * V) - (V * X + X * V) * U) -
      (V * (U * X - X * U) + (U * X - X * U) * V) =
    (U * V - V * U) * X + X * (U * V - V * U)
  exact InfoGeometry.Core.JordanAssociator.commutator_symm_operator U V X

/-- The already-owned Jordan commutator agrees with the native adjoint action. -/
theorem jordan_commutator_eq_ad (U V : Matrix n n ℂ) :
    jordanLeft (R := ℂ) U * jordanLeft (R := ℂ) V -
        jordanLeft (R := ℂ) V * jordanLeft (R := ℂ) U =
      LieAlgebra.ad ℂ (Matrix n n ℂ) ⁅U, V⁆ := by
  apply LinearMap.ext
  intro X
  exact InfoGeometry.Core.JordanMultiplicationClosure.commutator_apply U V X

/-- The symmetric mixed composition is inner action by the symmetric product. -/
theorem jordan_ad_add_swap (U V : Matrix n n ℂ) :
    jordanLeft (R := ℂ) U * LieAlgebra.ad ℂ (Matrix n n ℂ) V +
        jordanLeft (R := ℂ) V * LieAlgebra.ad ℂ (Matrix n n ℂ) U =
      LieAlgebra.ad ℂ (Matrix n n ℂ) (U * V + V * U) := by
  apply LinearMap.ext
  intro X
  change (U * (V * X - X * V) + (V * X - X * V) * U) +
      (V * (U * X - X * U) + (U * X - X * U) * V) =
    (U * V + V * U) * X - X * (U * V + V * U)
  noncomm_ring

/-- Reversing both composition orders gives the same symmetric mixed action. -/
theorem ad_jordan_add_swap (U V : Matrix n n ℂ) :
    LieAlgebra.ad ℂ (Matrix n n ℂ) U * jordanLeft (R := ℂ) V +
        LieAlgebra.ad ℂ (Matrix n n ℂ) V * jordanLeft (R := ℂ) U =
      LieAlgebra.ad ℂ (Matrix n n ℂ) (U * V + V * U) := by
  apply LinearMap.ext
  intro X
  change (U * (V * X + X * V) - (V * X + X * V) * U) +
      (V * (U * X + X * U) - (U * X + X * U) * V) =
    (U * V + V * U) * X - X * (U * V + V * U)
  noncomm_ring

/-- Exchanging coefficients in the mixed difference retains a sandwich defect. -/
theorem ad_jordan_sub_swap (U V : Matrix n n ℂ) :
    LieAlgebra.ad ℂ (Matrix n n ℂ) U * jordanLeft (R := ℂ) V -
        LieAlgebra.ad ℂ (Matrix n n ℂ) V * jordanLeft (R := ℂ) U =
      jordanLeft (R := ℂ) ⁅U, V⁆ +
        (2 : ℂ) • (LinearMap.mulLeftRight ℂ (U, V) -
          LinearMap.mulLeftRight ℂ (V, U)) := by
  apply LinearMap.ext
  intro X
  change (U * (V * X + X * V) - (V * X + X * V) * U) -
      (V * (U * X + X * U) - (U * X + X * U) * V) =
    (U * V - V * U) * X + X * (U * V - V * U) +
      (2 : ℂ) • (U * X * V - V * X * U)
  simp only [two_smul]
  noncomm_ring

/-- Symmetric Jordan composition contains the plus sandwich correction. -/
theorem jordan_mul_add_swap (U V : Matrix n n ℂ) :
    jordanLeft (R := ℂ) U * jordanLeft (R := ℂ) V +
        jordanLeft (R := ℂ) V * jordanLeft (R := ℂ) U =
      jordanLeft (R := ℂ) (U * V + V * U) +
        (2 : ℂ) • (LinearMap.mulLeftRight ℂ (U, V) +
          LinearMap.mulLeftRight ℂ (V, U)) := by
  apply LinearMap.ext
  intro X
  change (U * (V * X + X * V) + (V * X + X * V) * U) +
      (V * (U * X + X * U) + (U * X + X * U) * V) =
    (U * V + V * U) * X + X * (U * V + V * U) +
      (2 : ℂ) • (U * X * V + V * X * U)
  simp only [two_smul]
  noncomm_ring

/-- Symmetric Lie composition contains the opposite sandwich correction. -/
theorem ad_mul_add_swap (U V : Matrix n n ℂ) :
    LieAlgebra.ad ℂ (Matrix n n ℂ) U * LieAlgebra.ad ℂ (Matrix n n ℂ) V +
        LieAlgebra.ad ℂ (Matrix n n ℂ) V * LieAlgebra.ad ℂ (Matrix n n ℂ) U =
      jordanLeft (R := ℂ) (U * V + V * U) -
        (2 : ℂ) • (LinearMap.mulLeftRight ℂ (U, V) +
          LinearMap.mulLeftRight ℂ (V, U)) := by
  apply LinearMap.ext
  intro X
  change (U * (V * X - X * V) - (V * X - X * V) * U) +
      (V * (U * X - X * U) - (U * X - X * U) * V) =
    (U * V + V * U) * X + X * (U * V + V * U) -
      (2 : ℂ) • (U * X * V + V * X * U)
  simp only [two_smul]
  noncomm_ring

/-- Adding the two symmetric compositions cancels the sandwich terms. -/
theorem jordan_ad_symmetric_sum (U V : Matrix n n ℂ) :
    (jordanLeft (R := ℂ) U * jordanLeft (R := ℂ) V +
        jordanLeft (R := ℂ) V * jordanLeft (R := ℂ) U) +
      (LieAlgebra.ad ℂ (Matrix n n ℂ) U * LieAlgebra.ad ℂ (Matrix n n ℂ) V +
        LieAlgebra.ad ℂ (Matrix n n ℂ) V * LieAlgebra.ad ℂ (Matrix n n ℂ) U) =
      (2 : ℂ) • jordanLeft (R := ℂ) (U * V + V * U) := by
  rw [jordan_mul_add_swap, ad_mul_add_swap]
  simp only [two_smul]
  abel

/-- Subtracting the symmetric compositions recovers four times the transport. -/
theorem jordan_ad_symmetric_sub (U V : Matrix n n ℂ) :
    (jordanLeft (R := ℂ) U * jordanLeft (R := ℂ) V +
        jordanLeft (R := ℂ) V * jordanLeft (R := ℂ) U) -
      (LieAlgebra.ad ℂ (Matrix n n ℂ) U * LieAlgebra.ad ℂ (Matrix n n ℂ) V +
        LieAlgebra.ad ℂ (Matrix n n ℂ) V * LieAlgebra.ad ℂ (Matrix n n ℂ) U) =
      (4 : ℂ) • (LinearMap.mulLeftRight ℂ (U, V) +
        LinearMap.mulLeftRight ℂ (V, U)) := by
  rw [jordan_mul_add_swap, ad_mul_add_swap]
  rw [show (4 : ℂ) = (2 : ℂ) + 2 by norm_num, add_smul]
  simp only [two_smul]
  abel

/-- Alternating the two actions yields the adjoint action of the square. -/
theorem ad_mul_jordan_self (U : Matrix n n ℂ) :
    LieAlgebra.ad ℂ (Matrix n n ℂ) U * jordanLeft (R := ℂ) U =
      LieAlgebra.ad ℂ (Matrix n n ℂ) (U * U) := by
  apply LinearMap.ext
  intro X
  change U * (U * X + X * U) - (U * X + X * U) * U =
    (U * U) * X - X * (U * U)
  noncomm_ring

/-- The other alternating order has the same square action. -/
theorem jordan_mul_ad_self (U : Matrix n n ℂ) :
    jordanLeft (R := ℂ) U * LieAlgebra.ad ℂ (Matrix n n ℂ) U =
      LieAlgebra.ad ℂ (Matrix n n ℂ) (U * U) := by
  apply LinearMap.ext
  intro X
  change U * (U * X - X * U) + (U * X - X * U) * U =
    (U * U) * X - X * (U * U)
  noncomm_ring

/-- The native iterated Lie action retains its quadratic sandwich term. -/
theorem ad_mul_self (U : Matrix n n ℂ) :
    LieAlgebra.ad ℂ (Matrix n n ℂ) U * LieAlgebra.ad ℂ (Matrix n n ℂ) U =
      jordanLeft (R := ℂ) (U * U) -
        (2 : ℂ) • LinearMap.mulLeftRight ℂ (U, U) := by
  apply LinearMap.ext
  intro X
  change ⁅U, ⁅U, X⁆⁆ =
    (U * U) * X + X * (U * U) - (2 : ℂ) • (U * X * U)
  rw [InfoGeometry.OperatorAlgebra.MatrixOperatorIdentities.lie_lie_expansion]
  abel

/-- The existing Jordan quadratic identity as an equality of endomorphisms. -/
theorem jordan_mul_self (U : Matrix n n ℂ) :
    jordanLeft (R := ℂ) U * jordanLeft (R := ℂ) U =
      jordanLeft (R := ℂ) (U * U) +
        (2 : ℂ) • LinearMap.mulLeftRight ℂ (U, U) := by
  apply LinearMap.ext
  intro X
  change U * (U * X + X * U) + (U * X + X * U) * U =
    (U * U) * X + X * (U * U) + (2 : ℂ) • (U * X * U)
  calc
    U * (U * X + X * U) + (U * X + X * U) * U =
        (U * X + X * U) * U + U * (U * X + X * U) := add_comm _ _
    _ = (2 : ℕ) • (U * X * U) + ((U * U) * X + X * (U * U)) :=
      sub_eq_iff_eq_add.mp
        (InfoGeometry.Core.JordanAssociator.symm_quadratic_sandwich U X)
    _ = (U * U) * X + X * (U * U) + (2 : ℂ) • (U * X * U) := by
      simp only [two_smul]
      abel

/-- Square-zero coefficients annihilate the Lie-after-Jordan composition. -/
theorem ad_mul_jordan_eq_zero {U : Matrix n n ℂ} (hU : U * U = 0) :
    LieAlgebra.ad ℂ (Matrix n n ℂ) U * jordanLeft (R := ℂ) U = 0 := by
  rw [ad_mul_jordan_self, hU]
  exact map_zero (LieAlgebra.ad ℂ (Matrix n n ℂ))

/-- Square-zero coefficients annihilate the Jordan-after-Lie composition. -/
theorem jordan_mul_ad_eq_zero {U : Matrix n n ℂ} (hU : U * U = 0) :
    jordanLeft (R := ℂ) U * LieAlgebra.ad ℂ (Matrix n n ℂ) U = 0 := by
  rw [jordan_mul_ad_self, hU]
  exact map_zero (LieAlgebra.ad ℂ (Matrix n n ℂ))

/-- The ordinary Lie square need not vanish when its coefficient is square-zero. -/
theorem ad_mul_self_of_mul_self_eq_zero {U : Matrix n n ℂ}
    (hU : U * U = 0) :
    LieAlgebra.ad ℂ (Matrix n n ℂ) U * LieAlgebra.ad ℂ (Matrix n n ℂ) U =
      -((2 : ℂ) • LinearMap.mulLeftRight ℂ (U, U)) := by
  rw [ad_mul_self, hU]
  apply LinearMap.ext
  intro X
  change (0 : Matrix n n ℂ) * X + X * 0 - (2 : ℂ) • (U * X * U) =
    -((2 : ℂ) • (U * X * U))
  simp

/-- The ordinary Jordan square has the opposite sandwich correction. -/
theorem jordan_mul_self_of_mul_self_eq_zero {U : Matrix n n ℂ}
    (hU : U * U = 0) :
    jordanLeft (R := ℂ) U * jordanLeft (R := ℂ) U =
      (2 : ℂ) • LinearMap.mulLeftRight ℂ (U, U) := by
  rw [jordan_mul_self, hU]
  apply LinearMap.ext
  intro X
  change (0 : Matrix n n ℂ) * X + X * 0 + (2 : ℂ) • (U * X * U) =
    (2 : ℂ) • (U * X * U)
  simp

/-- Cyclic trace identifies the transport on every matrix, with no parity premise. -/
theorem trace_mulLeftRight_add_swap (U V X : Matrix n n ℂ) :
    trace ((LinearMap.mulLeftRight ℂ (U, V) +
      LinearMap.mulLeftRight ℂ (V, U)) X) =
      trace ((U * V + V * U) * X) := by
  change trace (U * X * V + V * X * U) = trace ((U * V + V * U) * X)
  rw [trace_add, add_mul, trace_add,
    trace_mul_cycle U X V, trace_mul_cycle V X U]
  exact add_comm _ _

/-- The symmetric two-sided transport is symmetric for the bilinear trace pairing. -/
theorem trace_mulLeftRight_add_swap_pairing (U V X Y : Matrix n n ℂ) :
    trace (((LinearMap.mulLeftRight ℂ (U, V) +
      LinearMap.mulLeftRight ℂ (V, U)) X) * Y) =
      trace (X * ((LinearMap.mulLeftRight ℂ (U, V) +
        LinearMap.mulLeftRight ℂ (V, U)) Y)) := by
  change trace ((U * X * V + V * X * U) * Y) =
    trace (X * (U * Y * V + V * Y * U))
  calc
    trace ((U * X * V + V * X * U) * Y) =
        trace (U * (X * (V * Y))) + trace (V * (X * (U * Y))) := by
      rw [add_mul, trace_add]
      simp only [mul_assoc]
    _ = trace ((X * (V * Y)) * U) + trace ((X * (U * Y)) * V) := by
      rw [trace_mul_comm U (X * (V * Y)), trace_mul_comm V (X * (U * Y))]
    _ = trace (X * (U * Y * V)) + trace (X * (V * Y * U)) := by
      simp only [mul_assoc]
      exact add_comm _ _
    _ = trace (X * (U * Y * V + V * Y * U)) := by
      rw [mul_add, trace_add]

/-- Adjoint-paired transport is literally the existing two-term Kraus map. -/
theorem mulLeftRight_add_star_eq_krausMap (U : Matrix n n ℂ) :
    LinearMap.mulLeftRight ℂ (U, star U) +
      LinearMap.mulLeftRight ℂ (star U, U) =
      krausMap ![U, star U] := by
  apply LinearMap.ext
  intro X
  simp [LinearMap.mulLeftRight_apply, krausMap, Fin.sum_univ_two]

/-- The adjoint-paired transport preserves positivity at every finite amplification. -/
theorem amplification_mulLeftRight_add_star_posSemidef
    {r : Type*} [Fintype r] [DecidableEq r]
    (U : Matrix n n ℂ) (X : Matrix (r × n) (r × n) ℂ)
    (hX : X.PosSemidef) :
    (amplification (r := r)
      (LinearMap.mulLeftRight ℂ (U, star U) +
        LinearMap.mulLeftRight ℂ (star U, U)) X).PosSemidef := by
  rw [mulLeftRight_add_star_eq_krausMap]
  exact amplification_krausChannel_posSemidef ![U, star U] X hX

end InfoGeometry.OperatorAlgebra.MatrixLieJordanOperators

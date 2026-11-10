/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

noncomputable section

open scoped BigOperators

open InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
open InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

namespace InfoGeometry.Arithmetic.PrimeSpinorWittenIndex

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem exists_noncomm_pair_readout :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- Single-mode real spinor Witten factor `<(1, a), (1, -a)>` in any `[Ring R]`. -/
def ringRealSpinorWittenFactor
  {R : Type*} [Ring R] (a : R) : R :=
  spinorBilinear (thermalSpinorPlus a) (thermalSpinorMinus a)

/-- In any non-commutative `[Ring R]`, the single-mode real spinor Witten factor equals `1 - a * a`. -/
theorem ringRealSpinorWittenFactor_eq_one_sub_square
  {R : Type*} [Ring R] (a : R) :
  ringRealSpinorWittenFactor a = 1 - scalarWeightFromSpinor a :=
  spinorBilinear_plus_minus_eq_one_sub_square a

def finiteRealSpinorWittenReadout
  {PrimeLabel R : Type*} [CommRing R]
  (modes : Finset PrimeLabel)
  (amplitude : PrimeLabel → R) : R :=
  finitePrimeSpinorBilinearProduct modes amplitude

theorem finiteRealSpinorWittenReadout_eq_weylDenominator_squareWeights
  {PrimeLabel R : Type*} [CommRing R]
  (modes : Finset PrimeLabel)
  (amplitude : PrimeLabel → R) :
  finiteRealSpinorWittenReadout modes amplitude =
  finitePrimeWeylDenominator modes
    (fun p => scalarWeightFromSpinor (amplitude p)) := by
  exact finitePrimeSpinorBilinearProduct_eq_weylDenominator_squareWeights modes amplitude

theorem finiteRealSpinorWittenReadout_eq_mobiusFermionPartition_squareWeights
  {PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
  (modes : Finset PrimeLabel)
  (amplitude : PrimeLabel → R) :
  finiteRealSpinorWittenReadout modes amplitude =
  InfoGeometry.Arithmetic.MobiusFermionBosonization.finiteMobiusFermionGradedPartition
    modes
    (fun p => scalarWeightFromSpinor (amplitude p)) := by
  exact finitePrimeSpinorBilinearProduct_eq_mobiusFermionPartition_squareWeights modes amplitude

theorem finiteRealMajoranaWittenIndex_cancel
  (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
  (hP : P.primes.Nonempty) :
  (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 :=
  InfoGeometry.Arithmetic.PrimeBitWittenIndex.finite_witten_index_cancel P hP

end InfoGeometry.Arithmetic.PrimeSpinorWittenIndex

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeSpinorWittenIndex.Readout
import InfoGeometry.Arithmetic.PrimeSpinorWittenIndex.Pfaffian

noncomputable section

open InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
open InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

namespace InfoGeometry.Arithmetic.PrimeSpinorWittenIndex

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem exists_noncomm_pair_packet :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- Single-mode Pfaffian/Witten/Determinant identity over any non-commutative `[Ring R]`. -/
theorem ring_local_pfaffian_witten_readout
  {R : Type*} [Ring R] (a : R) :
  majoranaBlockPfaffian (primeSpinorMajoranaBlock a) =
    ringRealSpinorWittenFactor a ∧
  ringRealSpinorWittenFactor a =
    1 - scalarWeightFromSpinor a ∧
  majoranaBlockPfaffian (primeSpinorMajoranaBlock a) *
    majoranaBlockPfaffian (primeSpinorMajoranaBlock a) =
    majoranaBlockDeterminant (primeSpinorMajoranaBlock a) :=
  ⟨rfl,
   ringRealSpinorWittenFactor_eq_one_sub_square a,
   majoranaBlockPfaffian_sq_eq_determinant (primeSpinorMajoranaBlock a)⟩

structure PrimeSpinorWittenIndexPacket
  (PrimeLabel R : Type*)
  [CommRing R] where
  modes : Finset PrimeLabel
  amplitude : PrimeLabel → R

/-- Ground inhabitant of `PrimeSpinorWittenIndexPacket` over `ℤ`. -/
def intEmptyPrimeSpinorWittenIndexPacket : PrimeSpinorWittenIndexPacket ℕ ℤ where
  modes := ∅
  amplitude := fun _ => 0

namespace PrimeSpinorWittenIndexPacket

theorem finite_readout
  {PrimeLabel R : Type*}
  [CommRing R]
  (P : PrimeSpinorWittenIndexPacket PrimeLabel R) :
  finiteRealSpinorWittenReadout P.modes P.amplitude =
  finitePrimeWeylDenominator P.modes
    (fun p => scalarWeightFromSpinor (P.amplitude p)) := by
  exact finiteRealSpinorWittenReadout_eq_weylDenominator_squareWeights
    P.modes P.amplitude

theorem PrimeSpinorWittenIndex
  {PrimeLabel R : Type*}
  [CommRing R]
  (P : PrimeSpinorWittenIndexPacket PrimeLabel R) :
  finiteMajoranaPfaffianReadout P.modes P.amplitude =
    finiteRealSpinorWittenReadout P.modes P.amplitude ∧
  finiteRealSpinorWittenReadout P.modes P.amplitude =
    finitePrimeWeylDenominator P.modes (fun p => scalarWeightFromSpinor (P.amplitude p)) ∧
  finiteMajoranaPfaffianReadout P.modes P.amplitude *
    finiteMajoranaPfaffianReadout P.modes P.amplitude =
    finiteMajoranaDeterminantReadout P.modes P.amplitude := by
  refine ⟨?_, ?_, ?_⟩
  · exact finiteMajoranaPfaffianReadout_eq_spinorWittenReadout P.modes P.amplitude
  · exact P.finite_readout
  · exact finiteMajoranaPfaffian_sq_eq_determinant P.modes P.amplitude

end PrimeSpinorWittenIndexPacket

end InfoGeometry.Arithmetic.PrimeSpinorWittenIndex

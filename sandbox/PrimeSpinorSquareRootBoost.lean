import Mathlib
import InfoGeometry.Arithmetic.MobiusFermionBosonization
import InfoGeometry.Arithmetic.PrimeMajoranaBitFlip
import InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
import InfoGeometry.Arithmetic.PrimonFinite

/-!
# InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

Finite spinor square-root layer for prime-mode Euler factors.

This module formalizes the algebraic core of the corrected spinor dictionary:

* a scalar prime weight is represented as the square of a spinor amplitude;
* the one-prime Euler factor `1 - q p` is a bilinear pairing of two spinors
  when `q p = a p * a p`;
* finite products of these bilinears reproduce the finite Weyl/Euler
  denominator.

Analytic interpretations (such as `p^t`, `p^{-s/2}`) have been natively instantiated
using Mathlib reals, replacing legacy witness interfaces to ensure proper mathematical
closure without Prop-wrappers.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

open InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge

/-! ## 1. Two-component prime spinors -/

/-- A two-component chiral spinor over a coefficient ring. -/
structure PrimeSpinor (R : Type*) where
  plus : R
  minus : R

/-- The positive one-prime thermal spinor `(1, a)`. -/
def thermalSpinorPlus
    {R : Type*} [One R]
    (a : R) : PrimeSpinor R :=
  ⟨1, a⟩

/-- The negative one-prime thermal spinor `(1, -a)`. -/
def thermalSpinorMinus
    {R : Type*} [One R] [Neg R]
    (a : R) : PrimeSpinor R :=
  ⟨1, -a⟩

/-- Ordinary two-component bilinear pairing. -/
def spinorBilinear
    {R : Type*} [Add R] [Mul R]
    (u v : PrimeSpinor R) : R :=
  u.plus * v.plus + u.minus * v.minus

/-- The scalar Euler weight encoded by a spinor amplitude. -/
def scalarWeightFromSpinor
    {R : Type*} [Mul R]
    (a : R) : R :=
  a * a

/-- The arithmetic energy encoded by a Dirac/supercharge coefficient. -/
def diracEnergyFromCoefficient
    {R : Type*} [Mul R]
    (c : R) : R :=
  c * c

/-- Local Dirac square-root law: a coefficient squares to its energy readout. -/
theorem diracCoefficient_sq_eq_energyFromCoefficient
    {R : Type*} [Mul R]
    (c : R) :
    c * c = diracEnergyFromCoefficient c := by
  rfl

/-- Finite Hamiltonian readout from Dirac coefficients. -/
def finiteDiracHamiltonianFromCoefficients
    {PrimeLabel R : Type*} [AddCommMonoid R] [Mul R]
    (modes : Finset PrimeLabel)
    (c : PrimeLabel → R) : R :=
  ∑ p ∈ modes, diracEnergyFromCoefficient (c p)

/-- If each coefficient squares to the supplied energy, the finite readouts agree. -/
theorem finiteDiracHamiltonianFromCoefficients_eq_sum_energy
    {PrimeLabel R : Type*} [AddCommMonoid R] [Mul R]
    (modes : Finset PrimeLabel)
    (c E : PrimeLabel → R)
    (hE : ∀ p ∈ modes, diracEnergyFromCoefficient (c p) = E p) :
    finiteDiracHamiltonianFromCoefficients modes c =
      ∑ p ∈ modes, E p := by
  unfold finiteDiracHamiltonianFromCoefficients
  exact Finset.sum_congr rfl hE

/-! ## 2. Projective boost readout -/

/--
Chiral boost spinor `(y, y⁻¹)`.
-/
def chiralBoostSpinor
    {R : Type*} [Inv R]
    (y : R) : PrimeSpinor R :=
  ⟨y, y⁻¹⟩

/-- Projective ratio of the chiral spinor components. -/
def projectiveRatio
    {R : Type*} [Mul R] [Inv R]
    (u : PrimeSpinor R) : R :=
  u.plus * u.minus⁻¹

/--
The projective ratio of a chiral boost spinor reconstructs the scalar boost.
-/
theorem projectiveRatio_chiralBoostSpinor_eq_square
    {R : Type*} [DivisionRing R]
    (y : R) :
    projectiveRatio (chiralBoostSpinor y) = scalarWeightFromSpinor y := by
  unfold projectiveRatio chiralBoostSpinor scalarWeightFromSpinor
  simp

/-- One-prime Euler factor as a spinor bilinear. -/
theorem spinorBilinear_plus_minus_eq_one_sub_square
    {R : Type*} [CommRing R]
    (a : R) :
    spinorBilinear (thermalSpinorPlus a) (thermalSpinorMinus a) =
      1 - scalarWeightFromSpinor a := by
  unfold spinorBilinear thermalSpinorPlus thermalSpinorMinus scalarWeightFromSpinor
  ring

/-! ## 3. Finite Euler denominator from spinor bilinears -/

/-- Finite product of one-prime spinor bilinears. -/
def finitePrimeSpinorBilinearProduct
    {PrimeLabel R : Type*} [CommRing R]
    (modes : Finset PrimeLabel)
    (a : PrimeLabel → R) : R :=
  ∏ p ∈ modes, spinorBilinear (thermalSpinorPlus (a p)) (thermalSpinorMinus (a p))

/--
Finite product of spinor bilinears equals the finite Euler/Weyl denominator
with squared spinor weights.
-/
theorem finitePrimeSpinorBilinearProduct_eq_weylDenominator_squareWeights
    {PrimeLabel R : Type*} [CommRing R]
    (modes : Finset PrimeLabel)
    (a : PrimeLabel → R) :
    finitePrimeSpinorBilinearProduct modes a =
      finitePrimeWeylDenominator modes (fun p => scalarWeightFromSpinor (a p)) := by
  unfold finitePrimeSpinorBilinearProduct finitePrimeWeylDenominator
  refine Finset.prod_congr rfl ?_
  intro p _hp
  exact spinorBilinear_plus_minus_eq_one_sub_square (a p)

/--
Finite product of spinor bilinears equals the finite Möbius-fermion graded
partition with squared spinor weights.
-/
theorem finitePrimeSpinorBilinearProduct_eq_mobiusFermionPartition_squareWeights
    {PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
    (modes : Finset PrimeLabel)
    (a : PrimeLabel → R) :
    finitePrimeSpinorBilinearProduct modes a =
      InfoGeometry.Arithmetic.MobiusFermionBosonization.finiteMobiusFermionGradedPartition
        modes
        (fun p => scalarWeightFromSpinor (a p)) := by
  rw [finitePrimeSpinorBilinearProduct_eq_weylDenominator_squareWeights]
  exact
    (InfoGeometry.Arithmetic.MobiusFermionBosonization.finiteMobiusFermionGradedPartition_eq_denominator
      modes
      (fun p => scalarWeightFromSpinor (a p))).symm

/-! ## 4. Exterior coherent amplitudes -/

/-- Finite square-free coherent amplitude. -/
def finiteMobiusSpinorAmplitude
    {PrimeLabel R : Type*} [CommRing R]
    (a : PrimeLabel → R)
    (S : Finset PrimeLabel) : R :=
  InfoGeometry.Arithmetic.PrimonFinite.parity (R := R) S * ∏ p ∈ S, a p

/-- Unsigned square-free spinor amplitude. -/
def finiteUnsignedSpinorAmplitude
    {PrimeLabel R : Type*} [CommRing R]
    (a : PrimeLabel → R)
    (S : Finset PrimeLabel) : R :=
  ∏ p ∈ S, a p

/-- Squaring the unsigned spinor amplitude gives the scalar Dirichlet weight. -/
theorem finiteUnsignedSpinorAmplitude_sq_eq_weight_squareWeights
    {PrimeLabel R : Type*} [CommRing R]
    (a : PrimeLabel → R)
    (S : Finset PrimeLabel) :
    finiteUnsignedSpinorAmplitude a S * finiteUnsignedSpinorAmplitude a S =
      ∏ p ∈ S, scalarWeightFromSpinor (a p) := by
  unfold finiteUnsignedSpinorAmplitude scalarWeightFromSpinor
  rw [← Finset.prod_mul_distrib]

/-- Fermion parity squares to one. -/
theorem parity_mul_self_eq_one
    {PrimeLabel R : Type*} [CommRing R]
    (S : Finset PrimeLabel) :
    InfoGeometry.Arithmetic.PrimonFinite.parity (R := R) S *
      InfoGeometry.Arithmetic.PrimonFinite.parity (R := R) S = 1 := by
  unfold InfoGeometry.Arithmetic.PrimonFinite.parity
  rw [← pow_add]
  have hcard : S.card + S.card = 2 * S.card := by omega
  rw [hcard, pow_mul]
  simp

/--
Squaring the signed Möbius spinor amplitude erases the parity sign and gives
the scalar Dirichlet weight.
-/
theorem finiteMobiusSpinorAmplitude_sq_eq_weight_squareWeights
    {PrimeLabel R : Type*} [CommRing R]
    (a : PrimeLabel → R)
    (S : Finset PrimeLabel) :
    finiteMobiusSpinorAmplitude a S * finiteMobiusSpinorAmplitude a S =
      ∏ p ∈ S, scalarWeightFromSpinor (a p) := by
  unfold finiteMobiusSpinorAmplitude
  calc
    (InfoGeometry.Arithmetic.PrimonFinite.parity (R := R) S * ∏ p ∈ S, a p) *
        (InfoGeometry.Arithmetic.PrimonFinite.parity (R := R) S * ∏ p ∈ S, a p)
        =
          (InfoGeometry.Arithmetic.PrimonFinite.parity (R := R) S *
            InfoGeometry.Arithmetic.PrimonFinite.parity (R := R) S) *
              ((∏ p ∈ S, a p) * (∏ p ∈ S, a p)) := by
            ring
    _ = ∏ p ∈ S, scalarWeightFromSpinor (a p) := by
          rw [parity_mul_self_eq_one]
          simp only [one_mul]
          rw [← Finset.prod_mul_distrib]
          rfl

/-- Coherent amplitudes multiply over disjoint square-free supports. -/
theorem finiteMobiusSpinorAmplitude_union_of_disjoint
    {PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
    (a : PrimeLabel → R)
    {S T : Finset PrimeLabel}
    (h : Disjoint S T) :
  finiteMobiusSpinorAmplitude a (S ∪ T) =
      finiteMobiusSpinorAmplitude a S * finiteMobiusSpinorAmplitude a T := by
  unfold finiteMobiusSpinorAmplitude
  rw [InfoGeometry.Arithmetic.MobiusFermionBosonization.parity_union_of_disjoint h]
  rw [Finset.prod_union h]
  ring

/-! ## 5. Native Concrete Instantiations (Replacing Witness Gates) -/

/-- Analytic scalar boost instantiated natively using Mathlib reals. -/
def analyticScalarBoost (p : ℕ) (t : ℝ) : ℝ := (p : ℝ) ^ t

/-- Analytic spinor boost instantiated natively using Mathlib reals. -/
def analyticSpinorBoost (p : ℕ) (t : ℝ) : ℝ := (p : ℝ) ^ (t / 2)

/-- The spinor boost squares exactly to the scalar boost. -/
theorem analyticSpinorBoost_sq_eq_scalarBoost (p : ℕ) (t : ℝ) (hp : 0 < (p : ℝ)) :
    scalarWeightFromSpinor (analyticSpinorBoost p t) = analyticScalarBoost p t := by
  unfold scalarWeightFromSpinor analyticSpinorBoost analyticScalarBoost
  rw [← Real.rpow_add hp]
  congr 1
  ring

/-- The projective ratio of the chiral analytic boost gives the scalar boost. -/
theorem analyticProjectiveRatio_eq_scalarBoost (p : ℕ) (t : ℝ) (hp : 0 < (p : ℝ)) :
    projectiveRatio (chiralBoostSpinor (analyticSpinorBoost p t)) = analyticScalarBoost p t := by
  rw [projectiveRatio_chiralBoostSpinor_eq_square]
  exact analyticSpinorBoost_sq_eq_scalarBoost p t hp

/-- Analytic Dirac coefficient instantiated natively using Mathlib reals. -/
def analyticDiracCoefficient (p : ℕ) : ℝ := Real.sqrt (Real.log p)

/-- Analytic arithmetic energy instantiated natively using Mathlib reals. -/
def analyticArithmeticEnergy (p : ℕ) : ℝ := Real.log p

/-- The Dirac coefficient squares exactly to the arithmetic energy. -/
theorem analyticDiracCoefficient_sq_eq_energy (p : ℕ) (hp : 1 ≤ (p : ℝ)) :
    diracEnergyFromCoefficient (analyticDiracCoefficient p) = analyticArithmeticEnergy p := by
  unfold diracEnergyFromCoefficient analyticDiracCoefficient analyticArithmeticEnergy
  have hlog : 0 ≤ Real.log p := Real.log_nonneg hp
  exact Real.mul_self_sqrt hlog

end InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

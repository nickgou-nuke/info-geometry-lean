import Mathlib
import InfoGeometry.Arithmetic.MobiusFermionBosonization
import InfoGeometry.Arithmetic.PrimeMajoranaCARGate

/-!
# InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

Finite spinor square-root layer for prime-mode Euler factors.

This module formalizes the algebraic core of the corrected spinor dictionary:

* a scalar prime weight is represented as the square of a spinor amplitude;
* the one-prime Euler factor `1 - q p` is a bilinear pairing of two spinors
  when `q p = a p * a p`;
* finite products of these bilinears reproduce the finite Weyl/Euler
  denominator.

Analytic statements involving `p^t`, `p^{-s/2}`, infinite products, Riemann
states, or zero-mode interpretations are kept behind witness interfaces.
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

/--
Finite Hamiltonian readout from Dirac coefficients.

For the analytic interpretation, `c p = sqrt (log p)`.
-/
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

For the analytic interpretation `y = p^{t/2}`, this is the finite algebraic
stand-in for `(p^{t/2}, p^{-t/2})`.
-/
def chiralBoostSpinor
    {R : Type*} [Inv R]
    (y : R) : PrimeSpinor R :=
  ⟨y, y⁻¹⟩

/--
Projective ratio of the chiral spinor components.

For `(p^{t/2}, p^{-t/2})`, this readout is `p^t`.
-/
def projectiveRatio
    {R : Type*} [Mul R] [Inv R]
    (u : PrimeSpinor R) : R :=
  u.plus * u.minus⁻¹

/--
The projective ratio of a chiral boost spinor reconstructs the scalar boost.

This is the finite algebraic form of
`p^{t/2} / p^{-t/2} = p^t`.
-/
theorem projectiveRatio_chiralBoostSpinor_eq_square
    {R : Type*} [Field R]
    (y : R) :
    projectiveRatio (chiralBoostSpinor y) = scalarWeightFromSpinor y := by
  unfold projectiveRatio chiralBoostSpinor scalarWeightFromSpinor
  simp

/--
One-prime Euler factor as a spinor bilinear.

This is the finite algebraic form of
`<(1, p^{-s/2}), (1, -p^{-s/2})> = 1 - p^{-s}`.
-/
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

/--
Finite square-free coherent amplitude.

For `a p = p^{-s/2}`, this is the finite amplitude
`(-1)^|S| prod_{p in S} p^{-s/2}`.
-/
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

/-! ## 5. Witness gates for analytic spin lifts and zero modes -/

/--
Spin-lift/double-cover gate.

The finite theorems above prove the square-root amplitude algebra.  Analytic
readouts such as `p^t`, `p^{t/2}`, and a concrete boost representation are
supplied by an owner model through this witness interface.
-/
structure SpinLiftDoubleCoverGate
    (PrimeLabel ScalarBoost SpinorBoost : Type*) where
  scalarBoost : PrimeLabel → ScalarBoost
  spinorBoost : PrimeLabel → SpinorBoost
  SpinorSquaresTo : SpinorBoost → ScalarBoost → Prop
  ProjectiveRatioMatches : SpinorBoost → ScalarBoost → Prop
  square_law : ∀ p, SpinorSquaresTo (spinorBoost p) (scalarBoost p)
  projective_ratio_law : ∀ p, ProjectiveRatioMatches (spinorBoost p) (scalarBoost p)

namespace SpinLiftDoubleCoverGate

/-- Explicit debt: analytic spin-lift squaring needs a concrete boost owner. -/
theorem square
    {PrimeLabel ScalarBoost SpinorBoost : Type*}
    (G : SpinLiftDoubleCoverGate PrimeLabel ScalarBoost SpinorBoost)
    (p : PrimeLabel) :
    G.SpinorSquaresTo (G.spinorBoost p) (G.scalarBoost p) :=
    G.square_law p

/-- Explicit debt: projective-ratio matching needs a concrete boost owner. -/
theorem projective_ratio
    {PrimeLabel ScalarBoost SpinorBoost : Type*}
    (G : SpinLiftDoubleCoverGate PrimeLabel ScalarBoost SpinorBoost)
    (p : PrimeLabel) :
    G.ProjectiveRatioMatches (G.spinorBoost p) (G.scalarBoost p) :=
    G.projective_ratio_law p

end SpinLiftDoubleCoverGate

/--
Three-square-root dictionary for one finite prime-mode model.

It keeps separate:

* spin lift of a boost: `spinLift² = scalarBoost`;
* Dirac square root of arithmetic energy: `diracCoefficient² = energy`;
* thermal spinor amplitude: `thermalAmplitude² = thermalWeight`.
-/
structure PrimeThreeSquareRootDictionary
    (PrimeLabel R : Type*) [Mul R] where
  scalarBoost : PrimeLabel → R
  spinLift : PrimeLabel → R
  arithmeticEnergy : PrimeLabel → R
  diracCoefficient : PrimeLabel → R
  thermalWeight : PrimeLabel → R
  thermalAmplitude : PrimeLabel → R
  spinLiftSquare :
    ∀ p : PrimeLabel, scalarBoost p = scalarWeightFromSpinor (spinLift p)
  diracSquare :
    ∀ p : PrimeLabel, arithmeticEnergy p = diracEnergyFromCoefficient (diracCoefficient p)
  thermalSquare :
    ∀ p : PrimeLabel, thermalWeight p = scalarWeightFromSpinor (thermalAmplitude p)

namespace PrimeThreeSquareRootDictionary

/-- Re-export of the spin-lift square law. -/
theorem spin_lift_square
    {PrimeLabel R : Type*} [Mul R]
    (D : PrimeThreeSquareRootDictionary PrimeLabel R)
    (p : PrimeLabel) :
    D.scalarBoost p = scalarWeightFromSpinor (D.spinLift p) :=
  D.spinLiftSquare p

/-- Re-export of the Dirac coefficient square law. -/
theorem dirac_square
    {PrimeLabel R : Type*} [Mul R]
    (D : PrimeThreeSquareRootDictionary PrimeLabel R)
    (p : PrimeLabel) :
    D.arithmeticEnergy p = diracEnergyFromCoefficient (D.diracCoefficient p) :=
  D.diracSquare p

/-- Re-export of the thermal amplitude square law. -/
theorem thermal_square
    {PrimeLabel R : Type*} [Mul R]
    (D : PrimeThreeSquareRootDictionary PrimeLabel R)
    (p : PrimeLabel) :
    D.thermalWeight p = scalarWeightFromSpinor (D.thermalAmplitude p) :=
  D.thermalSquare p

end PrimeThreeSquareRootDictionary

/--
Majorana spinor readout packet.

This packages the finite bit-flip layer together with the finite spinor
bilinear layer, while leaving analytic zero-mode interpretations to the
separate witness gate.
-/
structure PrimeSpinorSquareRootPacket
    (PrimeLabel R Operator ZeroReadout : Type*) [DecidableEq PrimeLabel] [CommRing R] where
  modes : Finset PrimeLabel
  amplitude : PrimeLabel → R
  majoranaCAR : InfoGeometry.Arithmetic.PrimeMajoranaBitFlip.PrimeMajoranaCARGate
    PrimeLabel Operator
  zeroModeGate : InfoGeometry.Arithmetic.PrimeMajoranaBitFlip.MajoranaZeroModeGate
    Operator Operator ZeroReadout

namespace PrimeSpinorSquareRootPacket

/-- Packet-level finite spinor bilinear partition theorem, proved from the owner theorem. -/
theorem bilinear_partition
    {PrimeLabel R Operator ZeroReadout : Type*}
    [DecidableEq PrimeLabel] [CommRing R]
    (P : PrimeSpinorSquareRootPacket PrimeLabel R Operator ZeroReadout) :
    finitePrimeSpinorBilinearProduct P.modes P.amplitude =
      finitePrimeWeylDenominator P.modes
        (fun p => scalarWeightFromSpinor (P.amplitude p)) :=
  finitePrimeSpinorBilinearProduct_eq_weylDenominator_squareWeights P.modes P.amplitude

end PrimeSpinorSquareRootPacket

end InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

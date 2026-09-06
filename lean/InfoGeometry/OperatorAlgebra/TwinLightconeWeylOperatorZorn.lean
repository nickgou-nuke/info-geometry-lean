import InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn
import InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce
import InfoGeometry.Canonical.PauliHestenesSpinMomentum

/-!
# Twin light-cone/Weyl soldering in an outer operator-Zorn block

For an operator-valued four-vector `(x0,x1,x2,x3)`, the Weyl soldering is

`[[x0+x3, x1-i x2], [x1+i x2, x0-x3]]`.

Two such four-vectors are placed on the diagonal of an outer associative Zorn
block.  Two independent chiral gauge operators occupy the off-diagonal
entries.  Cartan conjugation fixes the boundary waves and reverses the gauge
channels; sheet exchange swaps both pairs.

This is a nested matrix construction.  It does not assert that arbitrary
operator coefficients form a split-octonion algebra, nor that a boundary pair
by itself is a physical two-state-vector experiment.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.TwinLightconeWeylOperatorZorn

open scoped Matrix
open InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn
open InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce
open InfoGeometry.Canonical.PauliHestenesSpinMomentum

variable {A : Type*}
variable [Ring A] [StarRing A] [Algebra C A]

abbrev Matrix2 (A : Type*) := Matrix (Fin 2) (Fin 2) A

/-- Central realization of the complex imaginary unit in the coefficient
algebra. -/
def imagUnit : A :=
  algebraMap C A Complex.I

/-- Longitudinal future light-cone coordinate. -/
def lightPlus (x : FourOperatorVector A) : A :=
  x.scalar + x.spatial 2

/-- Longitudinal past light-cone coordinate. -/
def lightMinus (x : FourOperatorVector A) : A :=
  x.scalar - x.spatial 2

/-- Right-circular transverse coordinate. -/
def circularRight (x : FourOperatorVector A) : A :=
  x.spatial 0 - imagUnit * x.spatial 1

/-- Left-circular transverse coordinate. -/
def circularLeft (x : FourOperatorVector A) : A :=
  x.spatial 0 + imagUnit * x.spatial 1

/-- Pauli--Weyl soldering of an operator-valued four-vector. -/
def weylMatrix (x : FourOperatorVector A) : Matrix2 A :=
  !![lightPlus x, circularRight x;
     circularLeft x, lightMinus x]

@[simp] theorem weylMatrix_zero_zero (x : FourOperatorVector A) :
    weylMatrix x 0 0 = lightPlus x := rfl

@[simp] theorem weylMatrix_zero_one (x : FourOperatorVector A) :
    weylMatrix x 0 1 = circularRight x := rfl

@[simp] theorem weylMatrix_one_zero (x : FourOperatorVector A) :
    weylMatrix x 1 0 = circularLeft x := rfl

@[simp] theorem weylMatrix_one_one (x : FourOperatorVector A) :
    weylMatrix x 1 1 = lightMinus x := rfl

/-- Two boundary four-vectors, mathematically independent of their later
pre/post-selection interpretation. -/
@[ext]
structure BoundaryFourVectorTwin (A : Type*) [Ring A] where
  forward : FourOperatorVector A
  backward : FourOperatorVector A

/-- Two independent chiral gauge channels. -/
@[ext]
structure ChiralGaugePair (A : Type*) where
  leftToRight : Matrix2 A
  rightToLeft : Matrix2 A

/-- Outer Zorn block with twin Weyl waves on the diagonal and chiral gauge
operators off diagonal. -/
def twinWeylGaugeZorn
    (psi : BoundaryFourVectorTwin A)
    (gauge : ChiralGaugePair A) :
    ZornBlock (Matrix2 A) :=
  ⟨weylMatrix psi.forward,
    weylMatrix psi.backward,
    gauge.leftToRight,
    gauge.rightToLeft⟩

@[simp] theorem twinWeylGaugeZorn_n_plus
    (psi : BoundaryFourVectorTwin A) (gauge : ChiralGaugePair A) :
    (twinWeylGaugeZorn psi gauge).n_plus_op =
      weylMatrix psi.forward := rfl

@[simp] theorem twinWeylGaugeZorn_n_minus
    (psi : BoundaryFourVectorTwin A) (gauge : ChiralGaugePair A) :
    (twinWeylGaugeZorn psi gauge).n_minus_op =
      weylMatrix psi.backward := rfl

@[simp] theorem twinWeylGaugeZorn_sigma_plus
    (psi : BoundaryFourVectorTwin A) (gauge : ChiralGaugePair A) :
    (twinWeylGaugeZorn psi gauge).sigma_plus_op =
      gauge.leftToRight := rfl

@[simp] theorem twinWeylGaugeZorn_sigma_minus
    (psi : BoundaryFourVectorTwin A) (gauge : ChiralGaugePair A) :
    (twinWeylGaugeZorn psi gauge).sigma_minus_op =
      gauge.rightToLeft := rfl

/-- Cartan conjugation fixes both diagonal Weyl waves and negates the two
chiral gauge channels. -/
theorem cartanInvolution_twinWeylGaugeZorn
    (psi : BoundaryFourVectorTwin A) (gauge : ChiralGaugePair A) :
    cartanInvolution (twinWeylGaugeZorn psi gauge) =
      (⟨weylMatrix psi.forward,
        weylMatrix psi.backward,
        -gauge.leftToRight,
        -gauge.rightToLeft⟩ : ZornBlock (Matrix2 A)) := by
  exact cartanInvolution_coordinates (twinWeylGaugeZorn psi gauge)

/-- Sheet exchange swaps forward/backward waves and left/right gauge maps. -/
theorem sheetExchange_twinWeylGaugeZorn
    (psi : BoundaryFourVectorTwin A) (gauge : ChiralGaugePair A) :
    sheetExchange * twinWeylGaugeZorn psi gauge * sheetExchange =
      (⟨weylMatrix psi.backward,
        weylMatrix psi.forward,
        gauge.rightToLeft,
        gauge.leftToRight⟩ : ZornBlock (Matrix2 A)) := by
  exact sheetExchange_conjugates (twinWeylGaugeZorn psi gauge)

/-- The exact square displays diagonal propagation and off-diagonal coupling
without commuting any operator coefficients. -/
theorem twinWeylGaugeZorn_sq
    (psi : BoundaryFourVectorTwin A) (gauge : ChiralGaugePair A) :
    twinWeylGaugeZorn psi gauge * twinWeylGaugeZorn psi gauge =
      (⟨weylMatrix psi.forward * weylMatrix psi.forward +
          gauge.leftToRight * gauge.rightToLeft,
        gauge.rightToLeft * gauge.leftToRight +
          weylMatrix psi.backward * weylMatrix psi.backward,
        weylMatrix psi.forward * gauge.leftToRight +
          gauge.leftToRight * weylMatrix psi.backward,
        gauge.rightToLeft * weylMatrix psi.forward +
          weylMatrix psi.backward * gauge.rightToLeft⟩ :
        ZornBlock (Matrix2 A)) := by
  apply zornBlock_ext <;>
    simp [twinWeylGaugeZorn]

section ScalarPauliRecovery

/-- Scalar complex four-vector associated with the repository's real Pauli
paravector. -/
def ofPauliParavector (p : PauliParavector) :
    FourOperatorVector C :=
  ⟨(p.energy : C),
    ![(p.px : C), (p.py : C), (p.pz : C)]⟩

/-- The generic light-cone/circular soldering specializes exactly to the
existing Pauli paravector matrix. -/
theorem weylMatrix_ofPauliParavector (p : PauliParavector) :
    weylMatrix (ofPauliParavector p) = p.pauliMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylMatrix, lightPlus, lightMinus, circularRight,
      circularLeft, imagUnit, ofPauliParavector,
      PauliParavector.pauliMatrix]

end ScalarPauliRecovery

end InfoGeometry.OperatorAlgebra.TwinLightconeWeylOperatorZorn

import Mathlib.Tactic
import InfoGeometry.Physics.SolovievCircularChiralProjectionBridge
import InfoGeometry.Algebra.ChiralGeneratorsToDerivationsBridge
import InfoGeometry.Optics.OperatorQGTSoldering
import InfoGeometry.Canonical.AmariSouriauThermodynamicGauge
import InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT
import InfoGeometry.Physics.MetriplecticDynamicsDrivers
import InfoGeometry.Clifford.Cl11HestenesKreinTripartiteCompletion

/-!
# Soloviev circular operator-information metriplectic bridge

This owner joins existing theorem-level structures along one common four-slot
coordinate spine.  It deliberately does not identify their carriers.

* The finite Soloviev QPNM Hamiltonian has the exact causal coordinates
  `(mean energy, coupling, zero circular phase, half energy difference)`.
* The same `Fin 4` natural-parameter vector can weight four native split-octonion
  `G₂` derivations selected from the established fourteen-generator family.
* On a finite Hilbert carrier the four natural parameters and four operator
  sufficient-statistic channels feed the genuine BKM interpolation; an
  independently typed Berry channel supplies the skew part of the operator QGT.
* A dually-flat log-partition packet supplies `η = ∇Ψ` and its Hessian readout.
* If that Hessian is identified explicitly with a para-Kähler metric, the
  para-QGT has exactly that Hessian as symmetric part and the established
  para-Berry form as skew part.
* Four conservative/dissipative trace drivers give the corresponding
  metriplectic channel decomposition.
* The causal doubled carrier already carries the represented `Cl(1,1)` atom:
  two square-plus-one generators with anticommuting product of square `-1`.

No theorem below asserts that the Soloviev Hamiltonian itself is a Gibbs state,
that a four-dimensional slice exhausts the fourteen-dimensional derivation
algebra, or that the BKM and trace-driver carriers are definitionally equal.
-/

noncomputable section

namespace InfoGeometry.Canonical.SolovievCircularInformationMetriplecticBridge

open scoped BigOperators
open Matrix
open InfoGeometry.Physics.SolovievCircular
open InfoGeometry.Physics.SolovievProjectedParameterBridge
open InfoGeometry.Algebra.CircularChiralDerivationsFourteen
open InfoGeometry.Algebra.ChiralGeneratorsToDerivationsBridge
open InfoGeometry.Optics.OperatorCausalSoldering
open InfoGeometry.Unified
open InfoGeometry.Canonical.AmariSouriauThermodynamicGauge
open InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT
open InfoGeometry.Physics
open SouriauOnsagerBKM

abbrev FourParameters := Fin 4 → ℝ
abbrev VZ := InfoGeometry.Algebra.ZornVectorMatrix ℝ
abbrev VDer := InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ)
abbrev VZEnd := Module.End ℝ VZ

/-! ## 1. Soloviev as an exact four-coordinate causal potential -/

/-- Causal coordinate order `(scalar, exchange, circular, chiral)` for the
real symmetric Soloviev two-sector matrix. -/
def solovievCausalParameters (eQ eP coupling : ℝ) : FourParameters :=
  ![(eQ + eP) / 2, coupling, 0, (eQ - eP) / 2]

@[simp] theorem solovievCausalParameters_scalar
    (eQ eP coupling : ℝ) :
    solovievCausalParameters eQ eP coupling 0 = (eQ + eP) / 2 := rfl

@[simp] theorem solovievCausalParameters_exchange
    (eQ eP coupling : ℝ) :
    solovievCausalParameters eQ eP coupling 1 = coupling := rfl

@[simp] theorem solovievCausalParameters_circular
    (eQ eP coupling : ℝ) :
    solovievCausalParameters eQ eP coupling 2 = 0 := rfl

@[simp] theorem solovievCausalParameters_chiral
    (eQ eP coupling : ℝ) :
    solovievCausalParameters eQ eP coupling 3 = (eQ - eP) / 2 := rfl

/-- Sum/difference reconstruction of the two physical diagonal energies. -/
theorem solovievCausalParameters_diagonal_reconstruction
    (eQ eP coupling : ℝ) :
    solovievCausalParameters eQ eP coupling 0 +
        solovievCausalParameters eQ eP coupling 3 = eQ ∧
      solovievCausalParameters eQ eP coupling 0 -
        solovievCausalParameters eQ eP coupling 3 = eP := by
  constructor <;> simp [solovievCausalParameters] <;> ring

/-- Exact Pauli/causal reconstruction of the real symmetric two-sector
Hamiltonian from the four coordinates. -/
theorem solovievCausalParameters_matrix_reconstruction
    (eQ eP coupling : ℝ) :
    !![solovievCausalParameters eQ eP coupling 0 +
          solovievCausalParameters eQ eP coupling 3,
       solovievCausalParameters eQ eP coupling 1;
       solovievCausalParameters eQ eP coupling 1,
       solovievCausalParameters eQ eP coupling 0 -
          solovievCausalParameters eQ eP coupling 3] =
      !![eQ, coupling; coupling, eP] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [solovievCausalParameters] <;> ring

/-- The diagonal circular Soloviev projection is exactly the causal four-slot
reconstruction with exchange coordinate `V₀` and vanishing circular phase. -/
theorem circularSolovievHamiltonian_eq_causal_reconstruction
    {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : InfoGeometry.Exceptional.Freudenthal.CubicJordanDatum J)
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (h_ortho : ∀ i j : Fin 3,
      D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (eQ eP V0 : ℝ) (i : Fin 3) :
    circularSolovievHamiltonian D rootMapPlus rootMapMinus eQ eP V0 i i =
      !![solovievCausalParameters eQ eP V0 0 +
            solovievCausalParameters eQ eP V0 3,
         solovievCausalParameters eQ eP V0 1;
         solovievCausalParameters eQ eP V0 1,
         solovievCausalParameters eQ eP V0 0 -
            solovievCausalParameters eQ eP V0 3] := by
  unfold circularSolovievHamiltonian
  rw [circular_coupling_diagonal D rootMapPlus rootMapMinus h_ortho V0 i]
  exact (solovievCausalParameters_matrix_reconstruction eQ eP V0).symm

/-! ## 2. Four natural parameters as a slice of the native G₂ derivation algebra -/

/-- Forget only the derivation multiplication law and retain its genuine linear
operator action on the split-octonion carrier. -/
def derivationLinearOperator (D : VDer) : VZEnd where
  toFun := D.toFun
  map_add' := D.map_add'
  map_smul' := D.map_smul'

/-- A four-slot derivation-valued potential.  `slot` chooses four of the native
fourteen gauge derivations; `θ` supplies their natural-parameter coefficients. -/
def gaugeDerivationFourPotential
    (θ : FourParameters) (slot : Fin 4 → GaugeGenerator) :
    Fin 4 → VZEnd :=
  fun i => θ i • derivationLinearOperator (derivationFromGaugeGenerator (slot i))

@[simp] theorem gaugeDerivationFourPotential_apply
    (θ : FourParameters) (slot : Fin 4 → GaugeGenerator)
    (i : Fin 4) (z : VZ) :
    gaugeDerivationFourPotential θ slot i z =
      θ i • derivationFromGaugeGenerator (slot i) z := by
  rfl

/-- The four-slot potential is a selected slice of a genuinely
fourteen-dimensional native derivation carrier. -/
theorem gaugeDerivationFourPotential_ambient_dimension :
    Module.finrank ℝ
      InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations = 14 :=
  g2_derivation_dim

/-! ## 3. Dually-flat natural parameters and the operator QGT -/

/-- A theorem-safe four-parameter information/operator packet.  The same
natural parameter vector indexes the dually-flat potential and the four BKM
operator-statistic channels. -/
structure QuantizedFourPotential (n : ℕ) where
  info : DuallyFlatLogPartition FourParameters FourParameters
  parameter : FourParameters
  density : FaithfulDensityOperator n
  sufficientStatistic : Fin 4 → FiniteOperatorAlgebra n
  berryChannel : OperatorFourVector (FiniteHilbertSpace n)

namespace QuantizedFourPotential

variable {n : ℕ}

/-- Expectation/dual affine coordinate `η = ∇Ψ`. -/
def dualParameter (P : QuantizedFourPotential n) : FourParameters :=
  P.info.dualCoord P.parameter

/-- Hessian/Fisher readout at the selected natural parameter. -/
def fisherMetric
    (P : QuantizedFourPotential n)
    (u v : FourParameters) : ℝ :=
  P.info.fisherMetric P.parameter u v

/-- Genuine operator-valued QGT: BKM modular interpolation in the symmetric
channel and the supplied Berry operator in the skew channel. -/
def qgt (P : QuantizedFourPotential n) :
    QGTFourVector (FiniteHilbertSpace n) :=
  QGTFourVector.ofBKMInterpolation
    P.density P.parameter P.sufficientStatistic P.berryChannel

/-- Faithful doubled-carrier soldering of the quantized four-potential. -/
def solderedQGT (P : QuantizedFourPotential n) :
    Module.End ℂ (Fin 2 → FiniteHilbertSpace n) :=
  QGTSoldering P.qgt

@[simp] theorem dualParameter_eq_grad
    (P : QuantizedFourPotential n) :
    P.dualParameter = P.info.gradΨ P.parameter :=
  rfl

@[simp] theorem fisherMetric_eq_hessian
    (P : QuantizedFourPotential n) (u v : FourParameters) :
    P.fisherMetric u v = P.info.hessianMetric P.parameter u v :=
  rfl

@[simp] theorem qgt_totalOperator_apply
    (P : QuantizedFourPotential n) (i : Fin 4) :
    P.qgt.totalOperator i =
      (P.density.modularInterpolation
        (P.parameter i) (P.sufficientStatistic i)).toLinearMap +
        Complex.I • P.berryChannel i :=
  rfl

/-- The same natural parameters can weight four native split-octonion
derivations without identifying the two representation carriers. -/
def gaugePotential
    (P : QuantizedFourPotential n)
    (slot : Fin 4 → GaugeGenerator) : Fin 4 → VZEnd :=
  gaugeDerivationFourPotential P.parameter slot

@[simp] theorem gaugePotential_apply
    (P : QuantizedFourPotential n)
    (slot : Fin 4 → GaugeGenerator)
    (i : Fin 4) (z : VZ) :
    P.gaugePotential slot i z =
      P.parameter i • derivationFromGaugeGenerator (slot i) z := by
  rfl

/-- Shared-coordinate packet: primal parameter, dual parameter, BKM/statistic
operator and derivation operator all use the same four-slot index. -/
theorem shared_four_coordinate_packet
    (P : QuantizedFourPotential n)
    (slot : Fin 4 → GaugeGenerator)
    (i : Fin 4) (z : VZ) :
    P.dualParameter = P.info.gradΨ P.parameter ∧
    P.qgt.totalOperator i =
      (P.density.modularInterpolation
        (P.parameter i) (P.sufficientStatistic i)).toLinearMap +
        Complex.I • P.berryChannel i ∧
    P.gaugePotential slot i z =
      P.parameter i • derivationFromGaugeGenerator (slot i) z := by
  exact ⟨rfl, rfl, rfl⟩

end QuantizedFourPotential

/-! ## 4. Soloviev central operator lift into the same causal soldering -/

section SolovievOperatorLift

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- Central operator lift of the real Soloviev causal coordinates. -/
def solovievOperatorFourVector
    (eQ eP coupling : ℝ) : OperatorFourVector W :=
  fun i => centralOperator (W := W)
    ((solovievCausalParameters eQ eP coupling i : ℝ) : ℂ)

/-- The operator soldering of the lifted Soloviev coordinates has exactly the
symmetric QPNM block form, with every scalar promoted to a central operator. -/
theorem solovievOperatorSoldering_matrix
    (eQ eP coupling : ℝ) :
    operatorSoldering (solovievOperatorFourVector (W := W) eQ eP coupling) =
      !![centralOperator (W := W) (eQ : ℂ),
         centralOperator (W := W) (coupling : ℂ);
         centralOperator (W := W) (coupling : ℂ),
         centralOperator (W := W) (eP : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply LinearMap.ext <;> intro w <;>
    simp [operatorSoldering_apply, solovievOperatorFourVector,
      solovievCausalParameters, centralOperator] <;>
    module

end SolovievOperatorLift

/-! ## 5. Para-Kähler interpretation of the dually-flat Hessian -/

/-- Under the explicit identification of the para-Kähler metric with the
log-partition Hessian, the para-QGT has exactly the information Hessian as its
symmetric part and the established skew para-Berry channel as its split part. -/
theorem paraQGT_of_information_hessian
    {n : ℕ}
    (P : QuantizedFourPotential n)
    (D : ParaKahlerDatum ℝ FourParameters)
    (hmetric : ∀ u v : FourParameters,
      D.metric u v = P.info.hessianMetric P.parameter u v)
    (u v : FourParameters) :
    (paraQGT D u v).re = P.info.hessianMetric P.parameter u v ∧
    (paraQGT D v u).ep = -(paraQGT D u v).ep := by
  constructor
  · rw [paraQGT_re, hmetric]
  · exact (paraQGT_conjugation D u v).2

/-! ## 6. Four-channel metriplectic response -/

section Metriplectic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Four copies of the repository-owned commutator-plus-Jordan metriplectic
algebraic driver. -/
def metriplecticFourGenerator
    (H S X : Fin 4 → TraceOperatorSpace ι) :
    Fin 4 → TraceOperatorSpace ι :=
  fun i => metriplecticGenerator (H i) (S i) (X i)

@[simp] theorem metriplecticFourGenerator_apply
    (H S X : Fin 4 → TraceOperatorSpace ι) (i : Fin 4) :
    metriplecticFourGenerator H S X i =
      conservativeDriver (H i) (X i) + dissipativeDriver (S i) (X i) :=
  rfl

/-- Each slot carries the defining metriplectic symmetry split: the
commutator driver is trace-skew and the Jordan driver is trace-symmetric. -/
theorem metriplecticFour_symmetry_packet
    (H S X Y : Fin 4 → TraceOperatorSpace ι) (i : Fin 4) :
    tracePairingNative (conservativeDriver (H i) (X i)) (Y i) =
        -tracePairingNative (X i) (conservativeDriver (H i) (Y i)) ∧
    tracePairingNative (dissipativeDriver (S i) (X i)) (Y i) =
        tracePairingNative (X i) (dissipativeDriver (S i) (Y i)) := by
  exact ⟨conservative_driver_trace_skew (H i) (X i) (Y i),
    dissipative_driver_trace_symmetric (S i) (X i) (Y i)⟩

end Metriplectic

/-! ## 7. The represented Cl(1,1) atom on the QGT doubled carrier -/

/-- The same doubled carrier used by causal/QGT soldering carries a native
`Cl(1,1)`-type atom: two anticommuting square-plus-one generators and their
square-minus-one product. -/
theorem causal_cl11_atom
    {W : Type*} [AddCommGroup W] [Module ℂ W] :
    carrierGamma (W := W) * carrierGamma (W := W) = 1 ∧
    carrierJ (W := W) * carrierJ (W := W) = 1 ∧
    carrierGammaJ (W := W) * carrierGammaJ (W := W) = -1 ∧
    carrierJ (W := W) * carrierGamma (W := W) =
      -(carrierGamma (W := W) * carrierJ (W := W)) := by
  exact ⟨carrierGamma_sq, carrierJ_sq, carrierGammaJ_sq,
    carrierJ_mul_carrierGamma⟩

/-- The independent tripartite finite atom also records elliptic, hyperbolic
and parabolic generators with squares `-1,+1,0`. -/
theorem tripartite_hypercomplex_atom :
    InfoGeometry.Algebra.HypercomplexTriad.I *
        InfoGeometry.Algebra.HypercomplexTriad.I =
      -(1 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) ∧
    InfoGeometry.Algebra.HypercomplexTriad.E *
        InfoGeometry.Algebra.HypercomplexTriad.E =
      (1 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) ∧
    InfoGeometry.Algebra.HypercomplexTriad.N *
        InfoGeometry.Algebra.HypercomplexTriad.N =
      (0 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) :=
  InfoGeometry.Clifford.Cl11HestenesKreinTripartiteCompletion.tripartite_local_flow_atom

end InfoGeometry.Canonical.SolovievCircularInformationMetriplecticBridge

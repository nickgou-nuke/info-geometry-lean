import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.PrimeGrandCanonicalMassieuBridge
import InfoGeometry.Arithmetic.PrimonFinite
import InfoGeometry.Arithmetic.ZetaSouriauComplexLift
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.SocketTarget
import InfoGeometry.Potential.Thermo
import InfoGeometry.Thermodynamics.SouriauTemperature

/-!
# InfoGeometry.Arithmetic.PrimeGrandCanonicalSouriauBregman

Finite complex-Souriau grand-canonical thermodynamics for the prime register.

This file keeps the theorem-carrying part finite and algebraic:

* complex Souriau temperature weights on a finite prime register;
* finite fermionic / bosonic / signed-Moebius partition readouts;
* Massieu-Planck and grand-potential scalar readouts;
* re-export of the existing finite Legendre/Bregman thermodynamic bridge;
* abstract sockets for the analytic zeta identifications and symmetry group.

No infinite Euler product, analytic continuation, Lee-Yang theorem,
Hilbert--Polya operator, or RH claim is made here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeGrandCanonicalSouriauBregman

open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.LogPotential
open InfoGeometry.LogPotential.LegendreModel
open InfoGeometry.Thermodynamics
open InfoGeometry.Arithmetic.PrimonFinite

/-- Bridge alias for the existing finite prime grand-canonical Massieu layer. -/
abbrev MassieuBridge :=
  InfoGeometry.Arithmetic.PrimeGrandCanonicalMassieuBridge.Bridge

/-! ## 1. Complex Souriau grand-canonical weights -/

/--
Complex grand-canonical mode weight.

The complex Souriau temperature contributes through the exponential kernel
`exp(-β(E - μ))`.
-/
def complexGrandModeWeight
    (β : SouriauTemperature) (energy mu : ℕ → ℝ) (p : ℕ) : ℂ :=
  Complex.exp (-(β.s * ((energy p - mu p : ℝ) : ℂ)))

lemma complexGrandModeWeight_ne_zero
    (β : InfoGeometry.Thermodynamics.SouriauTemperature)
    (energy mu : ℕ → ℝ) (p : ℕ) :
    complexGrandModeWeight β energy mu p ≠ 0 := by
  unfold complexGrandModeWeight
  exact Complex.exp_ne_zero _

lemma complexGrandStateWeight_ne_zero
    (β : InfoGeometry.Thermodynamics.SouriauTemperature)
    (energy mu : ℕ → ℝ) (S : InfoGeometry.Arithmetic.PrimonFinite.FState ℕ) :
    InfoGeometry.Arithmetic.PrimonFinite.weight
      (complexGrandModeWeight β energy mu) S ≠ 0 := by
  exact InfoGeometry.Arithmetic.PrimonFinite.weight_ne_zero
    (q := complexGrandModeWeight β energy mu) S
    (fun p _hp => complexGrandModeWeight_ne_zero β energy mu p)

/-- Finite fermionic grand partition over a finite prime register. -/
def complexFermionGrandPartition
    (P : PrimeRegister) (β : SouriauTemperature)
    (energy mu : ℕ → ℝ) : ℂ :=
  ZF P.primes (complexGrandModeWeight β energy mu)

/-- Finite signed fermionic / Möbius grand supertrace. -/
def complexFermionGrandSupertrace
    (P : PrimeRegister) (β : SouriauTemperature)
    (energy mu : ℕ → ℝ) : ℂ :=
  STrF P.primes (complexGrandModeWeight β energy mu)

/-- Finite bosonic grand partition. -/
def complexBosonGrandPartition
    (P : PrimeRegister) (β : SouriauTemperature)
    (energy mu : ℕ → ℝ) : ℂ :=
  ZB P.primes (complexGrandModeWeight β energy mu)

@[bridge_target_tag, rep_depth thermo]
theorem complexFermionGrandPartition_eq_prod
  (P : PrimeRegister) (β : SouriauTemperature)
  (energy mu : ℕ → ℝ) :
    complexFermionGrandPartition P β energy mu =
      ∏ p ∈ P.primes, (1 + complexGrandModeWeight β energy mu p) := by
  simpa [complexFermionGrandPartition] using
    (ZF_eq_prod P.primes (complexGrandModeWeight β energy mu))

@[bridge_target_tag, rep_depth thermo]
theorem complexFermionGrandSupertrace_eq_prod
  (P : PrimeRegister) (β : SouriauTemperature)
  (energy mu : ℕ → ℝ) :
    complexFermionGrandSupertrace P β energy mu =
      ∏ p ∈ P.primes, (1 - complexGrandModeWeight β energy mu p) := by
  simpa [complexFermionGrandSupertrace] using
    (STrF_eq_prod P.primes (complexGrandModeWeight β energy mu))

@[bridge_target_tag, rep_depth thermo]
theorem complexBosonGrandPartition_eq_prod_inv
    (P : PrimeRegister) (β : SouriauTemperature)
    (energy mu : ℕ → ℝ) :
    complexBosonGrandPartition P β energy mu =
      ∏ p ∈ P.primes, (1 - complexGrandModeWeight β energy mu p)⁻¹ := by
  simp [complexBosonGrandPartition, ZB]

lemma complexBosonGrandPartition_ne_zero
    (P : PrimeRegister) (β : SouriauTemperature) (energy mu : ℕ → ℝ)
    (h : ∀ p ∈ P.primes, (1 - complexGrandModeWeight β energy mu p) ≠ 0) :
    complexBosonGrandPartition P β energy mu ≠ 0 := by
  exact ZB_ne_zero (modes := P.primes) (q := complexGrandModeWeight β energy mu) h

@[bridge_target_tag, rep_depth thermo]
theorem complexBoson_mul_signedFermionGrandSupertrace_eq_one
    (P : PrimeRegister) (β : SouriauTemperature)
    (energy mu : ℕ → ℝ)
    (h : ∀ p ∈ P.primes, 1 - complexGrandModeWeight β energy mu p ≠ 0) :
    complexBosonGrandPartition P β energy mu *
        complexFermionGrandSupertrace P β energy mu = 1 := by
  rw [complexBosonGrandPartition_eq_prod_inv,
      complexFermionGrandSupertrace_eq_prod]
  rw [← Finset.prod_mul_distrib]
  exact local_susy_cancellation P.primes
    (complexGrandModeWeight β energy mu) h

/-! ## 2. Massieu / grand potential readouts -/

/-- Massieu-Planck potential `Φ = log Z`. -/
def massieuPlanck (Z : ℂ) : ℂ :=
  Complex.log Z

/-- Grand potential `Ω = -β⁻¹ Φ`. -/
def grandPotential (β Z : ℂ) : ℂ :=
  -β⁻¹ * massieuPlanck Z

@[simp, bridge_target_tag, rep_depth thermo]
theorem grandPotential_eq_neg_inv_beta_mul_massieu
    (β Z : ℂ) :
    grandPotential β Z = -β⁻¹ * massieuPlanck Z := rfl

/--
The generic Massieu/Legendre calibration packet.

This is the theorem-safe shell for the free-energy and Bregman layer.
-/
@[socket_debt_tag, rep_depth transport]
structure MassieuPlanckLegendreCalibration (Param : Type*) where
  beta : Param → ℂ
  chemicalPotential : Param → ℂ
  entropy : Param → ℂ
  energy : Param → ℂ
  particleNumber : Param → ℂ
  massieu : Param → ℂ
  grandPotential : Param → ℂ
  massieu_legendre_law :
    ∀ θ, massieu θ =
      entropy θ - beta θ * (energy θ - chemicalPotential θ * particleNumber θ)
  grandPotential_law :
    ∀ θ, grandPotential θ = - (beta θ)⁻¹ * massieu θ

/-! ## 3. Real thermodynamic bridge and Bregman readback -/

/--
Complex-Souriau wrapper around the existing finite prime grand-canonical
Massieu bridge.

The finite thermodynamic identities are re-exported from the existing real
Legendre/Bregman layer.  The analytic zeta identifications remain explicit
socket data.
-/
@[rep_depth transport]
structure PrimeGrandCanonicalSouriauBregmanPacket where
  massieuBridge : MassieuBridge
  zeta : ℂ → ℂ
  dzeta : ℂ → ℂ

namespace PrimeGrandCanonicalSouriauBregmanPacket

variable (B : PrimeGrandCanonicalSouriauBregmanPacket)

/-- Zeta free-energy potential, derived from the native complex thermodynamic owner. -/
def zetaPotential : ℂ → ℂ :=
  InfoGeometry.Arithmetic.ZetaSouriauComplexLift.freeEnergyOf B.zeta

/-- Zeta logarithmic-derivative force, derived from `zeta` and `dzeta`. -/
def zetaMomentMap : ℂ → ℂ :=
  InfoGeometry.Arithmetic.ZetaSouriauComplexLift.logDerivativeForce
    B.zeta B.dzeta

/-- The derived zeta potential is pointwise `-log ζ`. -/
theorem zetaPotential_is_negLogZeta (s : ℂ) :
    B.zetaPotential s = -Complex.log (B.zeta s) := by
  rfl

/-- The derived zeta moment map is pointwise `-ζ'/ζ`. -/
theorem zetaMomentMap_is_neg_zetaDeriv_over_zeta (s : ℂ) :
    B.zetaMomentMap s = -(B.dzeta s) / B.zeta s := by
  rfl

end PrimeGrandCanonicalSouriauBregmanPacket

/-! ## 4. Zeta-plane functional-equation symmetry -/

/--
Finite symmetry labels for the zeta-plane duality package.

This records the reflection/conjugation generators without claiming an analytic
continuation theorem.
-/
inductive ZetaPlaneSymmetry where
  | id
  | functionalEquation
  | conjugation
  | functionalConjugation

/-- Action of the finite zeta-plane symmetry labels. -/
def zetaPlaneAct : ZetaPlaneSymmetry → ℂ → ℂ
  | ZetaPlaneSymmetry.id, s => s
  | ZetaPlaneSymmetry.functionalEquation, s => 1 - s
  | ZetaPlaneSymmetry.conjugation, s => star s
  | ZetaPlaneSymmetry.functionalConjugation, s => 1 - star s

@[simp] theorem zetaPlaneAct_involutive (g : ZetaPlaneSymmetry) (s : ℂ) :
    zetaPlaneAct g (zetaPlaneAct g s) = s := by
  cases g <;> simp [zetaPlaneAct]

/-- Critical line preserved by the finite symmetry package. -/
theorem zetaPlaneAct_preserves_criticalLine
    (g : ZetaPlaneSymmetry) {s : ℂ}
    (hs : s.re = (1 : ℝ) / 2) :
    (zetaPlaneAct g s).re = (1 : ℝ) / 2 := by
  cases g <;> simp [zetaPlaneAct, hs] <;> norm_num

/-! ## 5. Souriau Lie-group thermodynamics socket -/

/--
Abstract Souriau thermodynamics of a symmetry group acting on the zeta plane.

The group action and invariance are recorded as theorem-safe interface data.
-/
@[socket_debt_tag, rep_depth transport]
structure SouriauZetaLieGroupThermodynamics
    (G : Type*) [Group G] where
  actOnBeta : G → ℂ → ℂ
  one_act : ∀ β, actOnBeta 1 β = β
  mul_act : ∀ g h β, actOnBeta (g * h) β = actOnBeta g (actOnBeta h β)
  partition : ℂ → ℂ
  massieu : ℂ → ℂ
  massieu_eq_log_partition : ∀ β, massieu β = Complex.log (partition β)
  isThermalSymmetry : G → Prop
  partition_invariant :
    ∀ g β, isThermalSymmetry g → partition (actOnBeta g β) = partition β

/-! ## 6. Prime specialization -/

/-- Prime energy specialization `E_p = log p`. -/
def primeEnergy (p : ℕ) : ℝ :=
  Real.log p

/-- Zero chemical potential specialization. -/
def zeroChemicalPotential (_p : ℕ) : ℝ :=
  0

/-- Finite prime bosonic grand partition. -/
def finitePrimeBosonGrandPartition
    (P : PrimeRegister) (β : SouriauTemperature) : ℂ :=
  complexBosonGrandPartition P β primeEnergy zeroChemicalPotential

/-- Finite prime signed grand supertrace. -/
def finitePrimeSignedGrandSupertrace
    (P : PrimeRegister) (β : SouriauTemperature) : ℂ :=
  complexFermionGrandSupertrace P β primeEnergy zeroChemicalPotential

/-- Finite prime Massieu potential. -/
def finitePrimeMassieu (P : PrimeRegister) (β : SouriauTemperature) : ℂ :=
  massieuPlanck (finitePrimeBosonGrandPartition P β)

/-- Finite prime grand potential. -/
def finitePrimeGrandPotential
    (P : PrimeRegister) (β : SouriauTemperature) : ℂ :=
  grandPotential β.s (finitePrimeBosonGrandPartition P β)

@[bridge_target_tag, rep_depth thermo]
theorem finitePrimeBosonGrandPartition_eq_prod
    (P : PrimeRegister) (β : SouriauTemperature) :
    finitePrimeBosonGrandPartition P β =
      ∏ p ∈ P.primes, (1 - complexGrandModeWeight β primeEnergy zeroChemicalPotential p)⁻¹ := by
  rfl

lemma finitePrimeBosonGrandPartition_ne_zero
    (P : PrimeRegister) (β : SouriauTemperature)
    (h : ∀ p ∈ P.primes,
      (1 - complexGrandModeWeight β primeEnergy zeroChemicalPotential p) ≠ 0) :
    finitePrimeBosonGrandPartition P β ≠ 0 := by
  exact complexBosonGrandPartition_ne_zero
    (P := P) (β := β) (energy := primeEnergy) (mu := zeroChemicalPotential) h

@[bridge_target_tag, rep_depth thermo]
theorem finitePrimeSignedGrandSupertrace_eq_prod
    (P : PrimeRegister) (β : SouriauTemperature) :
    finitePrimeSignedGrandSupertrace P β =
      ∏ p ∈ P.primes, (1 - complexGrandModeWeight β primeEnergy zeroChemicalPotential p) := by
  simpa [finitePrimeSignedGrandSupertrace] using
    (complexFermionGrandSupertrace_eq_prod P β primeEnergy zeroChemicalPotential)

@[bridge_target_tag, rep_depth thermo]
theorem finitePrimeGrandPotential_eq
    (P : PrimeRegister) (β : SouriauTemperature) :
    finitePrimeGrandPotential P β =
      -β.s⁻¹ * massieuPlanck (finitePrimeBosonGrandPartition P β) := by
  rfl

/-! ## 7. Owner theorem -/

/-- The finite Souriau/Bregman owner target is proved. -/
theorem primeGrandCanonicalSouriauBregmanOwnerTarget :
    ∀ (B : PrimeGrandCanonicalSouriauBregmanPacket),
      let M : MassieuBridge :=
        B.massieuBridge
      M.beta = M.temperature.s.re ∧
        (∀ β θ η : ℝ, 0 ≤ β → 0 ≤ M.temperatureRegularizedHamiltonian β θ η) ∧
        (∀ β θ : ℝ, M.temperatureRegularizedHamiltonian β θ
          (M.massieuModel.dualCoord θ) = 0) ∧
        (∀ θ η : ℝ, 0 ≤ M.massieuModel.fenchelGap θ η) ∧
        (∀ θ : ℝ, M.massieuModel.fenchelGap θ
          (M.massieuModel.dualCoord θ) = 0) := by
  intro B
  dsimp
  let M : MassieuBridge := B.massieuBridge
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [M] using M.beta_eq_realPart_of_bridge
  · intro β θ η hβ
    exact M.temperatureRegularizedHamiltonian_nonneg β θ η hβ
  · intro β θ
    exact M.temperatureRegularizedHamiltonian_eq_zero_at_contact β θ
  · intro θ η
    exact M.fenchelGap_nonneg θ η
  · intro θ
    exact M.fenchelGap_eq_zero_at_contact θ

end InfoGeometry.Arithmetic.PrimeGrandCanonicalSouriauBregman

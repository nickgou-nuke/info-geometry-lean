import InfoGeometry.Algebra.CuntzSupergradedSUSY
import InfoGeometry.Physics.SouriauMassieuPlanckFunctional
import InfoGeometry.Twistor.FiveGradedIncidence

/-!
# Chiral supercharge / Souriau four-vector bridge

This file keeps the super-Poincare and Souriau identifications explicit:
chiral supercharges define an algebra element by anticommutator, while the
finite Souriau Gibbs layer sees the scalar Minkowski contraction `β·p`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ChiralSuperPoincareSouriauBridge

open InfoGeometry.Algebra.SupergradedSUSY
open InfoGeometry.Physics.SouriauMassieuPlanckFunctional

abbrev SpacetimeIndex := Fin 4

abbrev FourVector := SpacetimeIndex → ℝ

/-- Minkowski pairing with signature `(+, -, -, -)`. -/
def minkowskiPair (x y : FourVector) : ℝ :=
  x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3

/-- Relativistic Souriau scalar readout from inverse-temperature and momentum four-vectors. -/
def betaEnergyPair (β p : FourVector) : ℝ :=
  minkowskiPair β p

/-- The quadratic energy-momentum Casimir in the chosen Minkowski convention. -/
def energyMomentumCasimir (p : FourVector) : ℝ :=
  minkowskiPair p p

/-- Diagonal Minkowski metric coefficients, encoded as integers for algebra-valued brackets. -/
def minkowskiMetricCoeff (μ ν : SpacetimeIndex) : ℤ :=
  if μ = ν then
    if μ = 0 then 1 else -1
  else
    0

theorem minkowskiMetricCoeff_time_time :
    minkowskiMetricCoeff 0 0 = 1 := by
  simp [minkowskiMetricCoeff]

theorem minkowskiMetricCoeff_space_self (μ : SpacetimeIndex) (hμ : μ ≠ 0) :
    minkowskiMetricCoeff μ μ = -1 := by
  simp [minkowskiMetricCoeff, hμ]

theorem minkowskiMetricCoeff_off_diag (μ ν : SpacetimeIndex) (hμν : μ ≠ ν) :
    minkowskiMetricCoeff μ ν = 0 := by
  simp [minkowskiMetricCoeff, hμν]

/-- Algebra commutator used by the Poincare socket. -/
def poincareCommutator {A : Type*} [Ring A] (x y : A) : A :=
  x * y - y * x

/-- Project a finite family of four-momenta to scalar Souriau energies via `β·p`. -/
def betaProjectedEnergy {ι : Type*} (β : FourVector) (p : ι → FourVector) : ι → ℝ :=
  fun i => betaEnergyPair β (p i)

theorem betaProjectedEnergy_apply {ι : Type*} (β : FourVector) (p : ι → FourVector)
    (i : ι) :
    betaProjectedEnergy β p i = minkowskiPair β (p i) :=
  rfl

/-- Finite relativistic Souriau partition function `Σ exp(-β·pᵢ)`. -/
def souriauPartitionFourVector {ι : Type*} [Fintype ι] (β : FourVector)
    (p : ι → FourVector) : ℝ :=
  souriauPartition 1 (betaProjectedEnergy β p)

/-- Finite relativistic Gibbs weights induced by the scalar contraction `β·pᵢ`. -/
def souriauGibbsWeightFourVector {ι : Type*} [Fintype ι] (β : FourVector)
    (p : ι → FourVector) : ι → ℝ :=
  gibbsWeight 1 (betaProjectedEnergy β p)

/-- The finite Souriau entropy identity after four-vector beta projection. -/
theorem souriauEntropy_fourVector_eq_massieu_add_meanBetaEnergy {ι : Type*} [Fintype ι]
    [Nonempty ι] (β : FourVector) (p : ι → FourVector) :
    boltzmannEntropy (souriauGibbsWeightFourVector β p) =
      massieuPlanckPotential 1 (betaProjectedEnergy β p) +
        1 * meanEnergy 1 (betaProjectedEnergy β p) := by
  simpa [souriauGibbsWeightFourVector] using
    (boltzmannEntropy_gibbsWeight_eq_massieu_add_beta_meanEnergy
        (beta := (1 : ℝ)) (energy := betaProjectedEnergy β p))

/--
Minimal Poincare Lie-algebra socket.

The Lorentz and translation generators are algebra elements satisfying the
standard Poincare commutator relations with metric coefficients explicit.
-/
structure PoincareAlgebraSocket (A : Type*) [Ring A] where
  lorentz : SpacetimeIndex → SpacetimeIndex → A
  momentum : SpacetimeIndex → A
  lorentz_skew : ∀ μ ν, lorentz μ ν = -lorentz ν μ
  momentum_commutes : ∀ μ ν, momentum μ * momentum ν = momentum ν * momentum μ
  lorentz_momentum_bracket :
    ∀ ρ σ μ,
      poincareCommutator (lorentz ρ σ) (momentum μ) =
        minkowskiMetricCoeff σ μ • momentum ρ -
          minkowskiMetricCoeff ρ μ • momentum σ
  lorentz_lorentz_bracket :
    ∀ ρ σ μ ν,
      poincareCommutator (lorentz ρ σ) (lorentz μ ν) =
        minkowskiMetricCoeff σ μ • lorentz ρ ν -
          minkowskiMetricCoeff ρ μ • lorentz σ ν -
          minkowskiMetricCoeff σ ν • lorentz ρ μ +
          minkowskiMetricCoeff ρ ν • lorentz σ μ

namespace PoincareAlgebraSocket

/-- Translation components commute in the Poincare socket. -/
theorem momentum_commutator_zero {A : Type*} [Ring A] (P : PoincareAlgebraSocket A)
    (μ ν : SpacetimeIndex) :
    poincareCommutator (P.momentum μ) (P.momentum ν) = 0 := by
  unfold poincareCommutator
  rw [P.momentum_commutes μ ν]
  simp

theorem lorentz_momentum_commutator {A : Type*} [Ring A] (P : PoincareAlgebraSocket A)
    (ρ σ μ : SpacetimeIndex) :
    poincareCommutator (P.lorentz ρ σ) (P.momentum μ) =
      minkowskiMetricCoeff σ μ • P.momentum ρ -
        minkowskiMetricCoeff ρ μ • P.momentum σ :=
  P.lorentz_momentum_bracket ρ σ μ

theorem lorentz_lorentz_commutator {A : Type*} [Ring A] (P : PoincareAlgebraSocket A)
    (ρ σ μ ν : SpacetimeIndex) :
    poincareCommutator (P.lorentz ρ σ) (P.lorentz μ ν) =
      minkowskiMetricCoeff σ μ • P.lorentz ρ ν -
        minkowskiMetricCoeff ρ μ • P.lorentz σ ν -
        minkowskiMetricCoeff σ ν • P.lorentz ρ μ +
        minkowskiMetricCoeff ρ ν • P.lorentz σ μ :=
  P.lorentz_lorentz_bracket ρ σ μ ν

end PoincareAlgebraSocket

/-- Twistor/null-incidence data needed before the chiral algebra can be read geometrically. -/
structure TwistorChiralNullSocket where
  TwistorSpace : Type*
  nullCone : TwistorSpace → Prop
  incidence : TwistorSpace → TwistorSpace → Prop
  chiralPlus : TwistorSpace → Prop
  chiralMinus : TwistorSpace → Prop
  plus_incidence_null :
    ∀ Z W, chiralPlus Z → incidence Z W → nullCone W
  minus_incidence_null :
    ∀ Z W, chiralMinus Z → incidence Z W → nullCone W

namespace TwistorChiralNullSocket

theorem plus_incidence_forces_null (T : TwistorChiralNullSocket)
    {Z W : T.TwistorSpace} (hZ : T.chiralPlus Z) (hZW : T.incidence Z W) :
    T.nullCone W :=
  T.plus_incidence_null Z W hZ hZW

theorem minus_incidence_forces_null (T : TwistorChiralNullSocket)
    {Z W : T.TwistorSpace} (hZ : T.chiralMinus Z) (hZW : T.incidence Z W) :
    T.nullCone W :=
  T.minus_incidence_null Z W hZ hZW

end TwistorChiralNullSocket

/--
Chiral supercharge packet with explicit central charge, parity, beta four-vector,
energy-momentum four-vector, and twistor incidence socket.
-/
structure ChiralSuperPoincareSouriauPacket (A : Type*) [Ring A] where
  plusCharge : A
  minusCharge : A
  parityCharge : A
  centralCharge : A
  momentumOp : A
  beta4 : FourVector
  energyMomentum4 : FourVector
  twistorSocket : TwistorChiralNullSocket
  plus_nilpotent : plusCharge * plusCharge = 0
  minus_nilpotent : minusCharge * minusCharge = 0
  momentum_eq_chiral_anticommutator :
    momentumOp = algebraicAnticommutator plusCharge minusCharge
  centralCharge_central : IsCentralElement centralCharge
  parity_anticommutes_plus :
    algebraicAnticommutator parityCharge plusCharge = 0
  parity_anticommutes_minus :
    algebraicAnticommutator parityCharge minusCharge = 0

namespace ChiralSuperPoincareSouriauPacket

/-- Chiral Dirac-type odd operator `Q₊ + Q₋`. -/
def chiralDirac {A : Type*} [Ring A] (P : ChiralSuperPoincareSouriauPacket A) : A :=
  P.plusCharge + P.minusCharge

/-- Souriau inverse-temperature energy readout for the packet. -/
def betaEnergy {A : Type*} [Ring A] (P : ChiralSuperPoincareSouriauPacket A) : ℝ :=
  betaEnergyPair P.beta4 P.energyMomentum4

/-- Quadratic mass-shell Casimir readout for the packet. -/
def casimir {A : Type*} [Ring A] (P : ChiralSuperPoincareSouriauPacket A) : ℝ :=
  energyMomentumCasimir P.energyMomentum4

/-- If the chiral supercharges are nilpotent, `(Q₊ + Q₋)²` is their anticommutator momentum. -/
theorem chiral_dirac_square_eq_momentum {A : Type*} [Ring A]
    (P : ChiralSuperPoincareSouriauPacket A) :
    chiralDirac P * chiralDirac P = P.momentumOp := by
  calc
    chiralDirac P * chiralDirac P
        = P.plusCharge * P.plusCharge +
            (P.plusCharge * P.minusCharge + P.minusCharge * P.plusCharge) +
            P.minusCharge * P.minusCharge := by
          simp [chiralDirac]
          noncomm_ring
    _ = algebraicAnticommutator P.plusCharge P.minusCharge := by
          simp [P.plus_nilpotent, P.minus_nilpotent, algebraicAnticommutator]
    _ = P.momentumOp := P.momentum_eq_chiral_anticommutator.symm

/-- The central charge commutes with every algebra element by the packet law. -/
theorem centralCharge_commutes {A : Type*} [Ring A]
    (P : ChiralSuperPoincareSouriauPacket A) (a : A) :
    P.centralCharge * a = a * P.centralCharge :=
  P.centralCharge_central a

theorem betaEnergy_eq_minkowski_pair {A : Type*} [Ring A]
    (P : ChiralSuperPoincareSouriauPacket A) :
    betaEnergy P = minkowskiPair P.beta4 P.energyMomentum4 :=
  rfl

theorem casimir_eq_minkowski_square {A : Type*} [Ring A]
    (P : ChiralSuperPoincareSouriauPacket A) :
    casimir P = minkowskiPair P.energyMomentum4 P.energyMomentum4 :=
  rfl

end ChiralSuperPoincareSouriauPacket

end InfoGeometry.Canonical.ChiralSuperPoincareSouriauBridge

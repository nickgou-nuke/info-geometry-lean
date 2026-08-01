import Mathlib.Tactic
import InfoGeometry.Physics.ItakuraSaitoPrimes
import InfoGeometry.Physics.FreeEntropyDiffusionFunctional
import InfoGeometry.Physics.MD008RepresentationCharge

namespace InfoGeometry.Physics.ItakuraSaitoFradkinTseytlin


open InfoGeometry.Physics.FreeEntropyDiffusionFunctional
open InfoGeometry.Physics.MD008RepresentationCharge

/-!
# Itakura--Saito and scale-invariant finite packets

This module defines a few scalar formulas and finite count packets.  It does
not derive Fradkin--Tseytlin dynamics, Bohm--Madelung equations, KMS spectra,
or Standard Model field content.
-/

/-- The logarithmic spectral entropy potential -/
noncomputable def spectralEntropyPotential (x : ℝ) : ℝ := - Real.log x

/-- The Itakura-Saito divergence -/
noncomputable def itakuraSaitoDivergence (P Q : ℝ) : ℝ :=
  (P / Q) - Real.log (P / Q) - 1

/-- A scalar expression inspired by the logarithmic quantum-potential formula. -/
noncomputable def bohmMadelungQuantumPotential (_ρ : ℝ) (grad2LogRho : ℝ) (gradLogRhoSq : ℝ) : ℝ :=
  -- Representing -(ℏ²/4m) (∇² ln ρ + 1/2 (∇ ln ρ)²)
  -- We set constants to 1 for the formal structure
  - (grad2LogRho + (1/2) * gradLogRhoSq)

/-- Independent positive-scale and quantum-gradient data. -/
def FourthOrderScalePacket : Type :=
  {p : ℝ × ℝ // p.1 > 0}

namespace FourthOrderScalePacket

def spectral_base (P : FourthOrderScalePacket) : ℝ :=
  P.1.1

def is_positive (P : FourthOrderScalePacket) : P.spectral_base > 0 :=
  P.2

def quantum_potential_gradient (P : FourthOrderScalePacket) : ℝ :=
  P.1.2

/-- The fourth-order scalar term is canonically the gradient square. -/
def four_derivative_term (P : FourthOrderScalePacket) : ℝ :=
  P.quantum_potential_gradient ^ 2

/-- The scale relation is definitional, not separately supplied evidence. -/
theorem scaling_eq (P : FourthOrderScalePacket) :
    P.quantum_potential_gradient ^ 2 = P.four_derivative_term :=
  rfl

end FourthOrderScalePacket

/-- A finite count packet with explicit balance equations. -/
def ScaleInvariantCocycles : Type :=
  {p : (ℕ × ℕ) × ℕ //
    p.1.2 = 4 * p.1.1 ∧ p.2 = 3 * p.1.1}

namespace ScaleInvariantCocycles

def gauge_bosons (P : ScaleInvariantCocycles) : ℕ :=
  P.1.1.1

def weyl_spinors (P : ScaleInvariantCocycles) : ℕ :=
  P.1.1.2

def ft_scalars (P : ScaleInvariantCocycles) : ℕ :=
  P.1.2

def susy_balance (P : ScaleInvariantCocycles) :
    P.weyl_spinors = 4 * P.gauge_bosons :=
  P.2.1

def scalar_balance (P : ScaleInvariantCocycles) :
    P.ft_scalars = 3 * P.gauge_bosons :=
  P.2.2

end ScaleInvariantCocycles

/-- A concrete finite count packet with values `12`, `48`, and `36`. -/
def exampleCocycles : ScaleInvariantCocycles :=
  ⟨((12, 48), 36), by norm_num⟩

theorem exampleCocycles_ft_scalars_eq :
  exampleCocycles.ft_scalars = 36 := rfl

end InfoGeometry.Physics.ItakuraSaitoFradkinTseytlin

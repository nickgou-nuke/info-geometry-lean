/-
InfoGeometry/OperatorAlgebra/RealKreinModularSpectralTriple.lean

Real Krein modular spectral triple socket.

This module bridges modular sign/CPT data to phase-real spectral geometry:

  eps = modular sign,
  J = modular/CPT reflection,
  Kmod = J eps = Hestenes phase axis,
  D = commutator metric sensor.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.ModularSignCPT
import InfoGeometry.OperatorAlgebra.RealPhaseSpectralTriple
import InfoGeometry.OperatorAlgebra.RenormalizedTrace

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealKreinModularSpectralTriple

open scoped ENNReal
open InfoGeometry.OperatorAlgebra.ModularSignCPT
open InfoGeometry.OperatorAlgebra.RealPhaseSpectralTriple

/-! ## 1. Krein and modular phase data -/

/-- Bounded real-linear endomorphisms. -/
abbrev RealEnd
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  H →L[ℝ] H

/-- A genuine symmetric nondegenerate real Krein bilinear form. -/
structure KreinPairing
    (H : Type*) [AddCommMonoid H] [Module ℝ H] where
  pair : LinearMap.BilinForm ℝ H
  symmetric : pair.IsSymm
  nondegenerate : pair.Nondegenerate

namespace KreinPairing

variable {H : Type*} [AddCommMonoid H] [Module ℝ H]
variable (K : KreinPairing H)

/-- The Krein bilinear form is symmetric. -/
theorem pair_comm (u v : H) :
    K.pair u v = K.pair v u :=
  K.symmetric.eq u v

/-- The Krein bilinear form has trivial radical. -/
theorem pair_nondegenerate :
    K.pair.Nondegenerate :=
  K.nondegenerate

end KreinPairing

/--
The phase axis reconstructed from full/gapped modular sign-CPT data.
-/
def modularPhaseAxis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : ModularSignCPTDatum H) :
    PhaseAxis H where
  K := M.Kmod
  K_sq := M.Kmod_square

/-! ## 2. Real Krein modular spectral triple -/

/--
Real Krein modular spectral triple socket.

The carrier is fixed; modular signs, chiral sectors, spectral commutators,
weights, core traces, and renormalized readouts are attached as proof-carrying
operator data.
-/
structure RealKreinModularTriple
    (A H Core : Type*)
    [Ring A] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [AddCommMonoid Core] [Mul Core] where
  representedAlgebra : RepresentedAlgebra A H
  modularCPT : ModularSignCPTDatum H
  phaseAxis : PhaseAxis H
  phaseAxis_eq_modular :
    phaseAxis.K = modularCPT.Kmod
  realStructure : PhaseRealStructure H phaseAxis
  chiralGrading : ChiralGrading H phaseAxis
  spectralGenerator : SpectralGenerator H
  order_one : OrderOneCondition representedAlgebra spectralGenerator
  kreinPairing : KreinPairing H
  modularWeight : ModularWeightDatum (RealEnd H)
  coreTrace : CoreTraceDatum (RealEnd H) Core
  renormalizedTrace : Option (TypeIIIRenormalizedTraceDatum (RealEnd H) Core)

namespace RealKreinModularTriple

variable
    {A H Core : Type*}
    [Ring A] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [AddCommMonoid Core] [Mul Core]
    (T : RealKreinModularTriple A H Core)

/-- The modularly generated Hestenes phase axis. -/
def Kmod : RealEnd H :=
  T.modularCPT.Kmod

/-- The spectral Lipschitz readout from `D`. -/
def lipschitz (a : A) : ℝ :=
  lipschitzSeminorm T.representedAlgebra T.spectralGenerator a

theorem lipschitz_nonneg (a : A) :
    0 ≤ T.lipschitz a :=
  lipschitzSeminorm_nonneg T.representedAlgebra T.spectralGenerator a

/-- Re-export that the modular phase axis squares to `-1`. -/
theorem Kmod_square :
    T.Kmod.comp T.Kmod = -(1 : RealEnd H) :=
  T.modularCPT.Kmod_square

end RealKreinModularTriple

end InfoGeometry.OperatorAlgebra.RealKreinModularSpectralTriple

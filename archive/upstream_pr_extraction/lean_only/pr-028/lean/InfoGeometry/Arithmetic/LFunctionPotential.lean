/-
InfoGeometry/Arithmetic/LFunctionPotential.lean

Arithmetic spectral divisors and automorphic L-function barriers in the real doubled language.

This file formalizes the arithmetic boundary layer associated to automorphic
scattering data. Following the Erlanger Program of Klein symmetry invariant geometry,
we do not use the complex proxy ℂ. Instead, the spectral domain is the real
doubled carrier H₂ equipped with the Hestenes phase axis K = Jε.

The file is intentionally conservative:
* finite logarithmic potentials are stated only away from singular divisors;
* exact horizon/divisor identification is a proof field of the witness;
* no theorem tries to infer an exact zero from an informal divergence argument.
-/

import Mathlib.Tactic
import InfoGeometry.Arithmetic.ZetaPotentialSign
import InfoGeometry.Exceptional.SplitJordanPotential
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.TomitaTakesaki

noncomputable section

namespace InfoGeometry.Arithmetic.LFunction

open Filter
open Topology
open InfoGeometry.Krein
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Exceptional.SplitJordan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-! ### 1. Real-geometric spectral domain -/

/--
The arithmetic spectral domain is the real doubled plane H₂.
Following Klein's mandate, we treat it as a real metric space where the 
"complex" structure is a symmetry (the K axis).
-/
def SpectralDomain (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] := 
  DoubledSpace E

/-! ### 2. Abstract automorphic scattering L-functions -/

/--
An abstract L-function extracted from the Siegel constant term or scattering
matrix of an automorphic boundary, viewed as a map on the real doubled domain.
-/
structure ScatteringLFunction (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (G : Type*) [Monoid G] where
  /-- The real-linear or K-linear map representing the L-function value. -/
  Lval : DoubledSpace E → DoubledSpace E

  /-- The critical locus, typically a fixed axis or sheet in H₂. -/
  criticalLocus : Set (DoubledSpace E)

  /-- Concrete monoid representation of the automorphic symmetry on `H₂`. -/
  automorphicAction : G →* (DoubledSpace E ≃L[ℝ] DoubledSpace E)

  /-- The scattering map is equivariant for the supplied symmetry action. -/
  automorphic_equivariance :
    ∀ (g : G) (s : DoubledSpace E),
      automorphicAction g (Lval s) = Lval (automorphicAction g s)

/-! ### 3. Arithmetic spectral divisors and logarithmic barriers -/

/--
The arithmetic spectral divisor.
A point `s` in H₂ is an arithmetic horizon for `L` if the L-function value
vanishes (under the proper metric).
-/
def IsArithmeticHorizon
    {G : Type*} [Monoid G]
    (L : ScatteringLFunction E G)
    (s : DoubledSpace E) : Prop :=
  L.Lval s = 0

/--
The finite real-valued L-function logarithmic potential using the proper metric.
`Φ_L(s) = -log ‖L(s)‖_Krein`.
-/
def lFunctionPotential
    {G : Type*} [Monoid G]
    (L : ScatteringLFunction E G)
    (s : DoubledSpace E) : ℝ :=
  - Real.log ‖L.Lval s‖

/--
Filter-level statement that the arithmetic barrier diverges at `s₀`.
-/
def ArithmeticBarrierDivergesAt
    {G : Type*} [Monoid G]
    (L : ScatteringLFunction E G)
    (s₀ : DoubledSpace E) : Prop :=
  Tendsto
    (fun s => lFunctionPotential L s)
    (nhdsWithin s₀ {s | s ≠ s₀})
    atTop

/-! ### 4. Unified Jordan/L-function horizon witness -/

/--
The unified horizon witness in the real-doubled language.

`potentialEquivalence` is stated on the NonzeroNormPoint locus.
The correspondence is between the Jordan rank-collapse and the 
L-function vanishing on the real carrier.
-/
structure UnifiedHorizonWitness
    (J : Type*) [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanNormDatum J)
    (G : Type*) [Monoid G]
    (L : ScatteringLFunction E G) where

  /-- Map from a Jordan charge/state to the real spectral carrier H₂. -/
  spectralMap : J → DoubledSpace E

  /-- Smooth/harmonic finite renormalization term. -/
  renormalization : J → ℝ

  /-- Scaling constant relating the two finite potentials off the horizon. -/
  c : ℝ

  /--
  Finite potential identity away from the Jordan divisor.
  Uses the Krein norm ‖.‖ on H₂.
  -/
  potentialEquivalence :
    ∀ X : D.NonzeroNormPoint,
      lFunctionPotential L (spectralMap X.val) =
        c * splitPotential D X + renormalization X.val

  /--
  Exact divisor correspondence.
  -/
  horizonIff :
    ∀ X : J,
      D.norm X = 0 ↔ IsArithmeticHorizon L (spectralMap X)

  /--
  Optional asymptotic refinement: the arithmetic barrier diverges at the
  spectral image of every Jordan rank-deficient point.
  -/
  arithmeticBarrierDivergesOnHorizon :
    ∀ X : J,
      D.norm X = 0 →
        ArithmeticBarrierDivergesAt L (spectralMap X)

namespace UnifiedHorizonWitness

variable
    {J : Type*} [AddCommGroup J] [Module ℝ J]
    {D : CubicJordanNormDatum J}
    {G : Type*} [Monoid G]
    {L : ScatteringLFunction E G}

/--
A Jordan rank-deficiency horizon maps to an arithmetic L-divisor.
-/
theorem geometric_horizon_is_arithmetic_horizon
    (W : UnifiedHorizonWitness J D G L)
    (X : J)
    (hRankDeficient : D.norm X = 0) :
    IsArithmeticHorizon L (W.spectralMap X) :=
  (W.horizonIff X).1 hRankDeficient

/--
An arithmetic L-divisor in the spectral image pulls back to a Jordan
rank-deficiency horizon.
-/
theorem arithmetic_horizon_is_geometric_horizon
    (W : UnifiedHorizonWitness J D G L)
    (X : J)
    (hArithmetic : IsArithmeticHorizon L (W.spectralMap X)) :
    D.norm X = 0 :=
  (W.horizonIff X).2 hArithmetic

/--
The exact equivalence between the Jordan divisor and the arithmetic divisor.
-/
theorem geometric_horizon_iff_arithmetic_horizon
    (W : UnifiedHorizonWitness J D G L)
    (X : J) :
    D.norm X = 0 ↔ IsArithmeticHorizon L (W.spectralMap X) :=
  W.horizonIff X

/--
At a geometric horizon, the arithmetic logarithmic barrier diverges.
-/
theorem arithmetic_barrier_diverges_at_geometric_horizon
    (W : UnifiedHorizonWitness J D G L)
    (X : J)
    (hRankDeficient : D.norm X = 0) :
    ArithmeticBarrierDivergesAt L (W.spectralMap X) :=
  W.arithmeticBarrierDivergesOnHorizon X hRankDeficient

end UnifiedHorizonWitness

end InfoGeometry.Arithmetic.LFunction

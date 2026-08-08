import Mathlib.Tactic
import InfoGeometry.External.Auto.HurwitzTwistedSector

noncomputable section

namespace InfoGeometry.Arithmetic.HurwitzQuaternionSpectrum

open Complex Finset
open scoped BigOperators

/-!
# Exact Hurwitz Quaternionic Spectrum

This module is the rational-arithmetic companion to
`InfoGeometry.Quantum.HurwitzTwistedSector`.

It records the exact integer/half-integer Hurwitz lattice condition and connects
finite shifted Hurwitz-zeta traces to the already-defined Gamma-normalized
Mellin mode.  No analytic continuation or improper integral theorem is asserted.
-/

/-- All coordinates are in the integral Hurwitz lane. -/
def IntegralLane (a b c d : ℚ) : Prop :=
  a.den = 1 ∧ b.den = 1 ∧ c.den = 1 ∧ d.den = 1

/-- All coordinates are in the half-integral Hurwitz lane. -/
def HalfIntegralLane (a b c d : ℚ) : Prop :=
  a.den = 2 ∧ b.den = 2 ∧ c.den = 2 ∧ d.den = 2

/--
Exact Hurwitz quaternion: all four rational coordinates are simultaneously
integral or simultaneously half-integral.
-/
structure HurwitzQuaternion where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  sameLane : IntegralLane a b c d ∨ HalfIntegralLane a b c d

namespace HurwitzQuaternion

/-- The rational squared norm. -/
def normSq (q : HurwitzQuaternion) : ℚ :=
  q.a ^ 2 + q.b ^ 2 + q.c ^ 2 + q.d ^ 2

/-- Conjugation preserves the lane condition because rational denominators are unchanged. -/
def conj (q : HurwitzQuaternion) : HurwitzQuaternion :=
  { a := q.a
  , b := -q.b
  , c := -q.c
  , d := -q.d
  , sameLane := by
      rcases q.sameLane with h | h
      · left
        simp [IntegralLane, h.1, h.2.1, h.2.2.1, h.2.2.2]
      · right
        simp [HalfIntegralLane, h.1, h.2.1, h.2.2.1, h.2.2.2] }

theorem normSq_nonneg (q : HurwitzQuaternion) : 0 ≤ q.normSq := by
  unfold normSq
  nlinarith [sq_nonneg q.a, sq_nonneg q.b, sq_nonneg q.c, sq_nonneg q.d]

theorem normSq_pos_of_a_ne_zero (q : HurwitzQuaternion) (h : q.a ≠ 0) :
    0 < q.normSq := by
  unfold normSq
  have ha : 0 < q.a ^ 2 := sq_pos_of_ne_zero h
  nlinarith [sq_nonneg q.b, sq_nonneg q.c, sq_nonneg q.d]

theorem normSq_conj (q : HurwitzQuaternion) : q.conj.normSq = q.normSq := by
  unfold conj normSq
  ring

/-- Exact logarithmic energy after coercing the rational norm to `ℝ`. -/
def logNormEnergy (q : HurwitzQuaternion) : ℝ :=
  Real.log (q.normSq : ℝ)

theorem logNormEnergy_eq (q : HurwitzQuaternion) :
    q.logNormEnergy = Real.log (q.normSq : ℝ) := rfl

end HurwitzQuaternion

/-- Finite shifted Hurwitz-zeta trace. -/
def finiteHurwitzZetaTrace (N : ℕ) (a : ℝ) (s : ℂ) : ℂ :=
  ∑ n : Fin N, Complex.exp (-s * (Real.log ((n.1 : ℝ) + a) : ℂ))

/-- Finite version using the concrete Gamma-normalized Mellin atom. -/
def finiteHurwitzMellinTrace (N : ℕ) (a : ℝ) (s : ℂ) : ℂ :=
  ∑ n : Fin N,
    InfoGeometry.Quantum.ZetaSpectralBridge.gammaNormalizedMellinMode
      s ((n.1 : ℝ) + a)

/--
Finite Mellin compatibility for shifted Hurwitz sectors.

This is the ax!om-free version of the proposed bridge: the Mellin atom is the
concrete `exp (-s * log energy)` definition from `ZetaSpectralBridge`.
-/
theorem finite_mellin_compatibility (N : ℕ) (a : ℝ) (s : ℂ) :
    finiteHurwitzZetaTrace N a s = finiteHurwitzMellinTrace N a s := by
  simp [finiteHurwitzZetaTrace, finiteHurwitzMellinTrace,
    InfoGeometry.Quantum.ZetaSpectralBridge.gammaNormalizedMellinMode]

/-- The half-integer Mobius/Neveu-Schwarz finite shifted sector. -/
def twistedSectorTrace (N : ℕ) (s : ℂ) : ℂ :=
  finiteHurwitzZetaTrace N (1 / 2) s

/-- The periodic/integer finite sector. -/
def periodicSectorTrace (N : ℕ) (s : ℂ) : ℂ :=
  finiteHurwitzZetaTrace N 1 s

theorem twistedSectorTrace_eq_mellin (N : ℕ) (s : ℂ) :
    twistedSectorTrace N s = finiteHurwitzMellinTrace N (1 / 2) s := by
  exact finite_mellin_compatibility N (1 / 2) s

/-- Shifted trace agrees with the quantum shifted trace from `HurwitzTwistedSector`. -/
theorem finiteHurwitzZetaTrace_eq_quantum_trace (N : ℕ) (a : ℝ) (s : ℂ) :
    finiteHurwitzMellinTrace N a s =
      InfoGeometry.Quantum.HurwitzTwistedSector.finiteHurwitzZetaTrace N a s := by
  simp [finiteHurwitzMellinTrace,
    InfoGeometry.Quantum.HurwitzTwistedSector.finiteHurwitzZetaTrace,
    InfoGeometry.Quantum.ZetaSpectralBridge.gammaNormalizedMellinMode]

/-- Infinite shifted Hurwitz trace, delegated to the analytic-side quantum module. -/
def infiniteHurwitzTrace (a : ℝ) (s : ℂ) : ℂ :=
  InfoGeometry.Quantum.HurwitzTwistedSector.infiniteHurwitzTrace a s

/--
Conservative Mellin bridge for the modeled infinite Hurwitz trace.

This re-exports the property-explicit bridge from `HurwitzTwistedSector`.
-/
theorem infiniteHurwitzTrace_mellin_bridge
    (M : InfoGeometry.Quantum.HurwitzTwistedSector.InfiniteHurwitzTraceModel)
    (shift : ℝ) (s : ℂ) :
    M.heatTrace shift s = M.gamma s * M.infiniteHurwitzTrace shift s :=
  InfoGeometry.Quantum.HurwitzTwistedSector.infiniteHurwitzTrace_mellin_bridge M shift s

/-- Infinite half-integer Mobius/Neveu-Schwarz sector trace. -/
def neveuSchwarzInfiniteTrace (s : ℂ) : ℂ :=
  InfoGeometry.Quantum.HurwitzTwistedSector.neveuSchwarzInfiniteTrace s

/-- The exact-arithmetic wrapper inherits the quantum half-shift formula. -/
theorem neveuSchwarzInfiniteTrace_eq_riemann (s : ℂ) (hs : 1 < s.re) :
    neveuSchwarzInfiniteTrace s = ((2 : ℂ) ^ s - 1) * riemannZeta s :=
  InfoGeometry.Quantum.HurwitzTwistedSector.neveuSchwarzInfiniteTrace_eq_riemann s hs

/-- Exact-arithmetic wrapper for a spectral target realizing the NS/Mobius sector. -/
abbrev NeveuSchwarzSpectralTarget :=
  InfoGeometry.Quantum.HurwitzTwistedSector.NeveuSchwarzSpectralTarget

/-- Exact-arithmetic canonical NS/Mobius target inherited from the analytic core. -/
def neveuSchwarzCanonicalSpectralTarget : NeveuSchwarzSpectralTarget :=
  InfoGeometry.Quantum.HurwitzTwistedSector.neveuSchwarzCanonicalSpectralTarget

/-- Exact-arithmetic wrapper for a model-aware NS/Mobius target with heat bridge. -/
abbrev NeveuSchwarzSpectralTargetWithMellin :=
  InfoGeometry.Quantum.HurwitzTwistedSector.NeveuSchwarzSpectralTargetWithMellin

namespace NeveuSchwarzSpectralTarget

/-- Twisted-sector formulas propagate to exact-arithmetic spectral targets. -/
theorem targetTrace_eq_riemann
    (T : NeveuSchwarzSpectralTarget) (s : ℂ) (hs : 1 < s.re) :
    T.targetTrace s = ((2 : ℂ) ^ s - 1) * riemannZeta s :=
  InfoGeometry.Quantum.HurwitzTwistedSector.NeveuSchwarzSpectralTarget.targetTrace_eq_riemann
    T s hs

/-- Exact-arithmetic wrapper for upgrading an NS target with Mellin bridge data. -/
def withMellin
    (T : NeveuSchwarzSpectralTarget)
    (model : InfoGeometry.Quantum.HurwitzTwistedSector.InfiniteHurwitzTraceModel)
    (heatTrace : ℂ → ℂ)
    (h_infinite : ∀ s, model.infiniteHurwitzTrace (1 / 2 : ℝ) s = T.targetTrace s)
    (h_heat : ∀ s, heatTrace s = model.heatTrace (1 / 2 : ℝ) s) :
    NeveuSchwarzSpectralTargetWithMellin :=
  InfoGeometry.Quantum.HurwitzTwistedSector.NeveuSchwarzSpectralTarget.withMellin
    T model heatTrace h_infinite h_heat

end NeveuSchwarzSpectralTarget

namespace NeveuSchwarzSpectralTargetWithMellin

/-- Heat-side twisted formula propagates to exact-arithmetic targets. -/
theorem heatTrace_eq_riemann
    (T : NeveuSchwarzSpectralTargetWithMellin) (s : ℂ) (hs : 1 < s.re) :
    T.heatTrace s = T.model.gamma s * ((2 : ℂ) ^ s - 1) * riemannZeta s := by
  exact
    InfoGeometry.Quantum.HurwitzTwistedSector.NeveuSchwarzSpectralTargetWithMellin.heatTrace_eq_riemann
      T s hs

/-- Immediate trace-side propagation. -/
theorem targetTrace_eq_riemann
    (T : NeveuSchwarzSpectralTargetWithMellin) (s : ℂ) (hs : 1 < s.re) :
    T.targetTrace s = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
  exact
    InfoGeometry.Quantum.HurwitzTwistedSector.NeveuSchwarzSpectralTargetWithMellin.targetTrace_eq_riemann
      T s hs

end NeveuSchwarzSpectralTargetWithMellin

/-- Exact-spectrum wrapper for the finite Dirichlet-character Hurwitz combination. -/
def finiteHurwitzCharacterCombination
    (k N : ℕ) (χ : Fin k → ℂ) (s : ℂ) : ℂ :=
  InfoGeometry.Quantum.HurwitzTwistedSector.finiteHurwitzCharacterCombination k N χ s

theorem finiteHurwitzCharacterCombination_add
    (k N : ℕ) (χ ψ : Fin k → ℂ) (s : ℂ) :
    finiteHurwitzCharacterCombination k N (fun a => χ a + ψ a) s =
      finiteHurwitzCharacterCombination k N χ s +
        finiteHurwitzCharacterCombination k N ψ s :=
  InfoGeometry.Quantum.HurwitzTwistedSector.finiteHurwitzCharacterCombination_add k N χ ψ s

theorem finiteHurwitzCharacterCombination_smul
    (k N : ℕ) (c : ℂ) (χ : Fin k → ℂ) (s : ℂ) :
    finiteHurwitzCharacterCombination k N (fun a => c * χ a) s =
      c * finiteHurwitzCharacterCombination k N χ s :=
  InfoGeometry.Quantum.HurwitzTwistedSector.finiteHurwitzCharacterCombination_smul k N c χ s

theorem finiteHurwitzCharacterCombination_zero
    (k N : ℕ) (s : ℂ) :
    finiteHurwitzCharacterCombination k N (fun _ => 0) s = 0 :=
  InfoGeometry.Quantum.HurwitzTwistedSector.finiteHurwitzCharacterCombination_zero k N s

end InfoGeometry.Arithmetic.HurwitzQuaternionSpectrum

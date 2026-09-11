import InfoGeometry.Clifford.CliffordBott
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Algebraic State Space over the Split Clifford Direct Limit

This module specializes the algebraic state/Radon--Nikodym interface from
`ErlangenJaynesGromov` to the repo-native direct-limit split Clifford algebra
`Cl_infty`.

The construction is intentionally algebraic:

* a state is a normalized linear functional on `Cl_infty`;
* a trace/readout is supplied explicitly as a linear functional;
* the lifted nilpotent `ε∞` generates a parabolic RN-density path
  `1 + t ε∞`;
* if the reference state kills `ε∞`, the RN-density path stays normalized;
* the first variation of the state path on an observable `a` is exactly
  `τ (ε∞ * a)`.

No canonical trace on the direct limit, positivity theorem, C*-completion, or
analytic noncommutative Radon--Nikodym theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.Quantum.StateSpace

open InfoGeometry.Clifford.CliffordBott

/-- Algebraic state on `Cl_infty`: a normalized real-linear functional. -/
structure Cl_inftyState where
  /-- The underlying real-linear functional. -/
  toLinearMap : Cl_infty →ₗ[ℝ] ℝ
  /-- Normalization on the unit observable. -/
  map_one : toLinearMap 1 = 1

namespace Cl_inftyState

@[ext]
theorem ext {ω η : Cl_inftyState}
    (h : ∀ a : Cl_infty, ω.toLinearMap a = η.toLinearMap a) :
    ω = η := by
  cases ω with
  | mk ω hω =>
    cases η with
    | mk η hη =>
      simp only at h
      have hmap : ω = η := by
        exact LinearMap.ext h
      subst hmap
      rfl

end Cl_inftyState

/-- Real-linear readout/trace-like functional on `Cl_infty`. -/
abbrev Cl_inftyFunctional : Type :=
  Cl_infty →ₗ[ℝ] ℝ

/--
Algebraic Radon--Nikodym density witness between normalized linear states on
`Cl_infty`.
-/
structure Cl_inftyRNDensity (ω φ : Cl_inftyState) where
  /-- The density element. -/
  density : Cl_infty
  /-- Representation law for the target state relative to the reference state. -/
  rn_law : ∀ a : Cl_infty, φ.toLinearMap a = ω.toLinearMap (density * a)

namespace Cl_inftyRNDensity

theorem density_normalized {ω φ : Cl_inftyState} (D : Cl_inftyRNDensity ω φ) :
    ω.toLinearMap D.density = 1 := by
  have h := D.rn_law 1
  have hφ := φ.map_one
  rw [h] at hφ
  simpa using hφ

end Cl_inftyRNDensity

/-- The lifted square-zero direct-limit generator. -/
abbrev nilpotentRNGenerator : Cl_infty :=
  clInfinityNilpotentShield

@[simp]
theorem nilpotentRNGenerator_sq :
    nilpotentRNGenerator * nilpotentRNGenerator = 0 := by
  exact clInfinityNilpotentShield_sq

/-- Parabolic algebraic RN-density path `1 + t ε∞`. -/
def parabolicRNDensity (t : ℝ) : Cl_infty :=
  1 + t • nilpotentRNGenerator

@[simp]
theorem parabolicRNDensity_zero :
    parabolicRNDensity 0 = (1 : Cl_infty) := by
  simp [parabolicRNDensity]

/-- Exact first-difference law for the parabolic RN-density path. -/
theorem parabolicRNDensity_sub_zero (t : ℝ) :
    parabolicRNDensity t - parabolicRNDensity 0 = t • nilpotentRNGenerator := by
  simp [parabolicRNDensity]

/-- Iterating the parabolic RN density realizes the direct-limit power law. -/
theorem parabolicRNDensity_pow (t : ℝ) (n : ℕ) :
    (parabolicRNDensity t) ^ n = parabolicRNDensity ((n : ℝ) * t) := by
  simpa [parabolicRNDensity, nilpotentRNGenerator] using
    clInfinity_parabolic_pow t n

/--
A readout packet for the nilpotent RN generator.

The field `readout_law` is the explicit algebraic substitute for a canonical
trace theorem on the direct limit: it says that the supplied first-variation
functional is the observable readout `τ(ε∞ * a)`.
-/
structure NilpotentRNReadout (τ : Cl_inftyState) where
  /-- First-variation functional attached to the lifted nilpotent generator. -/
  epsilonReadout : Cl_inftyFunctional
  /-- The first variation preserves normalization. -/
  epsilonReadout_one : epsilonReadout 1 = 0
  /-- Compatibility with the algebraic RN-generator expression. -/
  readout_law :
    ∀ a : Cl_infty, epsilonReadout a = τ.toLinearMap (nilpotentRNGenerator * a)

/--
Affine state path driven by an explicitly supplied first-variation functional.

This is the algebraic Jaynes/Gromov state-space move: no positivity, topology, or
canonical trace is asserted; the thermodynamic tangent vector is a linear
functional.
-/
def affineStatePath
    (τ : Cl_inftyState)
    (epsilonReadout : Cl_inftyFunctional)
    (hεOne : epsilonReadout 1 = 0)
    (t : ℝ) : Cl_inftyState where
  toLinearMap := τ.toLinearMap + t • epsilonReadout
  map_one := by
    simp [τ.map_one, hεOne]

@[simp]
theorem affineStatePath_apply
    (τ : Cl_inftyState)
    (epsilonReadout : Cl_inftyFunctional)
    (hεOne : epsilonReadout 1 = 0)
    (t : ℝ)
    (a : Cl_infty) :
    (affineStatePath τ epsilonReadout hεOne t).toLinearMap a =
      τ.toLinearMap a + t * epsilonReadout a := by
  simp [affineStatePath]

@[simp]
theorem affineStatePath_zero
    (τ : Cl_inftyState)
    (epsilonReadout : Cl_inftyFunctional)
    (hεOne : epsilonReadout 1 = 0) :
    affineStatePath τ epsilonReadout hεOne 0 = τ := by
  ext a
  simp [affineStatePath]

/--
State path generated by a nilpotent RN readout packet.

This packages only an algebraic affine normalized-state path on `Cl_infty`.
It is not a positivity theorem, a canonical trace construction, or a full
noncommutative Radon--Nikodym flow theorem.
-/
def rnStatePath
    (τ : Cl_inftyState)
    (R : NilpotentRNReadout τ)
    (t : ℝ) : Cl_inftyState :=
  affineStatePath τ R.epsilonReadout R.epsilonReadout_one t

/--
Explicit algebraic RN path witness when the density representation law is
available.

This records an exact owner-side readout law for the supplied affine path; it
does not promote the construction to a general analytic RN theorem.
-/
abbrev ParabolicRNPathWitness
    (τ : Cl_inftyState)
    (R : NilpotentRNReadout τ) : Prop :=
  ∀ (t : ℝ) (a : Cl_infty),
    (rnStatePath τ R t).toLinearMap a =
      τ.toLinearMap (parabolicRNDensity t * a)

namespace ParabolicRNPathWitness

/-- The explicit density representation yields a conventional RN witness at each time. -/
def densityAt
    {τ : Cl_inftyState}
    {R : NilpotentRNReadout τ}
    (W : ParabolicRNPathWitness τ R)
    (t : ℝ) :
  Cl_inftyRNDensity τ (rnStatePath τ R t) where
  density := parabolicRNDensity t
  rn_law := W t

end ParabolicRNPathWitness

/--
First variation of the affine algebraic state path.
-/
theorem affineStatePath_hasDerivAt_zero
    (τ : Cl_inftyState)
    (epsilonReadout : Cl_inftyFunctional)
    (hεOne : epsilonReadout 1 = 0)
    (a : Cl_infty) :
    HasDerivAt
      (fun t : ℝ => (affineStatePath τ epsilonReadout hεOne t).toLinearMap a)
      (epsilonReadout a) 0 := by
  have hpath :
      (fun t : ℝ => (affineStatePath τ epsilonReadout hεOne t).toLinearMap a)
        = fun t : ℝ => τ.toLinearMap a + t * epsilonReadout a := by
    funext t
    exact affineStatePath_apply τ epsilonReadout hεOne t a
  rw [hpath]
  have hlin :
      HasDerivAt (fun t : ℝ => t * epsilonReadout a) (epsilonReadout a) 0 := by
    simpa using (hasDerivAt_id 0).mul_const (epsilonReadout a)
  simpa using hlin.const_add (τ.toLinearMap a)

/--
First variation of the RN-generated state path.

The derivative is stated as the algebraic RN-generator readout `τ(ε∞ * a)`.
-/
theorem rnStatePath_hasDerivAt_zero
    (τ : Cl_inftyState)
    (R : NilpotentRNReadout τ)
    (a : Cl_infty) :
    HasDerivAt (fun t : ℝ => (rnStatePath τ R t).toLinearMap a)
      (τ.toLinearMap (nilpotentRNGenerator * a)) 0 := by
  have h := affineStatePath_hasDerivAt_zero τ R.epsilonReadout R.epsilonReadout_one a
  simpa [rnStatePath, R.readout_law a] using h

end InfoGeometry.Quantum.StateSpace

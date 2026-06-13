# Centered Zeta Coordinate API

> Status: `live API overview`
> Audited: 2026-06-10
> Owner module: `lean/InfoGeometry/Arithmetic/ZetaSymmetryAdaptedDefinitions.lean`
> Boundary: finite coordinate algebra and conditional xi parity only. This note
> does not claim RH, zeta-zero confinement, analytic continuation, Euler product
> convergence, KMS/CFT physics, or topological protection as Lean theorems.

This note records the exact Lean surface supporting the centered zeta chart:

```text
s = 1/2 + u + iv
z = u + iv
```

The important formal move is that the classical Riemann reflection `s ↦ 1 - s`
becomes the centered inversion `z ↦ -z`.

## Owner Namespace

```lean
namespace InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions
```

## Centered Chart

```lean
abbrev CenteredChart :=
  InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart

def centeredParameter (x : CenteredChart) : ℂ :=
  (fromCentered x).toComplex
```

Kernel-checked readout:

```lean
theorem centeredParameter_eq_half_plus_u_plus_iv (x : CenteredChart) :
    centeredParameter x =
      ((x.u + (1 / 2 : ℝ) : ℝ) : ℂ) + (x.v : ℂ) * Complex.I
```

The critical line is the zero-locus of the centered scale coordinate:

```lean
def centeredCriticalLine (x : CenteredChart) : Prop :=
  x.u = 0

theorem criticalMirror_fixed_iff_centeredCriticalLine (x : CenteredChart) :
    criticalMirror x = x ↔ centeredCriticalLine x
```

## Reflection And Central Inversion

```lean
def riemannReflection (s : ℂ) : ℂ :=
  1 - s

def offsetParameter (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) + z
```

The centered inversion theorem is:

```lean
theorem riemannReflection_offsetParameter (z : ℂ) :
    riemannReflection (offsetParameter z) = offsetParameter (-z)
```

This is the precise theorem-level version of:

```text
s = 1/2 + z
1 - s = 1/2 - z
```

For the real two-coordinate chart:

```lean
theorem centeredParameter_functionalDual (x : CenteredChart) :
    centeredParameter (functionalDual x) =
      riemannReflection (centeredParameter x)

theorem centeredParameter_conjugation (x : CenteredChart) :
    centeredParameter (conjugation x) = star (centeredParameter x)
```

## Dirichlet Mode Split

The finite Dirichlet mode is factored into:

```lean
def criticalLineWeight (L : ℝ) : ℂ
def scaleEnvelope (L u : ℝ) : ℂ
def phaseWave (L v : ℝ) : ℂ
def centeredDirichletMode (L : ℝ) (x : CenteredChart) : ℂ
```

The critical-line reduction is:

```lean
theorem centeredDirichletMode_of_centeredCriticalLine
    {L : ℝ} {x : CenteredChart} (hx : centeredCriticalLine x) :
    centeredDirichletMode L x =
      criticalLineWeight L * phaseWave L x.v
```

The basic finite reflection readouts are:

```lean
theorem centeredDirichletMode_conjugation
theorem centeredDirichletMode_functionalDual
theorem centeredDirichletMode_criticalMirror
```

## Conditional Xi Parity

The centered completed-xi readout is:

```lean
def XiFromXi (xi : ℂ → ℂ) (z : ℂ) : ℂ :=
  xi (offsetParameter z)
```

The parity theorem is conditional on a supplied reflection law:

```lean
theorem XiFromXi_even_of_reflection
    (xi : ℂ → ℂ)
    (hxi : ∀ s, xi s = xi (riemannReflection s))
    (z : ℂ) :
    XiFromXi xi z = XiFromXi xi (-z)
```

The centered `J`-odd projector vanishes only from explicit Schwarz and Riemann
reflection hypotheses:

```lean
theorem centeredXi_JOddProjector_eq_zero_of_schwarz_reflection

theorem centeredXi_mem_JFixedCone_of_schwarz_reflection
```

## What This Does And Does Not Say

The proved coordinate layer says:

- the centered chart rewrites `s` as `1/2 + u + iv`;
- the critical line is `u = 0`;
- `s ↦ 1-s` becomes `z ↦ -z`;
- finite Dirichlet modes split into baseline, scale-normal, and phase factors;
- a supplied xi reflection law implies `Ξ(z)=Ξ(-z)`.

It does not say:

- all non-trivial zeta zeros have `u = 0`;
- the Riemann Hypothesis has been proved;
- `u` has been formally identified with a global topological charge;
- non-orientable topology annihilates off-line zeros;
- analytic continuation or Euler product convergence is closed.

Those remain separate theorem obligations.

## Verification

```bash
lake env lean lean/InfoGeometry/Arithmetic/ZetaSymmetryAdaptedDefinitions.lean
lake build InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions
python3 tools/sympy/zeta_symmetry_adapted_definitions.py
```

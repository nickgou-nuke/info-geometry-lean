# Hadjiivanov Monodromy: Coefficient Alignment Before Hecke Readout

## Status

- Lane: Black Book bridge note
- Scope: binomial reduction of the real Hadjiivanov monodromy power law
- Guardrail: prove the coefficient alignment first; Hecke invariants come afterward as a corollary, not as a substitute proof

## Core claim

The monodromy power reduction is an operator identity in a commuting rotor-plus-nilpotent algebra:

`M_real(h) = R(-2πh) ∘ (I + c · N)`

with `N² = 0` and `R(θ₁) ∘ R(θ₂) = R(θ₁ + θ₂)`.

Once the rotor part and the nilpotent shear part are aligned correctly, the `n`-th power collapses to

`M_real(h)^n = R(-2πnh) ∘ (I + n · c · N)`.

This is the coefficient-alignment statement the repo uses.

## Distilled invariant

The invariant content is:

- rotor coefficients add in the angle,
- nilpotent corrections grow linearly,
- all quadratic and higher nilpotent terms vanish because `N² = 0`,
- the phase factor and the parabolic shear remain separated.

That is the operator-theoretic reason the logarithmic monodromy stays in the same Jordan form under iteration.

## Repo corridor

The owner surfaces already carrying this material are:

- `lean/InfoGeometry/Quantum/RealKCategory.lean`
- `lean/InfoGeometry/Canonical/HadjiivanovMonodromyProjection.lean`
- `lean/InfoGeometry/Canonical/LogCftMonodromyBridge.lean`
- `lean/InfoGeometry/Clifford/LogCftMonodromy.lean`
- `lean/InfoGeometry/Clifford/MonodromyFlowAdapter.lean`
- `lean/InfoGeometry/Canonical/HadjiivanovRindlerModularBridge.lean`

The key Lean theorem surface is:

- `RealKCategory.rotor_mul`
- `RealKCategory.rotor_pow_mul`
- `RealKCategory.nilpotent_binomial_expansion`
- `RealKCategory.monodromy_power_binomial`

The canonical alias surface is:

- `Canonical.HadjiivanovMonodromyProjection.HadjiivanovMonodromyPowerTheorem`

## Formal move

The proof spine is:

1. isolate the rotor factor `R`,
2. isolate the nilpotent factor `I + cN`,
3. use commutation to separate the powers,
4. use rotor additivity to get `R^n = R(nθ)`,
5. use `N² = 0` to collapse the binomial expansion,
6. combine the two coefficients and keep the Jordan form intact.

This is the correct order for the proof.

## Hecke readout

The Hecke relation is downstream of the monodromy identity.
Once the coefficient-aligned power law is fixed, the braid/Hecke comparison is a spectral and normalization readout:

- the phase factor records the scalar twist,
- the nilpotent shear records the Jordan correction,
- the Hecke side sees the same monodromy through its braid eigenvalue package.

So the repo should not use Hecke to prove the monodromy power law.
It should use the monodromy power law to justify the Hecke readout.

## Remaining debt

What is not yet written as a separate bridge theorem:

- an explicit Hecke-compatibility lemma that names the coefficient-aligned monodromy power law as the input to the braid relation
- a dedicated alias from the projection file to the `RealKCategory` operator theorem

But the mathematical core is already in the owner file.

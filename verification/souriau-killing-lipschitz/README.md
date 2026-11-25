# Souriau Killing Lipschitz bridge

This focused package checks the parent repository's actual Lean owners with
Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

Import the bridge directly (adapted from PR #426 to
`SouriauDoubledKreinLipschitzBridge` to avoid colliding with the pre-existing
`Cl(1,1)` Minkowski/Rindler `SouriauKillingLipschitzBridge` module):

```lean
import InfoGeometry.Canonical.SouriauDoubledKreinLipschitzBridge
```

## Mathematical content

For the doubled real Krein carrier and the existing bounded relative modular
generator `G := relativeModularKGenerator hMod`, the bridge identifies

```text
relativeModularDeriv hMod A = G * A - A * G.
```

The commutator norm is a native real seminorm. Its kernel is exactly the
commutant of `G`, and kernel membership is equivalent to being fixed by the
actual exponential conjugation for every real time. Both the derivation and
its norm are `LipschitzWith (2 * ‖G‖₊)`. A continuous linear probe composes
with this estimate with the extra factor `‖probe‖₊`.
Completeness is used by the native Krein structure and analytic flow results.
The algebraic commutator, ordinary norm bounds, and spectral-distance results
also apply to an incomplete real inner-product space.

Two additive readouts that distinguish a kernel observable give an unbounded
spectral-distance value set. Accordingly, bounded spectral-distance values
require agreement on the kernel. The code does not reinterpret an unbounded
real supremum as infinity.

The upper `ThermodynamicGenerator` definitions use this same construction at
`hMod := P.modularData.modularSeed ψ`. The focused module does not import that
larger owner or introduce a new theorem about its named predicate.

## Explicit doubled real Krein dynamics

The actual carrier is `DoubledSpace E = WithLp 2 (E × E)`, equipped with the
existing canonical `instKreinSpaceProdL2`. Its metric symmetry and pairing are

```text
ε(x, ξ) = (x, -ξ)
[(x, ξ), (y, η)] = inner ℝ x y - inner ℝ ξ η
A♯ = ε ∘ adjoint A ∘ ε.
```

The real clock axis `K = modular_j ∘ ε` is Krein-self-adjoint, while the
sheet swap `modular_j` is Krein-skew-adjoint. The bridge proves the exact
seed criterion

```text
G(h)♯ = -G(h)  ↔  K ∘ h♯ = -(h ∘ K).
```

A Krein-self-adjoint, phase-antilinear seed satisfies this criterion. The
existing exponential theorem then proves `IsKreinIsometry` for the actual
`modularTransportFlow`, including the signed coordinate-pairing invariant.
For a Krein-skew generator, `δ(A)♯ = δ(A♯)`, so both adjoint sectors are
preserved. The actual signed readout `A ↦ [δ(A) u, v]` is Lipschitz with
constant `(‖u‖₊ * ‖v‖₊) * (2 * ‖G‖₊)` in the associated Hilbert norm.

The concrete seed `h = -ε` gives `G = modular_j` and `δ(ε) = 2 • K`.
Both are proved nonzero on every nontrivial `E`, and the corresponding
exponential flow preserves the Krein pairing.

Every bounded state-flow operator has `LipschitzWith ‖flow‖₊`. The existing
Hilbert-self-adjoint, phase-linear seed regime separately yields Hilbert
`Isometry` and constant one. These are distinct preservation conditions;
the indefinite quadratic form is not a metric norm.

## Reproducible validation

From the repository root:

```sh
python3 verification/souriau-killing-lipschitz/check.py build
python3 verification/souriau-killing-lipschitz/check.py env lean \
  -DwarningAsError=true lean/InfoGeometry/Canonical/ConnesSpectralTripleBridge.lean
python3 verification/souriau-killing-lipschitz/check.py env lean \
  -DwarningAsError=true lean/InfoGeometry/Canonical/SouriauDoubledKreinLipschitzBridge.lean
python3 verification/souriau-killing-lipschitz/check.py env lean \
  lean/InfoGeometry/Canonical/SouriauDoubledKreinLipschitzBridgeAudit.lean > souriau-axioms.log
python3 verification/souriau-killing-lipschitz/audit.py --log souriau-axioms.log
python3 tools/quality/proof_proxy_staged_gate.py --strict \
  lean/InfoGeometry/Canonical/ConnesSpectralTripleBridge.lean \
  lean/InfoGeometry/Canonical/SouriauDoubledKreinLipschitzBridge.lean \
  lean/InfoGeometry/Canonical/SouriauDoubledKreinLipschitzBridgeAudit.lean
```

The final command screens staged source, so stage the reviewed task-owned
files before running it. Regenerate the audit after changing declarations:

```sh
python3 verification/souriau-killing-lipschitz/audit.py --write
```

When pinned Mathlib artifacts are missing, use the same locked package:

```sh
python3 verification/souriau-killing-lipschitz/check.py exe cache get
```

The wrapper holds the repository-wide build lock. Dependencies use ordinary
directories in the checkout's `.lake/packages`; no linked worktree or
symlinked Lake root is used. No dependency update is required.

The audit inventories every explicit public declaration in the two changed
mathematical owners, including the original Connes API and the concrete
zero-Dirac inhabitant. It validates their actual transitive axiom output
against `propext`, `Classical.choice`, and `Quot.sound`. Generated structure
fields and recursors are not separately inventoried.

This is focused verification, not certification of the repository's complete
default targets or every unused imported declaration. See the
[theorem contract](../../docs/SOURIAU_KILLING_LIPSCHITZ_CONTRACT.md) for exact
carriers, source provenance, and analytic boundaries.

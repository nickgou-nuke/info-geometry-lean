# Physics of the Riemann Hypothesis — theorem ladder and formalization boundary

Source: `/home/goutev/Downloads/drazin/1101.3116v1.pdf`, Schumayer--Hutchinson,
`Physics of the Riemann Hypothesis`, arXiv:1101.3116v1.

This note records the repo-facing formalization boundary.  The paper is a review
article, not a single theorem paper.  Full native closure of the whole paper would
require analytic-continuation theory, scattering theory, trace formulae, quantum
chaos, BEC thermodynamics, and Hilbert--Polya operator construction.  Those are
not silently packaged as proved here.

## Closed finite packet added now

Lean owner:

- `lean/InfoGeometry/Arithmetic/PhysicsRiemannHypothesisFinite.lean`

SymPy/Sage twins:

- `tools/sympy/physics_riemann_hypothesis_finite.py`
- `tools/sage/physics_riemann_hypothesis_finite.sage`

Closed finite claims:

1. Finite Euler-product algebra for primes `2, 3`, exponent `k = 2`, and exponent
   bound `3`:
   `prod_p sum_{a=0}^3 p^{-2a} = 17425 / 11664`.
2. Concrete nonzero Euler factors `(1 - p^{-2})` for small primes.
3. Mobius definition sanity checks: square-factor obstruction and divisor-sum
   cancellation for `n = 6, 12` in Lean; `n <= 100` in SymPy/Sage.
4. Direct finite prime-count data through `10` and `30` in Lean; through
   `10, 30, 100, 200` in SymPy/Sage.
5. Finite Mertens data through `10` in Lean; through `50` in SymPy/Sage.

These are genuine kernel-/CAS-checked finite arithmetic statements.  No `axiom`,
`sorry`, `_True`, certificate field, or `True := by trivial` wrapper is used in the
new Lean module.

## Paper sections and proof status

### II. Historical background and mathematical necessities

Formalized finite/core fragments:

- Euler finite product shadow: closed in the new Lean/SymPy/Sage packet.
- Mobius definition and finite divisor cancellation: closed in the new packet.
- Prime-counting finite data: closed in the new packet.
- Existing analytic owner surface: `lean/InfoGeometry/Arithmetic/RiemannZetaEquivalences.lean`
  already contains kernel-checked mathlib-backed statements for:
  - completed-zeta parity in symmetry-adapted coordinates,
  - Euler product equals `riemannZeta` for `Re(s) > 1`,
  - Dirichlet series equals `riemannZeta` for `Re(s) > 1`,
  - eta L-function bridge on `Re(s) > 1`.

Open / not claimed here:

- analytic continuation construction itself beyond existing mathlib imports,
- RH,
- explicit formula for prime counting via nontrivial zeros,
- Riemann--von Mangoldt asymptotic as a native repo theorem unless separately
  located and checked.

### III.A Classical mechanics

Paper content: billiards / chaotic mechanics analogies, periodic-orbit language,
and Mobius/random-walk style statements.

Closed here:

- only finite Mobius and prime-counting arithmetic checks.

Open / not claimed:

- billiard-flow spectral statements,
- trace-formula equivalence,
- RH equivalences through dynamical asymptotics.

### III.B Quantum mechanics

Paper content: Hilbert--Polya motivation, scattering-state and bound-state
models, Berry--Keating `xp` heuristics, zeta on the critical line.

Closed here:

- no new operator theorem.  Existing socket/bridge files in the repo must be
  audited independently before any promotion.

Open / not claimed:

- a self-adjoint operator whose spectrum is exactly the nontrivial zeros,
- scattering-amplitude equivalence to zeta,
- Berry--Keating boundary-condition closure,
- any proof of RH from a physical Hamiltonian.

### III.C Nuclear physics

Paper content: random-matrix / spectral-statistics analogies.

Closed here:

- no new random-matrix theorem.

Open / not claimed:

- GUE statistics as a native theorem,
- asymptotic zero-spacing laws.

### III.D Condensed matter physics

Paper content: quasi-crystals, Lee--Yang style analogies, and zeta-like structures.

Closed here:

- no new condensed-matter theorem.

Open / not claimed:

- physical realization theorems or spectral equivalences.

### III.E Statistical physics

Paper content: primon gas / Bost--Connes / Bose--Einstein condensation style
partition functions and zeta poles.

Closed here:

- finite Euler-factor partition-function shadow.
- repo has existing files with primon/Bost--Connes names, but those require exact
  theorem-surface audit before closure claims.

Open / not claimed:

- thermodynamic-limit phase-transition theorem,
- BEC pole theorem as a native closed statement unless separately verified,
- KMS/Bost--Connes analytic closure.

## Next repair targets

A genuine full-paper program should proceed one owner slice at a time:

1. Audit existing `RiemannZetaEquivalences.lean` and primon/Bost--Connes files for
   remaining `sorry` / socket debt.
2. Promote only mathlib-backed zeta facts already closed by the kernel.
3. For every physics analogy, first create a finite exact verifier, then add a
   small Lean owner theorem, and keep the analytic/spectral statement as explicit
   open debt until proved.

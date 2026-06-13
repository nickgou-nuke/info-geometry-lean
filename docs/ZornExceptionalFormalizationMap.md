# Zorn / Clifford / Parafermion / Metriplectic Formalization Map

## Verified computational layer

The packet contains two exact SymPy validators that run without optional dependencies:

- `tools/sympy/zorn_split_octonion_invariants.py`
  - verifies Zorn conjugation, trace, norm, quadratic characteristic identity;
  - verifies symbolic left/right alternativity;
  - exhibits explicit non-associativity;
  - verifies idempotent and nilpotent potency boundaries.

- `tools/sympy/clifford_braiding_exact.py`
  - verifies the Clifford braid generators `B_i=(1+e_i e_{i+1})/sqrt(2)`;
  - proves exact `B_i^2=e_i e_{i+1}`, `B_i^4=-1`, `B_i^8=1`;
  - proves adjacent Artin relation and far commutation in an exact symbolic Clifford engine.

## Optional package surface checks

- `tools/python/clifford_package_braiding_smoke.py`
  - optional `clifford` package check against the exact Clifford braid relations.

- `tools/python/galgebra_pseudoscalar_smoke.py`
  - optional `galgebra` package check of the Cl(3,0) pseudoscalar complex-structure shadow `I^2=-1`.

These are smoke tests only. The exact authority is the SymPy symbolic implementation.

## Sage / GAP witnesses

- `tools/sage/zorn_split_octonion_invariants.sage.py`
  - exact rational checks over `QQ`.

- `tools/gap/zorn_split_octonion_invariants.g`
  - exact rational checks with `QUIT;` included for non-interactive build pipelines.

## Lean layer

- `lean/InfoGeometry/Algebra/ZornVectorMatrix.lean`
  - defines Zorn matrices, dot/cross, trace, norm, conjugation, and non-associative multiplication;
  - deliberately does not install a `Ring` instance.

- `lean/InfoGeometry/Algebra/CliffordBraidingInterfaces.lean`
  - separates Majorana static generator systems from certified braid data;
  - separates static parafermion systems from additional Yang--Baxter braid data.

- `lean/InfoGeometry/Geometry/MetriplecticKahlerInterfaces.lean`
  - fixes the metriplectic Casimir hypotheses by making `H` and `S` fields;
  - places entropy positivity over an ordered scalar codomain;
  - keeps Kähler compatibility separate from the dual-bracket thermodynamic skeleton.

## Boundary conditions

This packet does not claim:

- that Zorn matrices form an associative ring;
- that norm preservation alone gives `G₂(2)`;
- that parafermion commutation alone gives a Yang--Baxter braid representation;
- that Clifford products automatically produce continuum metric/symplectic tensors without vector embedding and scalar projection data.

The intended next formal proof targets are:

1. Lean proof of Zorn conjugation and quadratic identities.
2. Lean proof of explicit non-associativity and alternativity.
3. Lean instance of exact Clifford braid data from a concrete Majorana system.
4. Exact Fibonacci `F/R` braid validator over a cyclotomic field.
5. Split Albert cubic norm and Freudenthal rank skeleton.

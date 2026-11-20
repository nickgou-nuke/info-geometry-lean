# Holographic white paper: theorem contract

## Intake and scope

Source: Marco Gericke and Myo Oo, *Complete Holographic White Paper*,
version 6.1, Full Integration Edition (QIH-Enhanced), 48 pages. The cover is
dated 20 February 2026; PDF metadata records creation on 10 March 2026.
The user supplied `Complete_Holographic_White_Paper_v6_1_actual.pdf`.
SHA-256: `c1c8750e74207af5ee17a2ea796793b5c07476bead7dab76f3dbaeea10bcf478`.
The original attachment is retained separately from this source repository.

Repository base: `08c34e03f610b452e03422037949196dc7d92d6d` (`main`).
Keep Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` unchanged.

This task extracts explicit mathematical consequences and countermodels.
Reported experimental fits and physical identifications are source claims,
not theorem assumptions to be silently promoted into derived physics.

## Owner search and selected carriers

The bounded search covered canonical `lean/InfoGeometry` owners, related
`lean/Omega` names, exact definitions and consumers, and the pinned Mathlib
source. No graph-index freshness or exhaustive repository verification is claimed.

| Source atom | Carrier and exact target | Existing authority | Scope |
|---|---|---|---|
| Binary distinction, pp. 7-9 | Idempotent in the noncommutative endomorphism ring of a module | Related owner: `Core.PeirceDecomposition`; native linear-map algebra | Construct the recoverable corner from encoding/decoding |
| Boundary encoding, section 2.5, pp. 12-13 | Linear maps `E : Bulk -> Boundary`, `D : Boundary -> Bulk`, with `E D = id` | Mathlib `LinearMap`, kernels, ranges, linear equivalences; compare `OperatorAlgebra.CoisometricCoarseGraining` | Construct `D E`, retained/hidden decomposition, and faithful ordered operator lift; full recovery requires additional injectivity |
| Edge transport, sections 5.2-5.3, pp. 18-20 | Native quiver paths labeled by arbitrary real square matrices | `Canonical.OperatorContentNetwork.PathTransport` | Extend to finite weighted path amplitudes and cyclic trace readout; keep matrix order |
| Finite histories, section 5.11, p. 26 | Functions from a finite edge/time product to `ZMod 4` | Native finite function cardinality | A finite time horizon is explicit; no continuum path integral |
| Curvature and metric, sections 6.1-6.2, p. 29 | Real matrices, finite differences, finite weighted sums | `OperatorAlgebra.RealMatrixSplit`; native self/skew adjoint split | Prove skewness and the obstruction to a nonzero skew metric correction |
| Prime residues, sections 2.4 and 5.6 | Native `Nat.Prime`, `ZMod`, CRT | Mathlib prime arithmetic and `ZMod.chineseRemainder`; compare `Canonical.FiniteHeisenbergCRT` | Necessary residue constraint and composite counterexamples; no continuous gauge-group selection |
| Structural monoid necessity, section 4.1, p. 16 | Native `Multiplicative ℕ` with generator `ofAdd 1` | Native `Irreducible`, divisibility, list products | Prove unique finite factorization and unbounded powers with exactly one irreducible |
| Hyperboloid/sphere, p. 9 | Four real coordinates | Native real ordered-field arithmetic | Exact circle intersection and noncardinal point |
| Information budget, section 5.9, p. 25 | Explicit real rates and positive scales | Native square root and real inequalities | Conditional square-root formula and speed bound; no Lorentz-group derivation |
| Causal inequality, section 5.10.2, p. 26 | Nonnegative real distance | Ordered-field cancellation | At effective speed one, the printed inequality forces distance zero |

## Proof dependencies

Only actual mathematical implications count as edges:

1. Boundary consistency `E D = id` implies injective `D` and idempotent `P = D E`.
2. This identity yields an explicit linear equivalence
   `Bulk ≃ₗ Boundary × ker E` and identifies recoverable states with `range D`.
3. The same identity makes `A |-> D A E` an injective, multiplication-preserving
   native non-unital ring homomorphism of boundary endomorphisms into the bulk
   corner. Its image is exactly `P X P = X`, and it maps the boundary identity to `P`.
4. Full recovery `D E = id` additionally forces injective `E`; finite-dimensional
   capacity follows from that injectivity.
5. Existing ordered path transport gives endpoint gauge covariance of finite
   amplitudes. On loops, native cyclic matrix trace yields gauge invariance.
6. Finite differences give skew matrices; their finite weighted sum remains
   skew. A symmetric background plus a nonzero scaled skew term is symmetric
   exactly when that term is zero.

The arithmetic, quadratic intersection, and rate-budget results are separate
branches. No map deriving a Standard Model gauge group, spacetime metric,
Einstein equation, or entropy area law from their analogy is supplied.

## Explicit open or rejected claims

- The intersection on p. 9 is a circle; selecting four cardinal points requires
  additional data. The rays at 60 and 300 degrees are not antipodal.
- Residues 1 and 5 modulo 6 include composites. Unique factorization and
  unbounded powers do not alone imply prime-number-theorem asymptotics.
- Reconstruction requires hypotheses on encoding. A fixed-point condition
  alone gives no entropy scaling exponent or physical area law.
- Phase-weighted infinite sums require reality/convergence hypotheses. Square
  summability alone is not a trace-class criterion for diagonal operators.
- Finite matrices, finite path sums, and finite history counts do not construct
  a continuum limit, a spin double cover, a Hilbert-space quantization, or a
  gravitational field equation.
- The field strength in Eq. 30 is skew. Eq. 31 therefore cannot give a
  nontrivial symmetric metric perturbation in the stated form.
- The printed causal diamond at `c_eff = 1` has zero spatial extent.

## Acceptance contract

Focused imports, the required copyright header, complete proofs, no custom
axioms or proof holes, and only `propext`, `Classical.choice`, `Quot.sound` in
the declaration axiom audit. Preserve noncommutative multiplication.
Run the maintained locked source-closure checker against the exact pinned
runtime, inspect warnings, run placeholder and semantic gates, and obtain
independent source review and verification. Report this selected closure
separately from the root package build and from unformalized physical claims.

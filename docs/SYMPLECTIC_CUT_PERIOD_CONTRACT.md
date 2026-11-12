# Real symplectic cut moments and periods

## Source and intent

Task: `real-symplectic-cuts`. Base: `a392af178af1fe2bcba2ba39eb405700c6ee103c`.

Luca Cassia, Pietro Longhi, Maxim Zabzine, *Symplectic Cuts and Open/Closed
Strings I*, Communications in Mathematical Physics **406:15** (2025),
DOI [10.1007/s00220-024-05190-5](https://doi.org/10.1007/s00220-024-05190-5).
The user supplied `Symplectic_Cuts_and_OpenClosed_Strings_I.pdf` (51 PDF pages).
SHA-256: `b81a2cd47ba87bb26c82f7993859238818b326826d0eeb3242375b2e062fb84b`.
Page references below use printed paper pages. The source PDF is not republished.

This contract records the intended native Lean statements before owner edits.
It is not a compilation certificate. Final acceptance requires the focused build,
complete declaration axiom audit, independent semantic audit and separate QA.

## Dependency order and exact targets

1. **Real Hamiltonian structure** (Section 2.1, pp. 8–10).
   On a real inner-product space with a bounded real-linear operator `J`, assume
   `J ∘ J = -id` and skew-adjointness. Construct the continuous bilinear form
   `ω(u,v) = -2 * inner (J u) v`; prove alternation, nondegeneracy and the actual
   Fréchet derivative identity `D (fun z => ‖z‖²) z u = ω(J z,u)`.
   The real rotation family `cos(t) id + sin(t) J` has the group law and preserves
   this moment. No centrality of `J` is assumed.
2. **Signed auxiliary moments** (Section 2.2, pp. 10–12).
   Construct `J(x,y)=(-y,x)` from the existing doubled-space exchange/grading
   operators, with energy `‖x‖² + ‖y‖²`. Establish actual derivatives and the
   product Hamiltonian identities for `μ(m) - energy(w)` and
   `μ(m) + energy(w)`, conditional on the base moment identity. The ordinary
   product norm is not substituted for this energy.
3. **Classical real density** (Section 3.1, equations (3.5)–(3.7), pp. 20–21).
   For real `a,b,d > 0`, define
   `H(c) = exp(d*c)/(a*(b+d))` for `c ≤ 0`, and
   `H(c) = exp(-b*c)/(a*(b+d))` for `c ≥ 0`.
   Prove positivity, continuity, integrability and
   `∫ c, H(c) = 1/(a*b*d)`. Prove the two one-sided derivatives at zero and
   their incompatibility with differentiability there.
4. **Logistic transport and quantum density** (Section 3.2,
   equations (3.9), (3.11)–(3.15), pp. 21–23).
   Prove the genuine change of variables through the existing logistic map,
   using native Mathlib Beta density and its normalization. Derive
   `HD(c) = Gamma(a)*Gamma(b+d)*exp(d*c)/(1+exp(c))^(b+d)`, positivity,
   integrability and `∫ c, HD(c) = Gamma(a)*Gamma(b)*Gamma(d)` for
   `a,b,d > 0`. Prove smoothness and the differential identity
   `HD'(c) = (d-b*exp(c))/(1+exp(c))*HD(c)`, hence the stated real
   Picard–Fuchs equation. Parameters and theorem statements remain real;
   native Mathlib dependencies may use complex analysis internally.

These are analytic and real operator claims, not a finite numerical witness.
Native definitions and theorem types, rather than the number of declarations,
determine the accepted scope.

## Existing owners and native APIs

- `Canonical.RealMirrorComplexStructure`: the existing square-minus-identity
  predicate on real-linear maps.
- `Geometry.ParaHessianMixedPotential`: real doubled-space exchange/grading,
  continuous maps and actual Fréchet derivative patterns.
- `AmariBinarySimplexBridge` and `LogOddsSimplexGeometry`: logistic/logit and
  its derivative. These owners are reused rather than redefined.
- Mathlib inner-product calculus, `JacobianOneDim`, Beta/Gamma distributions,
  and improper exponential integrals provide the analytic foundations.
- The central-complex-structure operator owner is not used to impose an
  unrelated centrality hypothesis on the Hamiltonian operator.

The bounded lexical search for symplectic-cut and quantum-Lebesgue owners is
not asserted to be an exhaustive absence proof. Candidate authors inspect the
relevant owners and imports before integration.

## Source corrections and open debt

- A level-set inequality is not a reduced symplectic manifold. Smooth quotient
  structure, descent/nondegeneracy of the reduced form, boundary divisor and
  gluing require separate proofs. The boundary is `μ⁻¹(c)/U(1)`, not the raw
  level set. Differential regularity alone does not establish a free action.
- Integrating the explicit classical density does not prove its identification
  with the pushforward of the weighted positive-orthant measure. That density
  identification remains open unless separately included with a full proof.
- Integer charges need rank and lattice-primitivity conditions for an effective
  embedded torus action. The kernel/cokernel descriptions in (2.30)–(2.31)
  require an explicit lattice isomorphism. Rank alone does not make an orthant
  intersection a half-line.
- Calabi–Yau charge sums do not imply Ricci-flatness of the induced metric.
- The closed real quantum density is not a formalized Coulomb contour integral,
  GLSM partition function or Gromov–Witten generating function. Complex
  monodromy, branch/path choices, mirror maps and superpotential normalization
  remain open. Equation (6.8) is written with `∼`, not an exact equality.
- Positive real parameters cannot simultaneously satisfy their zero-sum
  specialization. That passage requires different analysis.
- No implication to Kerr horizons, Tomita theory, Peirce projectors, supercolor
  or quantum gravity is claimed.

## Review and validation responsibilities

- Generation: root (classical density and integration),
  `cut_moment_candidates` (Hamiltonian candidates),
  `cut_quantum_candidates` (transport/quantum candidates).
- Independent A-A: `cut_intake_audit`, source/semantic review, no owner edits.
- Independent QA-A: a distinct non-authoring agent after integration.
- Preserve Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`,
  and all remaining dependency pins. Respect the shared build lock and preserve
  existing caches. Focused CI may provide isolated compiler capacity.
- No `sorry`, `admit`, custom axioms, `native_decide`, unsafe proof bypasses or
  vacuous certificates. Every new declaration is included in a fresh axiom
  inventory; permitted foundations are `propext`, `Classical.choice`,
  `Quot.sound`.
- Acceptance records will distinguish the focused verified import closure from
  repository-wide checks and record any unrelated baseline failures.

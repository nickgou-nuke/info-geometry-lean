# Typed reconstruction of the split-atom brainstorm

## Status and scope

This change reconstructs a consistent mathematical program from the supplied
`Pasted markdown(20260905-025802).md`. It does not purport to recover a person's
literal thought process. Equations are retained only after their carriers and
operations have been separated.

**Verification status at authoring: full Lean proof scripts are supplied, but
Lean elaboration/kernel verification has not been run in the authoring
container.** Neither Lean nor Lake is installed there. The 42 exact SymPy
regression checks passed; they are not a substitute for Lean. The PR must
remain a draft until the narrow build and the transitive axiom audit pass.
There are no new `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide` declarations.
An import may still expose pre-existing defects; the audit is designed to
report rather than conceal those defects.

Entry point: `InfoGeometry.Canonical.SplitAtomReconstruction`.

The repository's pinned Lean/Mathlib v4.28.1 configuration is unchanged. Existing
files, other PRs, global import lists, and dependency manifests are unchanged.
The existing library glob discovers the new modules.

## 1. The Clifford atom and the correct module

Reuse `InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat`, the existing actual
algebra equivalence from Mathlib's `CliffordAlgebra q11` to `M₂(ℝ)`. Do not
infer that equivalence merely from the square of the volume element.

The convention in the supplied source is

    I = [0 1; -1 0], J = [1 0; 0 -1], K = I J = [0 -1; -1 0].

`SplitAtomInvolutions` proves the entire multiplication table, and explicitly
relates this `I` to the negative of the existing `HypercomplexTriad.I`. The
existing Peirce projectors and nilpotent raising matrix are reused. The
missing raising expansion is `N = (I-K)/2`, and the full operator decomposition
is `A = P+ A P+ + P+ A P- + P- A P+ + P- A P-`.

These are associative algebra identities. They do not by themselves define a
para-hyper-Kähler manifold. An involution alone need not have equal-rank
positive and negative eigenspaces. The projector's grading is specified by
`J`; it must not silently be identified with the Clifford grade involution,
which is represented here by conjugation with the volume element (equivalently
with `K`).

The ordinary unit group of `M₂(ℝ)` is `GL₂(ℝ)`. Determinant-one units form
`SL₂(ℝ)`, a proper restriction. Split quaternions and split octonions are
composition algebras with zero divisors, not division algebras. Group-component
claims such as the source's `Spin(1,1)` formula are not inferred from generator
squares or imported as hypotheses.

## 2. Punctures, arithmetic modular generators, and the logarithmic coefficient

`AnharmonicPunctures` uses the actual subtype `{z : ℂ // z ≠ 0 ∧ z ≠ 1}`.
The functions `tau(z)=1-z` and `sigma(z)=1/z` preserve that subtype; they are
bundled as `Equiv.Perm`, and their involution, braid, and order-three relations
are proved. This supplies the permutation relations; it does not rename this
carrier as `PSL₂(ℤ)` or assert a subgroup embedding.

The arithmetic matrices `S=[0 -1;1 0]` and `T=[1 1;0 1]` are separately
bundled in `Matrix.SpecialLinearGroup (Fin 2) ℤ`. Their underlying matrices
satisfy `S²=-1` and `(ST)³=-1`. The Möbius formula for this `S` is `-1/z`, not
`1/z`. Translation cannot act on the punctured subtype: the admissible point
`-1` is sent to `0`. The source's claimed `S₃ ⊂ PSL₂(ℤ)` is not used; a
level-two quotient construction is a separate arithmetic task.

Holomorphic `1-z` fixes only `z=1/2`. Reflection in the vertical line is the
antiholomorphic map `1-conj(z)`. These are different transformations.

For `q(z)=z/(z-1)` the module supplies a native `HasDerivAt` proof and the
local identities

    q'(z) = -1/(z-1)^2,
    q'(z)/q(z) = f(z) = 1/z - 1/(z-1) = -1/(z(z-1)),
    tau* (f(z) dz) = -f(z) dz,
    sigma* (f(z) dz) = -dz/(z-1).

The pullbacks include the derivatives of the coordinate transformations.
There is no single-valued global logarithm asserted on the punctured carrier.
The matrix coefficient `(f(z)/2) J` takes values in the **complexified** Cartan
line in `M₂(ℂ)`. Pairwise commutation and vanishing Lie brackets are proved.
This is not a global holonomy, residue-integral, or KMS theorem.

## 3. Clifford operations versus physical CPT and particle-hole symmetry

With the source's precise matrix convention, the corrected operations are

    grade(A)              = K A K,
    reversion(A)          = J Aᵀ J,
    CliffordConjugation(A)= -I Aᵀ I.

`SplitAtomInvolutions` identifies the first two with Mathlib's **native**
`CliffordAlgebra.involute` and `CliffordAlgebra.reverse` through the existing
Clifford equivalence. Reversion is antimultiplicative. Clifford conjugation
is grade after reversion and satisfies `A conjugate(A) = det(A) 1`.
The negative of an inner automorphism sends `1` to `-1`; it is not unital.
No one of these maps is declared to be relativistic CPT or antiunitary time
reversal merely because it is involutive.

`SplitAtomParticleHole` instead works on the complex spinor module `ℂ²` and
uses `C(v₀,v₁)=(conj(v₁),conj(v₀))`. It is bundled as a real-linear equivalence,
and its complex-antilinear law and conjugation of the Hermitian pairing are
proved. For the explicit Hermitian family `H_e=diag(e,-e)`, `CH_e=-H_e C`.
A nonzero eigenvector at a real eigenvalue is consequently paired with a
nonzero eigenvector at the negative eigenvalue. The eigenvector premise is
ordinary input data; particle-hole covariance is proved for this family,
not postulated for an arbitrary Hamiltonian.

## 4. Neutral metric, alternating forms, and what dissipation requires

`FlatSplitQuaternionGeometry` uses the four-dimensional regular module
`M₂(ℝ)`, not the two-dimensional real spinor module. It constructs the native
`LinearMap.BilinForm` given by the polarization of the determinant:

    g(A,B)=(A00 B11 + A11 B00 - A01 B10 - A10 B01)/2.

It proves symmetry, nondegeneracy, `g(A,A)=det(A)`, and the coordinate formula
`g(a1+bI+cJ+dK,a1+bI+cJ+dK)=a²+b²-c²-d²`. Left multiplication by `I` is an
isometry; left multiplication by `J` and by `K` is an anti-isometry. Each form
`omega_u(A,B)=g(uA,B)` for `u=I,J,K` is alternating and nondegenerate.

Two direct obstructions guard the interpretation. A symmetric `2x2` metric
compatible with both the specified `I` and `J` must vanish. The nonzero
`K`-form is not symmetric and has `omega_K(A,A)=0`; it cannot be the positive
Onsager tensor claimed by the source.

`FiniteOnsagerGram` provides a separate, genuinely positive construction on
finite real coordinate spaces. For arbitrary real matrices `A` and `R`,

    xᵀ ((A-Aᵀ)x + RᵀRx) = sum_i (Rx)_i² >= 0,
    xᵀ RᵀRx = 0 iff Rx=0.

No positivity hypothesis is substituted for this conclusion. Positivity is
proved from the Gram factor `R`. A physical entropy-production theorem would
add the evolution, entropy, degeneracy conditions and sign conventions; those
are not consequences of the split-quaternion algebra alone.

This PR stops at the flat tangent-space algebra. It does not assert a smooth
manifold connection, parallelism, closed differential forms, holonomy
reduction, Ricci-flatness, self-duality, or a Yang--Mills/string interpretation.

## 5. Positive density and the two time conventions

`SplitAtomThermalBoundary` constructs

    rho_eta = diag(exp(eta),exp(-eta))/(exp(eta)+exp(-eta)), eta real.

It proves both weights positive, their sum equal to one, both inverse laws,
normalization of the **existing** `thermalState`, reality and nonnegativity
of the expectation of `A†A`. The inverse premises of the existing
`kms_condition_beta_one` are discharged for this density.

The existing owner uses the physical convention `tau_t(A)=rho^(-it) A rho^(it)`
and the upper imaginary boundary `tau_i(A)=rho A rho^(-1)`. Its finite trace
identity is `phi(A tau_i(B))=phi(BA)`. For the opposite convention, whose
upper boundary is `rho^(-1) A rho`, the module proves
`phi(sigma_i(A) B)=phi(BA)`. One cannot freely switch the sign of modular time
while keeping the same boundary-order convention.

These are finite matrix boundary identities. The source's complex exponential
`exp((eta+i theta)J)` is not generally a positive density. A faithful density
matrix and the Tomita modular operator are also different carriers; in the
finite Hilbert--Schmidt realization the latter acts by left and right density
multiplication. No faithful-normal-state theorem, analytic strip condition,
automatic physical temperature, or `beta=2*pi` consequence is asserted here.

## 6. The tower and exceptional-algebra boundary

The existing `BottPeriodicity.splitBottStep` remains the owner of the graded
tensor factorization. `SplitAtomDoubling` adds identities valid over any
associative ring:

    repeated(a)=diag(a,a), twisted(a)=diag(a,-a),
    twisted(a) twisted(b)=repeated(ab).

The repeated map is a native ring homomorphism. The twisted old generators
anticommute with both new off-diagonal generators, whose squares are `+1`
and `-1`. The old anticommutator is preserved on the repeated diagonal.
These are the concrete sign corrections required before an ordinary block
matrix representation can implement the graded step.

The new `MatrixModel n` is explicitly just a matrix carrier; it is **not** a
new definition of the repository's Clifford algebra. Its dimension is `4^n`.
`SplitAtomCarrierObstructions` uses the actual existing Zorn and Albert bases
to exclude linear equivalences `M₈(ℝ) ≃ ZornVectorMatrix ℝ` (64 versus 8) and
`M₁₆(ℝ) ≃ H3Zorn ℝ` (256 versus 27). This does not exclude spinor actions,
embeddings, multiplication tensors, or triality.

No eight-dimensional nonassociative product is obtained by relabeling an
associative tensor power. The magic-square table in the source is not accepted
as an input theorem, and the exceptional algebras are not defined as tensor
products or renamed matrix spaces. Lie brackets, triality, real forms and
exceptional identifications require their own construction and proofs.

## Exact next development tasks

After compiler repair and axiom checking, the next local extensions are:

* package the puncture permutations as a faithful action of `S₃` and construct
  the separate level-two arithmetic quotient;
* extend the sign-twisted block identities via `CliffordAlgebra.lift`, prove
  generation and injectivity, and connect the resulting all-stage matrix
  equivalence to the existing graded tower;
* put the neutral tangent model on a flat manifold and prove the differential
  hypotheses rather than importing holonomy or curvature conclusions;
* construct and verify the analytic finite modular flow and then its actual
  modular-operator realization, keeping the two sign conventions explicit;
* use the existing nonassociative owners for triality/Albert/F4 development.
  In particular, this PR does not close the independent scalar trace bridge
  or all-derivations generation problem from PR #137.

These are documented tasks, not Lean parameters carrying the desired missing
conclusions. No theorem in this change assumes an exceptional classification,
a KMS state condition, metric positivity, or the claimed tower equivalences
in order to return that same conclusion.

## Reproduction

From an otherwise idle configured repository, with its pinned dependencies
already available:

    bash scripts/quality/check_split_atom_reconstruction.sh

This performs a narrow aggregate build and prints the transitive axiom sets of
all new theorems. Only `propext`, `Classical.choice`, and `Quot.sound` are
accepted. It does not run `lake update`, clean a cache, or edit the manifest.
The exact symbolic regression is independently reproducible with

    python3 tools/sympy/check_split_atom_reconstruction.py

The committed symbolic report describes those 42 checks only. Compiler and
axiom results must be recorded separately before marking the PR verified.

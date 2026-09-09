# Reconstruction after source-owner search

## Basis and verification

The target is the newly supplied `Pasted text(20260905-170709).txt`:
spin-network/chirality prose, graph Dirac--Hodge code, real square-minus-one
symmetry, cycle thermodynamics, and a scalar-gap doubled operator.
The search map is `DIRAC_HODGE_REUSE_MAP.md`. Code owners were inspected
before implementing new proofs. Existing Dirac--Hodge and partner-orthogonality
modules are not duplicated.

The entry point is:

```lean
import InfoGeometry.Canonical.ProjectiveGraphZornBilayer
```

The field carrier remains the existing `OperatorZornMatrix A`, definitionally
`NCZornElement A`. Its multiplication is unchanged. The coefficient algebra
A may be noncommutative and is not assumed finite-dimensional. The finite graph
is inherited from the attachment and the repository graph owner; its vertices
are configuration/state labels, not points of an assumed external spacetime.

The existing positive-ray quotient is the finite statistical state carrier.
Normalization is a section through that quotient, not a replacement ontology.
Only the new Schnakenberg constructor uses the unweighted Euclidean edge
pairing, stated explicitly. This is not the indefinite split-Zorn norm and not
a claimed unique information metric on all quantum states.

**Status:** complete proof scripts, not kernel-verified in this environment.
The native launcher was actually run and returned exit 2 because `lake` is
unavailable. Python and Bash syntax checks passed, the new-source token scan
passed, and the independent exact checks passed. These are not Lean
elaboration or a transitive axiom audit. The parent modules are also
unverified here. Keep the PR draft pending the actual native check.

## 1. Existing Dirac--Hodge implementations

The supplied `Omega`, `d`, `delta` and `D` would duplicate already owned objects.
`Topology/DiscreteDiracHodge.lean` has concrete three-degree cochains and
chirality. `EckmannDiscreteHodge.lean` has adjoint/quadratic-form/kernel results.
The unmerged `Streaming/BipartiteGraphDirac.lean` at PR #148 also constructs
exactly the two-degree rectangular-incidence model in the new attachment.
Its file was fetched at its exact commit. It is not silently imported into a
parent branch that does not contain it.

These results do not identify a grading eigenspace with a retarded/advanced
propagator, select an arrow of time, or prove protected scattering. A graph
orientation and a parity operator do not by themselves supply that extra
structure. The SU(2), Pin-bundle and physical protection interpretations in
the opening source paragraphs are not claimed as consequences of these files.

## 2. The missing Schnakenberg construction is filled on its existing owner

`DirectedThermoGraph.SchnakenbergDecomposition` previously exposed a record
with gradient and cycle fields, reconstruction, and uniqueness. The theorem
`schnakenberg_decomposition` consumes such a record. It does not construct it.
The new `SchnakenbergHodgeConstruction` supplies that record using actual
Mathlib submodules and finite-dimensional orthogonal projection.

The owner's conventions are

    d phi(e) = phi(dst e) - phi(src e),
    incidence J(v) = sum_outgoing J - sum_incoming J.

Consequently

    <d phi,J>_edges = -<phi,incidence J>_vertices.

The sign differs from the attachment's incoming-minus-outgoing `delta`;
zero divergence is unaffected. The new code proves this equality by finite
sum interchange, then proves that `(range d)^orthogonal` is exactly the
existing `IsCycleFlow` predicate.

Let K = range d in the native Euclidean edge space. Define

    A_gradient = projection_K A,
    A_cycle = A - projection_K A.

Membership, reconstruction, and uniqueness are derived. In particular,

    exists_unique (B,C), IsGradientFlow B and IsCycleFlow C and A = B+C

no longer takes a decomposition as an argument. No connectedness or full-rank
incidence assumption is needed. Vertex potentials are not asserted unique:
constants on connected components remain their gauge freedom. Loops and
parallel edges are permitted by the existing source/target representation.

This is a graph cycle/cocycle split. On a graph with no two-cells, its cycle
space must not be mislabeled as the range of a two-form codifferential. The
three-sector exact/coexact/harmonic theory with faces is a separate existing
owner, not silently collapsed into this two-sector result.

For every divergence-free J,

    sum_e J_e d phi_e = 0,
    sum_e J_e A_e = sum_e J_e (A_cycle)_e.

This is an orthogonality statement. It does not need detailed balance, and
it does not imply nonnegativity for arbitrary independently chosen J and A.

## 3. Homogeneous states, actual fluxes, and relative production

`GraphCycleEntropy.graphAtRay` fills the existing graph's probability field
with `PositiveRayCore.gaugeSection q`. Its kinetic readouts use the owner's
actual stochastic current and flux affinity, not its uncalibrated stored
`flow` and `affinity` fields.

For positive rates and q=[w], with p=normalize(w):

    x_e = p(src e) k_e^+,
    y_e = p(dst e) k_e^-,
    J_e = x_e-y_e,
    A_flux,e = log(x_e/y_e).

The exact correction is

    A_flux = log(k^+/k^-) - d log p.

Its second term is an exact logarithmic ratio. Common positive rescaling of
w leaves the graphAtWeight adapter unchanged. For a conserved stochastic
current, its pairing with d log p is zero. The production therefore equals
the pairing with the constructed cycle component of the rate affinity.

Nonnegativity is reused from the owner's actual positive-flux theorem:

    sigma = sum_e (x_e-y_e) log(x_e/y_e) >= 0.

The new zero criterion proves

    sigma=0 iff x_e=y_e for every edge.

That theorem has no steady-state hypothesis; with positive rates it
characterizes edgewise balance for the chosen state. By contrast, steady
current alone does not imply zero production. Nor is sum J log(k^+/k^-)
guaranteed nonnegative away from stationarity.

The state-scale gauge and the kinetic-rate scale are kept distinct. Define

    traffic = sum_e (x_e+y_e).

A common kinetic rescaling k^+,k^- -> c k^+,c k^- multiplies both sigma and
traffic by c and leaves the flux log-affinity unchanged. The source therefore
exposes the scale-invariant comparison sigma/traffic, not a raw rate as an
absolute quantity. Its API is Option-valued: zero traffic gives `none`, not
a silently totalized physical zero. Positive rates and a nonempty edge set
prove that the ratio is defined. A physically admissible rescaling has c>0;
the cancellation theorem itself holds algebraically for every c nonzero.

## 4. Real partner separation, without a false involution or Pin identification

`HestenesKramersBridge` already owns the intrinsic phase partner K, K^2=-I,
and Hilbert orthogonality. It also records that K is an anti-isometry of the
Krein pairing. `HestenesRealStructures.KramersSymmetry` is a different
interface: phase-antilinear and Krein-isometric. These are not conflated.

The source calls a square-minus-one operator an involution and its proof
attempts to use a left-scalar pairing law on the second slot. The new module
does not repair this by adding more unverified pairing fields. It reuses the
native doubled carrier and completes the algebraic consequence:

    T^2=-I and Tx=cx, c real, imply (c^2+1)x=0, hence x=0.

This is instantiated with both the actual phase partner and the existing
KramersSymmetry interface. For nonzero x, Kx is not on span_R{x}. If a chosen
linear operator commutes with the actual phase axis, an eigenvector and its
partner have the same real eigenvalue. That compatibility is explicit, not
silently inferred from the square-minus-one law.

A real complex structure alone is not a complex antiunitary Kramers theorem.
No Pin bundle, scattering matrix, edge localization, or suppression of
backscattering is asserted from these algebraic statements.

## 5. The full operator-Zorn bilayer square

The source's Lean `D_BdG_sq` uses a real scalar Delta. Its algebraic cancellation
is appropriate to that specialization. The prose cannot transfer it to a
general operator-valued gap or infer a positive spectral lower bound merely
from nonzero coupling.

The new `OperatorZornBilayerDefect` works on two copies of the unchanged
nonassociative operator-Zorn module. For any real-linear D and independent
full Zorn couplings U,V, define

    B(X,Y) = (D X + U star Y, V star X - D Y),
    L_U X = U star X,
    C(D,U) X = D(U star X) - U star D X,
    as(U,V,X) = (U star V) star X - U star (V star X).

The exact native statement is

    B^2(X,Y) =
      (D^2 X + (U star V) star X - as(U,V,X) + C(D,U)Y,
       D^2 Y + (V star U) star Y - as(V,U,Y) - C(D,V)X).

The two ordered gap products are not identified. Their equality, an adjoint
relation between U and V, positivity, and self-adjointness are not postulated.
The attachment's U=V=Delta case is a specialization with both associators and
both gap commutators still present.

Only when D is the already constructed coefficient derivation delta_P does
its proved Leibniz identity yield

    C(delta_P,U)X = (delta_P U) star X.

The generic D is not assumed to obey Leibniz. In particular, a graph Hodge
Dirac operator on a different cochain carrier is not declared to be delta_P.
A genuine carrier/action comparison would need its own intertwining theorem.

The plain sheet swap S(X,Y)=(Y,X) is Mathlib's product linear equivalence. For
equal coupling Delta its anticommutator with B is

    (B S + S B)(X,Y) = (2 Delta star X, 2 Delta star Y),

so the source's involutive swap is not automatically particle-hole symmetry.
A nonzero Delta=nPlus(1) already has a nonzero zero mode (nMinus(1),0) for D=0.
Thus nonzero coupling alone cannot imply a spectral mass gap.

Finally the parent's positive projective expectation witness is reused rather
than rebuilt. With its full NC-Zorn X and pole E,

    Read_[2:1](L_(X star X) E - L_X(L_X E)).sigma_minus[2] = 1/3.

The associator defect survives normalization and positive expectation.
Expectations are applied after the products and their parentheses, never
factored into a product of scalar readouts. The example's real matrices are
coefficients, not an associative replacement of the Zorn algebra.

## Verification and next boundary

Run in a complete idle checkout at the parent plus this patch:

```sh
bash scripts/quality/check_projective_graph_zorn_bilayer.sh
```

The launcher uses the existing locked narrow-build entry point. It then
checks all explicit new declarations, including definitions, with native
`#print axioms`. Only propext, Classical.choice, and Quot.sound are allowed;
missing readbacks, compiler failures and audit warnings fail the gate.
No dependency update or cache cleaning is performed.

Independent exact diagnostics and manifest regeneration:

```sh
python3 tools/quality/check_projective_graph_zorn_bilayer.py
python3 tools/quality/audit_projective_graph_sources.py
```

The current local native attempt did not execute Lean. A successful build and
complete transitive axiom audit remain required. Independent symbolic and
finite-example checks, including freely noncommuting coefficients, establish
neither elaboration nor absence of transitive proof holes.

The added mathematical construction is the finite graph projection into the
existing Schnakenberg record. Further weighted/continuum/Type III state
geometry, a graph-Dirac-to-Zorn action intertwiner, a self-adjoint coercive
operator-gap theorem, and physical Kramers/Andreev scattering statements are
not installed as assumed conclusion fields. Existing archetypes are reused;
missing compatibility is left as a precise theorem to construct, not erased.

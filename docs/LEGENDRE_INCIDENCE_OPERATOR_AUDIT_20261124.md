# Legendre, incidence, and real operator reconciliation

## Revision, intake, and status

Source baseline: `fe24e350b08fdea04f74c0748ef9fd9417c47529` (main inspected on
2026-11-24). This report distinguishes inspected source from a newly executed
kernel check. It is not a whole-repository build certificate.

The user asked:

> legender-fenchel tranform pairs primari and dual spaces of the dual flat affine parakehler manifold which is mapped to a supergrassmanian in the codebase and supersymmetry at the deepest level with chiral parity supercharges x points grd x the dual lines legender trnform the legender product lifted to operators derivatives replaced by derivations operator n froms soureau primal dual dual flat operator spaces afine with symmetric antisymmetric conenctions commutators anticommutators and defects triple kantor products what was in the codebadebe and what can be cmplementeed points dual lines operators 4-vctors primal dual forward backward or the chiral absis sum difference sym andtisym there is something we miss like the twitors incidences like line incidences defining hyperplanes pluker geometry and grasmamn sumpergeometry parakehler manifold for the base homogenous coordinates for the cartan operator geometry geometry as invariants how can we reconcile the net of fragmenteed results sdoureau primal dual lift to operators of symmetry like those for the noether theorem killing field lipshitz grouop we had something what is it

External intake: the attached 220-slide Frédéric Barbaresco presentation,
`Thermodynamics_Informed_Neural_Network_T.pdf`, especially PDF pages 100 and
189. The attachment itself is not copied into the repository. Page 100 uses
the Massieu convention `Phi = -log Z`; page 189 states the GENERIC degeneracy
conditions in addition to skewness and positive semidefiniteness.

Classification: source audit and four focused mathematical owners connecting
actual Fenchel, Hessian-graph, real-dual-twistor, and Peirce constructions.
Kernel/build/axiom status is recorded separately below.

## Exact implementation contract

Contact owner: `lean/InfoGeometry/Twistor/FenchelContactIncidence.lean`.

Native objects and reused owners:

- A real normed vector space `E` and its continuous dual `E →L[ℝ] ℝ`.
- The ordinary real module `E × (ℝ × ℝ)` for homogeneous epigraph coordinates.
- `Geometry.fenchelGap` and `Geometry.FenchelYoungEquality`, without a duplicate
  gap definition.
- `Convex.fenchelConj`, whose real conditional supremum needs
  `BddAbove (Convex.fenchelSet f p)` for the Fenchel inequality.
- `Twistor.RealDualTwistor.Carrier`, `Incident`, and the native endomorphism
  `dyad : Carrier W → Module.End ℝ W`.

For arbitrary functions `f` and `fStar`, set

```text
P_f(x) = (x, f(x), 1)
ell_(p,c)(y,t,s) = p(y) - t - c*s
contactPair(f,fStar,x,p) = (P_f(x), ell_(p,fStar(p)))
Delta(f,fStar,x,p) = f(x) + fStar(p) - p(x)
```

The required exact statements are:

1. Both factors of `contactPair` are nonzero, even when `p = 0` or `E` is
   the zero vector space. The last point coordinate is `1`; the covector
   evaluates to `-1` on `(0,1,0)`.
2. Evaluation is `-Delta`; incidence is equivalent to Fenchel--Young equality.
3. The actual endomorphism `D = dyad contactPair` is nonzero and satisfies
   `D * D = (-Delta) • D`; hence `D * D = 0` iff equality holds.
4. When `fStar = Convex.fenchelConj f` and the support set is bounded above,
   `ell` is nonpositive on every affine epigraph point `(y,t,1)` with `f(y) ≤ t`.
5. Under that boundedness hypothesis, square-zero is equivalent to the
   selected affine support value being a greatest element of the support set.
6. From global `ConvexOn ℝ Set.univ f` and a local actual derivative
   `HasFDerivAt f p x`, derive the greatest-element assertion directly by
   restricting to affine lines. This derives boundedness and contact, then
   the nonzero dyad is square-zero. It requires neither a Riesz identification
   nor an assumed contact equality.
7. The last-coordinate functional `lambda(y,t,s) = s` satisfies
   `lambda(P_f(x)) = 1`. The native operator `P = P_f(x) tensor lambda` is
   idempotent. Derive `P D = D` and `D P = -Delta P`; at contact this gives
   `P D (1-P) = D`, an actual upper Peirce corner.

No convexity or differentiability hypothesis is required for items 1--3.
Calling an arbitrary `fStar` a conjugate would be unjustified. Item 4 is weak
separation; a supporting hyperplane with contact also needs equality. These
statements do not assert a quantization, a super-Grassmannian point, a global
manifold, a moment-map equation, or a physical supercharge.

The candidate preserves the full native endomorphism, rather than replacing
it by a scalar. Existing `dyad_frameAction` already provides contragredient
conjugation covariance. A general frame change need not preserve the chosen
epigraph normalization or constitute a Legendre transform of `f`.

The final projector/corner result supplies the exact idempotent and odd-corner
input for the existing ring-wide `PeirceSpine/Supercharge` identities. The
cut depends on `x` and the homogeneous chart; identifying it with one fixed
Zorn/Peirce chirality requires an additional intertwiner. The projector is
not asserted to be self-adjoint for any Hilbert metric. A paired supercharge
additionally requires a chosen lower corner; physical supersymmetry, dynamics,
and positivity do not follow from this construction.

## Existing source map

All paths below are relative to `lean/InfoGeometry/` on the baseline.

| Topic | Strong source owners | Exact scope |
|---|---|---|
| Fenchel duality | `Convex/FenchelConjugate`, `Geometry/LegendreDuality`, `Convex/Legendre` | Native continuous dual; real conditional supremum, boundedness-aware inequality and attainment; reusable gap/equality; convex differentiable first-order support derived by affine-line restriction. |
| Dual coordinates | `Geometry/DualFlat`, `Geometry/LegendreHessianInverse` | Actual `fderiv`/Hessian definitions; inverse gradient and continuous linear equivalence supplied in the respective interfaces. |
| Hessian graph | `Geometry/DualFlatKreinLegendreGraph` | Normalized neutral pullback equals the symmetric duality pairing; symplectic graph pairing is zero. Its last theorem is an isotropy alias, not graph maximality. |
| Actual examples | `Geometry/BinaryLegendreEntropyFlow`, `Lie/SplitOctonionParaHessianBridge` | Logistic graph with actual derivative and positive tangent metric; actual Zorn active sector with an indefinite mixed quadratic potential and its literal Hessian. |
| Real polarization | `Clifford/PhaseSpaceGeneralizedMetric`, `Clifford/ParaKahlerGeneralizedMetric` | Symmetric duality equivalence, exchange involution, B-field transforms; product with chirality has square `-1`. Positivity needs a separate hypothesis. |
| Graph and graded charts | `SuperGrassmannian/ProjectorGraphChart`, `GradedGraphChart`, `FreeSupermoduleChart`, `GraphChartCocycle`, `GradedGraphTransition` | Native graph submodules/projectors/quotients, degree-preserving chart, coefficient naturality, overlap and transition laws. Not a constructed global supermanifold. |
| Zorn Grassmannian | `SuperGrassmannian/ZornGraphChart` | Actual injective chart into `Module.Grassmannian R (ZornVectorMatrix R) 4`. |
| Point/covector and operator | `Twistor/RealDualTwistor`, `RealTwistorDualIncidence` | Nondegenerate real evaluation forms, full annihilator description, nonzero rank-one square-zero criterion, conjugation covariance. |
| Operator incidence | `Twistor/RealTwistorIncidence` | Graph/range/kernel description, projective incidence, intersection controlled by kernel of operator difference. |
| Klein/Plücker | `Twistor/PhaseNativePluckerBridge`, `Projective/ExteriorKleinTwoPlaneEquiv`, `Twistor/PluckerInfinityChart` | Actual null phase-to-Klein identity; real two-plane/projective Klein equivalence; explicit two-plane graph chart. |
| Chiral supercharges | `OperatorAlgebra/PeirceSpine/Supercharge`, `StarGrading` | Ring-wide graded Leibniz, square-zero odd operators, anticommutator equal to an inner derivation; separate star/adjoint laws. |
| Lie/Jordan operators | `OperatorAlgebra/LieJordanDualTransport`, `LieJordanCliffordDouble`, `LieJordanBoundaryCalculus` | Native endomorphisms and `LieAlgebra.ad`; ordered defects, real square-minus-one phase, genuine doubled operator. |
| Triple products | `Algebra/AssociativeHomotope`, `OperatorAlgebra/PeirceSpine/KantorCornerAnomaly` | Associative homotope, its Jacobi bracket, actual upper/lower corner closure and reference intertwiner. Generic full Kantor identities remain hypotheses in their separate owner. |
| Zorn derivations | `Algebra/Zorn/NativeStanDerivationBilinear` | Actual bilinear derivation-valued map with `D_(x,y)(z) = [[x,y],z] - 3(x,y,z)`. |
| Souriau affine symmetry | `Algebraic/CartanSouriauAffineCocycle`, `CartanSouriauMassieuDirectionalCalculus`, `Canonical/SouriauKKSContragredientBridge` | Actual action/cocycle laws, finite statistical directional derivative, bracket-preserving KKS covariance. |
| Noether/Killing/Lipschitz | `Canonical/NoetherInference`, `EmergentKillingField`, `Clifford/LipschitzWittRieszPrimary`, `RealLipschitzPin` | Infinitesimal bilinear invariance and conditional orbit relation; real matrix trace identity; actual Clifford-group homomorphism to quadratic isometries. |

## Necessary distinctions

### 1. Hessian graph, neutral nullity, and fixed chirality

On `V × V*`, use

```text
eta((x,p),(y,q)) = (p(y)+q(x))/2
omega((x,p),(y,q)) = q(x)-p(y)
Gamma(x,p) = (x,-p)
```

For symmetric `H`, `omega((u,Hu),(v,Hv)) = 0`, while
`eta((u,Hu),(v,Hv)) = H(u)(v)`. A positive Hessian graph is positive for
`eta`, not neutral-null. A skew map instead gives a neutral-null graph.

Moreover `Gamma(graph H) = graph(-H)`. Over the reals, fixed-grading
invariance of `graph H` forces `H = 0`. An ordinary Hessian graph should route
to an ordinary Lagrangian Grassmannian; the existing graded chart requires an
even map for its specified internal gradings.

The Geometry symplectic convention above is the negative of
`Quantum/DualFlatKreinGraph.symplecticPair`. A cross-owner Hamiltonian formula
must retain this sign.

### 2. Different Grassmannian dimensions

- A vector in `R^3 ⊕ (R^3)*` maps to `Lambda^2 R^4` (six coordinates).
  Its nonzero null ray gives a two-plane in `R^4`, hence `Gr(2,4)`.
- A Hessian on `R^3` has a three-dimensional graph in `R^6`, hence
  `LGr(3,6)`. Its exterior representative is in `Lambda^3 R^6` (20 coordinates).
- The Zorn graph chart gives a four-plane in an eight-dimensional carrier.

These maps are not interchangeable. Likewise, the real `2 × 2` determinant
has signature `(2,2)`, not Lorentz signature `(3,1)`. The separate
`Twistor/PluckerLorentzRealForm` uses a complex Klein carrier with a specified
real structure; it cannot silently replace the entirely real split chart.

### 3. Souriau signs and entropy

The actual finite statistical owner uses

```text
F(beta) = log Z(beta), dF = -Q, Hess F = Cov.
```

The presentation uses `Phi = -F`, `Q = dPhi`, and Fisher metric
`g = -Hess Phi`. At attained Fenchel contact,

```text
S(Q) = F(beta) + beta(Q) = -F*(-Q).
Hess_Q S = -g^(-1), when the inverse exists.
```

The positive inverse-Hessian theorem for the convex conjugate `F*` uses the
convex dual coordinate `eta = -Q`. It must not be relabeled physical entropy
with the same sign. A supremum Fenchel conjugate of the concave `Phi` is not
the intended thermodynamic transform.

### 4. Adjoint split, grading, and thermodynamic split

For a self-adjoint Peirce cut, matching corners by `Nminus = Nplus*` makes
`Nplus + Nminus` self-adjoint and `Nplus - Nminus` skew-adjoint. Both are odd
under parity. Their commutator and anticommutator are even. These are distinct
involutions and distinct decompositions.

In GENERIC, `zdot = L dE + M dS` conserves energy and produces entropy under
skewness of `L`, positive semidefiniteness of `M`, and the separate conditions
`L dS = 0`, `M dE = 0`. A symmetric/skew matrix split alone does not provide
those degeneracy conditions, a Poisson Jacobi identity, or a moment map.

For a noncommutative algebra, the ordered Leibniz rule is
`delta(ab) = delta(a)b + a delta(b)`. Adding Jordan multiplication to an inner
derivation introduces the exact defect `-2asb`, already retained in
`LieJordanDualTransport`.

## Completed connections and their exact contracts

### Actual C² potentials, graph geometry, and incidence

Owner: `Geometry/LegendreGraphGeometry.lean`.

For an arbitrary real module `V` and bilinear map `H : V →ₗ[ℝ] V*`,
`graph_symplectic_orthogonal` proves the actual submodule equality

```text
(graph H)^perp_omega = graph(H.flip).
```

Consequently, graph self-orthogonality is equivalent to the existing
`IsSymmetricDuality H`. A separate theorem proves maximality among isotropic
submodules. Neither statement needs a dimension hypothesis. The neutral form
on a symmetric graph is `2 * H(u)(v)` in the unnormalized twistor convention.
The real incidence space is proved equal to the coordinate-swapped graph by
an actual `Submodule.comap`, and fixed para-grading invariance is equivalent
to `H = 0` over the reals.

With `[FiniteDimensional ℝ V]`, the existing graph/source and graph/quotient
linear equivalences yield the correct dimension and a native
`Module.Grassmannian ℝ (V × V*) (finrank ℝ V)` point. Mathlib's index here is
quotient rank. The graph chart is injective.

For a real normed space `E`, the derivative statement is first made on
`E × (E →L[ℝ] ℝ)`. The explicit `continuousDualCarrierMap` then forgets
continuity in the dual value. Given an actual `HasFDerivAt p H x`,

```text
range(forgetContinuousDual ∘ D(id,p)_x) = graph(forgetContinuousDual ∘ H).
```

For a scalar potential `f`, the sole local analytic hypothesis
`ContDiffAt ℝ 2 f x` gives both the derivative of `fderiv ℝ f` and Schwarz
symmetry of its Hessian. The final corollaries therefore derive actual
symplectic self-orthogonality of the tangent range and, in finite dimension,
identify the Grassmannian point with that same range. Convexity, positivity,
and an assumed Hessian symmetry are not needed for these C² corollaries.

### Cotangent operators and the infinitesimal symmetry equation

Owner: `Geometry/CotangentOperators.lean`.

The existing contragredient `frameAction g` transports the full native graph
by the congruence `H^g = (g^-1)* H g^-1`. Symmetry and alternation are preserved.
For every native real endomorphism `A`, define

```text
AHat(v,p) = (A v, -p comp A).
```

The resulting lift is linear, injective, and bracket-preserving, bundled as
an actual `LieHom`. It commutes with the primal/dual para grading and satisfies
both infinitesimal neutral and symplectic invariance equations. Native
submodule preservation is equivalent to

```text
map(AHat, graph H) <= graph H  iff  H comp A + A.dualMap comp H = 0.
```

This is the constant-`H` infinitesimal invariance condition. It is not the
position-dependent Killing equation, which also differentiates the metric.

On the full algebraic dual carrier, `h_A(v,p) = p(A v)` has an explicit native
linear tangent coefficient `T_A(z)`. Its interpretation is justified by the
complete quadratic expansion

```text
h_A(z+t*w) = h_A(z) + t*T_A(z)(w) + t^2*h_A(w).
omega(AHat z,w) = T_A(z)(w).
T_B(z)(AHat z) = -h_(A*B-B*A)(z).
```

Thus commuting endomorphisms give an exact infinitesimal conservation
criterion. No topology on the full algebraic dual or integrated flow is
assumed. The Geometry/Quantum symplectic sign difference is a separate
explicit theorem. Ordered noncommutative products are retained throughout.

### Contact superderivation and explicit moving-frame transport

Owner: `Twistor/FenchelContactTransport.lean`, in the existing
`FenchelContactIncidence` namespace.

For the actual contact projector `P`, construct `Gamma = 2*P - 1` and prove
`Gamma^2 = 1`. At Fenchel equality the nonzero dyad `D` satisfies

```text
Gamma*D = D,  D*Gamma = -D,  Gamma*D*Gamma = -D.
delta(A) = D*A - (Gamma*A*Gamma)*D.
```

Here `delta` is a native real `Module.End` on the full noncommutative
endomorphism algebra. The existing Peirce A27/A28 owners yield `delta^2 = 0`
and the graded Leibniz law. Nonvacuity is proved by `delta(P) = -D`, hence
`delta != 0`. Global convexity and an actual local derivative produce this
nonzero square-zero operator for the actual `fenchelConj`, with contact
derived by the first contact owner.

A continuous linear equivalence of primal coordinates transports the actual
Fenchel conjugate through equality of its defining support sets. The lifted
homogeneous frame conjugates `P`, `D`, `Gamma`, and `delta` by a native
`conjAlgEquiv`. No boundedness assumption is needed for this equality of
identically transported real suprema.

Finally the explicit Mathlib transvection

```text
(v,t,s) -> (v+s*x, t+s*f(x), s)
```

sends the reference point `(0,0,1)` to `(x,f(x),1)`. It conjugates the reference
projector and grading to the moving ones. Under contact it also conjugates
the reference dyad with covector `(p,-1,0)` and its superderivation. The
reference pair is an algebraic contact normal form; the zero dual function
in that normal form is not asserted to be the Fenchel conjugate of the zero
primal function at every covector.

### Precise remaining boundaries

The implemented chain now has actual maps at the graph, incidence, frame,
Lie-action, and Peirce-superderivation steps. It does not construct global
inverse-gradient coordinates, a para-Kähler manifold atlas, a supermanifold,
a quantization map, or a pair of adjoint physical supercharges. The homogeneous
reference cut has its explicitly constructed carrier; identifying it with an
independently chosen Zorn cut still requires a separate intertwiner.

Specializing the cotangent action to an inner derivation or a corrected Zorn
derivation requires supplying that native endomorphism. An integrated
Noether theorem additionally requires an actual flow or group action and the
appropriate Hamiltonian assumptions. For dually flat connections,
`(nabla+nabla*)/2` and `(nabla*-nabla)/2` must be handled on their connection
and tensor carriers respectively; the operator star split does not construct
those geometric connections.

## Source defects excluded from the synthesis

`Canonical/CoordinateFreeSouriauDerivation.CoordinateFreeSouriau` requires
`inverseTemperature p = norm (beta p)` for **every** function
`norm : Tangent p → ℝ`. At any point, constant-zero and constant-one choices
contradict each other. The packet is uninhabitable when the base has a point.
It is not evidence for a constructed thermal Killing field.

`Canonical/CoordinateFreeSouriau.ScalarDerivation` assumes only a ring but
uses the commutative-order expression `a D(b) + b D(a)`. It should not serve
as the noncommutative derivation owner. Its `ConformalSouriau` also inherits
the zero metric-Lie-derivative equilibrium condition, forcing the conformal
factor to vanish wherever the metric has a nonzero pairing.

These are findings about the named packets. Stronger actual native
derivation, affine-cocycle, and Killing-invariance owners exist elsewhere and
are listed above.

## Validation record

The four owners expose 113 explicitly declared public definitions and
theorems. `verification/legendre-incidence/audit.py` generates the exact
`#print axioms` inventory, verifies that its source coverage is current, and
accepts only `propext`, `Classical.choice`, and `Quot.sound` in actual Lean
output. The focused package reads these canonical owners directly and retains
all root toolchain and Mathlib dependency pins.

Independent source reviews checked the actual graph and derivative claims,
C² Hessian symmetry, quotient-rank Grassmannian construction, nonzero contact
data, noncommutative product order, cotangent signs, Peirce theorem projections,
and conjugation/transvection APIs. Source review and kernel validation remain
distinct evidence. A final review record is maintained with the validation
package.

The strict OpenGauss source screen passes for all four owners and the audit
module with zero findings. Explicit scalar distributivity/additive proofs in
the cotangent owner keep the scalar computations distinguishable from the
retained noncommutative operator products.

### Historical environment result

The earlier contact-only attempts could not start `lake` (wrapper exits 126
and 127). That result was an executable-availability failure, not a Lean
proof failure. A pinned Lean 4.34.1 runtime and clean Mathlib dependency cache
were subsequently found in the shared workspace. The focused wrapper supports
an explicitly selected package root, verifies every dependency source revision
and tracked cleanliness before/after the run, and uses Lake's native location
override without changing tracked pins or linking Lake roots.

### Current verification status

The first local focused kernel build is queued on the maintained shared build
lock. The PR is prepared as a draft with focused CI so this execution boundary
remains explicit. No successful kernel result, push-gate result, or whole-
repository build certificate is asserted. Current commands and results are
recorded in `verification/legendre-incidence/VALIDATION.md`; update that record
with observed compiler and axiom results before promoting the draft.

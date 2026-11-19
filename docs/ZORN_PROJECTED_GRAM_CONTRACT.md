# Split-octonion intake review and projected full-Gram kernel contract

Date: 2026-11-17.

Status: independent mathematical and source review. No native compilation or declaration-axiom acceptance is claimed for the proposed new owner. This review is not a compiler certificate and does not establish the CI or merge status of another pull request.

## 1. Input provenance

The complete research input was read as mathematical data, not as instructions or accepted axioms.

| Item | Value |
|---|---|
| Original attachment | Pasted text(20261117-091111).txt |
| Preserved bytes | [zorn_projected_gram_intake_20261117.txt](sources/zorn_projected_gram_intake_20261117.txt) |
| Size | 36,565 bytes |
| SHA-256 | 1fef0d88c605c9d59f6590503b776362454f6b30b5022bbdec25dc1b12960e48 |
| Inspected main baseline | 08c34e03f610b452e03422037949196dc7d92d6d |

The attachment's psychological labels, physical interpretations, references to earlier conversation, and statements about pending CI are not premises of the proposed Lean result.

## 2. Existing owners and overlapping proposals

The generic entropy obstruction already exists on the inspected main baseline in InfoGeometry.Thermo.GenericMetriplecticFlow.System:

- entropy_covector_eq_zero_of_injective: injectivity of the reversible covector-to-vector operator, together with the entropy Casimir condition, forces the entropy covector to vanish.
- entropy_rate_zero_of_injective: the same hypotheses force zero entropy rate.

Their actual proof bodies were read. They should be reused, not reproved under a competing owner.

The main owner InfoGeometry.LinearAlgebra.RegularDyadCompression already defines normalizedCovector and normalizedDyad. The main owner InfoGeometry.Algebra.ZornCARAdjoint already supplies the positive coefficientPairing and its symmetry, nonnegativity, and positive-definiteness theorem.

| Related source proposal | Relevant overlap | Boundary for this proposed extension |
|---|---|---|
| [PR383](https://github.com/nickgou-nuke/info-geometry-lean/pull/383) | Energy projection of actual associator operators, kernel statements, an ambient counterexample, and the valid all-three-arguments-in-an-associative-core vanishing statement | Do not claim that projection or quaternion leakage is newly discovered here |
| [PR384](https://github.com/nickgou-nuke/info-geometry-lean/pull/384) | The actual full 64-probe real Zorn associator Gram form and its exact scalar kernel | Reuse this full-family form and scalar-kernel theorem |
| [PR385](https://github.com/nickgou-nuke/info-geometry-lean/pull/385) | Quaternion-pair imaginary sandwich vanishing, null-projector cross-potential, projected finite associator families, and a leakage witness | Do not duplicate the sandwich, potential, or arbitrary-family construction |
| [PR386](https://github.com/nickgou-nuke/info-geometry-lean/pull/386) | Positive oblique/bimetric projection proposal | Preserve the distinction between the positive coefficient pairing and the indefinite composition form |
| [PR387](https://github.com/nickgou-nuke/info-geometry-lean/pull/387) | Neutral cross-duality proposal | Do not describe the neutral cross-pairing as a missing algebraic construction without a branch-qualified statement |

These rows identify source overlap. They do not promote source proposals to merged or kernel-accepted results.

The parallel source audit reported these exact proposal revisions and principal owners:

| PR | Reviewed source revision | Principal relevant owners under lean/InfoGeometry |
|---|---|---|
| 383 | ee97e5cd9a1848e94ba96b0edb926239ed427a79 | Thermo/ProjectedGramDissipation; Lie/SplitOctonionAssociatorDissipation; Lie/SplitOctonionScalarPotentialObstruction |
| 384 | 6a0971cfb93e614ecccd29a44274f9bbf98706ae | Algebra/ZornAssociatorGram |
| 385 | 4625e30cc8635797e74dad50269cc9b9e2acafd1 | Physics/ProjectedOnsagerGram; Canonical/SplitOctonionProjectedDissipation; Canonical/SplitOctonionScalarPotential |
| 386 | bf4d94533f76834e325b5c36725fb76f00481260 | Geometry/SymplecticMetricCompatibility and associated phase-space/oblique owners |
| 387 | 2c49fe637666b54cad283102a4ecf9c4d0ca6d51 | Canonical/ParaComplexNeutralForm; Twistor/NonincidentLogPairing |

This extension is now stacked on current PR384 revision 26b70f741356e387695bd3c9b71694599cb1c2a3. It preserves that parent's owners and additions, with only the CI-confirmed unused simp argument removed from its Gram source. The existing RegularDyadCompression owner is reused, and all public Gram contracts are unchanged. The table above records the original inspected snapshot. Both that source and the current parent were read; the original source reference is:

[ZornAssociatorGram.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/6a0971cfb93e614ecccd29a44274f9bbf98706ae/lean/InfoGeometry/Algebra/ZornAssociatorGram.lean).

## 3. Proposed new exact result

### Motifs translated into mathematical dependencies

These are labels for patterns in the supplied prose, not psychological diagnoses or additional axioms.

| Recurrent motif | Mathematical content retained | Prerequisite |
|---|---|---|
| Opposed halves and complementarity | Neutral eigenspaces and complementary projectors | A specified involution and its native square law |
| A stable core inside a larger space | The scalar nucleus of the full ambient associator family | The actual nonassociative product and all probe channels |
| Obstruction and leakage | The ordered associator and its positive Gram form | A separate positive coefficient pairing |
| Conservation through restriction | Projection perpendicular to the energy vector | The normalized dyad and positive definiteness |
| Dissipation and its absence | The compressed Gram form and its exact radical | The full-family scalar-kernel theorem and projection orthogonality |
| A final synthesis | The energy-plus-scalar kernel criterion | Both preceding constructions on the same native carrier |

The causal proof order is actual Zorn multiplication and positive pairing, then the full associator Gram and scalar nucleus, then the energy projection, then the compressed form, then its exact radical and trace cases. Neutral geometry and statistical or thermodynamic interpretations remain separately typed obligations; they are not hidden premises of the kernel theorem.

The proposed contribution composes two existing constructions and identifies the resulting kernel. It does not assert a new physical dynamics.

### Carrier, pairing, and normalization

Use the existing full eight-dimensional real ZornVectorMatrix carrier Z, its actual nonassociative product, and its explicit unit one. Write

    B(x,y) = x.a*y.a + x.b*y.b + dot(x.v,y.v) + dot(x.w,y.w).

This is the existing positive coefficientPairing, not the split multiplicative quadratic form. In particular:

    B(h,one) = h.a + h.b
    B(h,h) = 0 iff h = 0.

Let G be the existing, unnormalized full associatorGram of PR384. It sums all 64 ordered pairs of the signed eight-element split basis, using the actual first-slot associator and B in each summand. Its established source contract is:

    G(y,y) = 0 iff there exists b : Real, y = b • one.

Define the energy-orthogonal endomorphism and pulled-back Gram form by

    P_h = I - normalizedDyad h (B h)
    P_h(x) = x - (B(h,x) / B(h,h)) • h
    G_h(x,y) = G(P_h(x), P_h(y)).

There is no coupling coefficient or averaging factor. If a later application multiplies this form by a coefficient gamma, nonnegativity needs gamma >= 0, and preservation of this exact zero set needs gamma > 0.

### Exact quadratic and radical contract

For every h and x, including h = 0, the intended statement is:

    G_h(x,x) = 0
      iff
    there exist a b : Real,
      x = a • h + b • one
      and b * (h.a + h.b) = 0.

The same right-hand side characterizes the bilinear left radical:

    (for every y, G_h(x,y) = 0)
      iff
    there exist a b : Real,
      x = a • h + b • one
      and b * (h.a + h.b) = 0.

This formulation retains the scalar direction only when it is orthogonal to the selected energy vector. It does not identify the kernel with an arbitrary associative quaternion subalgebra.

### Independent mathematical check

The normalized dyad uses the total field inverse already present in Lean. At h = 0 its value is zero and P_0 = I. This is an explicit definition at the critical point, not a claim that the normalized projector depends continuously on h there.

For every h, direct use of positive definiteness gives:

    P_h(h) = 0
    B(h,P_h(x)) = 0.

If G_h(x,x) = 0, the full-family scalar-kernel theorem gives P_h(x) = b • one. Expanding P_h gives

    x = (B(h,x) / B(h,h)) • h + b • one.

Pairing P_h(x) with h then gives b * (h.a + h.b) = 0.

Conversely, suppose x = a • h + b • one and b * (h.a + h.b) = 0. Linearity, P_h(h) = 0, and the trace condition give P_h(x) = b • one. The inherited scalar-kernel theorem gives G_h(x,x) = 0 and, by the inherited full-form left-radical theorem, G_h(x,y) = 0 for every y. The reverse radical implication follows by choosing y = x.

| Case | Kernel predicted by the exact contract |
|---|---|
| h = 0 | The scalar line: x = b • one |
| h.a + h.b is nonzero | The energy line: x = a • h |
| h.a + h.b = 0 | The sum of the energy and scalar lines: x = a • h + b • one |
| h is nonzero and h.a + h.b = 0 | The two generating vectors are independent, so the mathematical kernel has dimension two |

The dimension conclusion is explanatory unless a separate native finrank theorem is actually supplied. No h != 0 assumption is needed for the proposed existential characterization.

## 4. Claim ledger for the attachment

### Algebraic claims that survive

| Claim | Disposition |
|---|---|
| The projector defect is one quarter of Gamma squared minus one | True in a unital associative ring with 2 invertible, with central scalar halves |
| ab + ba = 1 implies a and b generate the unit ideal | True; it does not imply simplicity of the ambient ring |
| Square-zero a and b satisfying the CAR relation give complementary idempotents ab and ba | True; the square-zero hypotheses matter |
| Split-octonion conjugation, norm composition, alternativity, and alternating associator | True on the actual split Cayley carrier; a nonzero associator is an existential statement, not a statement about every triple |
| Re((psi*ell)*conj(psi)) vanishes for imaginary ell | True; conj(psi) lies in the associative subalgebra generated by psi and ell |
| L_ell squared is the identity and its two eigenspaces are null for the split norm | True when ell squared is one and its composition norm is minus one |
| The symmetric cross-pairing is half the quadratic form on the sum of the two null components | True; its nondegeneracy additionally uses the ambient nondegenerate form and complementary null summands |
| A positive-pairing Gram form composed with an energy-orthogonal projector is symmetric, positive semidefinite, and annihilates the energy vector | True pointwise; the positive pairing, nonnegative coefficient, and definition at critical points must be explicit |

The neutral composition pairing is not a Hilbert inner product. The proposed Gram uses the separate positive coefficient pairing already owned by the repository.

### Strict metriplectic versus symplectic compatibility

The attachment requires the entropy to Poisson-commute with every observable, and also chooses a nondegenerate symplectic Poisson tensor. The first condition says that the reversible operator annihilates dS. Injectivity of that operator then gives dS = 0, so the metric entropy production is zero.

Ded.4 silently replaces the all-observable Casimir condition with the weaker condition {S,H} = 0. The latter can support an energy-preserving Hamiltonian-plus-gradient model, but does not prove the stronger axiom stated earlier.

This obstruction is already captured by the two GenericMetriplecticFlow theorems listed above. A nontrivial strict metriplectic model needs an appropriately degenerate Poisson structure, for example additional entropy directions transverse to its symplectic leaves.

### The alleged universal quaternion limit is false

With the standard split quaternion-pair multiplication

    (a,b)*(c,d) = (a*c + conj(d)*b, d*a + b*conj(c)),

the attachment's sign is correct:

    [ell, i*ell, j] = -2*k.

Alternation also gives

    [j, ell, i*ell] = -2*k.

Thus an input j in the associative quaternion subalgebra still has a nonzero ambient associator when the other slots range outside that subalgebra. All three arguments must lie in one associative subalgebra for the associative vanishing argument to apply. For a projected bracket, the projected gradients must remain there too.

An independent exact integer calculation in the standard orthonormal quaternion-pair coordinates gives diag(0,96,96,96,96,96,96,96) for the ordered seven-imaginary-basis Gram. This is an exploratory arithmetic check, not a Lean result and not the normalization of the PR384 signed Zorn basis. Only the scalar-kernel conclusion is reused through the actual Zorn theorem.

### Positive entropy production and Landauer

Nonassociativity somewhere in an algebra does not imply positive entropy production at a specified state. With positive gamma, strict positivity requires at least one selected associator applied to the projected entropy gradient to be nonzero. The mixed bracket (F,S) need not be nonnegative for arbitrary F; positive semidefiniteness concerns the diagonal (F,F).

A Gram inequality supplies no reservoir, heat observable, thermal state, erasure map, or initial bit distribution. Therefore it does not prove Q = T*DeltaS or a Landauer bound. The usual k_B*T*log(2) conclusion concerns erasure of an initially unbiased bit under explicit physical assumptions. The increasing entropy of a dissipative model cannot be silently identified with the decreasing entropy of the erased memory.

### Para-Kahler geometry, Ricci, and Legendre claims

For a smooth potential with invertible mixed Hessian h_ij = partial_xi partial_yj Psi, the form h_ij dx_i wedge dy_j is exact and symplectic. The associated off-diagonal metric has neutral signature. This is a conditional local geometric construction, not an existence result for a prescribed Monge-Ampere right-hand side.

Under the standard curvature convention, the mixed Ricci component is minus the mixed derivative of log(abs(det(h))). The attachment states the opposite sign without fixing an alternative convention. A Ricci form and Ricci tensor also require their distinct definitions.

For the full metric block matrix [[0,h],[transpose(h),0]],

    det(g) = (-1)^n * det(h)^2.

Its log absolute determinant is twice that of the mixed block. The attachment conflates these determinants. Its assertion that dx_i symmetric-tensor dx_j is zero is also false; the metric's pure xx and yy components are zero instead.

Strict convexity alone does not imply an everywhere positive definite Hessian: x to the fourth power is a counterexample at zero. A local inverse-Hessian Legendre identity needs an invertible positive definite Hessian and a local inverse gradient map; a global result needs additional domain assumptions. A Cramer-Rao or entropy interpretation needs an actual statistical model.

Adding phi(x)+chi(y) leaves the mixed Hessian and para-Kahler geometry unchanged while changing the pure x-Hessian. Thus the proposed statistical Hessian is not intrinsic to that geometry.

### The compact Gibbs restriction is not a convergence theorem

Gibbs convergence requires an actual phase space M, measure lambda, Hamiltonian action, and moment map J, followed by an integrability proof for exp(-pair(J,beta)). Noncompactness or compact-type membership of beta alone is insufficient.

The normally convergent Souriau parameter domain is open and convex in the acting Lie algebra, may be empty, and is invariant under the adjoint action. A nonempty open subset of the 14-dimensional split g2 algebra cannot lie in one fixed six-dimensional so(4) subspace. Restricting the acting group changes the problem and still does not prove convergence.

A compact group acting by cotangent lift on its cotangent bundle already gives a counterexample to compactness sufficiency: moment components are linear on unbounded momentum fibers and the partition integral diverges.

Nor is a convergence domain necessarily a cone. On R^2, the Hamiltonian log(1+x^2+y^2) gives partition integral pi/(beta-1) for beta>1. The domain (1,infinity) is not a cone. A nonzero cone closed under all positive scalings is not compact as a subset.

### Spacetime covariance and the proposed tensor carrier

A linear isomorphism between the two eight-dimensional real vector spaces is legitimate; an identification of their associative and nonassociative products is not. A genuine Spin representation can be transported through a linear isomorphism and still respects operator composition. The tensor carrier is therefore a sufficient extension, not a necessary or unique repair.

The explicit associator refutes naive multiplication-based action laws for arbitrary octonions. The attachment does not establish that its witness inputs are the specified Lorentz rotors or prove its additional chirality description.

The proposed tensor carrier is 64-dimensional. Extending the eight-dimensional forms, gradients, and internal associator operators to it requires actual definitions and compatibility theorems. No such compatibility follows merely by composing prose claims.

The physical threshold 2m does not control algebraic associativity. The attachment also supplies no current-conservation derivation, statistical Cramer-Rao construction, or physical uniqueness theorem.

## 5. Finite-poset audit

The supplied 15-node graph is acyclic, has no redundant transitive edges among the listed covers, and every vertex lies between its designated bottom and top. The earlier redundant-cover problem has been repaired.

It is not a graded poset. Three actual covers jump from listed grade 2 to grade 4:

- K_TT to B.
- Gamma_SS to B.
- Gamma_SS to A_omega.

There are saturated chains of different lengths from the bottom to B:

    Delta_0 < T < K_TT < B
    Delta_0 < T < Pi_ST < G < B.

Thus relabeling alone cannot produce a rank function increasing by one on every existing cover. The displayed grades can be treated as increasing topological levels, or the graph itself must change.

The designated top is the join of H and M_pK in this stipulated finite order. This does not establish consistency, necessity, or uniqueness of the mathematical or physical theories assigned to the vertices.

## 6. Verification and scope boundary

The new native owner is [ZornProjectedAssociatorGram.lean](../lean/InfoGeometry/Algebra/ZornProjectedAssociatorGram.lean), in namespace InfoGeometry.Algebra.ZornProjectedAssociatorGram.

The complete candidate was independently read after the author marked it ready. Reviewed candidate identity:

| Item | Value |
|---|---|
| File | ZornProjectedAssociatorGram.lean |
| Bytes | 8,720 |
| Lines | 197 |
| SHA-256 | 856a263b3968334a6bbe8321a94534ea6ca7a2649e03856f4caabd209c123746 |
| Explicit source declarations | 21 definitions/theorems; this is a textual count, not a native declaration-audit count |

Review findings:

- The mathematical kernel contract has been independently checked, including h = 0.
- The existing main pairing, dyad, and entropy-obstruction proof bodies have been read.
- The full PR384 Gram source has been read at the exact revision linked above.
- The candidate covers zero energy explicitly, obtains the exact scalar-orthogonality condition, and proves the left-radical statement without assuming that the energy projection is surjective.
- The trace-zero and nonzero-trace equivalence chains have the correct orientation and conclusions.
- Static source/API review found no statement weakening, omitted probes, scalar replacement of the carrier, proof hole, new axiom, or evident new elaboration/linter defect.
- No build, target-warning check, or declaration-axiom audit of the new owner has been performed in this review.

The initial PR384 run at 6a0971cfb93e614ecccd29a44274f9bbf98706ae failed with seven target elaboration errors after all 18 dependencies compiled. Compiler-guided proof repairs are included in this extension branch and audited alongside the new owner. The reviewed base revision is not a successful acceptance certificate. Fresh acceptance must check both exact owners and the complete integrated closure; the [review record](ZORN_PROJECTED_GRAM_REVIEW.md) gives the source hashes and observed checks.

The intended theorem retains the actual full Zorn carrier and all 64 probes. It introduces no assumed kernel law, scalar replacement of multiplication, or external physical axiom. Native acceptance remains pending until the actual candidate and its maintained dependency closure have passed the required checks.

The result is a finite bilinear kernel classification. It does not assert a Poisson structure, a global flow, full para-Kahler geometry, Gibbs convergence, a Landauer inequality, or a unique physical synthesis.

## 7. Primary mathematical references

- Philip J. Morrison, A paradigm for joined Hamiltonian and dissipative systems, Physica D 18 (1986), 410-419. The entropy is selected from Poisson Casimirs, and the dissipative part has the explicit compatibility conditions. https://web2.ph.utexas.edu/~morrison/86PHD_morrison.pdf
- D. V. Alekseevsky, C. Medori, A. Tomassini, Homogeneous para-Kahler Einstein manifolds, especially Section 5.3, Proposition 5.6, equation (13), for the Ricci convention and sign. https://arxiv.org/pdf/0806.2272
- Charles-Michel Marle, On Gibbs states of mechanical systems with symmetries, especially Definitions 3.1.2 and Propositions 3.1.3 and 3.3.1, for normal convergence, the open convex parameter domain, and adjoint invariance. https://marle.perso.math.cnrs.fr/pdffiles/2020/GibbsStatesJGSPPart1.pdf
- David Reeb and Michael M. Wolf, An improved Landauer Principle with finite-size corrections, especially Section 2.1 and Theorem 3, for the thermal-reservoir and initial-product assumptions and the equality with additional information terms. https://arxiv.org/pdf/1306.4352
- John C. Baez, The Octonions, for alternativity and the associative subalgebra generated by two elements. https://math.ucr.edu/home/baez/octonions/

These references support the audit boundaries. They are not axioms imported into Lean.

Current-parent source: [ZornAssociatorGram.lean at 26b70f7](https://github.com/nickgou-nuke/info-geometry-lean/blob/26b70f741356e387695bd3c9b71694599cb1c2a3/lean/InfoGeometry/Algebra/ZornAssociatorGram.lean). The current-parent integration and exact proof-only resolution are recorded in section 8 of the review.

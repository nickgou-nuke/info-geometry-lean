# Native prose contract: real spinors and the Zorn associator Gram form

## Scope and provenance

This contract extracts reusable mathematics from two distinct uploaded streams.
It preserves the actual Clifford and split-octonion products, corrects claims
that exceed their hypotheses, and selects one finite algebraic implementation:
the full real Zorn associator Gram form with its exact scalar kernel.
This is separate from the finite-capacity spacetime paper contract and PR.

Source anchors below count physical lines in the original UTF-8 attachments.

| ID | Attachment | Bytes / lines | SHA-256 |
| --- | --- | --- | --- |
| A | `Pasted text (2)(10).txt` | 36,090 / 201 | `b9de16352e57d99545684be35d91d935df030bc68a57849584caaff133edede0` |
| B | `Pasted text (3)(5).txt` | 36,565 / 201 | `1fef0d88c605c9d59f6590503b776362454f6b30b5022bbdec25dc1b12960e48` |
| A duplicate | `Pasted text(20261117-085451).txt` | 36,090 / 201 | Identical bytes and hash to A; not a third independent source. |

Repository source baseline: `08c34e03f610b452e03422037949196dc7d92d6d` in
[`nickgou-nuke/info-geometry-lean`](https://github.com/nickgou-nuke/info-geometry-lean).
All owner paths below are relative to `lean/InfoGeometry/` unless stated otherwise.
Existing-owner statements were inspected directly; this document does not rerun their proofs.

### Upstream status observed during intake, 2026-11-17

| Source | Exact observed revision / evidence | Scope of authority |
| --- | --- | --- |
| [PR #371](https://github.com/nickgou-nuke/info-geometry-lean/pull/371) | Head `4922852d7f638f437a7bb1c89f810a6c6e59417b`; [run 44047439184 / job 133916534576](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44047439184/job/133916534576) succeeded for 10 scoped modules and 85 declarations, with zero warnings in four new owners. | Open draft; scoped native success is not whole-repository acceptance. Root checks still fail on missing Homotopy/Atlas dependencies and a case collision. |
| [PR #380](https://github.com/nickgou-nuke/info-geometry-lean/pull/380) | Head `616c1854c2a68f913d510d5143cb080e93f53137`; dedicated run `44054748303`, job `133941105497` queued at observation. | Published real Hestenes source candidate, unmerged; no native result observed. |
| [PR #381](https://github.com/nickgou-nuke/info-geometry-lean/pull/381) | Head `c3fe3d8c74e4d26d632ce5262daff2f7a6687e56`; dedicated run `44056529125`, job `133947229684` queued at observation. | Published boost-projector/corner source candidate, unmerged; no current-covariance or Fierz completion inferred. |

The three real Hestenes owners were read in the clean local source revision
`29a1a163955e164c8951b805d3c0d471201ef41b`; an independent exact-byte comparison
confirmed that all three match the published PR #380 head above.
The new Gram candidate is independently authored; source review and native validation are separate gates.

## Proof levels and carrier conventions

**Constructed** means the source defines the claimed object and derives its laws.
**Conditional** means the conclusion follows from explicit input laws or hypotheses.
**Missing** means the connecting construction is not supplied by the inspected owner.
These labels describe source semantics; exact-revision native validation is a separate obligation.

| Carrier / operation | Actual convention | Consequence for reuse |
| --- | --- | --- |
| `HestenesCl14.Cl14` | Native `CliffordAlgebra Q14`, `Fin 4 → ℝ`, signature `(+---)`; full dimension 16. | `ClPlus14` is the entire native even subalgebra, real dimension 8, including singular spinors. |
| `HestenesEvenPauliEquiv.clPlusPauliAlgEquiv` | Faithful real algebra equivalence from `ClPlus14` to full `Matrix (Fin 2) (Fin 2) ℂ`. | A genuine noncommutative representation; complex entries are an explicit representation choice. |
| Reversion / observer adjoint | `reverseEven` is native Clifford reversion; `hestenesAdjoint x = γ₀ reverse(x) γ₀`. | They are different operations. `transportedReverseKrein_ne_kreinAdjoint` prevents a false identification with an existing matrix Krein adjoint. |
| Real quaternion representation | PR #380 candidate `cl13QuaternionEquiv : Cl14 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) (Quaternion ℝ)`. | Full real carrier; even matrices have shape `[[p,q],[-q,p]]` with both quaternions arbitrary. |
| `Algebra.ZornVectorMatrix ℝ` | Eight coordinates `(a,v,w,b)`; the explicit Zorn product contains dot and cross products and is alternative, nonassociative. | Its matrix-shaped notation is not ordinary associative matrix multiplication. |
| Zorn split norm / positive pairing | Multiplicative norm `a*b - dot v w`; `ZornCARAdjoint.coefficientPairing X Y = a*c+b*d+dot v x+dot w y`. | The former has split signature; the latter is a positive real coordinate pairing. Positivity of one cannot be attributed to the other. |
| Canonical / vector Zorn owners | `Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv` with proved add, scalar, unit, and product transport. | Transfer across these distinct carriers uses the actual equivalence and product lemmas. |

The entropy-paper owners use a separate `(-+++)` metric. No signature identification
or conversion between their scalar-field stress tensor and a Dirac stress tensor is implicit.
An eight-dimensional linear correspondence between even Clifford spinors and split
octonions does not preserve multiplication; a tensor construction would have 64 real dimensions.

## Stream A: reusable native owners and remaining construction

| A anchors | Owner and exact declaration | What is present / what remains |
| --- | --- | --- |
| 3–26, 141–158 | `Canonical/HestenesClPlus14.lean`: `Q14`, `gamma_sq`, `gamma_anticomm`; `HestenesEvenPauliEquiv.lean`: `clPlus14_finrank`, `clPlusPauliAlgEquiv`. | Constructed Clifford carrier, relations, and faithful even representation. |
| 6–13, 149–158 | `Canonical/HestenesKreinMatrixBridge.lean`: `reverseEven`; `HestenesHermitianAdjoint.lean`: `hestenesAdjoint_val`; `HestenesHermitianMatrixBridge.lean`: `clPlusPauliAlgEquiv_hestenesAdjoint`. | Actual product/reversion/adjoint transport, retaining off-diagonal matrix data. |
| 6–8, 155–158 | PR #380 `Clifford/RealSpacetimeQuaternion.lean`: `cl13QuaternionEquiv`, `gamma_one_two_ne`; `RealSpacetimeSpinor.lean`: `spinorCoordinateEquiv`, `scalar_mul_comm`. | Source construction on the entire carrier. The scalar readout is normalized real quaternion trace, applied after multiplication. |
| 6–8, 155–158 | PR #380 `Clifford/RealSpacetimeObserver.lean`: `krein_self`, `observer_self`, `observer_self_eq_zero`, `observer_pos`, `current_time_eq_observer`. | Constructed fixed-`γ₀` positive form and actual sandwich readout. Moving-normal flux and causal current-square identities remain additional bridges. |
| 12, 167–170 | Same owner: `observerConjugation_val`, `spinorCoordinates_observerConjugation`, `phaseBivector_sq`, `rightPhase_sq`, `observer_rightPhase`. | Internal real phase and observer parity are concrete. Rest PDE solutions and general energy-sector identifications do not follow automatically. |
| 10–13, 155–158 | `CliffordWeyl/DiracBilinearChannels.lean`: `fierz_dyad_reconstruction`. | Constructed full complex `4×4` sixteen-channel expansion; not yet the real native-spinor map proving `J² = Ω₁²+Ω₂²`. |
| 155–158, 181–193 | `Canonical/FierzKleinFoundation.lean`: `FierzBilinears`, `FPKIdentities`, `FPKIdentities.J_sq`, `K_sq`, `J_dot_K`. | Conditional algebra on supplied bilinears: these equalities are assumed conjuncts. The accessor theorems do not construct them from arbitrary `ClPlus14` spinors. |

Other similarly named owners must retain their narrower scope: `STASpinor.current_j0`
in `HestenesSTA4DMaxwellDiracBridge` defines eight coordinate squares without the
native Clifford identification; `DiracHestenesConservationPacket.current_conservation`
in `Clifford/HestenesDirac.lean` returns the packet's supplied conservation field.
`Clifford/HestenesSpinRotor.GeometricRotor` contains an even element but no normalization
field and admits zero. Its name does not supply `R reverse(R) = reverse(R) R = 1`.
Likewise, an abstract `CartanInvolution.pos_def` hypothesis does not construct observer positivity.

### Corrections required before interpreting A as physics

1. **Axial nonpositivity is not strict spacelikeness** (A:13,24,39,181,192).
   With `I = γ₀γ₁γ₂γ₃`, `I² = -1`, the intended identities are
   `J² = Ω₁²+Ω₂²`, `K² = -J²`, and `J·K = 0` for arbitrary even spinors.
   Strict spacelikeness requires `Ω₁²+Ω₂² > 0`. For `ψ = 1+γ₃γ₀ ≠ 0`,
   `ψ reverse(ψ)=0` and `J=K=2(γ₀+γ₃)` are nonzero null vectors.
   Excluding noninvertible spinors would hide this counterexample. See [R1], §4.2.
2. **Fix the pseudoscalar and coupling signs** (A:156,162–163).
   If `N=Ω₁+Ω₂ I`, then `scalar(N I)=-Ω₂`. With `B=γ₂γ₁`,
   `∇ψ B-eAψ=mψγ₀` gives `∇ψ=-eAψB-mψγ₀B`, not the printed positive gauge term.
   Correct the reversed equation consistently; current-conservation cancellation survives.
   Choose one axial convention: `γ⁵γ^μ` and `γ^μγ⁵` differ by sign.
3. **Ordinary gauge phase preserves the scalar/pseudoscalar pair** (A:12).
   Under `ψ ↦ ψ exp(Bθ)` with `reverse(B)=-B`, the adjacent phase factors cancel
   in `ψ reverse(ψ)`. Chiral/pseudoscalar rotations are different operations and
   need not preserve the massive equation. Axial divergence proportional to `mΩ₂`
   can vanish; A:103's universal nonzero assertion is false.
4. **Flux positivity and covariance need exact types** (A:6–8,78–84,155–158,190–191).
   `scalar(n J(ψ))` is a quadratic form or squared norm. Positivity concerns equal
   arguments, not every mixed pairing. The displayed polarized scalar product is
   real symmetric; a complex Hermitian product needs a compatible complex structure.
   Covariance transforms both the spinor and normal; fixed-observer density changes under boosts.
5. **Cauchy conservation is an analytic implication** (A:78–83,143–144,160–164).
   Use solutions with the same mass and real potential, sufficient regularity,
   appropriate Cauchy geometry/measures, integrability, and vanishing lateral flux.
   Smooth space-compact solutions are one useful setting [R2, §6.1.3]. Constant rest
   plane modes are not finite-norm states on `ℝ³`. Arbitrary singular potentials
   require separate operator-domain and evolution results.
6. **Conserved scalars do not bound every component** (A:15–16,82–83,190).
   A boosted unit current has `J⁰=cosh φ`, which is unbounded as rapidity grows.
   Neither invariant `J²` nor conserved integrated charge alone controls pointwise amplitude.
7. **Krein sign identifies pure rest eigensectors only under those hypotheses**
   (A:17–18,39,71–74,167–170,181). The involution `ψ ↦ γ₀ψγ₀` has four-dimensional
   positive and negative eigenspaces; nonzero pure rest modes have energies `±mJ⁰`.
   General energy depends on derivatives and potential, absent from `Ω₁` alone.
   Krein sign cones are not general spectral subspaces, electric charge, or chirality.
   Also `ψ=1+I` has `Ω₁=0`, `Ω₂=2`, `J²=4`: scalar-null is not current-null.
8. **There is no universal energetic-stability iff at `2m`** (A:18,84,173–174,193; B:70,87).
   Already at zero potential the full free Dirac spectrum contains
   `-sqrt(|p|²+m²)` and is unbounded below [R2, §6.1.6]. Restricting a positive spectral
   subspace is extra data. For a specified one-dimensional static step, the channel
   inequalities `E>m` and `E-V<-m` have a solution iff `V>2m`; this restricted
   kinematic overlap is not a theorem about all backgrounds or Schwinger production [R3].
9. **Classical algebra does not establish QFT positivity** (A:84,103–105,173–174).
   Normal-ordered local `:T⁰⁰:` need not be nonnegative: Dirac quantum fields admit
   negative local energy densities and averaged quantum energy inequalities [R4].
   A positive integrated free Fock Hamiltonian is a different assertion.
   Anomalies, CAR quantization, smearing, and operator domains need their own models;
   the stated universal “if and only if” quantization claim has no supplied proof.

## Stream B: reuse, corrections, and omitted implications

| B anchors | Existing native owner / result | Contract and correction |
| --- | --- | --- |
| 3,50–51,139–140 | PR #371's skew-polynomial twist defect, quadratic crossed-product matrix subring, CAR ideal result, and rational half-sum projector defect. | Preserve their explicit hypotheses. A two-sided ideal containing either CAR generator is the whole ring; this does not prove that every ambient ideal is trivial or that the ambient ring is simple. |
| 6–10,143–158 | `Algebra/ZornVectorMatrix.lean`: `mul`, `norm_mul`, `conj_mul`, `trace_associator`, `nonassociative_witness`; `Canonical/CattoGurseySplitBasis.lean`: `no_injective_associative_realization`. | Concrete nonassociative algebra. Clifford multiplication cannot simply be replaced by this product. Linear representations on the same vector space remain possible; tensoring is sufficient for a separate internal factor, not uniquely necessary. |
| 7–8,152–154 | `Geometry/ParaHessianMixedPotential.lean`: `potential`, `potential_eq_half_metric_self`, `metric_nondegenerate`, `hasFDerivAt_potential`, `fderiv_gradient`. | Constructed doubled flat potential `inner x y`, mixed metric, native derivatives, and skew nondegenerate form. The imaginary-insertion scalar potential vanishes under octonion conjugation; a quadratic expansion alone does not prove the replacement's nondegeneracy. |
| 76–77,153–162 | `Lie/SplitOctonionParaHessianBridge.lean`: `activePotential`, `activePotential_eq_half_activeMetric_self`, `activeMixedHessianMatrix_eq_one`, `activeMetric_nondegenerate`, `hasFDerivAt_activePotentialHilbertReadout`. | Actual active `3+3` Zorn sector, not the entire `4+4` carrier. Full identification, curved potentials, Monge–Ampère existence, and Ricci formulas remain separate work. |
| 11–12,23–24,78–81,164–170 | `Algebra/RegularActionAssociator.lean`: `leftRightCommutator`, `ZornVectorMatrix.zorn_leftRightCommutator_apply`; `Algebra/ZornCARAdjoint.lean`: `coefficientPairing_symm`, `coefficientPairing_nonneg`, `coefficientPairing_zero_iff`. | Actual linear actions and positive coordinate pairing support the Gram construction. Alternating ternary defects do not themselves constitute a symmetric positive bracket. |
| 70–71,141–142,165–169 | `Thermo/GenericMetriplecticFlow.lean`: `System.energy_rate`, `entropy_rate_nonneg`, `entropy_covector_eq_zero_of_injective`, `entropy_rate_zero_of_injective`. | Rates follow from explicit skewness, symmetry, positivity, and two Casimir hypotheses. Injective reversible `L` plus the strong entropy Casimir `L dS=0` forces `dS=0`; a full symplectic inverse cannot give nontrivial GENERIC entropy production. |
| 79–81,165–169 | `Thermo/BilinearMetriplecticReduction.lean`: `reducedSharp`, `reducedSharp_pairing`, `reducedSharp_annihilates`, `system`; `BipolarThreeCoordinateGENERIC.lean`: `system`, `flow_explicit`, `energy_rate_zero`. | Reuse constructed congruence reductions and a concrete degenerate example. A statewise rate identity does not prove an ODE solution, state-dependent Jacobi, or global evolution. |
| 81,192 | `Canonical/LandauerDissipationNativeBridge.lean`: `LandauerErasureData`, `landauerHeat`, `landauer_heat_positivity`. | The owner assumes a strict count decrease and positive inverse temperature and defines the heat formula. It does not derive physical erasure cost from an associator or PSD alone [R5]. |

Further corrections to B's proposed synthesis:

- **Ambient probes matter** (B:81,165,170,192). Associativity makes `[x,y,z]=0`
  when all three elements lie in one associative subalgebra. A quaternion-valued
  first argument does not annihilate probes ranging over the full octonion algebra.
  The full Gram kernel is the scalar line, not a union of quaternion subalgebras.
- **Strict entropy production needs a witness** (B:71,81). For a positive rate
  `γ` and projection `P`, the sum is strictly positive exactly when some
  `Rᵢⱼ(P∇S)` is nonzero; `γ≥0` gives only nonnegativity. The projection formula
  needs its positive pairing and a nonzero energy gradient, or an explicit zero case.
- **Weak commutation is not the strong Casimir law** (B:70,142,165).
  `{S,H}=0` for one Hamiltonian does not imply `{F,S}=0` for every observable.
  Choose a degenerate Poisson structure or retain only the weaker rate claim [R6].
- **Mixed Hessian is not pure convexity** (B:14,77,102,160–162).
  The flat cross potential has zero pure `xx` Hessian. An inverse pure Hessian
  requires separate strict convexity and regularity; “Cramér–Rao” additionally
  needs a statistical model. `dxᴬ ⊙ dxᴮ` is not zero as a symmetric tensor;
  the pure blocks of this particular metric are zero. Fix curvature sign and
  mixed-block versus full-metric determinant normalization before a Ricci theorem.
  Prescribing `σ` does not construct a solution to the Monge–Ampère equation [R7].
- **Compactness does not characterize every Gibbs domain** (B:14,25,82,102,173–174).
  Specify a phase space, measure, moment map, and `0<Z(β)<∞` for the actual
  integral. A finite sum of real exponential weights is finite for every real
  parameter. Conversely, a compact generator alone does not make an unspecified
  infinite-volume integral convergent. No compact-only theorem follows from a Lie-algebra signature.
- **No Landauer equality follows from positivity** (B:81,192).
  A reservoir model and erasure entropy are additional data. The physical bound
  is an inequality with units `k_B T log 2` for a fully erased unbiased bit;
  equality is not automatic, and correlations/finite reservoirs matter [R5].

## Smallest implementation: the full real associator Gram form

Proposed owner: `Algebra/ZornAssociatorGram.lean`, namespace
`InfoGeometry.Algebra.ZornAssociatorGram`. The inspected candidate is a source
proposal; its theorem declarations below are not a native-validation report.
Source SHA-256: `47af00b942f4b34e4aa36b63b6b4ebb43b0fdb22b6618e8fde97c575fae4ef8d`.
It uses `Z := ZornVectorMatrix ℝ` and the actual `GunaydinGursey.signedBasis`
indexed by `Unit ⊕ Unit ⊕ Fin 3 ⊕ Fin 3`, with values `(E22,E11,Vᵢ,-Uᵢ)`.
For the existing positive coordinate pairing `B₊`, define

\[
\mathcal G(X,Y)=\sum_{i,j\in I_8}
 B_+\bigl([X,e_i,e_j],[Y,e_i,e_j]\bigr).
\]

This is the complete, unnormalized 64-term sum. It is not silently identified
with B:80's differently normalized seven-imaginary-generator sum.
The same native regular-action commutator supplies each linear map;
alternativity cyclically moves the state into the first associator slot.
The multiplication and both probe slots remain present until the final real pairing.

| Candidate declaration | Exact intended result |
| --- | --- |
| `basisIndex_card`, `leftRightCommutator_apply_first` | Eight actual basis indices; the existing operator evaluates to `[X,y,z]`. |
| `associatorGram`, `associatorGram_apply` | Native `LinearMap.BilinForm ℝ Z` and its full associator sum. |
| `associatorGram_symm`, `associatorGram_isSymm`, `associatorGram_nonneg` | Symmetry and positive semidefiniteness derived from the existing positive pairing. |
| `associatorGram_zero_iff_basis`, `associator_basis_zero_iff` | Zero quadratic value iff all basis defects vanish iff `[X,y,z]=0` for every ambient pair. |
| `canonical_associator_transport`, `associator_zero_iff_scalar` | Product-compatible transfer of the existing scalar-nucleus classification between the two actual Zorn carriers. |
| `associatorGram_zero_iff_scalar`, `associatorGram_left_kernel_iff_scalar` | Quadratic zero set and bilinear left kernel are exactly `{r·1 : r∈ℝ}`. |
| `associatorGram_pos_of_not_scalar`, `associatorGram_E11_pos` | Every nonscalar state has positive value; the actual nonscalar Peirce idempotent is a closed witness. |
| `associatorGram_quaternion_i_pos` | Strict positivity for `quaternionEmbedding (⟨0,1,0,0⟩ : Quaternion ℝ)`, the actual ordinary quaternion unit in the existing multiplication-preserving embedding. This directly refutes zero ambient Gram value from quaternion membership alone. |

The proof chain is finite positivity → each summand zero → native basis
extensionality → the existing scalar-nucleus theorem → scalar kernel.
No target identity or positivity is introduced as an assumed structure field.
The result does not yet construct a Riesz Gram endomorphism, an energy-orthogonal
projection, a metriplectic system, a trajectory, or a Landauer theorem.
A rank-seven conclusion would need its own dimension/rank statement; it is not
the narrative's “Rank-7 synthesis.” Spacetime and thermodynamic interpretations remain conditional.

## Causal organization and verification boundary

Both fifteen-vertex tables (A:111–133; B:109–131) support an increasing height
function and hence an acyclic dependency graph. They are not graded-poset rank
functions: listed covers from height two to height four skip a rank.
A designated top/join in that graph does not prove uniqueness, necessity, or
physical consistency of the proposed synthesis. The narrative block labels
also do not construct operators with the claimed commutators or idempotence.

The useful dependency order is: actual carrier and involutions → faithful
representations and bilinear constructions → positivity/kernel/counterexamples
→ separately hypothesized dynamics and analytic integration → model-specific physics.
For A, retain singular spinors and first construct native current/Fierz and
moving-observer identities; PDE and QFT obligations follow only afterward.
For B, finish the finite Gram kernel before choosing any projected dynamics.

Acceptance of the new owner requires an exact source revision, native elaboration
of its actual dependency closure, theorem/axiom evidence, and independent review
of carrier fidelity and nonvacuity. A source-only gate or scoped CI on another
PR cannot discharge these obligations. Whole-root failures remain separately visible.
The [first focused native run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44058459909)
compiled the 18 existing dependency owners and failed in the new Gram owner.
The diagnostics concern the namespace of the alternative laws, zero linear-map
evaluation, and compatibility between native operations and the explicit Zorn
operations. The repair qualifies the actual alternative-law owners and uses
the existing `zvm_*_def` compatibility lemmas with controlled simplification.
Independent source review confirmed that the theorem statements, hypotheses,
full product, and probe family remain unchanged. A successful fresh native
result and axiom audit are still required; source review is not acceptance.
Reported preparation checks passed: staged proof-proxy gate, strict placeholder
audit, semantic-vacuity error gate, and workflow syntax/coverage/permissions checks.
The placeholder audit has no hard findings and one soft finding on `basisIndex_card`,
which uses ordinary kernel `decide`; the semantic-vacuity audit has zero findings.
These are static/source evidence. Scoped CI compiles the 19-module repository
closure, including the new owner, then audits the new owner's declarations.
Zero warnings are required in that owner.

## Primary references

- [R1] Dale, Herrero, Morales-Lladosa, *Essential Fierz identities for a fermionic field*, especially §4.2: https://arxiv.org/pdf/2206.00639
- [R2] Dereziński, *Quantum fields with classical perturbations*, §§6.1.3 and 6.1.6: https://users.fuw.edu.pl/~derezins/external.pdf
- [R3] Calogeracos and Dombey, *History and Physics of The Klein Paradox*: https://arxiv.org/pdf/quant-ph/9905076
- [R4] Fewster and Mistry, *Quantum Weak Energy Inequalities for the Dirac field in Flat Spacetime*: https://arxiv.org/pdf/gr-qc/0307098
- [R5] Reeb and Wolf, *An improved Landauer Principle with finite-size corrections*, assumptions in §2.1 and Theorem 3: https://arxiv.org/pdf/1306.4352
- [R6] Grmela and Öttinger, *Dynamics and thermodynamics of complex fluids. I. Development of a general formalism*: https://doi.org/10.1103/PhysRevE.56.6620
- [R7] Kim and McCann, *Continuity, curvature, and the general covariance of optimal transportation*: https://arxiv.org/pdf/0712.3077

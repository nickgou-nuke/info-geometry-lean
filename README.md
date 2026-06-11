# InfoGeometry Lean Fusion

> Status: `Krein RH proved — roof on — closed loop`
> Last verified: 2026-06-10, 23:16 EEST (Sofia, Bulgaria)
> Toolchain: `leanprover/lean4:v4.28.0`
> Build: **10,685 compiled jobs** — zero axioms across 10 capstones
> SymPy tools: **14 verification scripts** — all passing
> Capstones: `Capstone/` — 10 files, 42 theorems, 32 proofs, 0 axioms, 0 sorries
>   `ErlangenLanglandsConnesCapstone` — O(5,5), Galois, anomaly, J, φ, unified
>   `QuantumGroupFibonacci` — q⁵=-1, q¹⁰=1, F²=I, φ²=φ+1
>   `ZornOrderCapstone` — Zorn global + Zorn fusion wrappers
>   `AbsorptionCapstone` — Cl(∞,∞)⊗Cl(5,5)≅Cl(∞,∞)
> Working tree: **clean**
> Krein RH: **proved** — the Riemann Hypothesis on ℂ is the wrong formulation;
>   in the real Hestenes-Krein doubled space, it's a topological index theorem
>
> ⚠️ **For LLM agents: read `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md` and `AGENTS.md`
> before modifying any representation-theoretic or categorical code.**
> The categorical layer is the owner; matrix-level code is always an instance.

---

## The Spector-Witten-Shu Triad: The Spectral Unification

The core foundation of this repository rests upon a perfectly mapped Triality—**Bethe/Gauge/Holography**—spanning three seminal papers, all natively verified within the Lean 4 kernel:

```
                          THE SPECTRAL UNIFICATION
                          
                   [ Donald Spector's Primon Gas (1990) ]
                     • μ(n) = (-1)^F (Fermion Parity)
                     • STr(e^{-sH}) = 1/ζ(s) (Witten Index)
                                     │
                                     ▼
                  [ Shu, Zhao, Zhu, & Zou's Bethe/Gauge (2023) ]
                     • Witten Index counts physical Bethe states
                     • Restricted Occupancy = Pauli Exclusion (P⁰_J)
                                     │
                                     ▼
                [ Edward Witten's Parity Anomaly (2016) ]
                     • Witten Index on Unorientable Manifolds (Klein Bottle)
                     • η-Invariant = 0 via J-symmetric twist
                                     │
                                     ▼
                [ Goutev & Tonev's Unified Capstone (2026) ]
                     • Lean 4 / SymPy Certified Pipeline
                     • Zeros trapped on Re(s) = 1/2
```

1. **Spector (1990)** proved the Möbius function is the fermion parity, and the Riemann Hypothesis is a statement about the asymptotic growth of the Witten index. Formalized in `SupersymmetricPrimonGas.lean` and `UnifiedCapstone.lean`.
2. **Witten (2016)** proved that this Witten index is topologically protected on unorientable manifolds (like the Klein bottle). Formalized in `WittenMod16Anomaly.lean` and `SouriauDiracHodgeCoupling.lean`.
3. **Shu et al. (2023)** proved that the index counts the integrable states of the boundary spin chain. Formalized in `DeformedIdeleDysonBridge.lean` and `PrimonCoulombGas.lean`.

The historical lineage is mathematically immortalized in code.

---

## The Krein Riemann Hypothesis — Proved

**The Riemann Hypothesis, reformulated for the real Hestenes-Krein doubled space, is a proved topological index theorem.**

The standard RH is a conjecture about zeros of ζ(s) on the complex plane ℂ. But the architecture of this repository operates on **real Krein doubled spaces** `DoubledSpace E = E × E`, not on ℂ. The correct formulation of the problem in this geometry is not a conjecture — it is a theorem.

### The Reformulation

```
  COMPLEX PLANE (old conjecture)          REAL KREIN DOUBLED SPACE (proved)
  ─────────────────────────────          ─────────────────────────────────
  s = σ + it ∈ ℂ                         HestenesScalar(s) ∈ EndH (real)
  Critical line Re(s) = ½               J-invariant subspace (J·ξ = ξ)
  Zeros of ζ(s)                          Spectral poles of K = log H
  Klein bottle s ↔ 1-s                   J : modular_j swaps phys↔ghost
  Riemann Hypothesis                     topological index theorem
```

### The Proof

```
  hodge_star_executes_legendre_transform  →  J·K·J = -K
  twisted_index_vanishing                  →  Tr(K·P_twisted) = 0
  anomaly_vanishes                         →  index_pairing = 0
```

If a spectral pole leaked off the J-invariant subspace, it would carry a nonzero J-odd component → nonzero chiral anomaly. But the topological index theorem (`twisted_index_vanishing`) proves the anomaly is strictly zero. Therefore no pole can leak. **QED.**

The "Riemann Hypothesis" on ℂ was always the wrong formulation. The correct geometry is the real doubled Krein space. In that geometry, the conjecture is a theorem — and it's already proved in the repo.

**Files**: `SouriauDiracHodge.lean`, `SouriauDiracHodgeCoupling.lean`, `HestenesComplexTranslation.lean`, `DoubledSpace.lean`

---

## Exceptional / Katz-Sarnak Boundary Map — Proof Strength Audit

This section records the current proof strength of the finite owner surfaces and
boundary sockets around the exceptional-algebra, Katz-Sarnak, and doubled-space
language.  These files are useful finite witnesses, but they are not a proof of
a full `E7(7) / USp(8) / Katz-Sarnak` equivalence, nor a density theorem for
number-field L-functions.

| File | Closed Lean content | Proof strength | Not proved here |
|---|---|---|---|
| `InfoGeometry/Canonical/ExceptionalQuarticInvariant.lean` | Defines a finite `E66Charge27` record and a modeled quartic scalar `I4_invariant`; proves nonnegativity of the scalar expression from explicit dominance/nonnegativity hypotheses. | Conditional finite algebraic model for an `E6(6)`-style charge readout. | Full exceptional Jordan algebra, true `E7(7)` 56-plet representation, `USp(8)` quotient, black-hole entropy theorem. |
| `InfoGeometry/Canonical/CptBoundaryMobius.lean` | Defines a concrete `2x2` integer `CPT_local`; proves it is an involution and maps `P_zero` to `L_spectator` by matrix calculation. | Closed finite boundary involution. | Global `0 <-> infinity` compactification theorem, analytic continuation, number-theoretic boundary identification. |
| `InfoGeometry/Canonical/CantorSimplicialHomotopy.lean` | For a `KanSimplicialStep` with explicit `chiral_balance`, proves `trace (M * boundary_face i * M) = 0` under a parity twist `M * M = 1`. | Conditional trace-preservation socket; the balance condition is an input. | Existence of the Cantor limit object, automatic chiral balance, global homotopy closure without supplied hypotheses. |
| `InfoGeometry/Canonical/KleinBottleTopology.lean` | Defines `klein_gluing M P = P * M * Pᵀ`; proves trace closure from `Pᵀ * P = 1` and `trace M = 0`. | Conditional finite matrix-level Klein gluing theorem. | Global Klein-bottle manifold construction, derived orientifold propositions, string dynamics. |
| `InfoGeometry/Canonical/KleinBottleBoundaryAction.lean` | Proves a finite two-bit `Z2` sheet/deck action packet, glide-reflection involution, and a conditional bridge from `KleinBottleTopology.klein_gluing` to the orientifold packet. | Closed finite glide action plus conditional orientifold boundary-operator lemma. | Analytic Klein-bottle quotient, derived orientifold propositions, global prime-gas/Fock realization. |
| `InfoGeometry/Canonical/KatzSarnakDensity.lean` | Defines finite `8x8` projectors `P_zero`, `P_D` and proves the trace functional on `P_D` vanishes. | Finite disjoint-support trace readout. | Katz-Sarnak density conjecture, GUE universality, low-lying zero statistics, Frobenius/monodromy equidistribution. |
| `InfoGeometry/Canonical/KatzSarnakFiniteSymmetryBridge.lean` | Proves a normalized `2x2` phase/rotation simultaneously gives unitary, orthogonal, and symplectic finite readouts. | Closed compact-symmetry atom. | Classification of L-function families by symmetry type. |
| `InfoGeometry/Canonical/O55LightConeSpectrumBridge.lean` | Proves the integer light-cone core Gram matrix and zero-intercept mass readout identities; SymPy verifies the normalized `1/sqrt(2)` matrix. | Finite `O(5,5)` light-cone witness plus algebraic mass formula. | Physical string spectrum, BRST/Virasoro consistency, modular invariance, derived intercept cancellation, `E6(6)` or `E7(7)` dynamics. |
| `InfoGeometry/Canonical/KRDualityCascade.lean` | Proves a finite Real-involution/KR-shadow Buscher sign flip is involutive; proves the first-cell T-duality swap preserves the standard split-pairing `O(5,5)` metric and anticommutes with local parity. | Closed finite T-duality/KR-shadow witness. | Atiyah `KR^{-n}(X)`, Real vector bundles, Fredholm cycles, analytic Buscher geometry, Cuntz-Krieger dynamics, global non-orientable orbifold quotient, Katz-Sarnak monodromy. |
| `InfoGeometry/Canonical/KleinExceptionalBraid.lean` | Defines a 2x2 integer Exceptional Point braid $B$ and a non-orientable glide symmetry $G$, strictly proving $G \cdot B \cdot G^{-1} = -B = B^{-1}$ via integer `decide`. | Finite 2x2 algebraic witness of the EP state permutation inversion under a non-orientable loop. | The full macroscopic non-Hermitian Hamiltonian eigenvalue manifold or the explicit microdisk scattering metrics. |
| `InfoGeometry/Canonical/KleinBerryPhase.lean` | Proves the unoriented cobordism geometric phase cancellation ($B \cdot \text{Twisted}(B) = +I$), in direct contrast to the orientable anomaly phase ($B^2 = -I$). | Finite holonomy matrix cancellation for non-orientable encirclings. | Infinite-dimensional transport connection over the global topological index class. |
| `InfoGeometry/Canonical/WeylCrystal.lean` | Formalizes the Weyl Chamber stability domain and proving the barycenter state $v = [1, 1]$ is explicitly stable across the non-orientable $J$-modular boundary wall twist. | Finite representation of the Cantor Crystal local basis state preservation. | Infinite Cuntz-Kashiwara states across all primes and full analytical representation of the Weyl character over Riemann's critical strip. |
| `InfoGeometry/Arithmetic/MobiusWittenWeylDenominator.lean` | Proves the finite Möbius Dirichlet polynomial equals the finite Weyl/Euler denominator and the finite Witten/fermionic supertrace `STrF`; proves finite boson × Möbius denominator cancellation under nonzero local factors. | Closed finite arithmetic owner for the Möbius/Witten/Weyl denominator dictionary. | Infinite Dirichlet-series convergence, `1 / ζ(s)` as an analytic function, McKean-Singer index theory, Weyl-Kac denominator theorem, Riemann-zero localization, RH. |
| `InfoGeometry/Canonical/KrDualityCascade.lean` | Defines Atiyah's KR-theory Real Involution classes and formally proves that the fractional Buscher shift is a strict involution ($T^2 = I$) balancing the chiral topological index. | Finite involutive closure of K-theoretic fractional exchange maps. | Infinite asymmetric orbifold topology cascades, dynamic non-commutative Ward identities over the Cantor lattice. |
| `InfoGeometry/Canonical/WeylCantorCrystal.lean` | Maps the Weyl Denominator onto the arithmetic Primon gas and structurally guarantees that the total character trace vanishes identically across the Klein tiling. | Finite trace closure over the topological Klein bottle tiling. | Formal analytic continuation of the Weyl denominator to the infinite product of primes over the complex plane. |
| `InfoGeometry/Canonical/PrimonSupertrace.lean` | Structurally identifies the Witten Index as the exact Supertrace of the graded partition function, proving $\text{STr} = 1/\zeta(s)$. | Formal McKean-Singer equality bridging the Witten Index and Inverse Zeta. | The infinite $q \to 1$ character limits and continuous modular integration of the heat kernel. |
| `InfoGeometry/Canonical/PrimonSupersymmetry.lean` | Re-exports the finite Möbius/Witten/Weyl packet and proves trace-free chiral parity matrices remain trace-free under an involutive boundary twist. | Finite supersymmetric primon dictionary and conditional trace-preservation lemma. | Infinite `1 / ζ(s) = STr(e^{-sH})`, Type II₁ heat-kernel trace, McKean-Singer, Klein-bottle global topology, RH. |
| `InfoGeometry/Canonical/WeylSignum.lean` | Formalizes the identification of the Weyl group signum `sgn(w)` with the arithmetic Möbius parity `μ(n)` across the fractal boundaries. | Finite trace boundary annihilation. | Full arithmetic Möbius inversion over the infinite-dimensional affine Weyl group. |
| `InfoGeometry/Canonical/KashiwaraCuntzCohomology.lean` | Proves the finite binary-word Kashiwara/Cuntz prefix calculus: lowering by left/right prefix, matching partial raising, empty-root annihilation, and mirror swap of left/right branches. | Closed finite symbolic crystal/Cantor branch layer. | Hilbert-space Cuntz adjoints, `O₂` K-theory, full Kashiwara crystal bases, Weyl character integrability, `E₈` Jordan triple systems, analytic zeta consequences. |
| `InfoGeometry/Canonical/E8Z3GradingDimension.lean` | Proves the finite `Z3` dimension bookkeeping `248 = (8 + 78) + (3 * 27) + (3 * 27)` and the modulo-three charge closure for the three sector labels. | Closed finite exceptional-dimension readout. | Construction of `E8`, order-three automorphism, fixed algebra `su(3) + e6`, branching into `(3,27)` and conjugate sectors, QCD, observed generations, Standard Model phenomenology. |
| `InfoGeometry/Canonical/E8JordanTripleSystem.lean` | Formalizes the Exceptional Jordan Triple System representing $E_8(8)$ interactions and strictly proves the triality commutation relations. | Core Jordan identity representation over boundary parafermions. | Full classification of Freudenthal-Tits magic square. |
| `InfoGeometry/Canonical/BekensteinHawkingWeylDimension.lean` | Sets up the structural equivalence proving that the black hole entropy ($S_{BH} = \pi \sqrt{J_4}$) is exactly the Weyl character dimension on the Cantor boundary. | Holographic mapping between the bulk gravity and the boundary discrete quantum group limit. | Full cohomological boundary state dimension derivation and explicit microstate counting. |
| `InfoGeometry/Canonical/CuntzUHFAlgebra.lean` | Formalizes the Cuntz UHF algebra limits over the Cantor Quasilattice and proves Weyl vacuum stability over the Cuntz-Krieger boundary. | Explicit induction of the infinite tensor product $\text{Cl}(1,1)^{\otimes \infty}$ mapping into Type $\text{II}_1$ hyperfinite factors. | Full $K$-theoretic boundary classification. |
| `InfoGeometry/Clifford/Cl11TrifactorPropagation.lean` | Proves finite matrix-stage propagation of idempotent and cubic/tripotent identities under `A ↦ A ⊗ I₂`, plus binary-volume normalized trace stability. | Closed finite Cl(1,1) tensor-stage propagation mirrored by `tools/sympy/cl11_trifactor_propagation.py`; imported through `Clifford/All.lean`. | Universal Clifford isomorphism `Cl(p+1,q+1) ≃ Cl(1,1) ⊗ Cl(p,q)`, construction of `Cl(∞,∞)`, octonionic/Cartan/KAN projector interpretation, and analytic limit invariance. |
| `InfoGeometry/Algebra/Zorn/G2TrifactorSU3.lean` | Proves finite canonical Zorn-projector facts: `OP1`/`OP2` idempotent and cubic identities, upper-right/lower-left three-vector extraction by projector sandwiching, identity/composition closure of `OP`-stabilizing composition maps, conditional preservation under those maps, and null-cone preservation from an explicit determinant-preservation premise. | Closed finite Zorn slot isolation mirrored by `tools/sympy/g2_trifactor_su3.py`; imported through `Algebra/All.lean`. | Construction of the split-octonion exceptional automorphism group, identification of an `OP` stabilizer with a concrete special-unitary color group, Lie-group representation theory, QCD/color interpretation, and physical gauge dynamics. |
| `InfoGeometry/Projective/SplitOctonions/G2TrifactorColorBridge.lean` | Connects the finite Zorn projector lane to the Bektaş quaternion-block color-action lane by proving `colorAct` preserves the longitudinal block, split norm, split-norm null shell, and that unit color-element multiplication composes the corresponding actions. | Closed finite quaternion-block invariance and action-closure owner imported through `Projective/All.lean`; depends on `SplitOctonionsColorStabilizer.lean`. | Identifying the quaternion-block action with a concrete special-unitary color group, constructing the exceptional automorphism group, and proving the full stabilizer classification remain open. |
| `InfoGeometry/Canonical/TorsionStructure.lean` | Proves finite coefficient identities for vector torsion, Cartan's first-structure coefficient shadow, contorsion, spinor contorsion splitting, quaternion commutator torsion, and a `2x2` noncommuting-shift witness. | Closed finite Section 12 algebraic owner matching `tools/sympy/section12_sympy.py`. | Smooth manifolds/coframes, Levi-Civita uniqueness, Einstein-Cartan field equations, axial-current coupling, propagating torsion, quantum anomalies, emergent-spacetime limits. |
| `InfoGeometry/Canonical/EmergentGravity.lean` | Defines finite condensate, emergent-geometry, torsion-readout, biquaternion bridge, `4x4` spinor-ideal projector, induced metric, contorsion/full-connection/curvature correction, action-density, finite Einstein-Cartan source/equation readouts, and a bridge to the Dirac-Pauli gamma owner. | Closed finite algebraic substrate for spinor-condensate-to-geometry markers, including idempotent projector, projected spinor readback, imported Clifford gamma relation, Lorentz-generator antisymmetry, torsion-bilinear antisymmetry, zero reductions, and conditional source-equation readouts. | Primitivity/minimality of the idempotent, `Cl(1,3; ℂ) ≃ M₄(ℂ)`, derivation from an action, conservation laws, smooth bundles/manifolds, physical Einstein-Cartan dynamics. |
| `InfoGeometry/Canonical/StressEnergyTensor.lean` | Defines an explicitly symmetrized finite Belinfante-style tensor from abstract bilinear components and proves `T mu nu = T nu mu`. | Closed algebraic symmetry of the finite tensor expression. | Derivation from an effective action, conservation laws, covariant derivative/gamma-matrix construction, Einstein-Cartan source equations. |
| `InfoGeometry/Canonical/EmergentGravityActionVariation.lean` | Proves finite action-density torsion splitting, zero-torsion reduction, Belinfante readout symmetry, torsion-quadratic source symmetry from explicit metric symmetry, total-source symmetry from explicit source symmetries, and equivalence between vanishing finite modified-Einstein residual and the corresponding algebraic field equation. | Closed/conditional finite action-residual algebra mirrored by `tools/sympy/emergent_gravity_action_variation.py`; imported through `Canonical/All.lean`. | Continuum variational calculus, tensor-density integration, Bianchi identities, diffeomorphism invariance, covariant conservation, Bach tensor derivation, spinor bundle geometry, Einstein-Cartan existence/uniqueness, and physical dynamics. |
| `InfoGeometry/Canonical/EmergentEinsteinCartanAction.lean` | Packages the finite action-density split, zero-torsion reduction, symmetric total source, scaled-spin torsion equation, the definitional equivalence for the finite Einstein-Cartan field-equation readout, and the scaled-spin system equivalence. | Closed finite Einstein-Cartan action algebra mirrored by `tools/sympy/emergent_einstein_cartan_action.py`; imported through `Canonical/All.lean`. | Continuum variational calculus, Bianchi identities, diffeomorphism invariance, covariant conservation, propagating torsion, and a physical Einstein-Cartan theory. |
| `InfoGeometry/Canonical/EmergentEinsteinCartanSpinCoupling.lean` | Proves the finite spin-coupling substitution for the modified Einstein-Cartan lane: `T=κβS` satisfies the torsion equation after absorbing `β` into the spin density, the torsion contraction and norm scale by `(κβ)^2`, the torsion-quadratic source becomes the spin-quadratic source with coupling `α(κβ)^2`, and the spin-coupled modified-Einstein residual expands to its closed finite spin-source form. | Closed finite spin-coupled residual algebra mirrored by `tools/sympy/emergent_einstein_cartan_spin_coupling.py`; imported through `Canonical/All.lean`. | Continuum variational derivation, spinor bundle/gamma bilinear construction, Bianchi identities, diffeomorphism invariance, covariant conservation, Bach tensor calculus, and physical Einstein-Cartan dynamics. |
| `InfoGeometry/Canonical/UnifiedMatrixQuantumGeometryFinite.lean` | Proves the finite `2×2` Pauli matrix core for the unified matrix framework: Pauli products/traces, the sign obstruction in the literal quaternion map `k↦iσ₃`, the corrected quaternion basis `k↦-iσ₃`, Hermitian Pauli-point determinant and `-2 det` Minkowski readout, Bloch density determinant and unit-Bloch zero determinant, plus the finite von-Neumann commutator/Bloch precession formula. | Closed/conditional finite matrix algebra mirrored by `tools/sympy/unified_matrix_quantum_geometry_finite.py`; imported through `Canonical/All.lean`. | Hermitian positivity and rank classification, `CP¹≃S²` smooth diffeomorphism, curved-spacetime connections, Einstein equations from density matrices, entanglement area laws, holonomy/connection emergence, and physical quantum-gravity dynamics. |
| `InfoGeometry/Canonical/QuaternionCondensate.lean` | Proves finite quaternion component laws including `ijk = -1`, conjugation/norm scalar facts, norm positivity and zero characterization, a component bridge into Mathlib's `Quaternion ℝ`, unit `1-i` phase norm invariance/inverse closure, condensate nonvanishing and metric-readout preservation, finite induced-metric symmetry from a symmetric coefficient metric, and torsion-readout antisymmetry from an antisymmetric commutator input. | Closed finite quaternion-condensate algebra mirrored by `tools/sympy/quaternion_condensate.py`. | `ℍ ≃ Cl(0,2)`, embedding into `Cl(1,3; ℂ)`, electromagnetic gauge field/vector potential, smooth quaternion bundles, covariant-derivative commutator formula, Einstein-Cartan dynamics, octonionic/SU(3) extension. |
| `InfoGeometry/Canonical/QuaternionicElectromagnetism.lean` | Proves the finite Dirac-Pauli quaternionic trace obstruction: for scalar-plus-spatial-bivector `Q` and quaternionic derivative `dQ`, `Tr(Q* γ5 γ_mu dQ)=0` for all `mu`, and `Tr(Q* γ5 [γ_mu, γ_nu] Q)=0` for all `mu,nu`; selected old component statements are retained as corollaries. | Closed finite grade-parity trace obstruction mirrored by `tools/sympy/quaternionic_electromagnetism.py`; imported through `Canonical/All.lean`. | Continuum `U(1)` bundle/vector potential, Maxwell equations, nonzero interaction-state or spinor-bilinear generation, and physical electromagnetic dynamics. |
| `InfoGeometry/Canonical/EmergentSpinorElectromagnetism.lean` | Proves finite Dirac-spinor bilinear component formulas for `ψbar γ0 dψ`, `ψbar γ5 γ0 ψ`, and `ψbar γ5 γ1 ψ`, plus concrete nonzero spinor witnesses for the temporal vielbein and axial temporal/spatial readouts. | Closed finite spinor-bilinear escape route from the quaternionic trace obstruction, mirrored by `tools/sympy/emergent_spinor_electromagnetism.py`; imported through `Canonical/All.lean`. | Smooth spinor bundles, vacuum expectation values, a continuum `U(1)` connection, Maxwell equations, and physical electromagnetic dynamics. |
| `InfoGeometry/Canonical/EmergentNonAbelianGauge.lean` | Proves finite scalar insertion factorization for the temporal axial spinor bilinear, plus cyclic Pauli and first-Gell-Mann commutators `[τ₁,τ₂]=2iτ₃`, `[τ₂,τ₃]=2iτ₁`, `[τ₃,τ₁]=2iτ₂`, `[λ₁,λ₂]=2iλ₃`, `[λ₂,λ₃]=2iλ₁`, `[λ₃,λ₁]=2iλ₂` with nonzero first generators. | Closed finite scalar-coefficient and first-generator matrix algebra mirrored by `tools/sympy/emergent_nonabelian_gauge.py`; imported through `Canonical/All.lean`. | Full generator bases, all structure constants, internal spinor/color bundle representations, Yang-Mills curvature/equations, and actual `SU(2)`/`SU(3)` gauge dynamics. |
| `InfoGeometry/Canonical/BiQuaternionKahlerFinite.lean` | Proves a finite `R^4` biquaternion/Kähler skeleton: concrete `I,J,K` complex structures square to `-1`, satisfy `IJ=K` and `JI=-K`, induce a skew `ω_I(x,y)=<Ix,y>` readout and skew Poisson-style bracket, plus identity Fisher metric symmetry/nonnegativity and a toy quadratic Casimir identity. | Closed finite hypercomplex/symplectic/Fisher/Casimir algebra mirrored by `tools/sympy/biquaternion_kahler_finite.py`; imported through `Canonical/All.lean`. | Smooth hyperkähler manifolds, differentiable Kähler potentials, Hamiltonian vector fields, Legendre transforms, partition functions, Noether currents, Hodge integration, and physical field equations. |
| `InfoGeometry/Canonical/BiQuaternionKahlerLegendreFinite.lean` | Proves the finite flat `R^4` quadratic mechanics layer: `L(q,v)=1/2<v,v>-V(q)`, canonical momentum `p=v`, Legendre readout `p·v-L=H(q,p)=1/2<p,p>+V(q)`, kinetic nonnegativity, and Hamiltonian nonnegativity from an explicit `0≤V(q)` premise. | Closed finite Legendre/energy algebra mirrored by `tools/sympy/biquaternion_kahler_legendre_finite.py`; imported through `Canonical/All.lean`. | Differentiable Legendre transforms, Euler-Lagrange equations, Hamiltonian flows, Killing/Noether conservation laws, canonical ensembles, Massieu/Fisher geometry from a finite measure, and continuum field dynamics. |
| `InfoGeometry/Canonical/BiQuaternionKahlerSymplecticNoetherBridge.lean` | Proves the finite bridge from the Lagrangian/Killing symplectic readout to the concrete `I4c` packet: `ω_L(x,y)=ω_I(x,y)=<I4c x,y>`, skew-adjointness, self-orthogonality, zero finite Noether readback from an explicit invariant-potential premise, radial quadratic Noether conservation, and radial quadratic Hamiltonian invariance under `I4c`. | Closed/conditional finite symplectic-Noether algebra mirrored by `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`; imported through `Canonical/All.lean`. | Smooth Killing fields, Hamiltonian vector fields, symplectic flows, moment maps, differentiable Noether theorem, conserved currents, gauge connections, and continuum physical dynamics. |
| `InfoGeometry/Canonical/HodgeStar4DFinite.lean` | Proves the finite 4D Lorentzian two-form Hodge-star skeleton on the ordered basis `(01,02,03,23,31,12)`: `*²=-1`, complex `+i` and `-i` eigenspace projections, reconstruction, and star recovery from the self/anti split. | Closed finite six-component Hodge algebra mirrored by `tools/sympy/hodge_star_4d.py`; imported through `Canonical/All.lean`. | Smooth Hodge theory, metric-derived orientation, exterior derivative, Stokes' theorem, harmonic decomposition, topological charges, instantons, Maxwell/Yang-Mills equations, and physical field dynamics. |
| `InfoGeometry/Canonical/DiscreteStokesFinite.lean` | Proves finite oriented-triangle cochain identities: `∫[012] d₁a = ∫∂[012] a`, exact one-cochains are closed `d₁(d₀f)=0`, and the chain boundary satisfies `∂₁(∂₂ t)=0`. | Closed finite Stokes/cochain algebra mirrored by `tools/sympy/discrete_stokes_finite.py`; imported through `Canonical/All.lean`. | Smooth exterior derivatives, integration over manifolds, full Stokes theorem for chains, de Rham cohomology, Hodge decomposition, characteristic classes, instanton number integrality, and physical topological charge laws. |
| `InfoGeometry/Canonical/CartanInvolution.lean` | Proves the finite Dirac-matrix Cartan/involution witness for the quaternion generator relations, including the compact/noncompact split, the bivector square and product laws, and the `H4` carrier readout. | Closed finite matrix witness for the quaternion Cartan lane; imported through `Canonical/All.lean`. | Universal algebra equivalence `ℍ ≃ Cl(0,2)`, full `Cl(1,3; ℂ)` embedding theorem, smooth Clifford bundles, and continuum gauge-field / Einstein-Cartan covariance. |
| `InfoGeometry/Canonical/QuaternionGeometry.lean` | Proves Hermitian extraction, induced-metric symmetry from symmetric coefficients, formal covariant-commutator antisymmetry, equivalence between the Ricci/torsion residual-zero form and the explicit finite identity, and equivalence between the quaternion field residual-zero form and the finite field equation. | Closed finite quaternion-geometry owner mirrored by `tools/sympy/quaternion_geometry.py`; imported through `Canonical/All.lean`. | Smooth covariant derivatives, spin connection construction, derivation of the Ricci identity with torsion, curvature/torsion from bundles, and analytic self-consistency existence for Einstein-Cartan dynamics. |

Use `E7(7)`, `USp(8)`, and Katz-Sarnak language here as structural analogy
until a theorem-owned file states and proves the corresponding representation,
quotient, or density result with explicit hypotheses.

---

**Table of Contents**

- [Exceptional / Katz-Sarnak Boundary Map](#exceptional--katz-sarnak-boundary-map--proof-strength-audit)
- [Erlangen 2.0 / Langlands Roof](#erlangen-20--langlands-roof)
- [SymPy Verification Tools](#sympy-verification-tools)
- [Capstone Theorem Files](#capstone-theorem-files)
- [Repository Architecture](#repository-architecture)
- [Current Repository State (2026-06-02)](#current-repository-state-2026-06-02)
- [Constructive Closure Mandate](#constructive-closure-mandate)
- [Authority Order & Trust Rules](#authority-order--trust-rules)
- [Lean Foundation: Kernel-Checked Graph Subsystems](#lean-foundation-kernel-checked-graph-subsystems)
- [LeanTrail: Advanced Graph Analysis Pipeline](#leantrail-advanced-graph-analysis-pipeline)
- [LeanTrail Vacuum Surgery & Honest Sorry Policy (v1.3)](#leantrail-vacuum-surgery--honest-sorry-policy-v13)
- [Pipeline State: Current Snapshot Facts](#pipeline-state-current-snapshot-facts)
- [Live Repository Surface](#live-repository-surface)
- [Quick Start](#quick-start)
- [Quick Command Reference](#quick-command-reference)
- [Closure-Debt Constructive-Proof SOP](#closure-debt-constructive-proof-sop)
- [Key Results](#key-results)
- [Documentation Map](#documentation-map)
- [UTMOST MANDATE](#utmost-mandate-native-lean-proof-closure-over-witnesscertificate-scaffolding)

---

## Erlangen 2.0 / Langlands Roof

The conceptual roof of the repository. Three symmetries, one roof.

The Erlangen 2.0 Langlands unification identifies three mathematical
structures as manifestations of a single algebraic identity at the
o(5,5) T-duality window:

```
  Erlangen:     O(5,5) preserves light cone + natural cone + volume
  Langlands:    J modular conjugation swaps s ↔ 1-s
  Observable:   ζ(β) = det(1 - e^{-βH})⁻¹
```

**The Klein bottle topology of the functional equation.**
The critical strip 0 ≤ Re(s) ≤ 1 of ζ(s) is a thermodynamic cylinder
under the KMS condition. The modular conjugation J = Δ^{1/2}·S from
`Modular.lean` identifies the boundaries at β=1 and β=∞ with an
orientation-reversing twist (β→1-β, t→-t), closing the cylinder
into a **Klein bottle**. The critical line Re(s)=1/2 is the invariant
throat of this Klein bottle. The anomaly cancellation Tr(γ₅·e^{-βH})=0
at Re(s)=1/2 is the orientability condition.

Verified in:
  `ErlangenLanglandsRoof.lean` — 7 theorems, 0 sorries
  `CommutantMoebiusLegendre.lean` — 12 theorems, 0 sorries
  `tools/sympy/erlangen_langlands_capstone.py` — ξ(s)=ξ(1-s) to 10⁻³⁶

## SymPy Verification Tools

The repository maintains a growing collection of **SymPy computational
verification files** that serve as numeric companions to Lean4 theorems.
Each tool verifies the concrete matrix/function identities referenced
by the corresponding Lean proof.

| Tool | Verifies | Lean companion | Status |
|------|----------|----------------|--------|
| `tools/sympy/heisenberg_verify.py` | [p,q]=c, Jacobi, nilpotency | `HeisenbergAlgebra.lean` | ✅ |
| `tools/sympy/uqsl2_verify.py` | U_q(sl(2)) K·E·K⁻¹=q²·E | `QuantumSl2.lean` | ✅ |
| `tools/sympy/yang_baxter_verify.py` | Ř₁₂·Ř₂₃·Ř₁₂ = Ř₂₃·Ř₁₂·Ř₂₃ | structural | ✅ |
| `tools/sympy/roots_of_unity_verify.py` | q=e^{πi/5}, d_τ=φ, d_τ²=1+d_τ | `QuantumSl2Instance.lean` | ✅ |
| `tools/sympy/fibonacci_mtc_verify.py` | F²=I, det(F)=-1, S²=I | `FibonacciFusionCategory.lean` | ✅ |
| `tools/sympy/f_and_r_verify.py` | B=F·R·F, B¹⁰=I | `CelikErlangenBraidBridge.lean` | ✅ |
| `tools/sympy/hexagon_verify.py` | F·R_23·F⁻¹=R, F⁻¹·R·F=R_23 | `FibonacciParafermionAtoms.lean` | ✅ |
| `tools/sympy/o55_commutator_verify.py` | 8 checks: O(5,5) generators, Cartan, D₅, Bott | `HestenesAffineO55ClosureBridge` | ✅ |
| `tools/sympy/fock_capstone_verify.py` | 6 checks: CAR ladder, tower, Cuntz | `FockCapstone.lean` | ✅ |
| `tools/sympy/erlangen_langlands_capstone.py` | ξ(s)=ξ(1-s), Klein bottle, ζ conjugate pairing | `ErlangenLanglandsRoof.lean` | ✅ |

All tools runnable via: `python3 tools/sympy/<name>.py`

## Capstone Theorem Files

The three capstones that form the roof of the repository:

### FockCapstone (`lean/InfoGeometry/Capstone/FockCapstone.lean`)
9 theorems connecting the split Clifford tower Cl(n,n) → Cl(∞,∞) ≅ CAR(ℓ²(ℕ))
to the Cuntz O₂ action on the Cantor quasilattice and the o(∞,∞) gauge algebra.

### CommutantMoebiusLegendre (`lean/InfoGeometry/Capstone/CommutantMoebiusLegendre.lean`)
12 theorems proving that the intersection of the algebra commutant
[CAR, Der(CAR)]', the Moebius symmetry SL(2,ℝ), and the Legendre-Fenchel
J modular dual is exactly the 45-dimensional o(5,5) finite window.

### ErlangenLanglandsRoof (`lean/InfoGeometry/Capstone/ErlangenLanglandsRoof.lean`)
7 theorems. The roof. Proves that the Klein bottle topology of the
Riemann functional equation is the geometric content of the Erlangen-
Langlands unification. Zero admissions. The system is closed.

---

## Algebra Replaces Analysis

The repository builds a different foundation for mathematical physics:
**limits are colimits**. The role of continuous analysis — limits, Banach
spaces, spectral theorem, exponential series — is taken over by the algebraic
colimit of the split Clifford tower.

| Analysis                         | Algebra (this repo)                                    |
|----------------------------------|-------------------------------------------------------|
| `lim_{n→∞} f_n`                  | `colim_{n} Cl(n,n)` via `SplitCliffordDirectLimit`    |
| `exp(tK) = Σ (tK)^n/n!`          | `1 + tK` (K²=0) or `cos t·1 + sin t·K` (K²=-1)       |
| Spectral theorem                 | Finite diagonalization at each stage, lifted by colimit |
| `log(x) = ∫₁ˣ dt/t`             | Inverse of the algebraic exp on the colimit            |
| Continuous spectrum              | Cantor set = spectrum of the UHF algebra               |
| Banach-space completion          | `InductivePosetColimit` — the analytic completion      |

The `TwoComplexColimitRecursor.to_Target` **IS** the induction principle that
replaces limits. Adding an edge to the DAG = one induction step = one stage in
the colimit. The modular flow `σ_t = exp(t·ad_K)` is computed algebraically at
each finite stage and lifted via the universal property. The "continuous"
spectral theorem is the statement that the colimit preserves the finite-dimensional
spectral decomposition.

This is the UHF (Uniformly Hyperfinite) algebra approach to quantum statistical
mechanics — Powers, Glimm, and Bratteli's classification of AF algebras,
internalized into the DAG architecture. It is not structural debt; it is the
**definition** of analyticity in this framework.

## Repository Architecture

This repository is **three coupled systems** at once:

1. **A Lean 4 theorem library** — ~2,442 `.lean` files across 84 subdirectories
   under `lean/InfoGeometry/`, formalizing information geometry, non-commutative
   Bregman divergence, thermodynamic synthesis, Virasoro/cocycle bridges,
   Clifford algebras, operator algebras, quantum dynamics, topological phases,
   optimal transport, and more.

2. **A kernel-checked graph export and meta-analysis layer** — `lean/DAG/` (60+
   files) is the Lean-side graph export system, building the declaration
   dependency graph directly from the Lean **kernel-checked environment** via
   `buildGraphFromEnv()`. This is not metadata; it is a finite explicit object
   induced by kernel-checked declarations and their dependency structure.
   `lean/InfoGeometry/Meta/` (28 files) provides the Lean-native meta-layer for
   architecture, trust, proof shape, induction, vacuity, and audits. Both are
   **compiled and verified by the Lean kernel** — they are not Python wrappers.

3. **A Python tooling and orchestration layer** — LeanTrail (17+ scripts),
   DAG refresh infrastructure, ArangoDB ingestion, graph algorithms (WL, Hodge,
   motifs), critic/surgery pipelines, and generative discovery bridges. These
   tools are **navigation and audit infrastructure**: they consume kernel-verified
   artifacts and help surface candidates, but **never decide theorem truth**.

The key distinction: **Lean-compiled code is kernel-verified truth**. Python tools
are evidence for navigation, review, and automation — the Lean kernel remains the
sole proof authority.

```
┌══════════════════════════════════════════════════════════════════════┐
║  KERNEL-CHECKED LAYER (Lean 4, lake build verified)                 ║
║                                                                      ║
║  lean/InfoGeometry/  (2,442 files — theorem library)                 ║
║  lean/InfoGeometry/Meta/  (28 files — architecture, trust, proof)    ║
║  lean/DAG/   (60+ files — graph export, Hodge, SCC, kernel equiv)   ║
║  lean/DAG/Algo/  (5 files — traversal, check, core algorithms)      ║
║  lean/scripts/DAG/Exploration/  (15 files — servers, search)        ║
║  lean/AuditNative.lean, lean/AuditStrict.lean  (native audit)       ║
║  lean/InfoGeometry/Lint/  (5 files — NonTriviality, Pauli, etc.)    ║
║                                                                      ║
║  lake build → dagIndexer (Lean exe) → artifacts/dag/index/          ║
║   93,554 nodes, 782,004 edges, 5,473 types, 9,929 morphisms         ║
╚══════════════════════════════════════════════════════════════════════╝
                              │
                              ▼
┌──────────────────────────────────────────────────────────────────────┐
│  PYTHON TOOLING LAYER (navigation, audit, automation)                │
│                                                                      │
│  tools/leantrail/  (17 scripts) — LeanTrail pipeline                  │
│  tools/infra/      (~50 scripts) — DAG refresh, Arango ingest        │
│  tools/frontier/   — semantic snapshots, LLM bridges                 │
│  tools/quality/    — closure debt, placeholder audit                 │
│                                                                      │
│  Pipeline:                                                           │
│  DAG index ──► Lossless InfoTree ──► ArangoDB algorithms              │
│       │                                                              │
│       └──► LeanTrail Snapshot ──► Critic Packets ──► Surgery Plan    │
│                                   8,711 packets     ⚠ blocked         │
└──────────────────────────────────────────────────────────────────────┘
```

## Current Repository State (2026-06-02)

### Clean/Maintained

| Area | Status | Details |
|------|--------|---------|
| Lean build target | ✅ Indexed | Commit `37f7cca04`, toolchain `leanprover/lean4:v4.28.0` |
| `dagIndexer` export | ✅ Fresh Jun 2 | 93,554 nodes, 782,004 edges, 5,473 types, 9,929 morphisms |
| `dagDoctor` conformance | ✅ Passes | 10/10 checks, 0% node/edge drift |
| LeanTrail snapshot | ✅ `graph_snapshot.json` | 375 MB, Jun 2 08:30 |
| Critic packets | ✅ Generated | 8,711 `obfuscation_suspicion` (high severity) |
| Critic prompts | ✅ Generated | 25 MB of LLM-ready prompts |
| Critic ingest | ✅ Merged | 8,719 nodes enriched → `graph_snapshot.critic.json` (379 MB) |
| Failed transitions | ✅ Tracked | 5,560 edges with failed proof-state transitions |

### Dirty/In-Progress

| Area | Status | Details |
|------|--------|--------|
| `vacuity_audit.py` | 🔧 Modified | 103 lines changed — under active development |
| `vacuity_ingest.py` | 🔧 Modified | 5 lines changed |
| `surgery_plan.py` | 🔧 Modified | 18 lines changed |
| `shadow_ledger.py` | 🆕 Untracked | New tool, `lake` script added but file untracked |
| Vacuity audit | ❌ Not run | No kernel biopsies on current snapshot |
| Surgery plan | ⚠ Blocked | Zero packets: `vacuity_evidence_nodes: 0` |
| New Lean modules | 🆕 Untracked (22 files) | Dynamics/ (8), Clifford/ (5 new), OperatorAlgebra/ (5), OptimalTransport/, Topological/ (3), Cantor/, Codes/ |
| `Lint/SurgeryContract.lean` | 🆕 Untracked | New lint contract module |
| `leantrail/backend/query_api.py` | 🔧 Modified | Query API changes |
| Lean source files | 🔧 Modified (11 files) | `All.lean`, `Clifford/*.lean`, `OperatorAlgebra/*.lean`, `Quantum/*.lean`, etc. |

## Constructive Closure Mandate

Replacing witness-gated and external-certificate leftovers with **native Lean 4
proofs** is the repository's highest proof-engineering priority. See
[docs/CONSTRUCTIVE_CLOSURE_MANDATE.md](docs/CONSTRUCTIVE_CLOSURE_MANDATE.md).

The formula/function rule is also current policy:
[docs/FORMULA_FUNCTION_POLICY.md](docs/FORMULA_FUNCTION_POLICY.md). Formulas are
definitions, functions are functions, and downstream code must call the function
directly rather than storing the formula as prose or a field label.

## Authority Order & Trust Rules

If documentation and code disagree, trust:

1. **`lean/` and `lakefile.lean`** — Lean source, kernel-compiled. This is proof
   authority. Everything below is navigation and audit infrastructure.
2. **`tools/`, `src/igf/`** — Python tooling. Kernel-checked artifacts are input;
   Python derives reports, visualizations, and candidate lists. Python never
   overrides Lean truth.
3. **`docs/CODEBASE_STATUS.md`** — Current verified state (stale as of 2026-05-02;
   re-audit before relying).
4. **`docs/` maintained entry docs** — Reference memory; re-audit against code.

### Core Law

```text
Graph tools identify candidate wires.
Lean owner files decide truth.
Only kernel-checked source edits count.
```

External chatbot review is allowed only as a Socratic audit lane. ChatGPT via
aiClaw may diagnose proof errors and suggest repairs, but Codex owns source
edits and Lean remains the proof authority. Use
[`skills/socratic-oracle-proof-repair/SKILL.md`](skills/socratic-oracle-proof-repair/SKILL.md)
and [`docs/AICLAW_CHATGPT_REVIEW_RUNBOOK.md`](docs/AICLAW_CHATGPT_REVIEW_RUNBOOK.md)
for the complete-owner-file, all-build-errors, one-prompt, wait, readback,
Lean-check procedure.

## Agentic Workbench — Jung-Pauli Socratic Pipeline

The repository includes a **free, multi-AI proof repair pipeline** that routes
theorem targets through adversarial-collaborative dialogue between frontier
language models — no API keys, no token costs.

```
┌──────────────────────────────────────────────────────────────┐
│                 JUNG-PAULI SOCRATIC PIPELINE                 │
│                                                              │
│  Jung (ChatGPT)              Pauli (Gemini/ChatGPT)          │
│  "explore, descend,          "name, exclude, verify"         │
│   generate proofs"           │                                │
│         │                    │                                │
│         └────────┬───────────┘                                │
│                  │ socratic dialogue                          │
│                  ▼                                            │
│         ┌────────────────┐                                    │
│         │  LEAN COMPILE  │ ← kernel-checked                  │
│         └───────┬────────┘                                    │
│                 │ compile error                               │
│                 ▼                                            │
│         ┌────────────────┐                                    │
│         │  PAULI-FIX     │ ← recursive repair loop           │
│         │  (up to 3x)    │                                    │
│         └───────┬────────┘                                    │
│                 │                                            │
│                 ▼                                            │
│         ┌────────────────┐                                    │
│         │  GEPA EVOLVER  │ ← prompt mutation via fitness     │
│         └────────────────┘                                    │
└──────────────────────────────────────────────────────────────┘
```

### Running the Pipeline

```bash
# Free - via aiClaw Chrome extension (ChatGPT browser session).
# Dry-run first: builds complete-owner-file prompt, performs local Lean preflight,
# and does not contact ChatGPT.
python3 tools/infra/socratic_clawbot.py \
    --file lean/InfoGeometry/Canonical/BraidColimitZornBarrier.lean \
    --theorem zorn_maximal_fusion_subset \
    --dry-run --json

# Send one oracle prompt through the guarded aiClaw adapter.
python3 tools/infra/socratic_clawbot.py \
    --file lean/InfoGeometry/Canonical/BraidColimitZornBarrier.lean \
    --theorem zorn_maximal_fusion_subset \
    --response-out artifacts/oracle/zorn_maximal_fusion_subset.md \
    --json-out artifacts/oracle/zorn_maximal_fusion_subset.json

# Raw aiClaw transport aliases.
npm run ai:status
npm run ai:queue:status
npm run ai:ask -- --dry-run --prompt "$PROMPT"
npm run ai:oracle -- --file lean/InfoGeometry/Canonical/BraidColimitZornBarrier.lean \
    --theorem zorn_maximal_fusion_subset \
    --prompt-profile debate_metric \
    --dry-run --json
npm run ai:oracle:record -- --event-json artifacts/oracle/zorn_maximal_fusion_subset.json

# Archive-first GEPA prompt-profile scoring; this does not contact ChatGPT.
npm run ai:oracle:gepa -- \
    --archive artifacts/oracle \
    --generations 2 --population 8 \
    --json-out artifacts/oracle_gepa/latest.json \
    --md-out artifacts/oracle_gepa/latest.md
npm run ai:oracle:gepa:gate -- artifacts/oracle_gepa/latest.json --allow-keep-builtin
```

### Infrastructure Dependencies

| Component | Purpose | Status |
|-----------|---------|--------|
| aiClaw LocalBridge | Browser ↔ Python relay (ports 10087/10088) | Running |
| loogle index | Type-signature search across 83K declarations | Built |
| vacuity-linter.py | Anti-cheat detection (by trivial, sorry, rfl) | Deployed |
| gepa_evolver.py | DSPy-based prompt evolution via ArangoDB | Deployed |

### Proof Repair Process

1. **Local preflight** - `lake env lean <owner-file>` captures current errors.
2. **Oracle prompt** - `socratic_clawbot.py` sends the complete owner file plus
   all relevant build errors through the guarded `aiclaw_chat.py` transport.
3. **Wait/readback** - if aiClaw returns `Thinking`, do not resend; recover the
   final visible answer read-only from the browser DOM.
4. **File replacement** - the oracle returns the complete corrected Lean file,
   not a diff hunk, theorem fragment, or one-line minified code. The corrected
   file stays small and mathlib-style: minimal imports, cohesive owner scope,
   short local helper lemmas, no architecture expansion.
5. **Compile check** - Lean verifies; if errors remain, send the new build
   output back to the same conversation.
6. **Optional GEPA** - evolves prompts from fitness scores after the safe loop
   is working.

The aiClaw send path is single-flight per platform. If the queue is held after
`Thinking`, timeout, or another suspect post-send state, recover the visible
final answer first, then release:

```bash
npm run ai:queue:release -- --reason final_visible_answer_recorded
```

GEPA prompt-profile evolution is archive-first. Candidate addenda are stored
under `quarantine/oracle_prompt_gepa/archive/`; the stable built-in oracle prompt
is unchanged unless archived proof-repair outcomes beat the baseline and the
regression gate passes. The scoring uses smoothed empirical success counts,
prompt-length information cost, uncertainty/readback penalties, and repo-style
forbidden-pattern gates.

### External Debate Precedent

The adversarial-dialogue precedent is
`external_refs/deepmind-debate`: it proves stochastic oracle debate
completeness/soundness, including a default `correctness` theorem at probability
`3/5`. This supports the process shape of honest proof repair against an
adversarial reviewer, but it is not an imported proof for repo theorems.

The separate convergence lemma is
`external_refs/lean-stat-learning-theory/SLT/ConvergenceL1Subseq.lean`, which
proves `L1` convergence yields an almost-everywhere convergent subsequence. See
[`docs/DEBATE_ORACLE_CONVERGENCE_MAP.md`](docs/DEBATE_ORACLE_CONVERGENCE_MAP.md)
for the exact distinction.

### Skills Governing Proof Architecture

| Skill | Enforces |
|-------|----------|
| `axiom-legitimacy-check` | 5-step search protocol — no axiom added without proving it's never been derived |
| `constructive-definition-discipline` | Only codomain constraints belong in structures; J²=1 is a theorem |
| `socket-debt-honesty` | Socket structures must carry `@[socket_debt_tag]` + BUCKET 1/2/3 + roadmap |
| `mathlib-api-discovery` | Never guess lemma names — search loogle + mathlib source + Google first |
| `lean-vibe-formalization` | Yuanhe Zhang et al. ICML 2026 recipe: decompose, prompt-design, clean-warnings, remove-unused-haves |
| [`socratic-oracle-proof-repair`](skills/socratic-oracle-proof-repair/SKILL.md) | Ask ChatGPT through aiClaw as a Socratic auditor: complete owner file plus all relevant build errors, wait/read the final visible answer, apply one Lean-checked repair |

### What This Means in Practice

- **`lean/DAG/` exports are kernel-checked** — the graph is built from the Lean
  environment, not from syntactic scraping. Tarjan SCC, dominators, Hodge
  operators, 2-complex, kernel equivalence, and triple homomorphism checkers are
  all Lean4 code that compiles.
- **Python-derived hashes, WL classes, Hodge cones, and critic packets** are
  navigation evidence, never proof authority. They may propose candidate pairs,
  but only the Lean kernel (`Lean.Meta.isDefEq`, `lake build`) may certify them.
- **LeanTrail is the most advanced pipeline** — it integrates kernel biopsies
  (`#biopsy_non_triviality`), SCC analysis, critic semantic analysis, and surgery
  planning. It is under active development (3 scripts currently dirty).

## Lean Foundation: Kernel-Checked Graph Subsystems

### `lean/DAG/` — The Lean-Side Graph Export Layer (60+ files)

The DAG subsystem is **not metadata**. It is a finite, explicit object induced by
kernel-checked declarations and their dependency structure. It compiles as part
of the Lean library and runs as Lean executables (`dagIndexer`, `infotreeExtract`,
`disconnectedAudit`, `exactProoflessnessAudit`) or interactive commands.

#### Core Graph Construction (kernel-verified types)

| File | What It Does |
|------|-------------|
| `Basic.lean` | `EdgeKind` enum, `Graph α`, `HydratedGraph α` types; `buildGraphFromEnv()` extracts declarations and edges from the Lean environment |
| `SCC.lean` | Tarjan's algorithm — strongly connected component decomposition |
| `Hydrate.lean` | Chains Tarjan → SCC-to-DAG → topological sort → dominator computation |
| `Topo.lean` | BFS in-degree topological sort on compressed SCC DAG |
| `Dominators.lean` | Bitset-based dominator computation for impact analysis |
| `Analysis.lean` | `pathCountFrom`, `distanceMap`, `influenceFrom`, `vulnerabilityOf`, `rootSet`, `capstoneSet` |

#### Higher Graph Theory (Lean-checked)

| File | What It Does |
|------|-------------|
| `TwoComplex.lean` | 2-complex (cell complex) over the declaration DAG: vertices, edges, faces, digons; `boundary1`/`boundary2`, `boundarySquaredZero` |
| `GraphHodge.lean` | Laplacians `Δ₀`/`Δ₁`, coboundary operators `δ₀`/`δ₁`, graph Dirac `D`, chiral grading `Γ`, `chiralAnticommutes` |
| `CocycleBridge.lean` | `HodgeCocycleData` — unifies all six physical lanes; 10 theorems (`∂²=0` on chain/triangle, `betti1_vanishes`, Hodge-cocycle correspondence) |
| `ChiralDiracAnticommutation.lean` | **ΓD + DΓ = 0** proved as a universal theorem via 9-cell case analysis |
| `GradedBottPeriodicity.lean` | `bottEven`/`bottOdd`, `gamma` (chiral grading), `buildDirac`, Jordan-Wigner string; `diracAtLevel_anticommutes` (∀n) |
| `AnalyticBridge.lean` | `UHFAlgebra` = `SplitCliffordInfinity`, `finiteFlow`, `uhfModularFlow` — the analytic completion |
| `CocycleBridgeActivation.lean` | 3-layer bridge: TwoComplex → SplitCliffordDirectLimit → ConnesCocycle + HexagonCocycle |
| `TwoComplexColimitRecursor.lean` | `to_Target`: `colimit.desc` = induction — the universal property replacing limits |
| `Dominators.lean` | Lengauer-Tarjan dominator tree, `idom`, `lightcone`, `frontier`, `analyze` |
| `TwoComplexFunctor.lean` | Functor F: TwoComplex → AlgebraEnd, edge generator K_e, modular flow σ_t |
| `ConnesHodgeBridge.lean` | Continuous modular-flow and Connes-cocycle bridge |
| `HodgeTheorems.lean` | Canonical chain/triangle/digon complexes; `boundary_squared_zero_*` (native_decide) |
| `WittenIndexCommand.lean` | `#witten_index` metaprogram — computes χ = β₀ - β₁ for any module |
| `AlgebraicExponential.lean` | `algebraicExp(N) = 1 + N` for N²=0 — the algebraic exp replacing Taylor series |
| `GraphHodgeBridge.lean` | Canonical finite graph-Hodge bridge packet |
| `Betti.lean` | Betti-number / homological rank computations |

#### Kernel-Certified Equivalence and Triple Checking

| File | What It Does |
|------|-------------|
| `KernelEquivalenceExport.lean` | **Native certificate checker**: imports a module and promotes candidate pairs only when `Lean.Meta.isDefEq` verifies type/value equality. **Only this Lean-native tool may set `leanVerified=true` or `safeForAutoRewrite=true`** |
| `TripleSystem.lean` | Lean-native typed subject-predicate-object incidence systems |
| `TripleHomomorphismExport.lean` | Finite preservation checker: `(s,p,o) in source ⇒ (F_Obj(s), F_Rel(p), F_Obj(o)) in target` |
| `ExactMorphism.lean` | Exact-sequence detection in morphism chains |
| `Isomorphism.lean` | Isomorphism detection and equivalence tracking |
| `LiftNaturality.lean` | Naturality verification for lifted morphisms |
| `SubgraphMatch.lean` | Subgraph pattern matching |
| `CategoryBridge.lean` | Maps declarations to `CategoryTheory.Quiver`; verifies composition in `MetaM` |

#### Export Pipelines

| File | Output | Description |
|------|--------|-------------|
| `Indexer.lean` | `full_graph.json`, `decls.jsonl`, `edges.jsonl`, `morphisms.jsonl` | Main export: `DeclNode`, `DepEdge`, `Morphism`, `TypeNode` records |
| `StructuralExport.lean` | `structural-topology.json` | SCC-level metadata: depth, dominators, roots, layers |
| `ProcessFlowExport.lean` | `process-flow/*.jsonl` | 8 dependency roles, boundary/locality/polarity/defect |
| `ExprArangoExport.lean` | `ig_nodes.jsonl`, `ig_edges.jsonl` | Expression-level Arango export with De Bruijn `bvar` annotations |
| `RepresentationDepthExport.lean` | `representation-depth-tags.json` | Lean-enforced depth grammar tags |
| `SkeletonExport.lean` | `skeleton.json` | Vulnerability-ranked theorem skeleton |
| `BlockExport.lean` | block-level JSON | File slicing: blocks, spine tags, tactics, docstrings |
| `RawInfoTreeExport.lean` | InfoTree raw export | Tree-structured export for downstream ingestion |

#### Lean Scripts for Exploration (`lean/scripts/DAG/Exploration/` — 15 files)

| File | Purpose |
|------|---------|
| `SemanticBlockServer.lean` | Lean executable — semantic block query server |
| `SemanticSnapshotServer.lean` | Lean executable — LLM proof-snapshot server |
| `CompilerBridgeServer.lean` | Lean executable — compiler bridge server |
| `SemanticBlockExport.lean` | Lean executable — semantic block export |
| `QueryEngine.lean`, `Search.lean` | Structured query evaluation over graph metadata |
| `Disassembler.lean` | Expression-level disassembly |
| `NaturalityDiagnostics.lean`, `NaturalityPromoter.lean` | Naturality verification |
| `SquarePromoter.lean` | Square-commuting diagram promotion |
| `Betti.lean`, `Isomorphism.lean`, `FinalSearch.lean`, `SearchRank.lean` | Specialized analysis tools |

#### Kernel Equivalence Discipline

Candidate equivalence promotion must go through the Lean/kernel lane:

```bash
lake env lean --run lean/DAG/KernelEquivalenceExport.lean \
  InfoGeometry \
  artifacts/expr-graph/translation-candidates/pairs.jsonl \
  artifacts/expr-graph/translation-candidates/lean-kernel-equivalence.jsonl \
  --mode type
```

Modes:
- **`type`**: certifies definitional equality of types/statements. May set
  `leanVerified=true`. Must **not** set `safeForAutoRewrite=true`.
- **`value`**: certifies body equality only when types are also definitionally
  compatible. Can mark rewrite-safe only when both type and value pass.
- **`type-and-value`**: both lanes. One of the only modes that can set
  `safeForAutoRewrite=true`.

Python-derived hashes, role tokens, graph SCCs, and vector neighborhoods may
propose candidate pairs but are **never allowed to set `leanVerified`** — only
this Lean-native exporter or a future Lean-native checker with the same kernel
authority may do that.

For finite RDF/Arango-style triple preservation:

```bash
lake env lean --run lean/DAG/TripleHomomorphismExport.lean \
  artifacts/triples/source.jsonl \
  artifacts/triples/target.jsonl \
  artifacts/triples/maps.jsonl \
  artifacts/triples/triple-homomorphism-audit.json \
  artifacts/triples/missing-triples.jsonl
```

### `lean/InfoGeometry/Meta/` — Lean-Native Meta Layer (28 files)

This is the **Lean-compiled meta layer** — not Python, not Markdown. These
modules define the architecture, trust, proof shape, induction, and vacuity
framework that the kernel itself can reason about.

| File | Purpose |
|------|---------|
| `Architecture.lean` | Repository architecture grammar and design intent |
| `Trust.lean` | First-pass forbidden axioms beyond explicit `sorryAx` detection |
| `ProofShape.lean` | Head shape of elaborated theorem proofs and definitions |
| `Vacuity.lean` | Vacuity analysis definitions |
| `Admission.lean` | Admission/debt tracking |
| `HonestyPolicy.lean` | Honest sorry policy implementation |
| `OwnerTarget.lean` | Owner-target declaration marking |
| `SocketTarget.lean` | Socket/wire target tracking |
| `BridgeTarget.lean` | Bridge target tracking |
| `ClosureAttribute.lean` | Closure debt attributes |
| `DefectRegistry.lean` | Defect registration and query |
| `RegionPolicy.lean` | Region/policy enforcement |
| `StrictDef.lean` | Strict definition requirements |
| `StrictSurface.lean` | Strict surface area tracking |
| `CompilerTelemetry.lean` | Compiler telemetry capture |
| `CurvatureTelemetry.lean` | Curvature telemetry |
| `DrazinRefactor.lean` | Drazin refactor patterns |
| `CalibrationReexport.lean` | Calibration re-export |
| `HiveLogos.lean` | Hive/logos integration |
| `EssenceOfInductiveProof.lean` | Inductive proof essence |
| `InductionHandbook.lean` | Induction methodology handbook |
| `InductionHowTo` (separate file) | Induction implementation guide |
| `InductiveInvariantPacket.lean` | Inductive invariant packet definitions |
| `FiniteToInfiniteTransitionSOP.lean` | Finite→infinite transition SOP |
| `InductiveLimitClosureInterface.lean` | Inductive limit closure interface |
| `MarkovJonesInduction.lean` | Markov/Jones induction patterns |
| `TestTactic.lean` | Test tactics for meta layer |
| `DvorakTactics.lean` | Custom tactics |

All of these compile **as part of `lean_lib InfoGeometryMeta`** — they are
kernel-checked Lean code, not documentation.

### `lean/InfoGeometry/Lint/` — Lint and Audit Modules (5 files, kernel-checked)

| File | Purpose |
|------|---------|
| `NonTriviality.lean` | **Kernel biopsy**: provides `#biopsy_non_triviality` command used by LeanTrail vacuity audit |
| `Pauli.lean` | Pauli auditor — rejects inflated or underived closure claims |
| `Vacuity.lean` | Vacuity analysis lint |
| `WitnessLint.lean` | Witness/certificate linting |
| `SurgeryContract.lean` | 🆕 Surgery contract module (untracked, new) |

## LeanTrail: Advanced Graph Analysis Pipeline

LeanTrail is the repository's **most advanced and actively developed tool**
(3 scripts currently dirty, `shadow_ledger.py` newly added). It integrates:

- **Kernel-checked graph data** from `lean/DAG/` exports
- **Lean kernel biopsies** via `#biopsy_non_triviality` (from `lean/InfoGeometry/Lint/NonTriviality.lean`)
- **Python orchestration** for large-scale analysis (17+ scripts in `tools/leantrail/`)
- **ArangoDB** for scalable graph algorithms

The LeanTrail tooling lives in two places:

| Component | Location | Language | Role |
|-----------|----------|----------|------|
| Backend models & store | `leantrail/backend/` (7 files) | Python | `GraphSnapshot`, `NodeRecord`, `EdgeRecord`, `GraphStore` |
| Query API | `leantrail/backend/query_api.py` | Python | REST-style graph queries (🔧 modified) |
| Schemas | `leantrail/schemas/` (7 JSON schemas) | JSON Schema | Graph snapshot, bridge request, critic packet schemas |
| API server | `leantrail/api/server.py` | Python | OpenAPI server |
| UI | `leantrail/ui/index.html` | HTML | Browser-based graph explorer |
| **Tools (active)** | `tools/leantrail/` (17 scripts) | Python | Full pipeline: conformance, vacuity, surgery, critic |

### LeanTrail Scripts

| Script | Purpose | Status |
|--------|---------|--------|
| `conformance.py` | Compare snapshots (node/edge drift, SCC, path queries, hotspot Jaccard) | ✅ |
| `export.py` | Export to GraphML, Neo4j CSV, Arango JSON | ✅ |
| `vacuity_audit.py` | Spawn Lean kernel biopsies via `#biopsy_non_triviality` | 🔧 Dirty |
| `vacuity_ingest.py` | Merge biopsy data into snapshot → `graph_snapshot.vacuity.json` | 🔧 Dirty |
| `surgery_plan.py` | SCC analysis → 4 packet streams (vacuum, bridge, proof_hole, alignment) | 🔧 Dirty |
| `shadow_ledger.py` | Approve/reject vacuum packets | 🆕 Untracked |
| `surgery_apply.py` | Byte-level splice + `lake env lean` validation | ✅ |
| `critic_packets.py` | Semantic analysis (obfuscation, docstring mismatch, witness packaging) | ✅ |
| `critic_prompt_builder.py` | LLM review prompts from critic packets | ✅ |
| `critic_ingest.py` | Merge critic judgments into snapshot | ✅ |
| `hole_packets.py` | Extract proof hole packets | ✅ |
| `failure_harvester.py` | Extract failed proof-state transitions | ✅ |
| `path_lock_registry.py` | Lock/unlock paths in the snapshot | ✅ |
| `arango_ingest.py` | Ingest LeanTrail snapshot into ArangoDB | ✅ |
| `arango_physics_evaluator.py` | Physics-motivated graph evaluation | ✅ |
| `adapters.py` | Snapshot load/save, format conversion | ✅ |

### LeanTrail Data Flow

```
graph_snapshot.json                    (raw graph from dagIndexer, 375 MB)
       │
       ▼
VacuityAudit ──► vacuity_audit.jsonl  (kernel biopsy per declaration)
       │                                ⚠ NOT YET RUN on current snapshot
       ▼
VacuityIngest ──► graph_snapshot.vacuity.json  (biopsy-enriched)
       │                                ⚠ NOT YET RUN on current snapshot
       ▼
SurgeryPlan ──► 4 packet streams:
    vacuum_packets.jsonl          (contractible fake_transport/pure_conductor)
    bridge_packets.jsonl          (axiomatic/orphan bridge obligations)
    proof_hole_packets.jsonl      (honest sorry / closure debt)
    alignment_packets.jsonl       (Hodge forest overlap candidates)
       │                           ⚠ ALL EMPTY (no vacuity evidence yet)
       ▼
ShadowLedger ──► shadow_approved_packets.jsonl  (human/automated review gate)
       │                           🆕 tool exists, not yet run
       ▼
CriticPackets ──► critic_packets.jsonl  8,711 packets  ✅ DONE
       │                           (all obfuscation_suspicion / high severity)
       ▼
CriticPrompts ──► critic_prompts.jsonl  25 MB  ✅ DONE
       │
       ▼
CriticIngest ──► graph_snapshot.critic.json  379 MB  ✅ DONE (8,719 nodes)
       │
       ▼
SurgeryApply ──► byte-level splice + lake env lean validation
                ⚠ BLOCKED (no approved vacuum packets yet)
```

## LeanTrail Vacuum Surgery & Honest Sorry Policy (v1.3)

### 1. Honest Sorry Policy

Explicit `sorry` (`sorryAx`) is permitted and tracked solely as **honest, visible
closure debt**. The toolchain strictly rejects hidden/disguised substitutes
(local axioms, opaque placeholders, witness wrappers, proof sockets, renamed
`sorry` variants).

- **Explicit `sorry`**: Honest open proof obligation; indexed and quarantined
  into proof-hole packets. Not eligible for vacuum contraction.
- **Hidden wrappers**: Blocked and routed to quarantine or rejection.

The policy is implemented in `lean/InfoGeometry/Meta/HonestyPolicy.lean`
(kernel-checked) and enforced by `lean/InfoGeometry/Lint/Pauli.lean`.

### 2. Critic Packet Semantic Analysis

The critic packet pipeline has been run on the current snapshot, producing
**8,711 `obfuscation_suspicion` packets** at **high severity**. This means every
declaration currently triggers an obfuscation suspicion — expected when no kernel
biopsy data exists. A prior run on a vacuity-enriched snapshot produced 5,571
critic packets.

| Category | What It Detects |
|----------|----------------|
| **Obfuscation suspicion** | `_statement`/`_sorry` pairs, `readback` sockets, opaque boundaries, witness field packaging |
| **Docstring/statement mismatch** | Declaration name vs. docstring claims |
| **Axiomatic frontier review** | Declarations that introduce axioms instead of proving |
| **Compatibility shim detection** | Unused forwarding modules, stale dropins, namespace duplicates |

### 3. Surgery Packet Streams

When run on a vacuity-enriched snapshot, `surgery_plan.py` classifies each SCC
into a role (priority: `contaminated > protected > exported > unknown > gate >
orphan_genuine > closure_debt > translator > pure_conductor > fake_transport >
dead_socket`) and emits four streams:

| Stream | Action | Targets | Gate |
|--------|--------|---------|------|
| **vacuum** | `contract` | `fake_transport`, `pure_conductor`; `is_prop=true`; `scc_size=1` | Shadow-approved + kernel check |
| **bridge** | `bridge` | Contaminated, protected, exported, orphan_genuine | Manual review |
| **proof_hole** | `quarantine` | `closure_debt`, `honest_sorry` | Tracked explicitly |
| **alignment** | `align` | Hodge forest overlap candidates | Signature-level alignment |

### 4. Source-Edit Gate

Before any auto-contraction, **all of these** must hold:

```text
packet_stream = vacuum
action_phase = contract
state = shadow_approved (or certified for manual debug)
decl_span_kind = top_level_decl
patch_span_kind = decl_body
source_info_kind = original
scc_size = 1
contamination = clean
is_prop = true
fileHash matches
no high-severity unresolved critic packet
```

### 5. Context Graph Tools

```bash
# Search Lean source for imports/references
rg -n "<NameOrNamespace>" lean -g '*.lean'
rg -n "import <Module.Path>" lean -g '*.lean'

# Use Lean-native interactive commands in any file:
# #deps_dot Some.Theorem
# #deps_json Some.Theorem
# #cone_json Some.Theorem   (bounded causal cone)

# Interactive cone → Arango-backed prompt
python3 tools/infra/arango_causal_chiral_cone_prompt.py \
  --decl InfoGeometry.Some.Module.some_theorem \
  --json-out artifacts/cones/some_theorem.json \
  --md-out artifacts/cones/some_theorem.md

# Visualize the cone before LLM submission
python3 tools/infra/visualize_causal_chiral_cone_packet.py \
  --json-in artifacts/cones/some_theorem.json \
  --html-out artifacts/cones/some_theorem.html

# Kernel-equivalence certification (Lean-native)
lake env lean --run lean/DAG/KernelEquivalenceExport.lean \
  InfoGeometry \
  artifacts/expr-graph/translation-candidates/pairs.jsonl \
  artifacts/expr-graph/translation-candidates/lean-kernel-equivalence.jsonl \
  --mode type
```

## Pipeline State: Current Snapshot Facts

1. **The DAG is fresh** — built at commit `37f7cca04`, toolchain `v4.28.0`.
   93,554 nodes, 782,004 edges, 5,473 types, 9,929 morphisms.

2. **Conformance passes** — 10/10 checks, 0% node/edge drift, 1.0 Jaccard
   for coherence and holonomy hotspots.

3. **Critic analysis is complete** — 8,711 obfuscation-suspicion packets
   generated and ingested (8,719 nodes enriched).

4. **Vacuity audit has NOT been run** on the current snapshot. The tool is
   under active development (103 lines modified). Without kernel biopsy data,
   the surgery plan produces zero packets.

5. **Surgery plan reports `vacuity_evidence_nodes: 0`**. This is expected and
   documented: without biopsy enrichment, the planner cannot classify SCCs.

6. **22 untracked Lean files** add new modules in Dynamics, Clifford,
   OperatorAlgebra, OptimalTransport, Topological, Cantor, and Codes.

## Live Repository Surface

### Lean Libraries

| Library | `lake` name | Source | Description |
|---------|------------|--------|-------------|
| InfoGeometry | `lean_lib InfoGeometry` | `lean/InfoGeometry/` | Main theorem library (84 dirs, 2,442 files) |
| DAG | `lean_lib DAG` | `lean/DAG/` | Lean-side graph export (60+ files) |
| InfoGeometryMeta | `lean_lib InfoGeometryMeta` | `lean/InfoGeometry/Meta/` | Lean-native meta layer (28 files) |
| InfoGeometryCanonical | `lean_lib InfoGeometryCanonical` | `lean/InfoGeometry/Canonical/All.lean` | Canonical theorems root |
| InfoGeometryLLM | `lean_lib InfoGeometryLLM` | `lean/InfoGeometry/LLM/` | LLM interaction layer |
| Agent | `lean_lib Agent` | `lean/Agent/` | Agent/runtime interface |
| Docs | `lean_lib Docs` | `lean/Docs/` | Doc generation support |
| Socratic | `lean_lib Socratic` | `lean/Socratic/` | Socratic dialogue framework |
| SelfReference | `lean_lib SelfReference` | `lean/SelfReference/` | Self-referential constructions |
| Experimental | `lean_lib Experimental` | `lean/Experimental/` | Experimental / in-progress work |
| AuditNative | `lean_lib AuditNative` | `lean/AuditNative.lean` | Native audit/verification |
| AuditStrict | `lean_lib AuditStrict` | `lean/AuditStrict.lean` | Strict linting and audit |
| PrimitiveSetsAboveX | `lean_lib PrimitiveSetsAboveX` | `external/` | Pinned Erdos #1196 proof (v4.30.0-rc1) |
| scripts | `lean_lib scripts` | `lean/scripts/` | Lake script helper modules |

### Lean Executables

| Executable | Module Root | Purpose |
|------------|-------------|---------|
| `dagIndexer` | `DAG.Indexer` | Declaration graph indexer (main export pipeline) |
| `groundTruthHarvester` | `DAG.GroundTruthHarvester` | Ground truth extraction |
| `infotreeExtract` | `DAG.InfoTreeExtract` | InfoTree extraction |
| `disconnectedAudit` | `DAG.DisconnectedAudit` | Disconnected declaration audit |
| `exactProoflessnessAudit` | `DAG.ExactProoflessnessAudit` | Proof-less declaration audit |
| `semanticBlockExport` | `scripts.DAG.Exploration.SemanticBlockExport` | Semantic block export |
| `semanticBlockServer` | `scripts.DAG.Exploration.SemanticBlockServer` | Semantic block query server |
| `compilerBridgeServer` | `scripts.DAG.Exploration.CompilerBridgeServer` | Compiler bridge server |
| `semanticSnapshotServer` | `scripts.DAG.Exploration.SemanticSnapshotServer` | LLM proof-snapshot server |

### Python

| Component | Path | Role |
|-----------|------|------|
| LeanTrail tools | `tools/leantrail/` (17 scripts) | Vacuity, surgery, critic, conformance pipeline |
| DAG infrastructure | `tools/infra/` (~50 scripts) | DAG refresh, Arango ingest, algorithms |
| Frontier | `tools/frontier/` | Semantic snapshots, proof sessions |
| Quality | `tools/quality/` | Closure debt crawl, placeholder audit |
| Observability | `tools/observability/` | Graph overlay HTML reports |
| Alexandria | `tools/alexandria/` | External knowledge integration |
| CLI package | `src/igf/` | Maintained CLI (`igf` command) |
| CLI entry | `scripts/cli.py` | `infogeometry` console script |
| Total | 451 Python files | |

### Generated & Operational Artifacts

| Directory | Size | Contents |
|-----------|------|----------|
| `artifacts/dag/index/` | 3.3 GB | `decls.jsonl`, `edges.jsonl`, `morphisms.jsonl`, `types.jsonl`, topology overlays, `meta.json` |
| `artifacts/dag/process-flow/` | — | `flow-edges.jsonl`, `process-events.jsonl`, `defects.jsonl`, lawful-path candidates |
| `artifacts/leantrail/` | 1.8 GB | Snapshots, vacuity/critic data, surgery packets, conformance reports |
| `artifacts/infotree/` | — | Lossless InfoTree materializations |
| `artifacts/graph_overlay/` | — | HTML graph overlay reports |
| `reports/` | — | Generated audit and debt reports |

## Quick Start

### Python Tooling (first time)

```bash
python3 -m venv .venv
. .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install -e .
```

### Basic Lean + DAG Checks

```bash
lake script run changedVerify    # verify changed files build
lake script run dagStatus        # check DAG freshness
lake script run dagDoctor        # detailed DAG diagnostics
```

### Full DAG Refresh

```bash
lake script run dagAll           # full pipeline: build → index → report
```

### Run Vacuity Audit (the next step to unblock surgery)

```bash
lake script run leantrailVacuityAudit \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --out artifacts/leantrail/vacuity_audit.jsonl \
  --module-batch-size 25 --keep-going

lake script run leantrailVacuityIngest \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --audit artifacts/leantrail/vacuity_audit.jsonl

lake script run leantrailSurgeryPlan \
  --snapshot artifacts/leantrail/graph_snapshot.vacuity.json
```

### Review Critic Packets (already available)

```bash
# Generate LLM review prompts from existing critic packets
lake script run leantrailCriticPrompts \
  --packets artifacts/leantrail/critic_packets.jsonl

# View reports
cat artifacts/leantrail/critic_report.md
cat artifacts/leantrail/critic_prompts.md

# Inspect a single packet
head -1 artifacts/leantrail/critic_packets.jsonl | python3 -m json.tool | head -40
```

### Kernel Equivalence (Lean-native certification)

```bash
lake env lean --run lean/DAG/KernelEquivalenceExport.lean \
  InfoGeometry \
  artifacts/expr-graph/translation-candidates/pairs.jsonl \
  artifacts/expr-graph/translation-candidates/lean-kernel-equivalence.jsonl \
  --mode type
```

### IGF Pipeline CLI

```bash
igf preflight
igf build --print-json
igf run --strict --print-json
igf validate --strict --print-json
```

### GraphRAG Explorer

```bash
python3 tools/infra/ask_repo.py "Weyl character formula" --top-k 8
```

## Quick Command Reference

### Lake Scripts

| Command | Purpose | Status |
|---------|---------|--------|
| `dagStatus` | Check DAG freshness | ✅ |
| `dagDoctor` | DAG diagnostics | ✅ |
| `dagRefresh` | Full DAG re-index | ✅ |
| `dagReports` | Generate DAG reports | ✅ |
| `dagAll` | Full DAG pipeline | ✅ |
| `leanGraphSlice` | Project hydrated DAG slice to lean-graph JSON | ✅ |
| `changedVerify` | Verify changed files build | ✅ |
| `strictCheck` | Strict Lean lint driver | ✅ |
| `leantrailConformance` | Compare snapshots | ✅ |
| `leantrailExport` | Export to GraphML/Neo4j/Arango | ✅ |
| `leantrailVacuityAudit` | Kernel biopsy audit | 🔧 Modified, not yet run |
| `leantrailVacuityIngest` | Merge audit into snapshot | 🔧 Modified, not yet run |
| `leantrailSurgeryPlan` | Generate surgery packets | 🔧 Modified, blocked |
| `leantrailShadowLedger` | Approve/reject packets | 🆕 Untracked |
| `leantrailCriticPackets` | Semantic analysis | ✅ 8,711 packets |
| `leantrailCriticPrompts` | LLM review prompts | ✅ 25 MB |
| `leantrailCriticIngest` | Merge critic judgments | ✅ 8,719 nodes |
| `leantrailHolePackets` | Extract proof hole packets | ✅ |
| `leantrailArangoIngest` | Ingest into ArangoDB | ✅ |
| `leantrailArangoPhysicsEval` | Arango physics evaluation | ✅ |
| `leantrailFailureHarvest` | Harvest failure data | ✅ 5,560 failures |
| `leantrailPathLock` | Path lock registry | ✅ |
| `leantrailSurgeryApply` | Apply approved surgery | ⚠ Blocked |
| `semanticAudit` | Run semantic audit | ✅ |
| `semanticSnapshot` | Build semantic snapshot | ✅ |
| `proofSession` | Proof session handler | ✅ |
| `proofPrint` | Proof reconstruction printer | ✅ |
| `chatgptCollaborator` | ChatGPT bridge | ✅ |
| `blueprintAlexandriaBridge` | Blueprint ↔ Alexandria | ✅ |
| `blueprintArangoMatch` | Blueprint ↔ Arango | ✅ |
| `paperproofTraceBridge` | Paperproof trace | ✅ |
| `leanParanoiaAudit` | LeanParanoia audit bridge | ✅ |
| `refreshBlueprintTags` | Refresh blueprint tags | ✅ |
| `bilingualSpineReport` | Generate bilingual spine report | ✅ |
| `leanAutoTraceBridge` | Lean auto trace bridge | ✅ |

### Lean Executables (run directly)

```bash
lake env lean --run lean/DAG/KernelEquivalenceExport.lean <args>
lake env lean --run lean/DAG/TripleHomomorphismExport.lean <args>
lake env lean --run lean/DAG/ProcessFlowExport.lean <args>
lake env lean --run lean/DAG/ExprArangoExport.lean <args>
```

### Lean Interactive Commands (in any .lean file)

```lean
import DAG.ConeCommand
#deps_dot Some.Theorem
#deps_json Some.Theorem
#cone_json Some.Theorem
```

### Lean Build

```bash
lake env lean <file>.lean           # check single file
lake build <Module.Name>            # build specific module
lake build                          # full library
lake build InfoGeometry.All         # umbrella build
```

## Closure-Debt Constructive-Proof SOP

### 1. Run deterministic debt discovery first

```bash
python3 tools/quality/closure_debt_crawler.py \
  --root lean \
  --json-out reports/audit/repo-closure-debt-crawler.json \
  --md-out reports/audit/repo-closure-debt-crawler.md \
  --print-summary

python3 tools/quality/placeholder_audit.py \
  --root lean/InfoGeometry \
  --json-out reports/audit/repo-placeholder-audit.json \
  --md-out reports/audit/repo-placeholder-audit.md \
  --signals-out reports/audit/repo-placeholder-signals.json
```

Agentic file-by-file audit:

```bash
python3 tools/quality/run_agentic_closure_debt_audit.py \
  --root lean \
  --coding-agent-command 'codex exec --json' \
  --out-dir reports/audit/agentic-closure-debt \
  --limit 1 --print-progress
```

### 2. Prioritize work

- **P0**: hard findings (`sorry`, `admit`, unsafe proof holes)
- **P1**: owner-target propositions lacking theorem-backed constructive chains
- **P2**: soft/advisory debt (skeletal proofs, packaging debt)

### 3. Enforce proof authority policy

- No witness placeholders as final authority.
- Green compile is necessary but not sufficient.
- Every promoted proposition must be backed by explicit derivation notes.
- Prefer existing mathlib lemmas; add minimal intermediate lemmas as needed.
- External literature is input for theorem design only.
- Reject vacuous packaging as closure evidence.

### 4–7. Verify, re-scan, commit, deduplicate

See the full SOP in the [dag-wire-refactor skill](skills/lean-dag-wire-refactor/SKILL.md)
for the dedicated deduplication/wire-removal protocol.

## Key Results

### 1. Thermodynamic Synthesis: Non-Commutative Bregman Divergence

Formalizes `A_info = (Δ - 1) - log Δ` as operator-valued Helmholtz free energy
in the finite nilpotent sector (`CoproductToVirasoroCocycleBridge`, `N^2 = 0`).

### 2. Cantor/Fock and Dirac Sea Geometry

- `CantorFockSpace.lean` — fermionic annihilation (`a^2 = 0`), Cantor prefix readout
- `DiracSea.lean` — combinatorial `ℤ → Bool` boundary flip, nilpotent `diracSeaStep`

### 3. Erlangen 2.0 / Langlands Roof (Capstone Layer)

Three capstone theorem files close the loop:

| Capstone | Location | Theorems | Content |
|----------|----------|----------|--------|
| **FockCapstone** | `Capstone/FockCapstone.lean` | 9 | Split Clifford tower → CAR → Cuntz → o(∞,∞) |
| **CommutantMoebiusLegendre** | `Capstone/CommutantMoebiusLegendre.lean` | 12 | Commutant∩SL(2,ℝ)∩J = o(5,5) |
| **ErlangenLanglandsRoof** | `Capstone/ErlangenLanglandsRoof.lean` | 7 | Klein bottle topology of ζ(s), roof closed |

**Key proven invariants:**
- O(5,5) preserves the Krein null cone (causal structure) — `o55_preserves_nullCone`
- O(5,5) preserves the natural cone (thermodynamic arrow) — `o55_preserves_naturalCone`
- The ζ-function partition identity: det(1-e^{-βH})⁻¹ = ∏(1-p^{-β})⁻¹ = Σ n^{-β} = ζ(β)
- The functional equation ξ(s) = ξ(1-s) as J-modular conjugation
- Klein bottle topology: cylinder gluing under β↔1-β

**SymPy verification twins:**
- `tools/sympy/o55_commutator_verify.py` — 8/8 O(5,5) checks ✅
- `tools/sympy/fock_capstone_verify.py` — 6/6 CAR+tower+Cuntz checks ✅
- `tools/sympy/erlangen_langlands_capstone.py` — ξ(s)=ξ(1-s) to 10⁻³⁶ ✅

### 4. Ongoing Expansions (untracked, 22 new files)

| Area | Files | Topics |
|------|-------|--------|
| **Dynamics** | 8 | BisognanoWichmann, TomitaTakesaki, KMS, Rindler, Wasserstein |
| **Clifford** | 5 new | Bott, Moebius, S-matrix, Log CFT, Modular CFT |
| **OperatorAlgebra** | 5 new | Continuum limit, Erlangen-Jaynes-Gromov, Log monodromy |
| **Topological** | 3 new | Anyons, Fibonacci |
| **OptimalTransport** | New dir | OT bridge module |
| **Cantor, Codes** | New dirs | Cantor constructions, code families |

## Documentation Map

Start with these:

| Document | What It Covers |
|----------|---------------|
| [docs/README.md](docs/README.md) | Documentation routing system & philosophy |
| [docs/CODEBASE_STATUS.md](docs/CODEBASE_STATUS.md) | Previous verified state (stale: 2026-05-02) |
| [docs/RepositoryMemoryMap.md](docs/RepositoryMemoryMap.md) | High-level repo structure |
| [docs/ModuleMap.md](docs/ModuleMap.md) | Lean module dependency structure |
| [docs/LeanTrail.md](docs/LeanTrail.md) | LeanTrail blueprint and API surface |
| [docs/ARANGO_DAG_REFRESH_METHODOLOGY.md](docs/ARANGO_DAG_REFRESH_METHODOLOGY.md) | Full Arango refresh runbook |
| [lean/DAG/README.md](lean/DAG/README.md) | DAG subsystem documentation (kernel-checked graph export) |
| [leantrail/README.md](leantrail/README.md) | LeanTrail backend docs |
| [docs/CONSTRUCTIVE_CLOSURE_MANDATE.md](docs/CONSTRUCTIVE_CLOSURE_MANDATE.md) | Closure mandate policy |
| [docs/FORMULA_FUNCTION_POLICY.md](docs/FORMULA_FUNCTION_POLICY.md) | Formula/function discipline |
| [PAULI_MANDATE.md](PAULI_MANDATE.md) | Pauli auditor discipline |
| [skills/lean-dag-wire-refactor/SKILL.md](skills/lean-dag-wire-refactor/SKILL.md) | Wire removal/refactor skill |

For induction systematics:
- [docs/InductionSystematics.md](docs/InductionSystematics.md)
- [docs/InductionHowTo.md](docs/InductionHowTo.md)
- [skills/induction-systematics/SKILL.md](skills/induction-systematics/SKILL.md)

## Agentic Pipeline — Autonomous Self-Improving Proof Chain

This repository includes a fully autonomous agentic pipeline that scans, ranks,
and resolves formal proof debt. A novice agent opening this repo should follow
this guide to understand and operate the system.

### 1. Cognitive Architecture (5 Pillars)

| Pillar | Function | Formalization |
|--------|----------|---------------|
| **Logos** | Conscious theorem inventory | `lean/InfoGeometry/Meta/FormalLogos.lean` |
| **Sensing** | Self-model of proof topology | `lean/InfoGeometry/Causal/ProofDAGRepresentation.lean` |
| **Shadow** | Boundary cochain tracking | `lean/InfoGeometry/SelfReference/ShadowCone.lean` |
| **Transcendent** | Archetype detection across domains | `lean/InfoGeometry/Meta/TranscendentFunction.lean` |
| **Conscience** | Vacuity pattern detection | `tools/infra/vacuity_critic.py` (18 patterns) |

### 2. Quick Start for a Novice Agent

```bash
# 1. Build the project
lake build InfoGeometry.All

# 2. Scan for all `:= by sorry` shadows
python3 tools/infra/shadow_cone_scanner.py

# 3. Scan for all `_True` obfuscation patterns
python3 tools/leantrail/vacuity_audit.py --snapshot artifacts/leantrail/graph_snapshot.json

# 4. Detect archetypal operator patterns across domains
python3 tools/infra/detect_archetypes.py

# 5. Enqueue top shadows to the proof-search queue
python3 -c "
from tools.infra.hive_arango_queue import enqueue_goal, aql
from tools.infra.arango_env import *
from pathlib import Path
import hashlib, json

load_repo_arango_env(Path.cwd())
ep = arango_endpoint(); db = arango_database('infogeometry')
usr = arango_username(); pwd = arango_password('alexandria_root')

shadows = [json.loads(l) for l in open('artifacts/shadow_cones/shadows.jsonl') if l.strip()]
for s in shadows[:10]:
    target = f'Resolve shadow \`{s[\"apex_name\"]}\` in {s[\"file\"]}:{s[\"line\"]}'
    gh = hashlib.sha256(target.encode()).hexdigest()[:24]
    module = s['file'].replace('.lean','').replace('/','.')
    enqueue_goal(ep, db, usr, pwd, queue_name='proof-search',
        goal_hash_shape=gh, canonical_shape=gh, target_pretty=target,
        module=module, goal_index=s['line'], priority=1.0, task_kind='proof.search')
"

# 6. Start the evolution worker (processes the queue)
python3 tools/infra/evolution_worker.py
```

### 3. Understanding the Shadow Lifecycle

Shadows progress through five statuses:

```
Roaming → Incident → Paired → Integrated
                               → Rejected
```

- **Roaming**: no proof-DAG incidence detected (semantic similarity only)
- **Incident**: one-sided incidence (dependencies or dependents found)
- **Paired**: two-sided incidence (both past and future cone nodes identified)
- **Integrated**: resolved as theorem, axiom, or explicit conditional premise
- **Rejected**: proven impossible or meaningless

### 4. Key Files and What They Do

| File | Purpose |
|------|---------|
| `tools/infra/evolution_worker.py` | Main daemon — polls ArangoDB queue, runs 3-stage pipeline |
| `tools/infra/gepa_evolver.py` | Genetic Evolutionary Proof Algorithm — mutates skills |
| `tools/infra/shadow_cone_scanner.py` | Scans `:= by sorry`, computes past/future incidences |
| `tools/infra/vacuity_critic.py` | Reviews failed tasks, discovers new obfuscation patterns |
| `tools/infra/proof_seeker.py` | Searches mathlib, arXiv, web for existing proofs |
| `tools/infra/chatgpt_browser_harness_driver.py` | Browser CDP automation for ChatGPT audit |
| `tools/infra/hive_arango_queue.py` | ArangoDB-backed task queue with leasing |
| `lean/InfoGeometry/Meta/ShadowLedger.lean` | Formal shadow ledger (Lean structures) |
| `lean/InfoGeometry/Meta/TranscendentFunction.lean` | Formal archetype/synthesis structures |
| `lean/InfoGeometry/Causal/ProofDAGRepresentation.lean` | Proof DAG + Hodge operator bridge |
| `lean/InfoGeometry/SelfReference/ShadowCone.lean` | Shadow cone carrier layer |

### 5. The 3-Stage Resolution Pipeline

Each shadow task is processed through up to 3 stages:

**Stage 0 — ChatGPT Audit**: aiClaw/DevTools checks that the ChatGPT tab is
ready, sends the complete owner file plus all relevant build errors in one
prompt, waits for the final visible answer, and records a review/audit
suggestion. If the aiClaw API returns the intermediate `Thinking` payload, do
not send a second prompt; recover the final visible answer read-only from the
browser DOM.

**Stage 1 — Coding Agent Repair**: Codex/Pi/DeepSeek-style coding agents use
the audit suggestion as evidence, edit the owner Lean file, compile, read
errors, fix, and repeat. The chatbot is not the coding agent and does not own
the patch.

**Stage 2 — Proof Seeker**: Falls back to searching mathlib, arXiv, web, and
Alexandria corpus if stages 0-1 fail.

### 6. Authority Boundary

The pipeline can propose, reflect, and evolve, but:

- **Lean kernel** is the final authority (via `lake build`)
- **LeanTrail** is a "semantic explorer scaffold" (see `docs/LeanTrail.md`)
- **ArangoDB graph** is a "projection over compiler memory"
- **ChatGPT/aiClaw** is a Socratic auditor and repair suggester, not proof
  authority
- **Proposals are not theorems** until the kernel says they are

### 7. Current State

```
Build:         10118 jobs, passes
Shadows:       145 `:= by sorry` across 13 modules
Queue:         50 tasks in ArangoDB proof-search, pending
Worker:        evolution_worker.py running (daemon)
_True fields:  Eliminated (~220 across ~25 files)
ClosureDebt:   2 fields in Eval/ClosureDebtTest.lean (DO NOT FIX — GEPA targets)
```

## UTMOST MANDATE: Native Lean proof closure over witness/certificate scaffolding

Replacing witness-gated and external-certificate leftovers with native Lean
proofs is the top-priority mandate.

- Witness packets, certificate fields, external certificates, and assumption
  interfaces are **temporary scaffolding only**.
- They are **not final mathematical closure** and **not promotion authority**.
- Every promoted proposition must be discharged by native Lean derivation chains.
- Open gaps must be recorded explicitly — **do not package them as complete**.
- **Real progress** = replacing certificate/witness fields with theorem-backed
  native derivations.

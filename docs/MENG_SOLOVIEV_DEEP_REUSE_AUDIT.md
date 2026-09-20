# Meng, Soloviev, and the existing operator infrastructure

Audit date: 2026-09-14. Scope: the supplied working tree, not an asserted fresh
checkout of GitHub. This is a reuse audit, not a new nuclear model.

## Finding

The repository contains substantially more than a two-state Soloviev matrix.
It already has arbitrary-index CAR/RPA interfaces, a graded bath centralizer,
exact Heisenberg channel decompositions, a concrete Zorn-valued common carrier,
five-grade representation maps, and a projected-Hamiltonian theorem on that
carrier. There are also native circular Peirce coordinates and nonzero
computed Kantor root-channel actions. Rebuilding those layers would duplicate
existing mathematics.

The remaining question is which *specific source Hamiltonian* those operators
represent. An algebraic grading, a multipole-labelled injection, and a
physical spherical tensor are different declarations until an explicit map
and its intertwining properties connect them.

## Search coverage and recovery checks

Before editing, the search inventoried 95,631 files and searched textual
contents recursively, including hidden/ignored files, recovery trees,
`proofs/`, `external_refs/`, archives, generated sources, and all `lean/`
subdirectories. Only Git metadata was excluded. Binary contents and targets
behind unfollowed symlinks were not interpreted as text.

The combined nuclear/algebraic query matched 4,905 files, including 2,456 in
`recovered/`, 1,011 in `lean/`, 426 in `proofs/`, and 232 in `docs/`.
Content searches for Soloviev/quasiparticles/phonons found 105 Lean files under
`lean/`. Their declaration inventories were inspected, then relevant owners
were followed through proof bodies and imports rather than selected by filename.

A second whole-tree nuclear-content pass found 239 matching Lean files with
122 distinct SHA-256 content groups. The 17 groups not byte-identical to a
matching `lean/` file have representatives under `proofs/`; recovered copies
were included in this comparison. This avoids mistaking repeated recovered
copies for additional independently implemented Hamiltonians.

Search commands, with outputs kept outside the source tree:

```sh
rg --files --hidden --no-ignore -g '!**/.git/**' > /tmp/meng-full-repo-files.txt
rg -l -i --hidden --no-ignore -g '!**/.git/**' \
  'solov[iy]e[vf]|soloviev|quasiparticle|quasi.particle|phonon|multipol|octupol|quadrupol|kantor|triple.product|three.body|three.nucleon|polarized.spin|polarised.spin|spin.frame|weyl.*chiral|chiral.*weyl|pauli|five.grad|5.grad' \
  . > /tmp/meng-full-content-hits.txt
rg -l -i --hidden --no-ignore -g '!**/.git/**' -g '*.lean' \
  'solov[iy]e[vf]|soloviev|quasiparticle|quasi.particle|phonon' \
  . > /tmp/meng-all-nuclear-lean.txt
```

Additional content passes checked spherical tensors, residual interactions,
Woods-Saxon terms, explicit three-body fields, grade transport, and triple
identities. A search miss alone is not a proof of nonexistence. Findings below
are tied to inspected declaration bodies; the scan is not a claim that every
file was manually read or every theorem compiled.

## Compare the source Hamiltonians first

### Meng's ideal ChP model

The [selection-rule paper](https://arxiv.org/abs/2006.12062), equations (1)-(3),
uses a reflection-asymmetric triaxial particle-rotor Hamiltonian. At the ideal
triaxial point its core includes

\[
H_{\rm core}=\frac{R_3^2+4(R_1^2+R_2^2)}{2\mathcal J_0}
 +\frac{E(0^-)}2(1-P_c),
\]

and its particle mean field contains quadrupole and octupole terms
proportional to \(r^2[\beta_{22}(Y_{22}+Y_{2,-2})/\sqrt2+\beta_{30}Y_{30}]\).
The special chiture symmetry also requires the specified particle/hole-shell
conditions. This is not simply a renamed generic QPM interaction.

### Soloviev's quasiparticle-phonon model

[Soloviev, Sushkov, Shirikova, *Dipole excitations in deformed nuclei*](https://www1.jinr.ru/Archive/Pepan/v-31-4/v-31-4-2.pdf),
printed pages 788-789, starts from a mean field, pairing, and separable
multipole interactions. After a Bogoliubov transformation, equation (6) is
\(H_{\rm QPNM}=\sum\epsilon_q\alpha^\dagger_{q\sigma}\alpha_{q\sigma}+H_v+H_{vq}\).
Equation (3) explicitly uses conjugate circular factors \(1\pm i\sigma\) in
the creation/annihilation-pair expansion of a phonon. Thus the circular-basis
comparison has a direct source formula, not only a geometric analogy.

The downloaded reference is `/tmp/meng-soloviev-dipole.pdf`, SHA-256
`fe4525274c8cc54ceb2b13eda93bf14d0f54a6089a2af4cc134894153beebce2`.
PDF pages 4 and 5 were rendered and visually checked. Meng's presentation
and paper remain at the locations recorded in `MENG_CHP_FORMALIZATION.md`.

## Existing owners: reuse, do not redefine

Paths below are relative to `lean/InfoGeometry/` unless prefixed otherwise.
“Source” means the statement and proof body were inspected; it does not by
itself mean that the whole import closure was rebuilt during this audit.

| Layer | Existing owner and declaration | Exact scope |
|---|---|---|
| Multimode quasiparticles | `Physics/NuclearQuasiparticleCARBridge.lean:184`, `freeQuasiparticleHamiltonian`; `comm_freeQuasiparticleHamiltonian_adag` | Finite sums over an arbitrary mode index; CAR supplied by `QuasiparticleCAR`. |
| Multimode phonons | `Physics/NuclearPhononRPAAlgebra.lean:100`, `harmonicPhononHamiltonian`; `comm_harmonicPhononHamiltonian_Qdag` | Exact consequences of the quasiboson CCR interface; not a derivation of that approximation from fermion pairs. |
| Graded interacting EOM | `Physics/NuclearGradedBathCommutant.lean:78`, `ThermalQuasiparticleModel`; `total_eom_grade_support` | Bath centralizer and interaction grade hypotheses give the grade-0/1/2 EOM support. |
| Explicit EOM channels | `Physics/NuclearHeisenbergChannelDecomposition.lean:63`, `heisenberg_evolution_eq_channels`; `heisenberg_evolution_decomposition` | Reuses the preceding model to decompose the actual commutator. |
| Concrete common carrier | `Physics/NuclearFiveGradeCommonCarrierRepresentation.lean:141`, `representation`; `representation_mul`, `representation_preserves_grade`, `phonon_CCR` | Real two-mode CAR acts on `ℕ → (Fin 4 → NativeZorn)`; phonon shifts and coefficient derivations commute with the fermionic action. |
| Actual common-carrier compression | `Physics/NuclearFiveGradeSolovievCommonCompression.lean:230`, `fullHamiltonian`; `projected_fullHamiltonian_on_model` | Compresses `Eqp • Nqp + omega • Nph + V • (creation + annihilation)` through explicit embedding/readout/projector maps. |
| Same-carrier assembly | `Physics/NuclearFiveGradeSameCarrierClosure.lean:36`, `nuclear_same_carrier_closure_packet` | Combines the Lie representation, CAR/CCR, grading, compression, and finite BdG results; not just unrelated carrier labels. |
| Independent checked complex realization | `Physics/NuclearCARPhononCommonCarrier.lean:250`, `oscillatorHamiltonian`; `compressedOscillatorHamiltonian_eq_soloviev` | Exact CAR and infinite algebraic occupation-ladder CCR, followed by a two-sector compression. |
| Concrete-to-generic five-grade interface | `Physics/NuclearFiveGradeKantorComponentBridge.lean:51`, `hasGrade_iff_isCommutatorComponent` | Identifies concrete occupation grades with the associative Kantor-Peirce commutator predicate; does not identify the Freudenthal carrier. |
| Generic multipole-labelled channel | `Nuclear/NuclearFiveGradedOperatorReexpression.lean:145`, `multipoleOperator`; `grading_commutes_multipole` | Injects an arbitrary `SymplecticTKKZero D` into degree zero. No rank-λ spherical-tensor matrix elements are computed in this declaration. |
| Operator-valued Zorn super-Hamiltonian | `Physics/NuclearOperatorZornSuperSolovievBridge.lean:102`, `diracSuperHamiltonian_invariant` | Reuses internal/outer parity and native associative operator-Zorn multiplication. |
| Higher operator/frame assembly | `Canonical/OperatorFourPotentialFiveGradeBridge.lean:61`, `nuclearSoldering`; `fiveGrade_recompose_zorn` | Existing Fock-valued soldering, Nambu-coordinate transport, even/odd splitting and entrywise five-component reconstruction. |

The Zorn-valued common carrier is already a substantial lift. Its displayed
Hamiltonian still has one oscillator and an explicit two-state readout.
“Full” in `fullHamiltonian` contrasts the pre-compression carrier with its
compression; it does not establish equality with every term of the published
microscopic QPM Hamiltonian.

## Kantor triples and the proposed three-body term

There are several genuinely different levels, all worth retaining:

1. `Algebra/KantorTripleFiveGrading.lean:13` bundles a trilinear product with
   its two Kantor identities. `D_comm_D` and `K_K_eq_DK_add_KD` prove operator
   consequences of those fields; they do not construct a nuclear force.
2. `Algebra/Zorn/CanonicalKantorOperators.lean` defines the concrete native
   polynomial
   \(V(x,y)z=(x\bar y)z+(z\bar y)x-(z\bar x)y\), and its `K` operator.
   `Lie/SplitOctonionStructurableKantor.lean:79` identifies the older operator
   names with this owner.
3. `Lie/SplitOctonionEllKantorRankOne.lean:56` and following declarations
   compute, on actual circular roots,
   \(V(E,F)E=-2E\), \(K(E,F)E=-E\), \(K(E,F)F=F\), plus mixed-channel
   identities. These are concrete calculations, not merely assumed triples.
4. `Canonical/H3ZornKantorTripleSystemBridge.lean:14` gives the H3 Jordan
   triple/inner-derivation normal form. Its `kantor_operator_vanishes` is the
   **Jordan boundary** result, not a nonzero nuclear interaction.

Consequently it would be wrong either to say “there is no triple algebra” or
to identify every ternary expression with a three-nucleon force. A physical
identification needs particle labels, antisymmetrization, coefficients, a
state-space action, and equality to the proposed Hamiltonian contribution.
These data are not supplied by the displayed Kantor identities.

The especially relevant content hit `proofs/ChiralIsospinEOMSU2.lean:52`
declares `V_chiral_3body`; its concrete `MyEOM` sets that field to zero at
line 162. Likewise `proofs/CPTConformantTriaxialHamiltonian.lean` sets
`H_spin`, `H_total`, and `H_coup` to zero. Those particular witnesses cannot
certify a nonzero microscopic force, regardless of their surrounding prose.
No source files were changed to hide or strengthen these limitations.

## Circular, polarized and Weyl frames

- `Lie/SplitOctonionEllCircularOperatorCoordinates.lean:37` already expands
  an arbitrary native Zorn element in a proved eight-element circular Peirce
  basis. It also gives diagonal axial action and left/right coordinate
  operators. This is a better starting point than inventing eight new labels.
- `Canonical/AlbertPeirceChiralFrameEmbedding.lean:30` embeds the real
  two-by-two chiral frame into three Albert Peirce channels, with injectivity,
  explicit product routing, and Peirce eigenvalue proofs.
- `Physics/BogoliubovPauliSolderedFrame.lean:179` reconstructs both an
  operator coordinate and a Pauli/tetrad soldering coordinate. The earlier
  minimal frame in that same file has a zero creator leg; the later combined
  frame uses the existing phase-linear/phase-antilinear operator split.
  Neither declaration alone supplies the source QPM amplitudes.
- `Physics/CircularChiralFockOperatorZornBridge.lean` already supplies
  operator-valued circular rails on the finite Fock carrier. Use its existing
  assembly through `Canonical/OperatorFourPotentialFiveGradeBridge.lean`.
- `Algebra/Zorn/G2NativeWeylRootSpaceTransport.lean` contains native Weyl
  root-space transport. A root-system Weyl action is not automatically the
  Weyl-spinor action of physical spacetime; an identification must specify the
  representations and the map between them.

The proposed translation must also distinguish **occupation grade**,
**angular multipole rank**, **fermion parity**, and **spatial parity**. For
example, being quadratic in fermion operators does not by itself assign an
electromagnetic E2 tensor or determine its spatial-parity character.

## Dependency order and the smallest next implementation

This is a reuse/dependency plan, not a claim to have extracted Lean's entire
declaration DAG:

```text
native Zorn + circular Peirce basis -> concrete V/K root computations
native Zorn derivation envelope   -> coefficient actions on common carrier
two-mode CAR -> five-grade spaces -> common representation -> compression
generic CAR/RPA + bath centralizer -> interacting Heisenberg channels
Fock circular rails + operator-Zorn -> soldering + component reconstruction

source multipole coefficients + specified angular action
    -> operators on one chosen existing carrier
    -> proved symmetry/intertwining identities
    -> existing selection-rule and compression theorems
```

The next substantive proof should connect a *specified source multipole*
to these existing operators, not create another CAR algebra, projector,
Kantor polynomial, abstract five-grading, or Soloviev two-state matrix.
For the Soloviev phonon formula, retain both pair-creation and pair-annihilation
channels and the source circular coefficients; do not silently replace a
composite fermion-pair operator by an independent exact boson. For Meng,
establish the particular rotation/exchange/parity action before applying
`MengChPSelectionRules`.

The audit located reusable structure for that task, but not a source-matched
intertwiner establishing the full proposed identification. That is a bounded
finding from the inspected owners, not a theorem of impossibility. No new
physics definitions or duplicate theorem wrappers were added in this pass.

## Verification and import boundary

Checks are serial and use `/tmp/info-geometry-build.lock`. The pinned Lean
4.28.1 is not installed; isolated checks use installed 4.28.x and cached
Mathlib without editing the manifest, toolchain, dependencies, or build cache.

The following existing owners compiled during this audit:

- `Algebra/KantorTripleFiveGrading.lean`;
- `Canonical/KantorPeirceFiveGrading.lean` (existing unused-section warnings);
- `Physics/NuclearGradedBathCommutant.lean`;
- `Physics/NuclearHeisenbergChannelDecomposition.lean`;
- `Physics/NuclearQuasiparticleCARBridge.lean`;
- `Physics/NuclearPhononRPAAlgebra.lean`.

An import-only audit at `/tmp/MengSolovievOwnerAudit.lean` also completed
successfully. Eleven existing theorem dependencies were checked with
`#print axioms`: the two abstract Kantor identities, product-grade propagation,
free quasiparticle and harmonic phonon EOMs, two graded EOM results, and four
common-carrier CAR/CCR/commutation/compression results. All report only subsets
of `propext`, `Classical.choice`, and `Quot.sound`; none depends on `sorryAx` or
a custom axiom. This includes the existing complex
`NuclearCARPhononCommonCarrier` compression, not the blocked real Zorn-valued
branch. Explicit structure hypotheses remain hypotheses, even with a clean
axiom report.

Attempts to check the deeper real common-carrier compression and concrete
Kantor-component bridge stop in
`Canonical/SplitCliffordSourceWickBase.lean:3`: the required
`InfoGeometryCore.Basic` module is unavailable on the validation path. No
source for that module was located in the repository-wide inventory.
This is an import/environment blocker, not evidence that the downstream
mathematical statements are false, and not permission to replace the deeper
owners with a new shallow model. A full pinned-repository build is not claimed.

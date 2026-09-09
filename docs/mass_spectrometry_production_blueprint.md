# Mass-Spectrometry Foundation Model Production Blueprint

## Status and scope

This document turns the theorem-facing `InfoGeometry.MassSpectrometry` development into an implementation plan for large-scale training and deployment.

The repository remains the mathematical specification authority. PyTorch, JAX, CUDA, Triton, Rust, C++, Spark, Ray, and distributed GPU runtimes are implementation layers that must be checked against the formal contracts.

The blueprint keeps two classes of statements separate:

1. **Theorem-certified invariants** — exact algebraic and structural facts already formalized in Lean.
2. **Empirical engineering properties** — dataset sizes, model accuracy, latency, memory use, distributed scaling, and real-time feasibility, all of which must be measured.

The core production principle is:

```text
Public MS data
    -> certified mathematical representation
    -> numerical/GPU implementation
    -> Transformer residual injection
    -> scientific readout
```

Hard structural invariants should be enforced by construction. They should not be replaced by soft penalty terms when the architecture can make violations impossible.

---

## 1. Objective

Build a production-scale mass-spectrometry foundation model in which the mathematical invariants formalized in `InfoGeometry.MassSpectrometry` are preserved through preprocessing, numerical execution, training, and inference.

The target architecture is:

```text
Raw mzML / MGF / repository records
              |
              v
Dataset ingestion and normalization
              |
              v
PeakSpectrum / MellinTransformerBridge
              |
              v
CausalCrossGramian / ValuedFragmentationDAG
              |
              v
SinkhornAssignment / BirkhoffAssignment
              |
              v
CausalTransferArchitecture
              |
       +------+------+
       |             |
       v             v
CausalRetraction   ChiralDiscreteMajoranaBridge
       |             |
       +------+------+
              |
              v
SpectralToken(K, K†)
              |
              v
SpectralResidualEncoder
              |
              v
TransformerBackbone / runDecoderStack
              |
              v
Abstract downstream scientific readout
```

Molecular-graph decoding remains a separate theorem boundary until the repository has genuine chemistry graph owners.

---

## 2. Phase I — Corpus construction

### 2.1 Initial public sources

Candidate sources include:

- GNPS spectral libraries and public datasets;
- MoNA;
- MassBank;
- MetaboLights;
- CASMI blind-evaluation datasets;
- optional licensed or proprietary datasets later.

Do not assume a fixed number of usable Orbitrap spectra before ingestion. The first data-engineering deliverable is a reproducible census.

### 2.2 Dataset census

Create:

```text
dataset_manifest.parquet
```

with counts stratified by:

```text
repository
instrument_vendor
instrument_model
mass_analyzer
fragmentation_method
collision_energy
ion_mode
charge
adduct
ms_level
structure_available
experimental_vs_insilico
```

Acceptance criteria should include exact counts for:

```text
Orbitrap experimental MS2 with structure
Orbitrap experimental MS2 without structure
QTOF experimental MS2 with structure
multi-energy molecule groups
MS3+ sequences
```

Only after this census should training-corpus scale claims be made.

---

## 3. Phase II — Canonical dataset schema

Use one common record independent of source repository:

```text
SpectrumRecord
  spectrum_id
  source_repository
  source_accession
  raw_file_checksum
  instrument_vendor
  instrument_model
  analyzer
  fragmentation_method
  collision_energy_value
  collision_energy_unit
  normalized_collision_energy
  precursor_mz
  precursor_charge
  adduct
  polarity
  ms_level
  parent_scan_id
  peaks_mz[]
  peaks_intensity[]
  smiles
  inchi
  inchikey
  molecular_formula
  exact_mass
```

Keep source collision-energy values and normalized values separately. HCD NCE, laboratory-frame eV, stepped NCE, CID voltage, and vendor-specific collision settings are not interchangeable without an explicit conversion model.

---

## 4. Phase III — Spectral canonicalization

Lean owner:

```text
InfoGeometry.MassSpectrometry.PeakSpectrum
```

Reference mathematical transformation:

```text
Spectrum n
  -> Spectrum.canonicalize
  -> CanonicalSpectrum
  -> SpectralSentence = FreeMonoid Peak
```

Production implementation requirements:

- preserve every centroided peak;
- preserve peak multiplicity;
- preserve intensity;
- sort deterministically by mass;
- preserve sequence length;
- do not quantize into a fixed raster as the canonical representation.

Do not evaluate Lean directly on millions of spectra during training. Instead use:

```text
Lean specification
    -> generated fixtures
    -> CPU reference implementation
    -> production implementation
    -> conformance tests
```

Recommended storage:

```text
Apache Parquet / Arrow
+ compressed variable-length arrays
```

WebDataset shards may be added for high-throughput training.

---

## 5. Phase IV — Data quality and leakage control

Random spectrum splitting is insufficient because the same molecule may appear across repositories, collision energies, adducts, instruments, and replicate spectra.

Use hierarchical deduplication and grouping by:

```text
InChIKey
-> molecular connectivity
-> scaffold
-> source spectrum
```

Maintain at least three evaluation regimes.

### 5.1 Spectrum-held-out

Same molecules may appear in training. Measures interpolation.

### 5.2 Molecule-held-out

No identical molecular connectivity appears in training. Measures structural generalization.

### 5.3 Scaffold-held-out

No close scaffold family appears in training. Measures genuine de-novo difficulty.

CASMI-like blind evaluations belong primarily to the final regime.

---

## 6. Phase V — Mellin spectral frontend

Lean owners:

```text
MellinMassEncoding
MellinTransformerBridge
GPUExecutionContracts
```

For positive mass `m` and reference mass `m0`:

```math
tau(m;m0) = log(m/m0).
```

For rotary frequency `omega_k`:

```math
theta_k = omega_k tau.
```

The pairwise rotary action is:

```math
R_theta(x1,x2)
 = (x1 cos(theta) - x2 sin(theta),
    x1 sin(theta) + x2 cos(theta)).
```

The exact Lean invariant is:

```math
||R_theta x||^2 = ||x||^2.
```

The common-scale identity is:

```math
R_{omega log(lambda m / lambda m0)}
 = R_{omega log(m/m0)}.
```

Runtime conformance tests should use a floating-point tolerance appropriate to FP32, TF32, BF16, or FP16.

This theorem does not imply immunity to additive calibration errors, nonlinear mass-axis distortion, noise, or peak assignment errors.

---

## 7. Phase VI — Spectral feature encoder

Input shape:

```text
[B, N, peak_features]
```

Initial peak features should include:

```text
relative log mass
normalized intensity
precursor-relative neutral loss
charge/adduct embedding
collision-energy embedding
instrument embedding
optional isotope features
```

Output:

```math
Z in R^{B x N x d}.
```

Start with `d = 64` or `128`.

Do not force the entire Transformer residual width to equal the Clifford spinor width. The 64-dimensional structured spinor channel can be one subspace inside a larger residual architecture.

---

## 8. Phase VII — Cross-stage causal operator

Lean owner:

```text
CausalCrossGramian
```

For feature slices `Z1` and `Z2`:

```math
K_raw = Z1 Z2^T.
```

The theorem layer proves:

```math
(K_12)^T = K_21,
```

and recovers the auto-Gramian when the two feature slices coincide.

A production score may be enriched by a finite KAN-style potential:

```math
K_score(i,j)
 = (Z1 Z2^T)_{ij}
   Phi(tau_i, tau_j, E, z, instrument).
```

The runtime parameterization may use:

- an MLP;
- radial basis functions;
- B-splines;
- low-rank factors;
- another differentiable finite family.

The current Lean layer does not claim a universal Kolmogorov-Arnold representation theorem or B-spline approximation theorem.

---

## 9. Phase VIII — Hard causal support

Lean owners:

```text
ValuedFragmentationDAG
CausalTransferArchitecture
```

This invariant should be implemented architecturally, not merely as a penalty.

Define a support mask:

```math
M_ij = 1[ edge(i,j) and m_j < m_i ].
```

Then:

```math
K_ij = M_ij K_score(i,j).
```

The theorem-backed consequence is:

```math
K_ij != 0 -> m_j < m_i,
```

and therefore:

```math
Delta m_ij > 0.
```

A ReLU penalty on mass-increasing transitions may be logged as a diagnostic, but it should not be the primary enforcement mechanism when the illegal transition can simply be masked out.

---

## 10. Phase IX — Peak/fragment assignment

Lean owners:

```text
SinkhornAssignment
BirkhoffAssignment
```

Numerical pipeline:

```text
cost/affinity
  -> positive kernel
  -> log-domain Sinkhorn iterations
  -> approximately balanced matrix
  -> BalanceCertificate or equivalent numerical acceptance check
```

Monitor:

```math
r(A) = A 1 - 1,
c(A) = A^T 1 - 1.
```

A useful numerical residual is:

```math
L_balance = ||r(A)||_2^2 + ||c(A)||_2^2.
```

This is primarily a convergence/implementation diagnostic.

The exact theorem layer begins once a balanced matrix is certified to belong to the doubly stochastic polytope.

Important semantic boundary:

```math
A in B_n
```

means `A` is a soft convex combination of permutation matrices. It does not mean every soft matrix is itself one literal discrete assignment.

---

## 11. Phase X — Chiral directed representation

Lean owner:

```text
DirectedOperatorDoubling
```

Construct:

```math
D_K = [[0, K], [K^T, 0]].
```

This is deterministic and should not require trainable parameters.

The exact invariant is:

```math
Gamma D_K Gamma = -D_K.
```

A runtime diagnostic may be:

```math
e_chiral = ||Gamma D_K Gamma + D_K||_F.
```

The expected value is floating-point zero. A large residual indicates an implementation bug, not a model-learning problem.

---

## 12. Phase XI — Moore-Penrose reconstruction

Lean owner:

```text
CausalRetraction
```

For directed operator `K`, compute a stabilized pseudoinverse `K†`.

Possible implementations:

- SVD;
- truncated SVD;
- low-rank QR;
- damped least squares;
- a structured low-rank solver.

Parent and fragment projectors:

```math
P_parent = K† K,
P_fragment = K K†.
```

Log all four Penrose residuals:

```math
e1 = ||K K† K - K||,
e2 = ||K† K K† - K†||,
e3 = ||(K K†)^T - K K†||,
e4 = ||(K† K)^T - K† K||.
```

The exact Lean construction is the source of truth. Numerical tolerances are implementation-specific.

---

## 13. Phase XII — Majorana/Pfaffian diagnostic lane

Lean owner:

```text
ChiralDiscreteMajoranaBridge
```

Define:

```math
A_K = Gamma D_K
    = [[0, K], [-K^T, 0]].
```

The theorem layer proves:

```math
A_K^T = -A_K.
```

Potential production uses:

- skew-operator diagnostics;
- singularity/rank monitoring;
- local Pfaffian features;
- structured expert routing;
- mode decomposition.

For one scalar channel:

```math
A(a) = [[0,a],[-a,0]],
Pf(A) = a,
det(A) = a^2.
```

The bridge is algebraic. Do not interpret molecular fragments as physical Majorana particles.

---

## 14. Phase XIII — Spectral token formation

Lean owner:

```text
SpectralLatentInjection
```

Construct:

```math
T_spec = SpectralToken(K, K†).
```

The production encoder maps this structured object into the Transformer residual carrier:

```math
E_spec : T_spec -> R^{d_model}.
```

A useful decomposition is:

```math
E_spec
 = E_K
 + E_Kdagger
 + E_peak
 + E_collision_energy
 + E_instrument.
```

Use separate normalization before fusion where necessary.

---

## 15. Phase XIV — Transformer residual injection

Lean owner:

```text
InfoGeometry.LLM.TransformerArchitecture
SpectralLatentInjection
```

The formal injection is:

```math
x' = x + E_spec(S).
```

Then:

```math
h = runDecoderStack(L, x').
```

For a spectroscopy-only training batch, the base residual may be zero:

```math
x = 0.
```

For a genuinely multimodal model:

```text
text embedding ---------+
                        |
spectral embedding -----+--> shared residual backbone
                        |
metadata embedding -----+
```

Do not convert the entire spectrum into a long text prompt when a direct latent path is available.

---

## 16. Phase XV — Loss design

Separate hard constraints from trainable objectives.

### 16.1 Hard structural constraints

Implement by construction:

```text
mass direction
DAG edge legality
chiral doubling
SpectralToken lane structure
```

These should generate diagnostics, not primary weighted losses.

### 16.2 Numerical conformance objectives

Useful for approximate algorithms:

```math
L_Sinkhorn = row/column balance residual,
L_MP = e1 + e2 + e3 + e4.
```

### 16.3 Learned scientific objectives

A production objective may be:

```math
L_total
 = lambda_spec L_spectrum
 + lambda_path L_path
 + lambda_energy L_energy
 + lambda_structure L_structure
 + lambda_contrast L_contrast.
```

Possible components:

#### Spectrum reconstruction

Predict held-out peaks or a complete spectrum.

#### Energy-conditioned prediction

Given the same precursor at one collision condition, predict spectra at another condition.

#### Path likelihood

For an observed or inferred path `pi`:

```math
L_path = -log P_E(pi) = K_E(pi).
```

#### Contrastive spectrum/structure alignment

Bring spectra from the same molecular identity together and separate unrelated structures.

#### Molecular structure loss

Use only where trusted molecular labels are present. This is not currently theorem-certified by PR #88.

---

## 17. Phase XVI — Training curriculum

Do not begin with full de-novo molecular graph generation.

### Stage A — Spectral self-supervision

Tasks:

```text
masked peak reconstruction
next-fragment prediction
collision-energy prediction
precursor reconstruction
spectrum denoising
```

### Stage B — Cross-energy learning

Group spectra by molecular identity and collision condition.

Train mappings such as:

```math
(S, E1) -> S_E2.
```

### Stage C — Fragment assignment

Introduce candidate formulas or substructures and train the Sinkhorn/Birkhoff routing layer.

### Stage D — Molecular retrieval

Rank the correct molecule from a large candidate set.

### Stage E — De-novo molecular graph generation

Only after the spectral latent representation demonstrates robust out-of-distribution behavior.

---

## 18. Phase XVII — Future molecular graph decoder

This should be a separate theorem boundary.

Potential future Lean owners:

```text
InfoGeometry.Chemistry.Element
InfoGeometry.Chemistry.Atom
InfoGeometry.Chemistry.Bond
InfoGeometry.Chemistry.MolecularGraph
InfoGeometry.Chemistry.GraphIsomorphism
InfoGeometry.Chemistry.SubstructureEmbedding
InfoGeometry.Chemistry.Fragmentation
```

Recommended node fields:

```text
element
isotope
formal charge
aromaticity
hydrogen count
chirality
```

Recommended edge fields:

```text
bond order
aromatic flag
stereochemical label
```

The invariant target should eventually be a molecular graph isomorphism class `[G]`, not a raw SMILES string.

SMILES should be treated as a serialization/readout layer.

---

## 19. Phase XVIII — Distributed DGX training

Start with PyTorch DDP.

Add FSDP or tensor parallelism only when model size or memory measurements justify it.

Recommended stack:

```text
PyTorch
torch.compile
NCCL
DDP
BF16
FlashAttention
Triton kernels where profiling justifies them
```

Data path:

```text
object store
  -> Parquet/WebDataset shards
  -> CPU preprocessing workers
  -> pinned-memory queues
  -> GPU batch assembly
  -> DDP workers
```

Prefer variable-length spectra. Bucket by peak count rather than padding every spectrum to one fixed sequence length.

---

## 20. Phase XIX — Performance benchmarking

Do not treat proposed throughput and latency numbers as planning constants before measurement.

Benchmark:

```text
spectra/s/GPU
peaks/s/GPU
forward latency
forward+backward latency
GPU utilization
HBM bandwidth
peak memory
NCCL scaling efficiency
Sinkhorn runtime fraction
pseudoinverse runtime fraction
Transformer runtime fraction
```

Measure across:

```text
batch sizes: 1, 8, 32, 64, ...
peak counts: 32, 64, 128, 256, 512, ...
precision: FP32, TF32, BF16
GPU count: 1, 2, 4, 8
```

Only then derive realistic epoch-time and real-time-inference claims.

---

## 21. Phase XX — Lean-to-GPU conformance

`KernelRefinement` should become an operational testing discipline.

For every production kernel maintain:

```text
Lean specification
    -> reference CPU implementation
    -> GPU implementation
    -> property/conformance tests
```

Minimum conformance targets:

```text
canonicalization
Mellin rotation
mass causal mask
rank causal mask
cross-Gramian
causal transfer mask
doubled operator
grading conjugation
Sinkhorn balance
Moore-Penrose projection identities
Majorana skew conversion
```

Example runtime check:

```python
assert_close(
    gamma @ doubled(K) @ gamma,
    -doubled(K),
)
```

The runtime test is not the theorem. It is evidence that one implementation refines the theorem-level specification.

---

## 22. Phase XXI — Evaluation matrix

### Spectral metrics

```text
cosine similarity
spectral entropy similarity
peak precision/recall
mass error in ppm
neutral-loss accuracy
```

### Structural retrieval

```text
top-1
top-5
top-10
scaffold retrieval
```

### De-novo metrics

```text
molecular-formula correctness
graph exact match
graph edit distance
fingerprint similarity
stereochemistry accuracy
```

### Physical-validity diagnostics

```text
illegal mass-increasing transitions: exactly 0 by construction
DAG cycles: exactly 0 for certified DAG outputs
invalid hard assignment support: exactly 0 for certified hard outputs
numerical Birkhoff residual
Moore-Penrose residuals
chiral conjugation residual
```

### Generalization regimes

Evaluate separately on:

```text
seen molecule / unseen spectrum
unseen molecule
unseen scaffold
unseen collision energy
unseen instrument model
cross-laboratory data
```

---

## 23. Phase XXII — Deployment

### 23.1 Offline identification

Input:

```text
mzML/MGF spectrum
```

Potential output:

```text
candidate structures
confidence scores
fragmentation DAG
peak-fragment assignments
neutral-loss annotations
simulated spectra
```

### 23.2 Real-time acquisition

Only enable after measured latency supports it.

Architecture:

```text
instrument spectrum event
  -> GPU inference
  -> candidate precursor state
  -> acquisition-policy engine
  -> next collision/isolation/MSn action
```

Keep the acquisition-policy engine separate from the neural model so deterministic instrument and safety constraints can be enforced independently.

---

## 24. Reproducibility and provenance

Every training record should retain:

```text
source repository
source accession
raw-file checksum
parser version
preprocessing version
instrument-normalization version
dataset version
```

Every model checkpoint should retain:

```text
git commit
Lean commit / PR head
dataset manifest hash
container/environment hash
GPU type
precision
optimizer
random seeds
```

This is required for high-assurance scientific reproducibility.

---

## 25. Immediate implementation sequence

1. Repair PR #88 CI and obtain a genuine `lake build`.
2. Build the unified GNPS/MoNA/MassBank ingestion manifest.
3. Count the actual experimental Orbitrap subset.
4. Establish molecule-held-out and scaffold-held-out splits.
5. Build `PeakSpectrum` canonicalization conformance tests.
6. Implement GPU Mellin rotary encoding.
7. Implement hard mass/DAG masking.
8. Implement cross-stage transfer `K`.
9. Implement log-domain Sinkhorn and numerical balance certification.
10. Implement or select a stabilized Moore-Penrose backend.
11. Construct `SpectralToken(K,K†)`.
12. Connect the spectral token to the existing Transformer residual stack.
13. Pretrain with spectral self-supervision.
14. Add multi-energy prediction.
15. Add candidate molecular retrieval.
16. Benchmark single-GPU and DGX scaling.
17. Only then add a molecular graph decoder.
18. Consider real-time acquisition only if measured latency supports it.

---

## 26. First production milestone

The first production milestone should stop before unrestricted de-novo molecular generation.

Target:

```math
(S,E)
  -> h_spectral
  -> { predicted spectrum at E', predicted DAG, molecular retrieval ranking }.
```

Required properties:

- zero mass-increasing DAG edges by construction;
- certified acyclic topology;
- Mellin common-scale invariant rotary encoding;
- numerically validated Birkhoff transport;
- Moore-Penrose reconstruction diagnostics;
- Lean/GPU conformance fixtures;
- molecule-held-out benchmarks;
- scaffold-held-out benchmarks.

Only after this system demonstrates genuine out-of-distribution spectral generalization should unrestricted molecular graph reconstruction become the primary target.

---

## 27. Formal/empirical boundary ledger

### Already theorem-facing in the repository

```text
canonical peak sorting
FreeMonoid spectral sentence
relative log-mass scale identities
Mellin/Givens pair norm preservation
Birkhoff decomposition for certified soft assignments
rank-certified acyclicity
physical mass decrease on valued DAG edges
path probability multiplication
path surprisal additivity
chiral doubling and Gamma conjugation
cross-Gramian transpose law
existence of nonsymmetric cross-Gramian examples
Moore-Penrose projector identities
projectivity grading-evenness
Gamma D skew Majorana shadow
finite Pfaffian/determinant identities
SpectralToken primal/dual carrier
Transformer residual-stack execution
KernelRefinement composition
```

### Still empirical or future theorem work

```text
actual public Orbitrap corpus size
model identification accuracy
sub-ppm or ppm empirical calibration performance
DGX throughput and latency
real-time LC-MS feasibility
B-spline/KAN universal approximation layer
molecular graph reconstruction correctness
SMILES/IUPAC/conformer correctness
mechanism labels such as McLafferty or retro-Diels-Alder
clinical/regulatory validity
```

This separation must remain visible in code, documentation, experiments, and publications.

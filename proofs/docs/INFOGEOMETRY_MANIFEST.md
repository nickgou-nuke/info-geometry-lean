# InfoGeometry Manifest

## Information Geometry of Holographic Quasicrystal Gravity

This repository contains a theorem-honest Lean 4 / SymPy architecture connecting finite algebraic proof anchors with explicit analytic sockets for a speculative but structured mathematical physics program:

- split real Clifford/CPT kinematics;
- q-CCR/CAR and Cuntz--Toeplitz deformation corridors;
- Penrose/PGA projective geometry and noncommutative tiling algebras;
- K-theory gap labels in `ℤ + φℤ`;
- golden KMS statistics with `q = φ⁻¹`;
- finite Fibonacci Hamiltonian anchors;
- black-hole entropy scalar holography;
- q-Fock / spectral triple sockets;
- information-geometric UV cutoff via Itakura--Saito and Cramér--Rao.

The guiding rule is: **prove finite algebraic/scalar/matrix identities in Lean; mirror them in SymPy; keep analytic C*-algebra, von Neumann, infinite spectral, and physical classification claims as explicit sockets.**

---

## Master Build

The master entry point is:

```lean
proofs/InfoGeometry.lean
```

It imports the currently verified capstone stack:

```lean
import SplitCliffordAlgebras
import ProjectiveCuntzToeplitzCARCCR
import ProjectivePenrosePGA
import NoncommutativeTilingAlgebra
import ConvexAlgebraicDuality
import GoldenCCR
import FractalHamiltonian
import BlackHoleHolography
import GoldenSpectralTriple
import InformationGeometricCutoff
import EinsteinThermodynamicBridge
import UnifiedGaugeField
import DiracKreinMetriplectic
import SuperBerezinianKlein
import GlideSymmetricInvariant
import CubicJordanPeirceDecomposition
import BraidIdealDescent
```

Build:

```bash
cd /home/goutev/auto/proofs
lake build InfoGeometry
```

Last successful build:

```text
Build completed successfully (8043 jobs).
```

---

## Architecture

### 1. Kinematics: Split Clifford / CPT

File:

```text
proofs/SplitCliffordAlgebras.lean
```

Main anchors:

- split Clifford factorization;
- tripotent `P³=P` witness;
- chiral projectors;
- CAR/CCR and Weyl sockets;
- split real structure retained as primary.

Representative theorem names:

```lean
clnn_succ_factor
gamma11_sq
chiralProjPlus11_idempotent
chiralProjMinus11_idempotent
```

### 2. q-CCR / Cuntz--Toeplitz Corridor

File:

```text
proofs/ProjectiveCuntzToeplitzCARCCR.lean
```

Main anchors:

- q-CCR endpoint relations;
- Fibonacci matrix identity;
- projective Möbius rescaling;
- finite Toeplitz vacuum defect;
- Kuzmin uniformization socket.

Key finite identity:

```lean
toeplitz_range_defect_projection
```

which encodes the finite model:

\[
I - SS^* = P_{vac}.
\]

### 3. Penrose/PGA and Noncommutative Tilings

Files:

```text
proofs/ProjectivePenrosePGA.lean
proofs/NoncommutativeTilingAlgebra.lean
```

Main anchors:

- golden ratio identity `φ²=φ+1`;
- Fibonacci substitution eigenvector;
- cross-ratio and projective invariance;
- finite convolution as matrix multiplication;
- trace/gap-label module `ℤ + φℤ`;
- tile frequencies.

Representative theorem names:

```lean
phi_sq_eq_phi_add_one
FibR_pf_eigen
gap_labeling_trace_scaling
tileFrequency_eq_evalTrace
thickFreq_eq_gapLabel
```

### 4. Convex Algebraic Duality

File:

```text
proofs/ConvexAlgebraicDuality.lean
```

Inspired by Rostalski--Sturmfels, `arXiv:1006.4894`.

Main anchors:

- toy diagonal spectrahedron/simplex;
- convex closure;
- conic gradient as projective tangent hyperplane;
- scalar KKT stationarity;
- spectrahedral/projective-dual sockets.

Representative theorem names:

```lean
traceOneDiag_convex
conic_euler
conic_tangent_hyperplane
scalar_kkt_stationary
```

### 5. Golden Statistics

File:

```text
proofs/GoldenCCR.lean
```

Main scalar bridge:

\[
\beta=\log\phi,
\qquad
q=e^{-\beta}=\phi^{-1}.
\]

Representative theorem names:

```lean
exp_neg_penroseBeta
qPenrose_eq_thickFreq
qPenrose_interior
golden_exchange_relation
```

This proves that the Penrose/Fibonacci `q` lies in Kuzmin's interior domain:

\[
|q|<1.
\]

### 6. Finite Fibonacci Hamiltonian

File:

```text
proofs/FractalHamiltonian.lean
```

Finite tight-binding anchor:

\[
H_\phi=
\begin{pmatrix}
1&1\\
1&\phi^{-1}
\end{pmatrix}.
\]

Representative theorem names:

```lean
fibHamiltonian2_symmetric
fibHamiltonian2_trace
fibHamiltonian2_det
qPenrose_eq_gapLabel
```

This proves:

\[
q=\phi^{-1}=-1+\phi\in \mathbb Z+\phi\mathbb Z.
\]

### 7. Black-Hole Holography Scalar Anchor

File:

```text
proofs/BlackHoleHolography.lean
```

Definitions:

\[
S_{BH}=\pi\sqrt{J_4},
\qquad
S_{micro}=N\log\phi.
\]

Main theorem:

```lean
black_hole_area_quantization
```

Formal consequence:

\[
\pi\sqrt{J_4}=N\log\phi
\Rightarrow
J_4=\left(\frac{N\log\phi}{\pi}\right)^2.
\]

The exceptional/Freudenthal origin of `J₄` is represented by:

```lean
CartanQuarticSocket
```

### 8. Golden Fock / Spectral Triple Socket

File:

```text
proofs/GoldenSpectralTriple.lean
```

Main abstract Dirac/number-operator consequence:

```lean
dirac_creates_particle_metric
```

which proves:

\[
[D,a_i^\dagger]=a_i^\dagger
\Rightarrow
D(a_i^\dagger\Omega)=a_i^\dagger\Omega.
\]

The full analytic q-Fock completion and spectral triple conditions remain sockets.

### 9. Information-Geometric UV Cutoff

File:

```text
proofs/InformationGeometricCutoff.lean
```

Scalar log barrier:

```lean
def MassieuBarrier (x : ℝ) : ℝ := - Real.log x
```

Scalar Itakura--Saito divergence:

```lean
def ItakuraSaito (x y : ℝ) : ℝ := x / y - Real.log (x / y) - 1
```

Proved:

```lean
itakuraSaito_scale_invariant
itakuraSaito_self
fractal_resolution_limit
minimal_phase_space_volume_pos
```

Core cutoff chain:

\[
\mathcal I>0,
\qquad
\mathcal I^{-1}\le \Sigma
\Rightarrow
0<\Sigma.
\]

Interpretation: the mathematical fractal may be infinite, but physical resolution has a strictly positive Cramér--Rao lower bound.

The Jordan/Albert version is a socket and explicitly uses the Jordan product:

```lean
structure JordanBarrierSocket where
  jordanProduct : StateSpace → StateSpace → StateSpace
  traceForm : StateSpace → ℝ
  itakuraSaitoUsesTraceJordanProduct : Prop
```

---

### 10. Scalar Thermodynamic Einstein Bridge

File:

```text
proofs/EinsteinThermodynamicBridge.lean
```

Main scalar Jacobson-style anchor:

```lean
no_bare_singularities
```

If the scalar Einstein equation of state identifies curvature with the
Fisher/Cramér--Rao source density, then the source side is strictly positive:

\[
0<\Sigma,
\qquad
R/2+\Lambda=\Sigma
\Rightarrow
0<R/2+\Lambda.
\]

The full tensor Einstein/Jacobson derivation remains an explicit socket:

```lean
TensorEinsteinJacobsonSocket
```

### 11. Unified Gauge-Field / TKK Socket

File:

```text
proofs/UnifiedGaugeField.lean
```

Main finite scalar accounting anchors:

```lean
total_energy_minus_gauge
gravity_gauge_scalar_accounting
```

The full Standard Model gauge embedding into the `g₀` sector of a 5-graded
TKK/exceptional algebra remains an explicit socket:

```lean
GaugeEmbeddingSocket
TKKGaugeGravityUnificationSocket
```

### 12. Glide and Peirce Topological Transition Anchors

Files:

```text
proofs/GlideSymmetricInvariant.lean
proofs/CubicJordanPeirceDecomposition.lean
```

Main finite anchors:

```lean
hamiltonian_preserves_plus_eigenspace
hamiltonian_preserves_minus_eigenspace
Pcanonical_is_tripotent
L_P_E1_eigen
L_P_E2_eigen
L_P_E3_zero
```

These prove that glide-symmetric Hamiltonians preserve the `±1` eigensectors,
and that the canonical Peirce difference `P=E₁-E₂` is tripotent with diagonal
Peirce eigenvalues `+1,-1,0` in the associative finite anchor.

Python witness:

```text
proofs/klein_metriplectic_flow.py
```

simulates a Klein-bottle-wrapped metriplectic toy flow and a Painlevé-like
Super-Berezinian stabilization near a collapsing bosonic determinant.

### 13. Braid Ideal Descent and q-Cross Map

File:

```text
proofs/BraidIdealDescent.lean
```

Main finite anchors/interfaces:

```lean
tauL
tauR
IsLeftTauIdeal
IsRightTauIdeal
qCrossMap
qCrossMap_tmul
YangBaxterIdealDescentSocket
```

The maps `tauL` and `tauR` are concrete tensor-product linear maps built from
canonical associativity/commutativity isomorphisms.  The q-cross map is the
scaled swap `C_q(η⊗x)=q • (x⊗η)`.  Full Yang--Baxter/PBW ideal inheritance is
kept as explicit socket data.

## SymPy Witnesses

Key witnesses:

```bash
python3 proofs/golden_ccr.py
python3 proofs/fractal_hamiltonian.py
python3 proofs/golden_fock_gram.py
python3 proofs/information_geometric_cutoff.py
python3 proofs/projective_cuntz_toeplitz_car_ccr.py
python3 proofs/noncommutative_tiling_algebra.py
```

Recent verified checks include:

- `exp(-log φ)=φ⁻¹`;
- `q=φ⁻¹=-1+φ∈ℤ+φℤ`;
- finite Hamiltonian trace/determinant;
- q-Fock Gram positivity for binary sectors `n=2,3`;
- Itakura--Saito scale invariance;
- diagonal matrix IS divergence witness.

---

## Theorem-Honesty Policy

The following are represented as sockets/interfaces unless directly proved in finite Lean anchors:

- C*-algebra completions and universal properties;
- von Neumann algebra modular theory;
- Kirchberg--Phillips / Gabe--Ruiz classification;
- infinite Fibonacci Hamiltonian Cantor spectrum and zero-measure theorems;
- full Bellissard gap labeling for the infinite tiling groupoid;
- q-Fock Hilbert completion positivity in all sectors;
- physical identifications involving black holes, E₇₍₇₎, and quantum gravity.

This separation is deliberate: **finite algebra is proved; infinite analysis is socketed.**

---

## References Integrated as Digests

- Kuzmin, *CCR and CAR Algebras are Connected Via a Path of Cuntz--Toeplitz Algebras*, Communications in Mathematical Physics, 2023.
  - Digest: `external/papers/kuzmin-ccr-car-cuntz-toeplitz/DIGEST.md`
- Rostalski--Sturmfels, *Dualities in Convex Algebraic Geometry*, arXiv:1006.4894.
  - Digest: `external/papers/rostalski-sturmfels-dualities-convex-ag/DIGEST.md`

---

## Minimal Build Commands

Lean master target:

```bash
cd /home/goutev/auto/proofs
lake build InfoGeometry
```

Direct Lean file check through the external mathlib environment:

```bash
cd /home/goutev/info-geometry-lean
lake env lean /home/goutev/auto/proofs/<File>.lean
```

SymPy audit:

```bash
cd /home/goutev/auto
python3 proofs/golden_ccr.py
python3 proofs/fractal_hamiltonian.py
python3 proofs/golden_fock_gram.py
python3 proofs/information_geometric_cutoff.py
```

---

## Status

The current master target builds:

```text
lake build InfoGeometry
Build completed successfully (8043 jobs).
```

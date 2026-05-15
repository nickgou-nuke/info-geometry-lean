# Chapter X: The Drazin Dilation Gap - Singularity as a Sector

## 1. Introduction

In the operator-algebraic treatment of singular dynamics, non-invertibility is
not discarded. It is split into sectors. The Drazin inverse isolates the regular
part of an operator, while the Moore-Penrose projectors record the metric
input/output geometry. Their mismatch produces the Drazin dilation gap.

The central generator is

```text
G = 1/2 * (P_R - P_L),
```

where `P_L` and `P_R` are the Moore-Penrose left/domain and right/range
projectors. The Drazin projector `P_D` marks the regular spectral core. The
commutator of `P_D` with the dilation gap produces the Drazin supercharge:

```text
Q_D = 2 * [P_D, G].
```

The theorem-safe correction is:

```text
Q0 = 1 - P_D       is the defect sector,
G  = 1/2(P_R-P_L) is the support-mismatch detector.
```

The Shadow is not `G` itself. The Shadow is the Drazin complement `Q0`.

## 2. Drazin-Penrose Anatomy

Let `P_D` denote the Drazin core projector. Let `P_L` and `P_R` denote the
Moore-Penrose left and right projectors. Define the geometric Cartan grading

```text
Gamma_G = P_R - P_L.
```

Define the dilation generator

```text
G = 1/2 * (P_R - P_L).
```

Then the repo-owned identity is

```text
Gamma_G = 2 * G.
```

The left and right anomaly channels are

```text
chi_L = [P_D, P_L],
chi_R = [P_D, P_R].
```

The fundamental Drazin-Penrose bracket is

```text
[P_D, Gamma_G] = chi_R - chi_L.
```

Equivalently,

```text
[P_D, G] = 1/2 * (chi_R - chi_L).
```

The Drazin supercharge is therefore

```text
Q_D := chi_R - chi_L
     = 2 * [P_D, G]
     = [P_D, Gamma_G].
```

This is the exact algebraic meaning of the Drazin dilation gap: it measures how
the Drazin regular core fails to commute with the Moore-Penrose input/output
dilation geometry.

## 3. Oddness And Even Kinetic Closure

Let `Gamma_S` be the spectral Cartan grading. The Drazin supercharge is odd:

```text
{Gamma_S, Q_D} = 0.
```

Consequently, its square is even:

```text
[Q_D^2, Gamma_S] = 0.
```

The raw Drazin super-Hamiltonian candidate is

```text
H_D := Q_D^2.
```

The regular-sector compression is

```text
K_reg := P_D Q_D^2 P_D.
```

The repo proves that this compressed operator is supported on the regular
Drazin sector:

```text
P_D K_reg = K_reg,
K_reg P_D = K_reg.
```

If `P0 := 1 - P_D` is the Drazin complementary/singular projector, then the
regular compression has no defect block:

```text
P0 K_reg = 0,
K_reg P0 = 0,
P0 K_reg P0 = 0.
```

This is the precise algebraic content behind the phrase:

```text
heat lives in the regular sector;
defect memory lives in the complementary sector.
```

## 4. Kinetic Shadow And Defect Shadow

The repo-safe closure formula is the odd-odd bracket:

```text
{Q_D, Q_D} = 2 * T_D + Z_D.
```

Here `T_D` is the Drazin translation or kinetic candidate, and `Z_D` is the
central/defect candidate.

Because

```text
{Q_D, Q_D} = 2 * Q_D^2,
```

one may write a square form only after choosing the central-term normalization:

```text
Q_D^2 = T_D + 1/2 * Z_D.
```

Do not write `Q_D^2 = H_kin + Z` as a theorem unless `Z` is explicitly defined
with the half-factor absorbed, or unless a concrete split witness supplies that
law.

## 5. Modular Regular Flow

The regular compressed kinetic lane is fixed by the spectral grading flow:

```text
Phi_t(K_reg) = K_reg.
```

The complementary Drazin support is annihilated by the transported regular
kinetic readout:

```text
P0 Phi_t(K_reg) = 0,
Phi_t(K_reg) P0 = 0.
```

The guardrail is important. If a modular flow is unital and linear or
subtraction-preserving, then fixing `P_D` also fixes `1 - P_D`. So the
difference is not "invariant versus non-invariant" as projectors. The difference
is regular kinetic transport versus residual singular support.

The theorem-safe sentence is:

```text
The regular support is the modularly invariant kinetic lane.
The complementary Drazin sector is invisible to that regular flow;
it appears only as residual noise, defect memory, or central charge after a
separate readout is supplied.
```

## 6. Physical Interpretation: Heat And Memory

The Drazin decomposition separates two kinds of information.

The regular Drazin sector carries dissipative or kinetic flow:

```text
heat/kinetic sector ~ P_D Q_D^2 P_D.
```

The complementary sector carries singular memory, anomaly, or defect data:

```text
defect/memory sector ~ Z_D.
```

The dilation gap prevents a common error: treating kernel or singularity data as
ordinary thermal degrees of freedom. Singular modes are not erased. They are
indexed.

The physical slogan is:

```text
heat flows through the regular sector;
memory is stored in the defect sector.
```

## 7. Schur Reduction And Effective Dynamics

In Schur reduction or coarse-graining, singular blocks often obstruct ordinary
inversion. The Moore-Penrose inverse resolves metric support, while the Drazin
inverse resolves spectral/core support. The dilation gap measures their
mismatch.

The hierarchy is:

```text
P_L, P_R        metric input/output support,
P_D             Drazin spectral core,
G               dilation gap,
Q_D             odd anomaly/supercharge,
P_D Q_D^2 P_D   regular kinetic generator,
Z_D             defect/central memory.
```

This gives the formal bridge from generalized inverse theory to effective
thermodynamics.

## 8. Final Doctrine

The Drazin dilation gap is the algebraic witness that the singular sector cannot
be collapsed into ordinary heat. It has to be split, indexed, and transported as
its own object.

The chapter's final formula is:

```text
Q_D = 2 * [P_D, G].
```

The closure law is:

```text
{Q_D, Q_D} = 2 * T_D + Z_D.
```

The regular kinetic compression is:

```text
K_reg = P_D Q_D^2 P_D.
```

And the defect principle is:

```text
P0 K_reg P0 = 0,
P0 = 1 - P_D.
```

So singularity is not removed. It is localized.

```text
The Drazin dilation gap turns non-invertibility into a supergraded sector
decomposition: regular heat on one side, protected memory on the other.
```

## Repo Mapping

```text
CertifiedInverseKernel.lean
  Owner structure carrying Drazin, Moore-Penrose, Cartan, and anomaly data.

DrazinPenroseDilationAlgebra.lean
  Defines P_D, P_L, P_R, Gamma_G, G, Delta, chi_L, chi_R.
  Proves Gamma_G = 2G and [P_D, Gamma_G] = chi_R - chi_L.

DrazinSupercharge.lean
  Defines Q_D = chi_R - chi_L.
  Proves Q_D = 2[P_D,G] and Q_D = [P_D,Gamma_G].
  Proves oddness, evenness of Q_D^2, and regular-support compression laws.

UnifiedSuperchargeAlgebra.lean
  Packages Q_D with primitive supercharges and proves the odd-odd split
  {Q_D,Q_D} = 2T_D + Z_D.

DrazinDilationGap.lean
  Provides theorem-safe generic sockets for the support/gap/supercharge
  distinction and witness-gated square splits.

DrazinDilationGapBridge.lean
  Provides Black-Book-facing aliases and readbacks over repo-owned theorem
  surfaces.
```

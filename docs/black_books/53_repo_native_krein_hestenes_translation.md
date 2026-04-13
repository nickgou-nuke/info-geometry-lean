# Kramers Pairs, Hestenes Real Structures, Drazin-Penrose-Dilation Supercharges, and Modular Lightcone Singularities on the Doubled Real Krein Carrier

## Executive summary

The semantic root of the theory remains the projective/state layer, but the algebraic root of the downstream operator lane is now the doubled real Krein carrier:

$$
(H,[\cdot,\cdot],J,\varepsilon,K),\qquad K:=J\circ\varepsilon,\qquad K^2=-1.
$$

Here the ambient Hilbert structure is analytic scaffolding; the primary owned datum is the Krein pairing. This is formalized in `Krein/InvolutiveSelfDualCarrier.lean`.

In this repo, "complex-linear" and "antilinear" are no longer primitive notions. They are replaced by carrier-native phase conditions:

$$
[A,K]=0 \quad\text{(`KLinear`)},\qquad AK=-KA \quad\text{(`KAntilinear`)}.
$$

Likewise, "unitary" is replaced by Krein-isometric. These notions are owner surfaces in `Canonical/HestenesRealStructures.lean`.

Kramers structure is therefore expressed on the doubled real carrier as a real symmetry

$$
\Theta : H \to H
$$

which preserves the Krein pairing, is `K`-antilinear, and squares to `-1`. This is formalized as `KramersSymmetry`, with stricter time-reversal packaging in `Canonical/TimeReversalKramers.lean`.

In parallel, the intrinsic Hestenes version of the Kramers partner is formalized as

$$
(\psi, K\psi),
$$

with `K^2 = -1`, orthogonality, and nontriviality lemmas in `Canonical/HestenesKramersBridge.lean`.

Majorana structure is expressed as a real involution

$$
C^2=1
$$

on the doubled carrier, preserving the Krein pairing, commuting with `K`, and preserving the grading. Its fixed locus is the Majorana sector. This is formalized as `MajoranaRealStructure` and `fixedSubmodule` in `Canonical/HestenesRealStructures.lean`.

The concrete odd/even operator algebra already owned by the repo is the Drazin-Penrose-dilation Cartan slice

$$
(P_D,Q_D,P_L,P_R,\Gamma_S,\Gamma_G,G,\Delta,\chi_L,\chi_R),
$$

formalized in `Canonical/DrazinPenroseDilationKKT.lean`, with exact relations

$$
\Gamma_G = 2G,\qquad
[P_D,\Gamma_G]=\chi_R-\chi_L,\qquad
[P_D,G]=\tfrac12(\chi_R-\chi_L).
$$

The anomaly pair `(χ_L, χ_R)` is the natural odd sector relative to spectral grading `Γ_S`.

The repo-native odd supercharge is already formalized as

$$
Q_D := \chi_R-\chi_L = 2[P_D,G],
$$

and its even square

$$
H_D := Q_D^2
$$

is the projected superHamiltonian. `Canonical/DrazinSupercharge.lean` proves oddness of `Q_D`, evenness of `H_D`, and a canonical split of `H_D` into kinetic plus defect-supported central part. `Canonical/KramersSuperchargeBridge.lean` links Kramers/Majorana structures to this projected Drazin supercharge lane.

The currently owned "central charge" is still not an intrinsic nontrivial central generator of the full Drazin algebra; it is exposed via index/central hooks and fused in `Canonical/UnifiedSuperchargeAlgebra.lean`.

Type III / modular lightcone singularity language does not yet have a final owner file. In repo-native terms, singularities should be located by support/kernel projections, modular spectra, fixed-point sectors of modular/dilation flows, and scaling-limit/central-sequence phenomena. The infinite-dimensional Drazin spectral doorway remains scaffold-level in `Canonical/DrazinSpectralBridge.lean`.

## Repo-native primitives

The correct primitive package is not

$$
(\mathcal H,i,T,C,\Gamma).
$$

It is

$$
(H,[\cdot,\cdot],J,\varepsilon,K),\qquad K=J\varepsilon.
$$

Dictionary:

$$
i \rightsquigarrow K,\qquad
\text{complex-linear} \rightsquigarrow K\text{-linear},\qquad
\text{complex-antilinear} \rightsquigarrow K\text{-antilinear},
$$

$$
\text{unitary} \rightsquigarrow \text{Krein-isometric},\qquad
\text{Majorana reality} \rightsquigarrow \text{fixed sector of a real involution}.
$$

This translation is explicit in `HestenesRealStructures.lean` on top of `InvolutiveSelfDualCarrier.lean`.

## Kramers pairs in repo language

Two faithful formulations are now present.

1. Intrinsic phase-partner:

$$
\operatorname{phasePartner}(\psi)=K\psi,\qquad
\operatorname{kramersPair}(\psi)=(\psi,K\psi).
$$

Owned lemmas include:

$$
K^2=-1,\qquad
\langle \psi, K\psi\rangle_{\mathbb R}=0,\qquad
\psi\neq 0 \Longrightarrow K\psi\neq \psi,
$$

and Krein sign law

$$
[K\psi,K\phi]=-[\psi,\phi].
$$

2. General real symmetry:

A `KramersSymmetry` is `Θ` with

$$
\Theta^2=-1,\qquad
\Theta \text{ Krein-isometric},\qquad
\Theta K=-K\Theta.
$$

Formalized in `HestenesRealStructures.lean`, with time-reversal packaging in `TimeReversalKramers.lean`.

So the repo supports both internal Hestenes partner `(ψ, Kψ)` and external symmetry `(ψ, Θψ)`.

## Majorana real structures in repo language

A `MajoranaRealStructure` is

$$
C : H \to H,\qquad C^2=1,
$$

with `C` Krein-isometric, `K`-linear, and grading-compatible.

Majorana sector:

$$
\operatorname{IsMajorana}(u) :\Longleftrightarrow Cu=u.
$$

Owned as `fixedSubmodule`, with closure under `K` and `ε`.

Distinctions:

- Majorana: `Cu = u`
- Kramers: `(u, Θu)`, `Θ^2 = -1`, `ΘK = -KΘ`
- chiral: `εu = ±u`

These are distinct structures on one doubled real carrier.

## The Drazin-Penrose-dilation Cartan slice

Owned operator algebra:

$$
\mathcal A_{\mathrm{DPD}}=\langle
P_D,Q_D,P_L,P_R,\Gamma_S,\Gamma_G,G,\Delta,\chi_L,\chi_R
\rangle.
$$

Owned identities (`DrazinPenroseDilationKKT.lean`):

$$
\Gamma_G=2G,\qquad
[P_D,\Gamma_G]=\chi_R-\chi_L,\qquad
[P_D,G]=\tfrac12(\chi_R-\chi_L).
$$

The anomaly pair `(χ_L, χ_R)` anticommutes with `Γ_S`, so it is the natural odd sector.

## Repo-native supercharge and central split

`DrazinSupercharge.lean` defines

$$
Q_D := \chi_R-\chi_L = 2[P_D,G].
$$

Owned results:

$$
\{\Gamma_S,Q_D\}=0
$$

(oddness),

$$
H_D := Q_D^2
$$

evenness/flow-fixedness, and canonical split

$$
H_D = H_{\mathrm{kin}} + Z_{\mathrm{def}},
$$

with defect-supported central channel and uniqueness of this split under the file’s split axioms.

## Kramers/Majorana bridge to supercharge lane

`KramersSuperchargeBridge.lean` proves:

- Kramers-conjugated `Q_D` remains odd when `Θ` commutes with `Γ_S`.
- If Majorana involution commutes with `χ_L, χ_R`, it commutes with

$$
Q_D=\chi_R-\chi_L
$$

and hence with

$$
H_D=Q_D^2.
$$

So Majorana fixed sector is stable under `(χ_L, χ_R, Q_D, H_D)` with the stated hypotheses.

## Unified supercharge canopy

`UnifiedSuperchargeAlgebra.lean` fuses:

- primitive doubled-carrier supercharges,
- transported Bogoliubov/quasilattice supercharges,
- projected Drazin odd supercharge `Q_D`,
- operatorial central-charge hook.

It identifies primitive phase channel with internal phase axis `J ∘ ε`, and packages odd/even closure, transport laws, second-order metric/curvature landing, and central-charge equality surface.

## What is still not finished

1. Infinite-dimensional spectral Drazin doorway remains scaffold-level:
   `Canonical/DrazinSpectralBridge.lean` (`STATUS: scaffold_only`).
2. Final modular/type III/lightcone canopy is future work and should start from:
   - kernel/support projections,
   - spectral projections of modular/transport generators,
   - centralizers/fixed-point sectors of modular or dilation flows,
   - modular spectra and Connes-type invariants,
   - scaling-limit or central-sequence phenomena.

## Short verdict

What is now owner-level code:

- doubled real Krein carrier,
- Hestenes phase axis `K = Jε`,
- `KLinear`, `KAntilinear`, `KreinIsometric`, `KramersSymmetry`, `MajoranaRealStructure`,
- Drazin-Penrose-dilation Cartan algebra,
- projected odd supercharge `Q_D`, even generator `H_D`, and canonical defect-central split,
- first Kramers/Majorana bridge into the projected supercharge lane.

Remaining frontier:

- modular/type III canopy,
- closure of infinite-dimensional spectral bridge.


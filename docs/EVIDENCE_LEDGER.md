# The Synthesis Evidence Ledger

This manifest formally lists the closed theorem surface for the Kasparov-Krein DIII synthesis, alongside the explicit open debt list identifying formalization boundaries.

It is paired with [FIBONACCI_MZM_FOLLOWUP_ROADMAP.md](FIBONACCI_MZM_FOLLOWUP_ROADMAP.md), which records the next braid/Majorana comparison lane as an explicit assumption-gated extension rather than a kernel-native theorem surface.

Finite `n`-indexed theorem families are not considered final until they are
transported to an inductive-colimit owner surface or explicitly documented as
finite-stage only.

## 1. Closed And Conditional Theorem Surface
The following components are either closed finite owner lemmas or explicit evidence boundaries integrated into the current import graph. This list is not a claim that the whole repository is globally zero-debt.

* **Andreev Boundary Unitarity** (`InfoGeometry.Projective.AndreevHorizonUnitarity`):
  - `finite_andreev_packet`: A verified unitary proof showing $A^2 = -1, A^4 = 1$.
  - `unitarity_preservation`: Norm conservation for boundary scattering.
* **DIII Algebraic Signatures** (`KasparovKreinDIIIBridge.lean`):
  - `d3_time_reversal_symmetry`: Validates $T^2 = -1$ constraint across the projective layer.
  - `d3_particle_hole_symmetry`: Validates $C^2 = +1$ constraint across the projective layer.
  - `klein_bottle_trace_absorption`: Demonstrates the $Z_2$ trace cancellation.
* **Betti Rank 32 Evidence Boundary** (`NonIsoConf3RankIngestion`):
  - `discharge_rank_decision`: a conditional boundary binding external Betti configuration data to the Lean target geometry.
* **MZM Braiding Unitary Limits** (`HorizonInformationScrambling.lean`):
  - `black_hole_fast_scrambling`: Proves the modular time flow acts as a unitary scrambler without loss of quadratic information form.
* **Thermodynamic Gauge & BCFW Closure** (`GrandUnificationLinker.lean`, `ThermodynamicGauge.lean`, `OnShellResidueBCFWBridge.lean`):
  - The causal non-equilibrium flow and finite topology linker corridor are locally free of `sorry`.
  - BCFW-style readouts remain finite algebraic statements under explicit premises, not analytic BCFW recursion theorems.
* **q-Supergrading / Delaunay Deficit Corridor** (`SuperCuntzDilationCurvature.lean`):
  - Records finite q-boundary readouts for the bosonic/fermionic split.
  - Adds explicit modular edge dilation and q-deficit lemmas.
  - Transfers the entropy readout into the Delaunay/Pachner interface under explicit hypotheses.
  - The stagewise `n`-indexed version is routed through `SuperCuntzDilationColimit.lean`.
* **Finite Wilson-loop Readout Layer (Option B Scaffold)** (`ThermodynamicGauge.lean`):
  - Added `finite_wilson_loop` as a conservative non-abelian finite holonomy construction.
  - Curvature/holonomy readout lemmas remain explicit assumption surfaces; certificate-style APIs are proof-surface debt under the strict audit rules.
* **Projective Frontier & Macaulay Track B Ingestion** (`Projective.All`, `MacaulayTrackBIngestion.lean`):
  - `Projective.All` compiles in the current import spike.
  - Track B computational artifact `[X_3](3) = 1296` is integrated as explicit evidence; the current certificate-style API is not strict proof-surface clean.
* **Finite `Pin(5,5)` / Wallpaper Weyl Cross-Sections** (`Pin55.lean`, `Pin55WeylWallpaper.lean`, `Pin55WallpaperQuotientBridge.lean`, `WallpaperPin55RootCrossSection.lean`, `WallpaperAffineWeylD5Bridge.lean`, `WallpaperKleinBottleCartan.lean`):
  - `pin_quotient_to_weyl` and `weyl_wallpaper_quotient_packet` provide the finite reflection-to-wallpaper quotient packet.
  - `wallpaperD4_is_klein_compatible` identifies the eight displayed wallpaper point symmetries as the Klein-compatible finite shadow.
  - `weylD5CrossSection_projects_wallpaper`, `weylD5CrossSection_action_projects_wallpaper`, and `weylD5CrossSection_preserves_splitMetric55` record the exact finite `D₅` cross-section and split-metric preservation.
  - `latticeEmbed_sum_zero`, `latticeEmbed_sigmaX`, `latticeEmbed_sigmaD`, and `wallpaper_to_affine_weyl_d5_packet` give the explicit coordinate-level affine bridge.
  - No global `O(5,5)`/`Pin(5,5)` classification theorem is claimed here; the ledger records only the finite owner surface.
* **Finite Holographic Shard / Cantor KMS Split** (`CantorKMSCylinderState.lean`, `HolographicCuntzShard.lean`):
  - `cylinderKMSWeight_children_sum` proves that the two depth-one children of a cylinder split the parent weight evenly.
  - `finiteShard_reconstructs_source` records the exact finite source-sector recovery identity for the 2×2 shard model.
  - `finite_holographic_shard_packet` packages the finite reconstruction, aperture projection, and partition identities.
  - No analytic holography, Reeh-Schlieder density, or full GNS completion is claimed from this surface.

## 2. Explicit Open Debt List (Unverified / Assumed)
While the algebraic signatures are physically mapped, the rigorous analytical proofs linking them to continuous differential geometry remain explicit structural debt.

| **Debt Target** | **Owner/Domain** | **Assumptions** | **Status** |
| :--- | :--- | :--- | :--- |
| **Full Kasparov Product Theorem** | `Algebra/Grothendieck` | Assumes exact functorial descent from continuous NCG $C^*$-algebras to finite matrix proxies. | `Open Debt` (Currently modeled as explicit interface readback). |
| **Continuous KO Anomaly Theorem** | `InfoGeometry/Topology` | Assumes continuous spacetime manifold orientability drops globally along the null boundary, matching $Z_2$. | `Open Debt` |
| **Geometric Horizon-Andreev Equivalence** | `InfoGeometry/Physics` | Assumes standard Schwarzschild horizon scattering acts identically to Bogoliubov-de Gennes junctions. | `Open Debt` |
| **Full Wilson-loop ↔ Bost–Connes Curvature Equivalence** | `Topology/ThermodynamicGauge` | Assumes analytic identification of the finite discrete Wilson holonomy/curvature trace with zeta/partition-function data in the relevant geometric limit. | `Open Debt` |
| **Certified Betti-to-Majorana Linkage** | `Categorical/FibonacciBraiding`| Assumes the non-isotropic configuration topology defects uniquely map to $SU(2)_3$ anyonic models. | `Open Debt` |
| **Inductive-Colimit Promotion for `n`-Families** | `Categorical/` and `Canonical/` colimit owners | Assumes the finite-stage family has an explicit transport theorem to the appropriate colimit owner; finite-stage readouts alone are not terminal. | `Open Debt` |
| **Global `O(5,5)` / `Pin(5,5)` Classification** | `Canonical/` and `Projective/` wallpaper/Weyl owners | Assumes a full classification of the ambient group, not just the finite reflection and coordinate cross-sections. | `Open Debt` |
| **Analytic Holography / Full GNS Completion** | `Canonical/` Cantor/Cuntz owner lane | Assumes a full operator-algebraic completion beyond the finite shard and cylinder identities. | `Open Debt` |

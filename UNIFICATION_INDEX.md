# Unification Index

Generated: `2026-03-21 14:26:58 EET`

This report tracks where the repository is reproducing standard mathematics, where it is building repo-specific bridges between known subjects, and where the surface is mostly packaging rather than deep unification.

## Criterion

A surface counts as real unification here only if it gives:
- two independently meaningful sides,
- an explicit structure-preserving bridge,
- a transport/invariance/equivalence theorem across that bridge,
- something stronger than `rfl`, direct forwarding, or tuple repackaging.

The categories below are local to the repo’s formal framework.
They do not automatically imply external novelty in the research-literature sense.

## Module Split

| Module | Status | Meaning | Note |
| --- | --- | --- | --- |
| `InfoGeometry.Math.Convexity` | `mostly_classical` | mostly standard mathematics reproduced in Lean | Direct convexity/Jensen/KL finite-form lemmas aligned with standard convex-analysis literature. |
| `InfoGeometry.Geometry.LegendreDuality` | `mostly_classical` | mostly standard mathematics reproduced in Lean | Fenchel-Young, gap, and equality-case layer; classical convex duality core. |
| `InfoGeometry.Geometry.DualFlat` | `mostly_classical` | mostly standard mathematics reproduced in Lean | Bregman three-point and Pythagorean identities in a standard dual-flat setting. |
| `InfoGeometry.EntropicInference` | `mostly_classical` | mostly standard mathematics reproduced in Lean | Constructive finite KL-Pythagorean decompositions and Jeffrey-style projection identities. |
| `InfoGeometry.Information.MultiLogPotential` | `mostly_classical` | mostly standard mathematics reproduced in Lean | Covariance/Fisher symmetry and exponential-family local information geometry. |
| `InfoGeometry.Canonical.RGFlow` | `classical_specialization` | standard theorem pattern in a repo-specific specialization | Real Banach fixed-point specialization plus constant-flow baseline; mathematically standard but not a nontrivial RG existence theory. |
| `InfoGeometry.Canonical.AnalyticalIndex` | `classical_adjacent_model` | built from standard vocabulary but uses a simplified repo-specific model | Finite-dimensional repo-specific analytical-index model using standard index-theoretic vocabulary. |
| `InfoGeometry.KK.KasparovCycle` | `classical_adjacent_model` | built from standard vocabulary but uses a simplified repo-specific model | Bounded KK-style cycle surface connected to the repo’s analytical-index model rather than full Kasparov theory. |
| `InfoGeometry.Canonical.KMSSinkhornBridge` | `repo_specific_unification` | genuine bridge or transport theorem inside the repo’s own framework | Explicit bridge between Sinkhorn dynamics and KMS-style closure conditions; literature-inspired but repo-specific. |
| `InfoGeometry.Canonical.TomitaTakesaki` | `repo_specific_unification` | genuine bridge or transport theorem inside the repo’s own framework | Split `Cl(1,1)` modular atom surface identified with the repo’s modular/CPT layer, not a full standard-form Tomita-Takesaki development. |
| `InfoGeometry.Canonical.OperatorAlgebraBridge` | `packaging_heavy_bridge_surface` | contains real theorems but a noticeable fraction is packaging/re-export/readiness surface | Contains some real closures, but a noticeable part of the file is API packaging and readiness bundling. |
| `InfoGeometry.Canonical.GrandSynthesis` | `mixed_capstone_surface` | mixes real theorem content with high-level capstone packaging | Contains honest determinant/Jacobian lemmas and real bridge theorems, but also capstone packaging/orchestration layers. |
| `InfoGeometry.Canonical.Rosetta` | `repo_specific_unification` | genuine bridge or transport theorem inside the repo’s own framework | Assumption-driven commuting-diagram capstone joining source tension, Einstein residual, chemical potential, modular anomaly, Weyl-to-KK, and Weyl-to-Jordan/KKT transport. |
| `InfoGeometry.Quantum.RealMajorana` | `repo_specific_unification` | genuine bridge or transport theorem inside the repo’s own framework | Real CAR/BdG transport scaffold with explicit Weyl-sector transport and polarization bridge structure. |
| `InfoGeometry.Quantum.ModularAnomaly` | `repo_specific_unification` | genuine bridge or transport theorem inside the repo’s own framework | Real-Majorana modular cocycle shadow with explicit commutator bridge and finite lattice determinant/Berezinian invariants. |
| `InfoGeometry.Quantum.BulkBoundary` | `repo_specific_unification` | genuine bridge or transport theorem inside the repo’s own framework | Finite-dimensional algebraic bulk-boundary mechanism transporting zero-mode witnesses through Bogoliubov structure. |
| `InfoGeometry.Quantum.HurwitzRGFlow` | `repo_specific_unification` | genuine bridge or transport theorem inside the repo’s own framework | Discrete 24-chart Hurwitz shell invariance transported into RG stationarity and vanishing beta function. |
| `InfoGeometry.Quantum.KitaevChain` | `classical_adjacent_model` | built from standard vocabulary but uses a simplified repo-specific model | Finite Pfaffian-sign phase scaffold with defect/critical crossing; not yet a full Fredholm/Witten-index package. |
| `InfoGeometry.Canonical.DoubleCopyUnification` | `packaging_heavy_bridge_surface` | contains checked transport-facing implications but remains thin | Real integration point for double-copy language, but current theorems are still mostly assumption-driven implication surfaces. |
| `InfoGeometry.Canonical.GrandSynthesisDoubleCopy` | `mixed_capstone_surface` | mixes real theorem content with high-level capstone packaging | Double-copy flavored synthesis layer above the thinner core unification file. |
| `InfoGeometry.Canonical.ArnoldMajoranaNetwork` | `repo_specific_unification` | genuine bridge or transport theorem inside the repo’s own framework | Network layer consuming transported Weyl/zero-mode witnesses; strong local unification but entirely repo-specific. |

## Theorem-To-Literature Table

| Theorem | Source theories | Bridge / morphism | Preserved structure | Transport type | Literature status | Note |
| --- | --- | --- | --- | --- | --- | --- |
| [`convexOn_neg_log`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Math/Convexity.lean#L19) | convex analysis | none; direct standard statement | convexity on `(0, ∞)` | classical reproduction | classical theorem | Safe core. |
| [`neg_log_jensen_sum`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Math/Convexity.lean#L28) | convex analysis, information theory | Jensen applied to `-log` | finite convex combination inequality | classical reproduction | classical theorem | Safe core. |
| [`fenchelYoung_ineq`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Geometry/LegendreDuality.lean#L86) | convex duality | primal/dual conjugacy | Fenchel majorization inequality | classical reproduction | classical theorem | Safe core. |
| [`three_point_identity`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Geometry/DualFlat.lean#L355) | information geometry, Bregman geometry | dual-flat gradient/Bregman relation | Bregman three-point law | classical reproduction | classical theorem | Safe core. |
| [`kl_pythagorean_jeffrey_toReal_strict`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/EntropicInference.lean#L452) | information geometry, KL projection geometry | strict positivity + Jeffrey reconstruction | KL decomposition | classical special case | classical theorem / finite constructive specialization | Strong standard-core formalization. |
| [`covariance_symm`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Information/MultiLogPotential.lean#L153) | statistics, information geometry | covariance expression for Fisher metric | symmetry of covariance/Fisher bilinear form | classical reproduction | classical theorem | Safe core. |
| [`existsUnique_fixedPoint_of_contracting`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RGFlow.lean#L247) | metric fixed-point theory, RG language | Banach contraction recast as RG step map | existence/uniqueness of fixed point | classical specialization | classical theorem / repo-specific interpretation | Mathematically standard; physics reading is interpretive. |
| [`analyticalIndex`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/AnalyticalIndex.lean#L59) | finite-dimensional linear algebra, index vocabulary | chiral kernel slices -> integer index | dimension difference of chiral slices | repo-specific model | repo-specific construction | Classical-adjacent, not full Atiyah-Singer. |
| [`indexInvariantAlong_of_conjugacy`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/AnalyticalIndex.lean#L654) | index-like invariance, conjugacy transport | chiral conjugacy along a path | analytical-index invariance | invariance theorem | repo-specific unification | Good example of strong local bridge content. |
| [`index_bridge_spectral`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/KK/KasparovCycle.lean#L83) | KK-style cycles, analytical index | spectral involution -> no-zero-eigenvalue crossing | analytical-index invariance of the constant family | invariance theorem | repo-specific unification | Finite-dimensional spectral stability bridge, not just a definitional alias. |
| [`sinkhorn_step_kmsClosure_of_control`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/KMSSinkhornBridge.lean#L177) | Sinkhorn dynamics, KMS/operator-algebra language | stepwise control hypothesis -> KMS closure | closure of next-step state | bridge theorem | repo-specific unification | Genuinely unifying in local sense; not classical Sinkhorn or full KMS theory. |
| [`neg_log_relative_volume_change_rn`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/DiracRicciBridge.lean#L37) | RN density, Kähler potential | relative volume change vs. logarithmic Kähler potential | additive potential identity | local bridge theorem | repo-specific unification | Still elementary, but no longer just a named definitional equality. |
| [`logAbsDetMatrix_mul`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/GrandSynthesis.lean#L158) | matrix analysis, determinant calculus | classical determinant chain rule | multiplicativity under matrix product | classical reproduction | classical theorem | Safe local theorem embedded in synthesis layer. |
| [`information_wheeler_dewitt_equivalence_of_fullCapstone`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/GrandSynthesis.lean#L1337) | thermodynamic KMS side, geometric-algebraic side | full-capstone equivalence | bi-implication of capstone state bundles | capstone equivalence | repo-specific synthesis theorem | Potentially meaningful local unification; not externally classical by name alone. |
| [`rosetta_source_tension_three_presentations`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/Rosetta.lean#L512) | singular/projector anomaly, Einstein residual, Fock chemical-potential lift, modular anomaly shadow | explicit commuting-diagram transport across layers | source tension across multiple codomains | transport theorem | repo-specific unification | Strong façade theorem: not one false equality, but a real transport chain. |
| [`kk_analyticalIndex_eq_of_weylScaleTransport`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/Rosetta.lean#L719) | Weyl scale transport, modular/Clifford transport, KK analytical index | scale-transport shadow packaged into modular/Clifford transport witness | analytical-index invariance | invariance theorem | repo-specific unification | Important because it closes the Weyl-to-KK gap on the public theorem surface. |
| [`weylScaleTransportScalarShadow_generalized_pythagorean_of_jordanBregman`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/Rosetta.lean#L886) | Weyl scale transport, Jordan/KKT geometry, Bregman Pythagorean law | scalar shadow interpreted through Jordan/KKT transport | generalized Pythagorean identity | transport theorem | repo-specific unification | This is the public Weyl-to-Jordan/KKT bridge. |
| [`unified_anomaly_bridge`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Quantum/ModularAnomaly.lean#L126) | modular cocycle, commutator transport, real-Majorana shadow | cocycle derivative -> commutator shadow | anomaly generator identity under transport | bridge theorem | repo-specific unification | Core modular anomaly bridge. |
| [`thermal_berezinian_index`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Quantum/ModularAnomaly.lean#L608) | finite lattice anomaly, determinant/Berezinian calculus | modular flow specialized to block lattice model | thermal Berezinian decay law | concrete model theorem | repo-specific unification | Concrete finite-lattice capstone, not just an abstract cocycle identity. |
| [`betaFunction_eq_zero_of_invariantAtScale`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Quantum/HurwitzRGFlow.lean#L105) | discrete Hurwitz shell symmetry, RG flow | shell invariance -> modular/Clifford invariant scale -> stationarity | vanishing beta function | transport theorem | repo-specific unification | Honest discrete-to-RG bridge; not an E8 theorem. |
| [`index_change_forces_defect_crossing`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Quantum/KitaevChain.lean#L256) | finite Pfaffian-sign chain algebra, IVT-style phase protection | continuous path + sign change -> critical defect crossing | topological-sector obstruction | phase-boundary theorem | classical-adjacent model / repo-specific specialization | Good finite phase-boundary theorem; not yet a full Witten-index theorem. |
| [`double_copy_geometric_equilibrium_imp`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/DoubleCopyUnification.lean#L23) | Ricci fixed-point language, somatic square-law surface | equivalence hypothesis -> proportionality implication | square-law transport under equilibrium assumption | implication theorem | packaging / thin bridge | Useful checked façade, but still thinner than the Rosetta or Weyl/KKT transport layers. |
| [`kk_supercomm_compact_of_even_rep`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean#L405) | KK compactness, operator bridge layer | re-export into operator-algebra readiness surface | compactness fact | direct forwarder | packaging theorem | Useful API surface, not a deep new bridge. |
| [`weylZeroModePair_under_bogoliubov_of_preservesChiralityPolarization`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Quantum/BulkBoundary.lean#L485) | real Majorana Weyl sectors, Bogoliubov transport, bulk-boundary zero modes | chirality-polarization-preserving transport | nonzero zero-mode pair in transported Weyl sectors | transport theorem | repo-specific unification | Strong local cross-domain bridge. |
| [`exists_network_fixed_transportWeylPlus_nonzero_ker_of_experts_fix_of_simplifiedBoundaryModel_under_bogoliubov`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean#L596) | Majorana/BulkBoundary zero-mode transport, mixture-of-experts network dynamics | simplified boundary model + Bogoliubov transport -> network fixed zero mode | fixed nonzero transported Weyl-plus kernel witness | repo-specific constructive unification | repo-specific construction | Good candidate for genuinely novel local theorem content. |
| [`chiralAnomalyIndex`](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/TopologicalInvariants.lean#L57) | topological invariants, anomaly/index language | repo-defined anomaly index construction | custom integer-valued invariant | repo-specific construction | analogue / repo-specific | Literature-adjacent naming; not a proof of classical Atiyah-Singer. |

## Reading Rule

- Treat `classical theorem` and `classical theorem / finite constructive specialization` rows as safe standard-core reading.
- Treat `repo-specific unification` rows as the strongest local candidates for genuine new formal mathematics inside the repo’s framework.
- Treat `packaging theorem`, `thin bridge`, and `analogue` rows cautiously; they may be valid Lean mathematics without carrying strong unification weight.

## Policy

- Standard subject names alone do not count as unification.
- Capstone naming alone does not count as novelty.
- The real contribution, when present, is the verified bridge that lets mathematics pass between theories.

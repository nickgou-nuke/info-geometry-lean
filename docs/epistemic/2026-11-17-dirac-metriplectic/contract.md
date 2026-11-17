# Dirac and metriplectic attachment theorem contract

**Status: source-reviewed candidates; kernel verification pending.** This contract records finite algebraic additions and their limits. Compilation, axiom dependencies, warnings, source hashes, and the verified revision must be filled from the actual root-controlled reports. No kernel-pass claim is made here.

## 1. Intake provenance

The four uploaded files contain two unique byte streams, each 201 lines. The original bytes are preserved in `dirac-hestenes-intake.txt` and `para-kahler-metriplectic-intake.txt`, with the upload-to-file mapping in `intake-manifest.json`.

| Intake group | Uploads | Bytes | SHA-256 |
| --- | --- | ---: | --- |
| Dirac/current text | `Pasted text (2)(9).txt`; `Pasted text (3)(4).txt`; `Pasted text(20261117-085441).txt` | 36,090 each | `b9de16352e57d99545684be35d91d935df030bc68a57849584caaff133edede0` |
| Metriplectic/geometry text | `Pasted text (4)(2).txt` | 36,565 | `1fef0d88c605c9d59f6590503b776362454f6b30b5022bbdec25dc1b12960e48` |

This companion branch starts from `08c34e03f610b452e03422037949196dc7d92d6d`. Source review began at repository revision `441f95c93cce4734788738715662eda503244b3d`. The recorded dependency contract is Lean `leanprover/lean4:v4.34.1` with Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; verification must check the integrated revision against those pins.

## 2. Native real Dirac candidate

**Integration target:** `lean/InfoGeometry/Canonical/HestenesNativeDiracCurrent.lean`, namespace `InfoGeometry.Canonical.HestenesNativeDiracCurrent`; candidate file `HestenesNativeDiracCurrent.lean`.

### Carrier and conventions

Reuse [HestenesClPlus14.lean][S1], whose actual definitions are

\[
V14=\mathrm{Fin}(4)\to\mathbb R,\qquad
Q14(x)=x_0^2-x_1^2-x_2^2-x_3^2,
\]
\[
Cl14=\operatorname{CliffordAlgebra}(Q14),\qquad
ClPlus14=\operatorname{CliffordAlgebra.even}(Q14).
\]

The generators are `gamma i = CliffordAlgebra.ι Q14 (basisVec i)`, and reversion is native `CliffordAlgebra.reverse`. Thus \(\gamma_0^2=1\), \(\gamma_i^2=-1\) for spatial indices, and distinct generators anticommute. These relations are reused proofs, not additional assumptions. The [native reversion][M1] and [exterior-equivalence][M2] APIs supply the reversal and injectivity arguments.

The five new definitions are

\[
J(\psi)=\psi\gamma_0\widetilde\psi,\quad
K(\psi)=\psi\gamma_3\widetilde\psi,\quad
\psi_s=1+\gamma_3\gamma_0,
\]
\[
v_s=2(e_0+e_3),\qquad B=\gamma_2\gamma_1.
\]

Their Lean names are `diracCurrent`, `axialCurrent`, `singularSpinor`, `singularCurrentVector`, and `phasePlane`. Both current definitions return the full native Clifford carrier; the candidate proves an actual vector representation for the displayed witness. It does not yet prove vector-valuedness for every even spinor.

### Complete public statement inventory

| Candidate declarations | Exact content |
| --- | --- |
| `singularSpinor_val`, `reverse_singularSpinor`, `singularSpinor_mul_reverse` | The embedded witness is \(1+\gamma_3\gamma_0\), its reverse is \(1-\gamma_3\gamma_0\), and their product is zero. |
| `diracCurrent_singularSpinor`, `axialCurrent_singularSpinor_eq_diracCurrent` | \(J(\psi_s)=2(\gamma_0+\gamma_3)=K(\psi_s)\). |
| `diracCurrent_singularSpinor_eq_iota`, `singularCurrentVector_time`, `singularCurrentVector_quadratic` | \(J(\psi_s)=\iota(v_s)\), \((v_s)_0=2\), and \(Q14(v_s)=0\). |
| `iota_injective` | `Function.Injective ι14`, proved through Mathlib's exterior-algebra equivalence. |
| `diracCurrent_singularSpinor_ne_zero`, `singularSpinor_ne_zero`, `diracCurrent_singularSpinor_sq` | \(J(\psi_s)\ne0\), \(\psi_s\ne0\), and \(J(\psi_s)^2=0\). |
| `axialCurrent_singularSpinor_ne_zero`, `axialCurrent_singularSpinor_sq` | \(K(\psi_s)\ne0\) and \(K(\psi_s)^2=0\). |
| `exists_nonzero_spinor_with_nonzero_null_current` | \(\exists\psi\in ClPlus14,\ \psi\ne0\land J(\psi)\ne0\land J(\psi)^2=0\). |
| `right_phase_equation_iff` | In any associative ring, \(B^2=-1\) implies \(DB-G=M\iff D=-(M+G)B\). No factors are commuted. |
| `phasePlane_sq`, `hestenes_equation_isolate` | The native \(B=\gamma_2\gamma_1\) has square \(-1\), and \(DB-eA\psi=m\psi\gamma_0\) implies \(D=-(m\psi\gamma_0+eA\psi)B\). Real coefficients use the native scalar action. |

Private proof support is limited to `reverse_gamma`, `gamma_zero_three`, `gamma_three_zero_sq`, `singularSpinor_mul_time`, and `singularSpinor_mul_space`: respectively generator reversal, anticommutation, \((\gamma_3\gamma_0)^2=1\), and the two products \(\psi_s\gamma_0=\psi_s\gamma_3=\gamma_0+\gamma_3\).

Here `D` is an algebra element, not a constructed derivative. The candidate formalizes a singular-current counterexample and a sign correction. General Fierz identities, positive flux, PDE conservation, integrated norms, and energy spectra remain separate targets. The real Dirac convention is grounded in Hestenes [P1].

### Reuse and existing consumers

[HestenesSTA4DMaxwellDiracBridge.lean][S2] defines an eight-real-coordinate `STASpinor` and a sum-of-squares `current_j0`; [STAMaxwellThoriumCapstone.lean][S3] consumes that coordinate density. Neither supplies the missing equality between that density and a scalar/time readout of the native Clifford sandwich. This equality is a subsequent bridge obligation. [HestenesDirac.lean][S4] carries conservation in an explicit packet; extracting that field is not a PDE derivation.

## 3. Casimir candidate: existing results and additions

**Integration:** the first four declarations of `MetriplecticCasimirObstructionCandidate.lean` extend [BilinearMetriplecticReduction.lean][S5]; the last two extend its concrete [Cl55MetriplecticReduction.lean][S6] consumer.

The existing bilinear owner defines
\[
L_{B,A}=A\circ(B^\flat)^{-1}\circ A^*:V^*\to V
\]
for a nondegenerate real bilinear form on finite-dimensional \(W\) and \(A:W\to V\). Its current exact-kernel theorem assumes strict positivity of \(B\). Native [bilinear duality][M3] and [contravariant dual equivalences][M4] support the new alternative below.

[GenericMetriplecticFlow.lean][S7] already proves `entropy_covector_eq_zero_of_injective`, `entropy_rate_zero_of_injective`, and `energy_covector_eq_zero_of_injective`. These are reused. The concrete Cl55 consumer already has reversible and dissipative directions \(e_1\) and \(e_0\), and proved entropy rate \(2\). [Cl55ParaKahlerMetric.lean][S8] owns its nondegenerate skew `diagonalOmega` and distinct positive `positiveMetric` on \(V55=(\mathrm{Fin}(5)\to\mathbb R)^2\).

| New declaration | Contract |
| --- | --- |
| `reducedSharp_eq_zero_iff_of_injective` | If \(A\) is injective, \(L_{B,A}\alpha=0\iff A^*\alpha=0\), for any nondegenerate \(B\). Positivity is unnecessary. |
| `reducedSharpEquiv` | For \(e:W\simeq_{\mathbb R}V\), construct \(e^*.\mathrm{trans}((B^\flat)^{-1}.\mathrm{trans}(e))\), an actual native linear equivalence \(V^*\simeq V\). |
| `reducedSharpEquiv_toLinearMap` | Its underlying linear map is exactly the existing `reducedSharp B hB e.toLinearMap`. |
| `reducedSharp_injective_of_equiv` | This sharp map is injective for an invertible state-coordinate change. |
| `twoModeSystem_reversible_not_injective` | The existing entropy-rate-\(2\) system has a noninjective reversible operator. |
| `twoModeSystem_reversible_ne_fullSharp` | That reversible operator differs from `reducedSharp diagonalOmega diagonalOmega_nondegenerate LinearMap.id`. Its reduction cannot be replaced by the full symplectic inverse. |

The general proof requires finite-dimensional \(W\), not finite-dimensional \(V\). The composition order is \(V^*\xrightarrow{e^*}W^*\xrightarrow{(B^\flat)^{-1}}W\xrightarrow e V\). “Casimir” here denotes an algebraic kernel covector; existence of a nonconstant global Casimir function is not established.

## 4. Correction ledger and remaining obligations

| Intake claim | Classification and required correction |
| --- | --- |
| Strict Fierz causal type for every nonzero spinor | **False as stated.** The candidate has both nonzero currents null. Under the usual even-spinor decomposition, \(J^2=\Omega_1^2+\Omega_2^2\), \(K^2=-J^2\), and \(J\cdot K=0\); strictness needs \(\Omega_1^2+\Omega_2^2>0\). These general identities are not yet candidate theorems. Also \(\operatorname{sc}((\psi\widetilde\psi)I)=-\Omega_2\) when \(I^2=-1\). |
| Current conservation and Cauchy-slice independence | **Conditional/open.** Corrected algebraic mass cancellation leaves a scalar commutator. A PDE result needs actual derivatives, regularity, product/reversion rules, and the field equation. Mixed currents require the same mass, charge, and potential. Slice independence additionally requires integrability and boundary/decay hypotheses. |
| Energy is bounded below iff a potential difference is below \(2m\) | **False.** The full free Dirac branch \(-\sqrt{\lVert p\rVert^2+m^2}\) is already unbounded below. In the specified static-step problem, \(m<E<V_0-m\) is nonempty iff \(V_0>2m\), not a general stability or Schwinger criterion [P2]. Rest-involution sign, chirality, frequency, and antiparticles require separate definitions. Normal ordering does not force pointwise positive energy density [P3]. |
| A full nondegenerate symplectic inverse supports a nonzero GENERIC entropy Casimir | **Incompatible requirements.** \(L(dS)=0\) and injective \(L\) force \(dS=0\). The weaker \(\{S,H\}=0\) does not establish \(\{F,S\}=0\) for every \(F\). The candidate connects this existing obstruction to the actual reduced Cl55 maps; Morrison's construction uses Poisson Casimirs [P4]. |
| Associator Gram automatically gives strict entropy production or vanishes on any associative subregister | **Conditional.** For a positive pairing, \(D(v,w)=\gamma\sum_a\langle R_aPv,R_aPw\rangle_+\) is symmetric and nonnegative when \(\gamma\ge0\). For \(\gamma>0\), \(D(s,s)=0\iff\forall a,\ R_aPs=0\). Strictness needs a nonzero channel. Restrict all three associator inputs to one associative subalgebra and require \(P\) to preserve it; ambient basis pairs need not vanish. [SplitOctonionLeftRegularAssociatorDefect.lean][S9] already proves the restricted-core multiplication law. |
| An indefinite form or an involution alone supplies positive flux/Gram estimates | **False without compatibility.** A positive metric needs a verified fundamental symmetry: \(g(u,v)=B(u,Jv)\), with \(g(u,u)>0\) for \(u\ne0\) and a \(B\)-self-adjoint involution \(J\). Positive Grams use the positive-metric adjoint. Future-unit-timelike observer flux is a diagonal quadratic form; mixed pairings need not be positive, and null normals give only semidefiniteness. Lorentz covariance is simultaneous in spinor and observer. |
| Tensoring a spin carrier with split octonions is necessary | **Unproved and unnecessary as a general requirement.** An associative representation can act on the underlying octonion vector space through \(\operatorname{End}_{\mathbb R}(\mathbb O_s)\). Raw octonion multiplication does not obey that representation law. A tensor construction is an optional choice whose actions and pairings still need definitions. |
| The proposed para-Kähler Hessian formulas establish the advertised metric, Ricci sign, and solution | **Needs correction.** With invertible \(A\) and \(g=\left(\begin{smallmatrix}0&A\\A^T&0\end{smallmatrix}\right)\), \(\det g=(-1)^n(\det A)^2\) and \(\log\lvert\det g\rvert=2\log\lvert\det A\rvert\). Pure symmetric tensor products do not vanish; their coefficients vanish in this metric. Ricci sign needs a curvature convention. Strict convexity alone does not ensure invertible Hessian (\(x^4\)); adding \(\phi(x)+\chi(y)\) leaves the mixed Hessian unchanged. Defining a determinant source does not solve a prescribed Monge–Ampère problem. |
| Gibbs convergence is confined to one fixed compact subalgebra | **False at the stated generality.** Specify phase space, action, moment map, and measure in \(Z(\beta)=\int e^{-\langle J,\beta\rangle}d\mu\). The standard normal-convergence domain is open and convex when nonempty [P5], so it cannot lie in a fixed proper linear subspace of the full parameter algebra. Ordinary convergence and normal convergence must not be conflated. |
| Energy preservation and nonnegative entropy rate imply Landauer, stability, or convergence | **Not implied.** The finite identities need a differentiable solution and chain rule to become trajectory statements. Existence, global convergence, heat definitions, reservoir assumptions, and any Landauer bound remain separate obligations. No equality \(\Delta Q=T\Delta S\) follows from these candidates. |
| A ranked narrative poset proves a unique physical theory or preferred carrier | **Unsupported.** A rank can establish acyclicity; graph joins describe that graph. Neither gives physical uniqueness, representation uniqueness, nor transitive reduction. |

An identically zero sandwich can be a substantive obstruction theorem; it should not be rejected solely because its conclusion is zero. Conversely, a positive or nonzero readout defined independently of its advertised Clifford/associator carrier does not establish the missing representation bridge.

## 5. Acceptance evidence required

1. Record the integrated commit, exact source hashes, source-closure order, Lean version, and unchanged Mathlib pin; preserve the two original intake streams and manifest separately.
2. Compile both additions and their actual repository import closure under the shared serial build lock. Record return codes and warnings; stale compiled artifacts do not certify changed sources.
3. Inspect axiom dependencies for every new owned declaration, including the null-current existential, nonzero proofs, sign theorem, dual-equivalence bridge, and concrete Casimir obstruction. Reject `sorryAx` and unreviewed added axioms.
4. Run the required placeholder and semantic-content gates on the selected owners. Confirm that nonzero/null witnesses and the entropy-rate-\(2\) consumer are actual deductions, not new assumption fields.
5. Publish the resulting report and its scope. General Fierz/flux results, PDE conservation, spectra, associator dissipation, curvature, Gibbs integrability, and thermodynamic limits remain outside this finite candidate's verification claim.

**Verification record: native compilation and axiom inspection pending.**

The selected checker targets are `InfoGeometry.Canonical.HestenesNativeDiracCurrent`,
`InfoGeometry.Thermo.BilinearMetriplecticReduction`, and
`InfoGeometry.Clifford.Cl55MetriplecticReduction`. Their current transitive source
closure contains 148 repository modules and 114 native import roots. The
Cl55 consumer contributes most of that existing closure. The focused
`.github/workflows/real-dirac-casimir.yml` covers those dependency paths, uses
exact merge-commit checkout, preserves the existing pins, runs the unchanged
native checker and recursive declaration-axiom audit, and requires zero
warnings in all three selected owners. It does not certify the large
`Canonical.All` aggregator or the root Lake package.

Independent reviewers checked the native Clifford calculation, its vector
identification and nonzeroness argument, the right-phase sign convention,
the bilinear-equivalence composition, the entropy-rate contradiction, and
the pinned Mathlib API names. These source reviews are separate from compiler
acceptance. The previous PR #375 local attempt reached its first unchanged dependency,
then failed because the workspace volume was full. The companion attempt
was canceled while it was still waiting for the lock and had produced no
compiler environment or module log. An independent checkout and output
directory on an available volume are used for fresh checks; the shared lock
and the dependency caches are unchanged.

Recorded source-level checks on 17 November 2026:

| Check | Observed result |
| --- | --- |
| `proof_proxy_staged_gate.py` | Passed on the staged patch. |
| Strict selected-owner placeholder scan | No `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, or literal `True` proof wrapper. |
| `semantic_content_audit.py --include-review --gate` for the three owners | Passed; 3 of 3 selected files read, complete selected coverage, zero blocking or review findings. This is a lexical/source gate, not kernel verification. |
| Focused workflow syntax and dependency triggers | YAML, every shell block, embedded Python, and coverage of the 148 current repository source dependencies checked. Independent source review also identified and added the semantic gate's four constructivity/quarantine dependencies. |
| Maintained root file wrapper, without waiting | Exit 2: shared build lock held; no elaboration performed. |
| Maintained root Lake wrapper for the three targets, without waiting | Exit 2: shared build lock held; concurrent build refused. |
| Read-only root path-package preflight | Missing `HomotopyHypothesis` and `Atlas` configurations and an uninitialized `GIFT` gitlink. This does not provide a compilation result. |

The native run uses the unchanged `tools/quality/check_clifford_dirac.py` with
the three repeated `--target` arguments above. It must finish compilation and
the fresh complete declaration audit before any kernel-verified label is used.

## Sources

Repository links below pin the source-review revision; they do not assert that the new candidate is already present there.

[S1]: https://github.com/nickgou-nuke/info-geometry-lean/blob/441f95c93cce4734788738715662eda503244b3d/lean/InfoGeometry/Canonical/HestenesClPlus14.lean
[S2]: https://github.com/nickgou-nuke/info-geometry-lean/blob/441f95c93cce4734788738715662eda503244b3d/lean/InfoGeometry/Canonical/HestenesSTA4DMaxwellDiracBridge.lean
[S3]: https://github.com/nickgou-nuke/info-geometry-lean/blob/441f95c93cce4734788738715662eda503244b3d/lean/InfoGeometry/Canonical/STAMaxwellThoriumCapstone.lean
[S4]: https://github.com/nickgou-nuke/info-geometry-lean/blob/441f95c93cce4734788738715662eda503244b3d/lean/InfoGeometry/Clifford/HestenesDirac.lean
[S5]: https://github.com/nickgou-nuke/info-geometry-lean/blob/441f95c93cce4734788738715662eda503244b3d/lean/InfoGeometry/Thermo/BilinearMetriplecticReduction.lean
[S6]: https://github.com/nickgou-nuke/info-geometry-lean/blob/441f95c93cce4734788738715662eda503244b3d/lean/InfoGeometry/Clifford/Cl55MetriplecticReduction.lean
[S7]: https://github.com/nickgou-nuke/info-geometry-lean/blob/441f95c93cce4734788738715662eda503244b3d/lean/InfoGeometry/Thermo/GenericMetriplecticFlow.lean
[S8]: https://github.com/nickgou-nuke/info-geometry-lean/blob/441f95c93cce4734788738715662eda503244b3d/lean/InfoGeometry/Clifford/Cl55ParaKahlerMetric.lean
[S9]: https://github.com/nickgou-nuke/info-geometry-lean/blob/441f95c93cce4734788738715662eda503244b3d/lean/InfoGeometry/Canonical/SplitOctonionLeftRegularAssociatorDefect.lean
[M1]: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/LinearAlgebra/CliffordAlgebra/Conjugation.lean
[M2]: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean
[M3]: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/LinearAlgebra/BilinearForm/Properties.lean
[M4]: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/LinearAlgebra/Dual/Defs.lean

- **[P1]** David Hestenes, *Clifford Algebra and the Interpretation of Quantum Mechanics*, equations 2.15 and 2.21–2.29: <https://davidhestenes.net/geocalc/pdf/caiqm.pdf>.
- **[P2]** Hiromichi Nakazato and Makoto Ochiai, *Unstable vacuum and fermion total reflection by the Klein step*, PTEP 2022 073B02, section 2 and Appendix A: <https://scoap3-prod-backend.s3.cern.ch/media/files/71260/10.1093/ptep/ptac085.pdf>.
- **[P3]** Hongwei Yu and Weixing Shu, *Quantum states with negative energy density in the Dirac field and quantum inequalities*, Phys. Lett. B570 (2003), 123–128: <https://arxiv.org/abs/hep-th/0307102>. See also C. J. Fewster and B. Mistry, *Quantum Weak Energy Inequalities for the Dirac field in Flat Spacetime*, Phys. Rev. D68 (2003), 105010: <https://arxiv.org/abs/gr-qc/0307098>.
- **[P4]** Philip J. Morrison, *A paradigm for joined Hamiltonian and dissipative systems*, Physica D18 (1986), 410–419: <https://web2.ph.utexas.edu/~morrison/86PHD_morrison.pdf>.
- **[P5]** Charles-Michel Marle, *On Gibbs States of Mechanical Systems with Symmetries*, JGSP57 (2020), Proposition 3.1.3: <https://marle.perso.math.cnrs.fr/pdffiles/2020/GibbsStatesJGSPPart1.pdf>.

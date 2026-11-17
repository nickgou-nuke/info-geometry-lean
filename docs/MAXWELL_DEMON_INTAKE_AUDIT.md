# Independent mathematical intake audit: Maxwell's demon and Landauer

## Disposition and evidence

**Disposition: accept a corrected, explicitly scoped finite mathematical core for implementation; do not transcribe the tutorial's formulas indiscriminately.** Several displayed formulas contain sign, normalization, or variable errors. The correct Gibbs identity, entropy balance, and complete memory-cycle accounting are mathematically substantial. A positive Gram entropy-production form alone does not establish any of the required thermal identities.

This is an independent non-authoring source/mathematical review by `/root/klein_workflow_audit`, dated 2026-11-17. It is not kernel acceptance. No Lean/Lake, tests, gates, or build-lock operations were performed, and no live repository source was edited.

Input: *A Friendly Guide to Exorcising Maxwell's Demon*, A. de Oliveira Junior, J. B. Brask, and R. Chaves, PRX Quantum **6**, 030201 (2025), DOI [10.1103/phkv-wrsd](https://doi.org/10.1103/phkv-wrsd). The supplied 47-page PDF has SHA256 `68b2415c86ddc54add9cabe0fa18cb0413020ee36d23ffc58e7b4026b7a43ea2`. I read the main text through p38, inspected relevant references on pp39–47, and visually checked the critical formulas on pp3, 8, 18, 24, 25, 31, and 32. Page numbers below are both PDF page numbers and the suffix of the printed article page number `030201-N`. Advanced experimental, finite-time, and single-shot claims in VIII are context, not accepted implementation targets here.

Seven existing source owners were independently read and byte-compared with main `08c34e03f610b452e03422037949196dc7d92d6d`; all match. Exact paths and SHA256 values are recorded in the source-provenance appendix below. PR358 overlap is separately reported by `/root/owner_discovery`; it is not counted here as independently accepted code.

## 1. Fix one convention before writing theorems

Use natural logarithms and dimensionless entropy:

\[
H(p)=-\sum_x p_x\log p_x,\qquad S(\rho)=-\operatorname{Tr}(\rho\log\rho).
\]

The extension at a zero eigenvalue/probability is \(0\log0=0\). Physical entropy is \(k_B H\) or \(k_B S\). One unbiased bit has dimensionless entropy \(\log2\), physical entropy \(k_B\log2\), and the usual thermal energy scale \(k_BT\log2\).

Set \(\beta=1/(k_BT)>0\) when deriving a lower bound on heat in energy units. Define

\[
Q_B=\operatorname{Tr}[H_B(\sigma_B-\rho_B)]
\]

as heat **delivered to the bath**, \(\Delta S_X=S(\sigma_X)-S(\rho_X)\), and erased entropy \(E_S=-\Delta S_S\). Work \(W_{\rm on}\) is positive when supplied to the device; extracted work is \(W_{\rm ext}=-W_{\rm on}\). With fixed endpoint system/bath Hamiltonians and the appropriate interaction-energy bookkeeping, \(\Delta E_S=W_{\rm on}-Q_B\).

This convention agrees with the usable Landauer equations (67)–(69). It avoids the tutorial's conflicting p3 statement that heat is positive into the system while its equations (1)–(3) use the bath-positive convention. Symbols must carry their role: `heatToBath`, `entropyChange`, and `entropyErased` should not share an ambiguous `deltaS`.

## 2. Correct finite identities and their assumptions

### Classical probabilities

Let \(A,B\) be finite nonempty sets and \(r\) a normalized nonnegative probability on \(A\times B\), with genuine marginals \(r_A,r_B\). The following identities underpin pp17–20, equations (39)–(57):

\[
\begin{aligned}
H(A,B)&=H(B)+H(A\mid B),\\
I(A:B)&=H(A)+H(B)-H(A,B)\\
 &=\sum_{a,b:r_{ab}>0}r_{ab}\log\frac{r_{ab}}{r_A(a)r_B(b)}\ge0.
\end{aligned}
\]

Whenever \(r_{ab}>0\), both relevant marginals are positive, so the displayed denominator is nonzero. Terms on zero-probability conditioning events must contribute zero; an arbitrary conditional distribution may be chosen there. Mutual information vanishes exactly for the independent product law. For a deterministic \(B=f(A)\), \(H(B\mid A)=0\) and \(I(A:B)=H(B)\). The reverse conditional entropy vanishes only when the map is injective on the supported outcomes.

For normalized probabilities \(p,q\), finite real KL requires \(\operatorname{supp}p\subseteq\operatorname{supp}q\); otherwise the correct extended KL is \(+\infty\). Strictly positive \(q\) is a simple sufficient contract. Lean's total `Real.log 0 = 0` does not by itself implement extended KL: naïvely evaluating the log formula on disjoint point masses can return zero and invalidate the equality case.

### Gibbs logarithm and free energy

For a finite nonempty spectrum, real energies \(h_x\), and finite real \(\beta\), define

\[
Z_\beta=\sum_xe^{-\beta h_x}>0,\qquad
\gamma_x=Z_\beta^{-1}e^{-\beta h_x}>0.
\]

Then, with the support convention above,

\[
\log\gamma_x=-\beta h_x-\log Z_\beta,
\qquad
D(p\Vert\gamma)= -H(p)+\beta\langle h\rangle_p+\log Z_\beta.
\]

The quantum counterpart uses a Hermitian finite matrix \(H\), its **actual** CFC exponential and logarithm, \(Z=\operatorname{Tr}(e^{-\beta H})>0\), and \(\gamma=e^{-\beta H}/Z\):

\[
\log\gamma=-\beta H-(\log Z)I,
\quad
D(\rho\Vert\gamma)=-S(\rho)+\beta\operatorname{Tr}(\rho H)+\log Z.
\]

These are the corrected mathematical content of equations (23)–(25), pp8–9, and (48), p19. They hold without assuming \(\rho\) commutes with \(H\). For \(\beta\ne0\),

\[
D(\rho\Vert\gamma)=\beta[F_\beta(\rho,H)-F_\beta(\gamma,H)],
\quad F_\beta(\gamma,H)=-\beta^{-1}\log Z.
\]

An **inequality** or unique-minimizer theorem also needs actual KL/Klein nonnegativity and \(\beta>0\). A trace identity alone is not that theorem. Negative finite \(\beta\) is mathematically allowed for finite spectra, but the free-energy comparison reverses. At \(\beta=0\), the logarithmic/KL expansion remains meaningful; the physical \(1/\beta\) free energy does not.

### Exact system–bath entropy and heat balance

The finite quantum contract behind equations (60)–(69), pp24–25, is:

- Finite-dimensional system and bath, with normalized positive semidefinite density matrices.
- A fixed Hermitian bath Hamiltonian \(H_B\) and finite real \(\beta\), giving the initial full-rank Gibbs bath \(\gamma_B\).
- Initial product \(\rho_{SB}=\rho_S\otimes\gamma_B\).
- A genuine unitary \(U\) on the joint space and final state \(\sigma_{SB}=U\rho_{SB}U^\dagger\), with partial-trace marginals.

The identities are

\[
\Delta S_S+\Delta S_B=I(S:B)_\sigma,
\qquad
\Delta S_B=\beta Q_B-D(\sigma_B\Vert\gamma_B),
\]

hence

\[
\boxed{\beta Q_B=-\Delta S_S+I(S:B)_\sigma+D(\sigma_B\Vert\gamma_B).}
\]

These are exact finite identities. Nonnegativity of the final mutual information and relative entropy gives \(\beta Q_B\ge-\Delta S_S\). For \(\beta>0\), divide to obtain the energy bound. The final bath need not be thermal, and the final joint state need not be a product. No weak-coupling, Markovian, quasistatic, energy-preserving-unitary, initial-system-Gibbs, or final-pure-state hypothesis is needed for this entropy/heat identity. Interpreting other quantities as work requires additional Hamiltonian accounting.

A finite **classical** implementation can instantiate this contract with an actual permutation of \(A\times B\) and its pushforward of \(p\otimes\gamma\). Shannon entropy is invariant under that permutation; the marginals and mean bath-energy difference are actual finite sums. This is a concrete closed dynamics model, not an arbitrary irreversible map with an entropy balance assumed afterward.

### Initial resources and correlations

The product hypothesis matters. For arbitrary initial \(r_{SB}\), the entropy-preserving joint evolution gives

\[
\Delta S_S+\Delta S_B=I_f-I_i.
\]

For a fixed Gibbs reference \(\gamma_B\), the more general exact identity is

\[
\beta Q_B=-\Delta S_S+(I_f-I_i)
 +D(\sigma_B\Vert\gamma_B)-D(\rho_B\Vert\gamma_B).
\]

Thus initial correlations and an initially athermal bath are resources, with explicit subtraction terms. Dropping those terms is not justified by positivity of a dissipation matrix.

**Counterexample to unconditional bit-erasure heat:** take classical bits with \(r_{00}=r_{11}=1/2\), bath Hamiltonian zero, and joint reversible map \((s,b)\mapsto(s\mathbin{\rm xor}b,b)\). The bath marginal is Gibbs at every finite \(\beta\), the system is perfectly erased, and \(Q_B=0\). Initial mutual information \(\log2\) is consumed. This violates no correctly stated bound.

### Binary erasure and finite-bath limitations

An initially unbiased bit with final error probability \(\varepsilon\) has erased entropy

\[
\log2-h_2(\varepsilon),\qquad
h_2(\varepsilon)=-\varepsilon\log\varepsilon-(1-\varepsilon)\log(1-\varepsilon).
\]

Under the thermal/product/dynamical assumptions, \(Q_B\ge k_BT[\log2-h_2(\varepsilon)]\). This is the lower bound intended by equation (71), p27, not a formula assigning the heat of every protocol. A zero lower bound at error \(1/2\) does not force zero actual dissipation. Biased inputs require their actual initial entropy in place of \(\log2\).

In the finite unitary product-Gibbs model, equality in the Landauer bound requires both final correction terms to vanish. This leaves the bath unchanged and implies no entropy erasure. A mixed system cannot be mapped exactly to a pure state with a finite full-rank bath: initial joint rank is \(\operatorname{rank}(\rho_S)d_B>d_B\), whereas a pure final system marginal forces a product with joint rank at most \(d_B\). Unitary evolution preserves rank. This is a direct finite-dimensional obstruction; it is not a universal assertion that every model requires infinite time. A zero-temperature bath can be rank deficient, and \(\beta=\infty\) needs a separate extended-value contract. Reeb–Wolf give the equality and purity refinements explicitly [R1].

## 3. Complete demon cycle: what is actually restored

For a joint classical law, an additive endpoint energy \(H_X+H_M\), and \(\beta\ne0\), direct finite algebra gives

\[
F(X,M)=F(X)+F(M)+\beta^{-1}I(X:M).
\]

The same relation is valid for finite quantum states with additive Hamiltonian and quantum mutual information. This is an identity about the joint state; it does not assert that every physical measurement realizes any prescribed transition.

In the tutorial's classical non-disturbing measurement model, a readable record \(M=g(Y')\) together with conditional independence \(X\perp Y'\mid M\) ensures \(I(X:Y')=I(X:M)\), as used in equation (74). Without those conditions, replace this by the appropriate data-processing comparison. Use normalized conditional record distributions; the p31 formula involving the old apparatus density divided by the outcome probability is not a general encoding construction.

Given the justified isothermal work bounds, unchanged system marginal during measurement, a cyclic feedback stroke, and reset of the apparatus using the bath without additional correlated side-information resources, equations (57), (75), and (76) combine as

\[
\begin{aligned}
W_{\rm meas}&\ge\Delta F_M+\beta^{-1}I,\\
W_{\rm fb}&\ge-\beta^{-1}I,\\
W_{\rm reset}&\ge-\Delta F_M,\\
W_{\rm total}&\ge0.
\end{aligned}
\]

In particular \(W_{\rm ext}\le\beta^{-1}I\), not the reverse inequality printed on p31. Sagawa–Ueda's primary feedback theorem has the correct orientation [R2]. Equality describes an ideal saturation case, not every cycle. Supplying work does not alone prove that heat is dissipated: work can raise internal energy or stored free energy.

For the four-party model of equations (77)–(80), p32, let \(C_f=\sum_{X\in\{S,B,M,W\}}S(\sigma_X)-S(\sigma_{SBMW})\) be final total correlation. Initial product plus joint unitarity imply \(\sum_X\Delta S_X=C_f\ge0\). With an actual finite initially Gibbs bath, use the exact correction instead of assuming \(\Delta S_B=\beta Q_B\):

\[
\boxed{\beta Q_B+\Delta S_S+\Delta S_M+\Delta S_W
 =C_f+D(\sigma_B\Vert\gamma_B)\ge0.}
\]

Cyclic \(S\) and an entropy-neutral battery yield \(\Delta S_M\ge-\beta Q_B\), the intended equation (80), even for a finite bath. A deterministic pure battery is a sufficient entropy-neutral assumption; an arbitrary physical battery need not satisfy it. To conclude no positive net work from a full cycle, also return the memory and working system in energy, use energy-preserving global dynamics, and account for endpoint interaction energy. Memory entropy alone is insufficient energy bookkeeping.

## 4. Printed errors and overclaims that must not enter code

| Location | Audit finding | Precise correction / witness |
|---|---|---|
| p3 versus pp4–5, (1)–(6) | Prose heat sign conflicts with the equations. | Use bath-positive \(Q_B\) throughout the proposed contract. |
| p8, (22) | Reversed log order for relative entropy; its second equality is also inconsistent with (17). | \(D(\sigma\Vert\rho)=\operatorname{Tr}[\sigma(\log\sigma-\log\rho)]=-S(\sigma)-\operatorname{Tr}(\sigma\log\rho)\), with support control. |
| p9, explanation of (28) | The displayed correlated mixture is called entangled. | \(\tfrac12(|L0\rangle\langle L0|+|R1\rangle\langle R1|)\) is explicitly a mixture of product states, hence separable. Correlation is sufficient for the example. |
| p18, (43) | A minus sign precedes the joint/product log ratio. | Remove it. For perfectly correlated fair bits, the printed expression is \(-\log2\), while (40), (44)–(46) give \(+\log2\). |
| p18, deterministic-measurement prose | \(Y=f(X)\) is said to imply \(H(X\mid Y)=0\). | It implies \(H(Y\mid X)=0\). Constant \(f\) and a fair bit give \(H(X\mid Y)=\log2\). |
| pp18–19, (47) | Observational entropy uses \(+V_x\) where \(V_x=\operatorname{tr}P_x\). | Use \(+\log V_x\). A single projector \(I_d\) gives \(\log d\), not \(d\). This coarse-graining topic is outside the minimal implementation. |
| p20, (52), (54), (55) | Inconsistent outcome index, missing \(1/\beta\) in an intermediate entropy term, and \(TI\) without a stated \(k_B=1\) convention. | Normalize actual conditional laws, retain \(\beta^{-1}\), and use \(k_BT I\) in energy units. |
| p23 after (58) | Reset is assigned \(\Delta S_S=+\log2\). | With the stated final-minus-initial definition, \(\Delta S_S=-\log2\). Erased entropy is \(+\log2\). |
| p24, (64) | Intermediate expression has \(S(\rho_S)\) where \(S(\sigma_B)\) is needed. | Use \(S(\sigma_S)+S(\sigma_B)-S(\sigma_{SB})\). |
| p24, (65) | Literally prints \(-\Delta S_S+I\ge0=\Delta S_B\). | Correct equality is \(\Delta S_B=-\Delta S_S+I\). Bath entropy need not increase: SWAP a pure system with a uniform zero-Hamiltonian Gibbs bath to obtain \(\Delta S_B=-\log2\). |
| pp24–25, derivation of (66) | Missing \(\log\) of the partition function, missing \(\beta\) factors in added energy terms, and wrong sign of the log-Gibbs trace. | \(\Delta S_B=S(\sigma_B)-\beta E_B(\gamma_B)-\log Z=S(\sigma_B)+\operatorname{Tr}(\sigma_B\log\gamma_B)+\beta Q_B\). The endpoint \(-D+\beta Q_B\) is correct with corrected \(D\). |
| p27, (71) and following prose | A lower bound is written as actual heat; zero bound is interpreted as zero heat. | State an inequality; saturation needs an additional optimal/quasistatic contract. |
| p31, below (75) | Extracted-work inequality is reversed. | \(W_{\rm ext}\le\beta^{-1}I\), consistent with (57) and [R2]. |
| p31, heuristic reset paragraph | \(k_BT\log2\) is called an entropy. | Entropy is \(k_B\log2\); energy is \(k_BT\log2\). Full-cycle zero production is an ideal reversible limit, while general production is nonnegative. |
| pp27–30, reversible-computation discussion | Logical reversibility, global unitary evolution, and zero thermodynamic entropy production are sometimes conflated. | A reversible logical map permits thermodynamically reversible implementation in an appropriate limit; it does not force every implementation to be nondissipative. Uncomputation is not unconditional erasure of unknown independent data. |

There are further contextual slips outside the selected core: p5 gives the free energy as a derivative of the unlogged partition function, contradicted by correct (14); the bare p6 claim that Jarzynski holds for arbitrary processes omits its ensemble/dynamics assumptions; pp36–38 use specialized bounds whose bath, control, time, support, and unit conventions cannot be transferred to the minimal finite contract. These are not accepted theorem targets in this audit.

## 5. Minimal native theorem contracts and existing ownership

The following order avoids inventing duplicates or presenting supplied certificates as derived physics.

| Priority | Native theorem contract | Existing owners and remaining substance |
|---|---|---|
| 1 | Actual finite matrix Gibbs logarithm; Gibbs entropy; relative-entropy/free-energy **identity** | Reuse `FiniteMatrixGibbsFunctional.gibbsDensity` and its strict positivity, `PolarFrameTraceDensity.normalizedDensity` / `neg_log_normalizedDensity`, and `MatrixEntropyUnitaryOrbit.matrixEntropy`. Prove the CFC logarithm of the actual exponential and identify the normalized trace state. |
| 2 | Finite classical product entropy, permutation invariance, MI = KL joint versus marginals, support-aware nonnegativity | Reuse actual `FiniteBipartiteSurprisal.productFinProb`, `marginalA`, `marginalB`, and `entropyMutualInformation`. The inspected owner defines the last quantity but does not prove the needed chain/KL theorem. Its linear operator-readout result assumes the entropy readouts. |
| 3 | Classical Gibbs-bath heat balance under an actual joint permutation, then Landauer and correlation correction | Reuse `Probability.FiniteGibbsVariational` identities and positivity/equality theorems. Derive the joint entropy balance and the bath-energy difference. A strict-positive first scope is legitimate but must be labelled; boundary cases such as pure reset need a subsequent support-aware extension or an explicit infeasibility theorem. |
| 4 | Native quantum joint entropy balance and four-party cycle | Requires actual partial traces, tensor-product entropy, quantum MI/Klein nonnegativity, and support handling. Reuse the existing unitary entropy owner; its faithful-matrix theorem alone does not supply these other facts. |
| 5 | Binary and cycle arithmetic corollaries | Reuse PR358 owners if accepted and dependency-compatible; do not duplicate theorem names or promote hypotheses in those owners to a fresh physical derivation. |

For priority 1, a precise bounded contract is: finite nonempty matrix index type; Hermitian \(H\); finite real \(\beta\); actual \(G=\operatorname{CFCexp}(-\beta H)\); \(Z=(\operatorname{Tr}G).\mathrm{re}\); \(\gamma=Z^{-1}\cdot G\). Prove

\[
\operatorname{CFC.log}\gamma=(-\beta)\cdot H-(\log Z)\cdot I,
\quad S(\gamma)=\beta(\operatorname{Tr}(\gamma H)).\mathrm{re}+\log Z.
\]

For a faithful normalized matrix \(P\), define the actual trace-log relative entropy using `CFC.log P` and `CFC.log gamma`, and prove its energy/entropy expansion. This restriction matches current faithful CFC owners and is a meaningful completed leaf. Do not call its output the full quantum Landauer theorem, and do not claim a minimization result without a proof of matrix relative-entropy nonnegativity.

Source coverage checked directly:

- `Probability/FiniteGibbsVariational.lean` already proves `finiteRelativeEntropy_gibbs_eq`, `finite_gibbs_variational_identity`, `finiteRelativeEntropy_nonneg`, equality cases, and the Gibbs minimization theorem for strictly positive normalized finite laws. A second scalar Gibbs proof is unnecessary.
- `Canonical/FiniteMatrixGibbsFunctional.lean` constructs the CFC exponential, proves strict positivity for **every real beta**, and builds the normalized weighted trace. Its unrelated `admissibleBeta` predicate must not be imposed on this finite Gibbs theorem.
- `Canonical/FiniteMatrixGibbsFaithfulness.lean` proves faithfulness of that constructed matrix functional.
- `Canonical/PolarFrameTraceDensity.lean` supplies actual normalization, trace-one, strict positivity, and the central logarithmic normalization shift.
- `Canonical/MatrixEntropyUnitaryOrbit.lean` supplies genuine matrix entropy, actual CFC logarithm naturality, unitary invariance for faithful matrices, and entropy under trace normalization.
- `Canonical/QuantumRelativeSurprisal.lean` supplies useful trace algebra with arbitrary provided log matrices. Its free-energy identity does not establish that those matrices are the actual CFC logarithms. The new bridge should close this gap.
- `Canonical/FiniteBipartiteSurprisal.lean` supplies real PMF constructions; its generic operator embeddings do not constitute quantum partial traces or a quantum tensor-entropy proof.

Owner-discovery reports PR358 (`473d39724c43ee5cef8ba971ff82dfe42ca084f4`) already contains BinaryErasure/Jarzynski/TraceErasure/ObservableErasure leaves. Those work bounds depend on moment, Jarzynski, or entropy-balance hypotheses; they do not supply the missing joint Gibbs pushforward accounting. The separately reported local `LandauerDissipationNativeBridge` also must not be confused with a derivation: defining a heat readout from a complexity decrease is a model choice, not a consequence of a reservoir dynamics theorem.

## 6. Boundary with the previous Gram construction

A projected Gram operator can prove \(\dot S=\langle\nabla S,M\nabla S\rangle\ge0\), kernel statements, and conservation of a chosen energy under suitable degeneracy conditions. It does not identify this \(S\) with Shannon/von Neumann entropy, construct a normalized probability/density, identify a Gibbs reservoir and its temperature, produce an initial product state, define physical heat, or account for a resettable memory. None of \(Q_B\), \(\beta\), \(k_B\), or an erased bit is supplied by positive semidefiniteness alone. No Landauer conclusion should be attached to PR383/384/385 by analogy.

## Primary references checked

- **[R1]** D. Reeb and M. M. Wolf, *An improved Landauer principle with finite-size corrections*, New J. Phys. 16, 103011 (2014), [arXiv:1306.4352](https://arxiv.org/pdf/1306.4352). Lemma 2 and Theorem 3 (PDF pp8–9) give entropy and heat balances; Corollary 4 and Proposition 5 (pp10–11) delimit equality and finite-temperature purity.
- **[R2]** T. Sagawa and M. Ueda, *Nonequilibrium thermodynamics of feedback control*, Phys. Rev. E 85, 021104 (2012), [arXiv:1105.3262](https://arxiv.org/pdf/1105.3262). Equations (72)–(73), PDF pp9–10, give the work-on lower bound and the extracted-work upper bound.
- **[R3]** M. Esposito, K. Lindenberg, and C. Van den Broeck, *Entropy production as correlation between system and reservoir*, New J. Phys. 12, 013013 (2010), [arXiv:0908.1125](https://arxiv.org/pdf/0908.1125). Equations (5)–(9) distinguish entropy change, bath entropy flow, and the nonnegative relative-entropy production; globally unitary entropy conservation does not imply vanishing reduced thermodynamic production.

These sources support the corrected thermal framework. Counterexamples and proposed finite Lean contracts above are explicit mathematical deductions, not claims of new experimentally verified physics or accepted kernel results.

## Source-provenance appendix

These seven files were read independently and byte-compared with the recorded
main revision. This records source identity, not compilation.

| Repository path | SHA256 |
|---|---|
| `lean/InfoGeometry/Probability/FiniteGibbsVariational.lean` | `c071e691b477da417904c9d9faecb864ea71e34a54a3ede2459e68879ab9d61b` |
| `lean/InfoGeometry/Canonical/FiniteBipartiteSurprisal.lean` | `c474d0fe4d99e3a48e9f5a81e7f9e766de2dc161c5600c577d5b8cf4069577c6` |
| `lean/InfoGeometry/Canonical/FiniteMatrixGibbsFunctional.lean` | `49abd537aa7af6fcaa2dfb9e71dbaca6296fb323c82f58a60d760cd94322b12d` |
| `lean/InfoGeometry/Canonical/FiniteMatrixGibbsFaithfulness.lean` | `ac69327344eb4bebf6900740f94c66ee54eb307df17a87c9d79bc9c7c4936675` |
| `lean/InfoGeometry/Canonical/PolarFrameTraceDensity.lean` | `dfefacc4ab062b0a97c83dd04aa252fc123364d027c16c0c099656b5a2535094` |
| `lean/InfoGeometry/Canonical/MatrixEntropyUnitaryOrbit.lean` | `fe620d1766ed05a94754bbfb9f3adb0b54292dce375c80f817afd857ab2fda65` |
| `lean/InfoGeometry/Canonical/QuantumRelativeSurprisal.lean` | `52442910d6882afd8cd5e39d99aa1c5ff9f4821b3f41e92b2a5e50efa19a6dba` |

The standalone independent audit before this publication appendix had SHA256
`90d54bdfc8d655fe4efc7a8f53412909e73ad5ce9d6fb60b73cbef77677ec531`.
The implemented leaf and its intentionally broader trace-one algebraic contract
are specified in [MATRIX_GIBBS_ENTROPY_CONTRACT.md](MATRIX_GIBBS_ENTROPY_CONTRACT.md).

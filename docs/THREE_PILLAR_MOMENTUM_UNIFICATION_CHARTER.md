# Three-Pillar Momentum Unification Charter

> Status: `canonical architectural charter (FROZEN)`
> Version: 1.2.0
> Date: 2026-08-14

For the theorem/interpretation/open-identification boundary used by the
current corpus, see
[`ERLANGEN_2_THEOREM_HONEST_MANIFEST.md`](ERLANGEN_2_THEOREM_HONEST_MANIFEST.md).

This document defines the strict, theorem-honest master architecture of the repository, separating kernel-proved theorems, structural interfaces, quotient descents, and open continuum domain limits.

## 0. Double-closure boundary

The exceptional/Albert tower and the Clifford--Witt tower already have a
kernel-checked **scalar invariant readout** in
`Physics/ZornAlbertCliffordMasterIntertwinerBridge.lean`:

$$N_{\rm Zorn}=N_{\rm Albert}=C_1$$

under its stated diagonal/factorization hypotheses.  They are not yet
identified by one cross-tower **representation** theorem.  In particular, the verified
`Cl(5,5)` supercharge packet has the scalar readout

$$\{Q,\bar Q\}=2I_{32}=2P_0,$$

not yet the full four-component relation
$$\{Q_\alpha,\bar Q_{\dot\beta}\}=2\sigma^\mu_{\alpha\dot\beta}P_\mu$$
on that same 32-dimensional carrier.  A categorical colimit transport
theorem likewise does not imply a Hilbert-norm continuum limit.

The exceptional dimension bookkeeping uses
$$
\mathfrak e_{7(7)}=27+(78+1)+27=133,
$$
with $\mathfrak g_0=\mathfrak e_{6(6)}\oplus\mathbb R$; the middle term is
$79$, not $79+1$.

The remaining high-value wires are therefore explicit and separate:

```text
Exceptional/Albert representation  ──?──  Cl(5,5)/D5 spinor representation
categorical UHF colimit     ──?──  analytic Cantor momentum limit
```

Until those intertwiners are supplied and kernel-checked, this charter claims
compatible finite towers and categorical transport, not a global equivalence.

---

## 1. The Three Independent Pillars

The repository does not follow a single linear causal stack. It is structured into three parallel, self-consistent mathematical pillars connected by explicit operator intertwiners:

```text
┌──────────────────────────────────────────┐  ┌────────────────────────────────┐  ┌──────────────────────────────────────────────┐
│       PILLAR A: Discrete/Cuntz/UHF       │  │  PILLAR B: Spinor/Pauli/SUSY   │  │        PILLAR C: Exceptional/Zorn            │
├──────────────────────────────────────────┤  ├────────────────────────────────┤  ├──────────────────────────────────────────────┤
│ 1. Cantor Carrier L²(C, μ_C) [CLOSED]    │  │ 1. Chiral Supercharges Q_α,Q̄_β̇ │  │ 1. Split-Octonions O_split                   │
│ 2. Cuntz Isometries V_0, V_1 [CLOSED]    │  │ 2. Anticommutator {Q, Q̄}       │  │ 2. Zorn Vector Matrix Algebra [CLOSED]       │
│ 3. A_word --(E_0)--> A_word --(τ_0)--> ℂ │  │ 3. Pauli Soldering P_μ σ^μ     │  │ 3. (4,4) = (1,3) ⊕ (3,1) Fixed Section [CL]  │
│    └─ φ_0 = τ_0 ∘ E_0 [CLOSED on Core]   │  │ 4. Determinant = P_μ P^μ (1,3) │  │ 4. Der(O_split) ≅ g_{2,2}                    │
│ 4. Algebraic Quotient q: A_word -> A_alg │  │ 5. Inverse Pauli Trace Readout │  │    ├─ (Z_2)^3 Fine: 7 Homogeneous Comps      │
│ 5. C*-Completion A_C = C*(V_0, V_1) [CL] │  │ 6. Poincaré Lie ISO(1,3)       │  │    └─ Z_3 Coarse: sl_3(ℝ) ⊕ 3 ⊕ 3* (14 dims) │
│ 6. φ = τ_UHF ∘ E_gauge [--> TARGET]      │  │                                │  │                                              │
│ 7. GNS(φ) & Modular Flow [--> TARGET]    │  │                                │  │                                              │
└──────────────────────────────────────────┘  └────────────────────────────────┘  └──────────────────────────────────────────────┘
```

### Distinction of Objects and Descents in Pillar A
- $\mathcal{A}_{\mathrm{word}} = \operatorname{WordPair} \to_0 \mathbb{C}$: Free word coefficient carrier.
- $E_0 : \mathcal{A}_{\mathrm{word}} \to \mathcal{A}_{\mathrm{word}}$: Degree-zero linear gauge projector (`CLOSED`).
- $\tau_0 : \mathcal{A}_{\mathrm{word}} \to \mathbb{C}$: Linear word trace functional (`CLOSED`).
- $\varphi_0 = \tau_0 \circ E_0$: Exact equality of linear maps on $\mathcal{A}_{\mathrm{word}}$ (`CLOSED`).
- $q : \mathcal{A}_{\mathrm{word}} \twoheadrightarrow A_{\mathrm{Cuntz}}^{\mathrm{alg}}$: Algebraic quotient map to Cuntz relation core.
- $A_C = C^*(V_0, V_1) \subset \mathcal{B}(L^2(\mathcal{C}, \mu_C))$: Concrete operator C*-algebra (`CLOSED`).
- $\varphi = \tau_{\mathrm{UHF}} \circ E_{\mathrm{gauge}}$ on completed positive maps: `ANALYTIC TARGET` via quotient descent and bounded extension.

### Distinction of Gradings in Pillar C
- **Fine $(\mathbb{Z}_2)^3$-Grading:** $\mathbb{O}_s = \bigoplus_{\gamma \in (\mathbb{Z}_2)^3} (\mathbb{O}_s)_\gamma$ with 7 non-zero homogeneous components outside degree-zero.
- **Coarse $\mathbb{Z}_3$-Grading:** $\mathfrak{g}_{2(2)} \cong \mathfrak{sl}_3(\mathbb{R}) \oplus V \oplus V^*$ with dimensions $8 + 3 + 3 = 14$ (color triality).

---

## 2. The Spacetime Momentum Triangle (The Tri-Origin Framework)

Spacetime emergence is NOT an identification $\mathcal{M}^4 \cong \varinjlim M_{2^n}(\mathbb{C})$. The inductive limit is an algebra of multiscale quantum observables.

Spacetime translations arise through the **Unification of Three Independent Momentum Constructions**:

```text
       SUSY Multiplet {Q, Q̄}
                  │
                  ▼
              P_μ^SUSY  ═══════════( J Intertwining on Ran J )═══════════►  P_μ^C
                                                                             ║
                                                                             ║ (Equality on Core 𝒟)
                                                                             ▼
       Modular Inclusions  ────────( Analytic Target )────────►  P_μ^mod ═══╝
                                                                             ▲
                                                                             ║ (Pointwise Norm Limit)
                                                                             ║
       Dyadic Differences  ───( D_{μ,n} = 2ⁿ(I - T_{μ,n}) )──────────────────╝
```

### The Grand Unification Objective on Common Dense Core $\mathcal{D} \subset L^2(\mathcal{C}, \mu_C)$

1. **Spinor Intertwining on Range:**
   $$J P_\mu^{\mathrm{SUSY}} \psi = P_\mu^C J \psi \qquad (\forall \psi \in S_{\mathrm{Spin}})$$
2. **Domain Equality:**
   $$P_\mu^C|_{\mathcal{D}} = P_\mu^{\mathrm{mod}}|_{\mathcal{D}}$$
3. **Self-Adjoint Closure:**
   $$\overline{P_\mu^C|_{\mathcal{D}}} = P_\mu^C = \overline{P_\mu^{\mathrm{mod}}|_{\mathcal{D}}} = P_\mu^{\mathrm{mod}}$$
4. **Pointwise Norm Convergence on Core $\mathcal{D}$:**
   $$\forall \psi \in \mathcal{D}, \qquad \lim_{n \to \infty} \left\| 2^n(I - T_{\mu,n})\psi - i P_\mu \psi \right\|_{L^2(\mathcal{C}, \mu_C)} = 0$$

### The Poincaré Lie Algebra on Core $\mathcal{D}$
For all $\psi \in \mathcal{D}$ with valid generator compositions:
- $[P_\mu, P_\nu]\psi = 0$
- $[M_{\mu\nu}, P_\rho]\psi = i(\eta_{\nu\rho} P_\mu - \eta_{\mu\rho} P_\nu)\psi$
- $[M_{\mu\nu}, M_{\rho\sigma}]\psi = i(\eta_{\nu\rho} M_{\mu\sigma} - \eta_{\mu\rho} M_{\nu\sigma} + \eta_{\mu\sigma} M_{\nu\rho} - \eta_{\nu\sigma} M_{\mu\rho})\psi$

---

## 3. Strict Signature and Kinematic Separation

1. **Complex Pauli Soldering (Lorentzian $1,3$):**
   $$\operatorname{Herm}_2(\mathbb{C}) \cong \mathbb{R}^{1,3}, \qquad \det(\operatorname{solder}(P)) = E^2 - p_x^2 - p_y^2 - p_z^2 = P_\mu P^\mu$$
   *Theorem Truth:* Pauli soldering realizes the Minkowski quadratic form as the determinant of the Hermitian $2 \times 2$ matrix.

2. **Real Split Octonion Fixed-Section (Lorentzian $1,3$ via $\operatorname{Fix}(\kappa)$):**
   $$N(X_{\mathrm{sym}}) = t^2 - x_1^2 - x_2^2 - x_3^2 = \eta_{1,3}(t, \mathbf{x}) \qquad (\text{Exact in } \texttt{SplitOctonionChiralMinkowskiFixedSectionBridge})$$
   $$N(X_{\mathrm{anti}}) = -(\tau^2 - y_1^2 - y_2^2 - y_3^2) = -\eta_{1,3}(\tau, \mathbf{y})$$
   $$\mathbb{R}^{4,4} \cong \mathbb{R}^{1,3} \oplus \mathbb{R}^{3,1}$$

3. **Kinematics:**
   - Dual quaternions encode Euclidean rigid body motions $SE(3) = SO(3) \ltimes \mathbb{R}^3$.
   - Relativistic Poincaré kinematics is carried by $SO^+(1,3) \ltimes \mathbb{R}^{1,3}$ (`HestenesCuntzSpacetimeAlgebra.lean`).

---

## 4. KMS Parameterization Convention

- **Gauge Flow Scaling:** $\alpha_t(S_j) = e^{it} S_j \implies \beta_c = \ln 2$.
- **Rescaled Modular Flow:** $\sigma_t^\varphi(S_j) = 2^{-it} S_j = e^{-it \ln 2} S_j \implies \beta = 1$.
- **Modular Surprisal Generator:**
  $$\mathcal{K} = -\log \Delta = L_{-\log \rho} - R_{-\log \rho}$$
  *(Exact in the finite faithful standard-form model; concrete Cantor analytic realization is a downstream theorem target).*

---

## 5. Master Theorem Status Ledger

| Component | Status in Lean 4 | Primary Owner Module |
| :--- | :---: | :--- |
| **$L^2(\mathcal{C}, \mu_C)$ Cuntz Operators & Adjoints** | `CLOSED` | `Canonical/CantorBernoulliL2OperatorTransport.lean` |
| **Spatial State Non-Separating Firewall** | `CLOSED` | `OperatorAlgebra/CantorBernoulliSpatialNonSeparatingBridge.lean` |
| **Native Spatial State on Generated Bernoulli C⋆-Subalgebra** | `CLOSED (spatial only; not gauge/KMS)` | `OperatorAlgebra/CantorBernoulliGeneratedCStarSpatialStateBridge.lean` |
| **Algebraic Word KMS Condition at $\beta_c = \ln 2$** | `CLOSED` | `OperatorAlgebra/CantorBernoulliAlgebraicWordKMSBridge.lean` |
| **Finite Matrix Trace Norm Bound $\|\tau_n\| = 1$** | `CLOSED` | `Canonical/CantorBernoulliStateNormBoundBridge.lean` |
| **$C^*$-Matrix State Transport & Faithfulness** | `CLOSED` | `Canonical/CantorBernoulliCStarMatrixTraceState.lean` |
| **2D Spinor/Pauli Intertwiner $J \sigma^\mu = \Sigma_C^\mu J$** | `CLOSED` | `Canonical/CantorBernoulliPauliMatrixIntertwiner.lean` |
| **Pauli Soldering & Inverse Trace Readout** | `CLOSED` | `Canonical/CantorBernoulliPauliSolderingIntertwinerBridge.lean` |
| **Commuting 4-Momentum on Spinor Sector $[P_\mu^C, P_\nu^C] = 0$** | `CLOSED` | `Canonical/CantorBernoulliPauliSolderingIntertwinerBridge.lean` |
| **$\mathbb{O}_s$ Chiral Fixed-Section $(1,3) \oplus (3,1) = (4,4)$** | `CLOSED` | `Lie/SplitOctonionChiralMinkowskiFixedSectionBridge.lean` |
| **Witt coordinate duality $V_- \simeq V_+^*$** | `CLOSED (local coordinate carrier)` | `Lie/SplitOctonionWittVectorCovectorBridge.lean` |
| **First Casimir $C_1=\det(\slashed P)=N(X_{\mathrm{sym}})$** | `CLOSED` | `Physics/SplitOctonionPoincareCasimirBridge.lean` |
| **Pauli--Lubanski definition and $P\cdot W=0$** | `CLOSED (algebraic substrate)` | `Physics/SplitOctonionPoincareCasimirBridge.lean` |
| **$C_1$ centrality under explicit Lorentz action** | `CLOSED (algebraic hypotheses)` | `Physics/PoincareCasimirCentralityBridge.lean` |
| **$C_2$ centrality $[C_2,\mathfrak{iso}(1,3)]=0$** | `CLOSED (explicit algebraic bracket hypotheses)` | `Physics/PoincareCasimirCentralityBridge.lean` |
| **General irreducible-representation values of $C_2$** | `OPEN` | Target: massive/massless representation layer |
| **Projective Rapidity & Monodromy $\kappa(\eta) = -\eta$** | `CLOSED` | `Lie/SplitOctonionProjectiveRapidityMonodromyBridge.lean` |
| **Native Mathlib GNS Structure on $\mathcal{B}(L^2)$** | `CLOSED` | `OperatorAlgebra/CantorBernoulliContinuousStateGNSBridge.lean` |
| **Quotient Descent $q : \mathcal{A}_{\mathrm{word}} \twoheadrightarrow A_{\mathrm{Cuntz}}^{\mathrm{alg}}$** | `IN PROGRESS` | `OperatorAlgebra/CantorBernoulliContinuousStateGNSBridge.lean` |
| **Algebraic $\ell^1$ bound $\|\varphi_0(c)\| \le \|c\|_1$** | `CLOSED (word core only)` | `OperatorAlgebra/CantorBernoulliLinearGaugeUHFFactorizationBridge.lean` |
| **Algebraic $\ell^1$ bound for $\tau_0$** | `CLOSED (word core only)` | `OperatorAlgebra/CantorBernoulliLinearGaugeUHFFactorizationBridge.lean` |
| **Word-core / finite UHF trace readout compatibility** | `CLOSED (finite stages)` | `OperatorAlgebra/CantorBernoulliLinearGaugeUHFFactorizationBridge.lean` |
| **Continuous Extension $\|\varphi_0(a)\| \le \|a\|$ to $A_C$** | `OPEN (not supplied by spatial state)` | Target: concrete gauge C⋆-state extension |
| **Pointwise Dyadic Convergence on Core $\mathcal{D}$** | `OPEN` | Target: Common Dense Core $\mathcal{D}$ |
| **Half-Sided Modular Translations $P_\mu^{\mathrm{mod}}$** | `OPEN` | Target: Borchers Translation Group |
| **Grand Momentum Equivalence $P_\mu^{\mathrm{SUSY}} \xleftrightarrow{J} P_\mu^C = P_\mu^{\mathrm{mod}}$** | `CAPSTONE` | Target: Full Emergent Spacetime |

## 6. Native categorical progress (verified)

The finite algebraic replacement is now strengthened by a genuine universal
property on the additive direct limit.  In
`Canonical/CantorDyadicColimitMomentumBridge.lean`,
`colimitMomentumOperator_unique` proves that the induced colimit endomorphism
is uniquely determined by its values on every canonical stage inclusion.  This
is a kernel-checked categorical statement, not a norm-limit or unbounded
generator theorem.

The corresponding categorical boundary remains explicit:

```text
finite coherent stage operators
        -> native additive direct-limit operator       CLOSED
        -> categorical uniqueness on stage inclusions   CLOSED
        - - - analytic Hilbert/core convergence - - -   OPEN
```

Likewise, `Lie/SplitOctonionCl55WittEmbeddingBridge.lean` proves only the
finite quadratic carrier embedding
`Q55 (wittToV55 x) = wittNorm x` and its coordinate left inverse.  It does
not claim a `Pin(5,5)` spin representation or an exceptional-to-Clifford
intertwiner.

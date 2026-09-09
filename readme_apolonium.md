# Apollonian Geometry, Weyl Gauge Scales, and Simplex Thermodynamics

## Executive Summary & Methodological Scope

This document unifies the **scalar Weyl scale transformations**, **Aitchison compositional geometry**, **Apollonian bipolar coordinates**, and **thermodynamic duality** on the response simplex. 

To maintain mathematical and metrological integrity, this reference rigorously distinguishes:
1. **Exact Algebraic Identities**: Proved in Lean 4 and symbolic CAS (e.g., CLR coordinates, metric relations on $\Delta^1$, cross-section quotients).
2. **Statistical Estimators**: The median log-shift algorithm and its empirical performance on measured spectra.
3. **Geometric & Physical Models**: The two-pole Apollonian coordinate framework and its domain of physical applicability.

---

## 1. Interpreting Weyl Gauge Scales in Multi-Distance Spectrometry

In multi-distance $\gamma$-ray spectrometry, changing the acquisition distance $d_j$ rescales observed photopeak count rates by an overall geometry factor $e^{\omega_j}$:
$$L_{ij} \;\longmapsto\; e^{\omega_j} L_{ij}.$$

Here $L_{ij} = R_{ij} + K_i X_j^2$ denotes the coincidence-restored rate for transition $i$ at distance index $j$. This scaling acts as a **scalar multiplicative group action**:

* **Log-Rate Coordinates:**
  $$\ell_{ij} = \ln(L_{ij} / L_{\rm unit}) \;\longmapsto\; \ell_{ij} + \omega_j.$$
  The multiplicative scale group $(\mathbb{R}^+, \times)$ is mapped by the real logarithm into the additive translation group $(\mathbb{R}, +)$.
* **Surprisal-Like Coordinates:**
  $$h_{ij} = -\ln(L_{ij} / L_{\rm unit}) \;\longmapsto\; h_{ij} - \omega_j.$$
  The negative log rates transform with the opposite sign as additive potentials.
* **Formal Implementation:**
  This scalar multiplicative action and its logarithmic generator are implemented in [`lean/InfoGeometry/Projective/WeylLogScaleBridge.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Projective/WeylLogScaleBridge.lean) (`scaleLog`, `weylMetricAction`, `weylFieldAction`). Identifying this scalar spectral rescaling with a spacetime conformal metric requires additional physical and geometric field structure.

---

## 2. Connecting Weyl Gauge to Aitchison Simplex Geometry

### 2.1 The Ensemble Geometric-Mean Normalization
For a set of positive scale factors $g_j$, define their centered log-shifts:
$$\widetilde{s}_j = \ln g_j - \frac{1}{m}\sum_{k=1}^m \ln g_k = \operatorname{clr}(g)_j.$$

* **The CLR Identity:** The centered scale vector $\widetilde{\mathbf{s}} = (\widetilde{s}_1, \dots, \widetilde{s}_m)$ is identically the **Centered Log-Ratio (CLR)** coordinate vector of Aitchison compositional geometry on the simplex $\mathcal{S}^{m-1}$.
* **Zero-Sum Constraint:**
  $$\sum_{j=1}^m \widetilde{s}_j = 0 \quad\Longleftrightarrow\quad \prod_{j=1}^m e^{\widetilde{s}_j} = 1.$$
  This condition anchors the scale at the ensemble's geometric mean. Calling $\prod_j e^{\widetilde{s}_j} = 1$ a thermodynamic partition function is a formal analogy; physically, it is a geometric-mean product normalization that removes the arbitrary reference distance $d_*$.

### 2.2 Median Estimator Scope
In the empirical transport pipeline:
$$\mu_i = \frac{1}{m}\sum_{j=1}^m \ell_{ij}, \qquad s_j = \operatorname{median}_i(\ell_{ij} - \mu_i).$$
* **Objective:** The sample median across lines $i$ minimizes the $L_1$ absolute error sum:
  $$s_j = \arg\min_s \sum_{i=1}^n |\ell_{ij} - \mu_i - s|.$$
* **Scope Demarcation:** The scalar median possesses a classical $50\%$ breakdown point for independent scalar samples. However, this property does *not* establish a $50\%$ breakdown point for the entire composite transport pipeline, which involves shared coincidence inputs $X_j = \sqrt{Q_j}$, errors-in-variables fits, and upstream coincidence covariance.

---

## 3. Scope and Boundaries of Mathematical Extensions

To prevent conflation between proved algebra and physical interpretation, the following scope boundaries are established:

| Claim / Construction | Formal Mathematical Truth | Physical / Operational Scope Boundary |
| :--- | :--- | :--- |
| **Median minimization** | Minimizes $\sum_i |\ell_{ij} - \mu_i - s_j|$ ($L_1$ absolute deviation). | Not "Laplace entropy"; it is a robust $L_1$ location estimator. |
| **Breakdown protection** | The 1D scalar median has a $50\%$ breakdown point against outliers. | Does not guarantee $50\%$ breakdown for the full multi-step, shared-input transport pipeline. |
| **Product normalization** | $\prod_j e^{\widetilde{s}_j} = 1 \iff \sum_j \widetilde{s}_j = 0$. | Product/scale normalization; calling it a thermodynamic partition function requires a separate physical definition. |
| **Simplex metric relation** | $b''(p) = 2 g_{\rm Aitchison}(p) - 2 g_{\rm FR}(p)$ on $\Delta^1$. | Exact algebraic identity between distinct Riemannian metrics on $\Delta^1$; they are not nested submanifolds. |
| **Binary response coordinate** | $p = KX/C$ maps $I(X) = \frac{C^2}{K} p(1-p)$. | $p$ is a probability only on the physical loss domain $0 \le p \le 1$. In multiline spectra, net $K$ can be signed (summing-in). |
| **Apollonian coordinates** | Exact static bipolar coordinates $\eta(P) = \ln(|P-A|/|P-B|)$. | Coordinate construction; the $(d+d_0)$ fit alone does not establish a Green's function, photon focusing, or entropy flow. |
| **Scale factor $4\pi/a^2$** | With $X = \sqrt{Q}$, $a$ has units $\text{counts}^{-1/4} \text{s}^{1/4} \text{cm}^{-1}$. | $4\pi/a^2$ carries area $\times \sqrt{\text{rate}}$ units; an explicit rate normalization is required to define a physical aperture area. |

---

## 4. The Binary Response Simplex $\Delta^1$ and Distinct Metrics

In a single photopeak channel governed by coincidence summing-out, the quadratic net response is:
$$I(X) = C X - K X^2, \qquad C > 0, \quad K > 0.$$

Where $0 \le K X \le C$, we define the dimensionless coordinates:
$$p = \frac{K X}{C}, \qquad q = 1 - p, \qquad \frac{K I}{C^2} = p(1-p), \quad (p, q) \in \Delta^1.$$

On the interior $0 < p < 1$, the simplex supports three distinct Riemannian metrics:
1. **Fisher--Rao Information Metric:**
   $$g_{\rm FR}(p) = \frac{1}{p(1-p)}.$$
2. **Aitchison Metric (Compositional Geometry):**
   $$g_{\rm Aitchison}(p) = \frac{1}{2p^2(1-p)^2}.$$
   For the log-odds $\ell = \operatorname{logit}(p) = \ln \frac{p}{1-p}$, the line element is $d\ell^2 = 2\,ds_{\rm Aitchison}^2$.
3. **Dikin Log-Barrier Hessian:**
   $$b(p) = -\ln p - \ln(1-p) \implies b''(p) = \frac{1}{p^2} + \frac{1}{(1-p)^2}.$$

* **Algebraic Identity:**
  $$\boxed{b''(p) = 2\,g_{\rm Aitchison}(p) - 2\,g_{\rm FR}(p).}$$
  Verified constructively in [`lean/InfoGeometry/Convex/BinaryBarrierCoordinateHessian.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Convex/BinaryBarrierCoordinateHessian.lean).

---

## 5. Thermodynamics: Potentials, Dual Readouts, and Modular Flow

### 5.1 Dual Readouts of the Surprisal Operator
Define the diagonal density state $\rho$ and its operator-valued surprisal $K$:
$$\rho = \begin{pmatrix} p & 0 \\ 0 & 1-p \end{pmatrix}, \qquad K = -\ln \rho = \begin{pmatrix} -\ln p & 0 \\ 0 & -\ln(1-p) \end{pmatrix}.$$

* **Dikin Barrier (Unweighted Trace):**
  $$b(p) = \operatorname{tr}(K) = -\ln p - \ln(1-p).$$
  Satisfies the self-concordance differential inequality: $|b'''(p)| \le 2\sqrt{b''(p)}\,b''(p)$.
* **Shannon Entropy (Density-Weighted Trace):**
  $$S(p) = \operatorname{tr}(\rho K) = -p\ln p - (1-p)\ln(1-p).$$

### 5.2 Massieu--Legendre Duality
* Natural parameter: $\theta = \ln \frac{p}{1-p} = \operatorname{logit}(p) = K_{22} - K_{11}$.
* Massieu potential: $\Psi(\theta) = \ln(1 + e^\theta)$.
  * Mean: $\Psi'(\theta) = p(\theta)$.
  * Variance / Fisher information: $\Psi''(\theta) = p(1-p) = g_{\rm FR}^{-1}$.
  * Legendre conjugate: $\Psi^*(p) = \sup_\theta (\theta p - \Psi(\theta)) = -S(p)$.

### 5.3 Metriplectic and Modular Dynamics
* **Metriplectic Flow:** Coupling Hamiltonian flow on $(q, r)$ with gradient dissipation on $p$:
  $$\dot{p} = -p(1-p)\theta, \qquad \dot{S} = p(1-p)\theta^2 \ge 0.$$
* **Tomita--Takesaki Modular Flow:**
  $$\sigma_t(A) = \rho^{it} A \rho^{-it}, \qquad \left.\frac{d}{dt}\sigma_t(A)\right|_{t=0} = -i[K, A].$$
  Off-diagonal matrix elements oscillate at frequencies equal to CLR surprisal differences: $\omega_{12} = \theta$.

---

## 6. Spectroscopic Cross-Section Duality and Angular Consistency

### 6.1 Dual Cross-Section Definitions
* **Photopeak Area:**
  $$S_i^{(\rm peak)} = \frac{4\pi C_i}{A P_i a^2} = \eta_{p, i} S_{\rm geom}.$$
* **Virtual Summing-Loss Envelope:**
  $$S_{{\rm v}, j} = \frac{4\pi K_j}{C_j a^2}.$$

### 6.2 Microscopic Factorization and the Angular Factor
In the microscopic interaction model:
* If the summing loss is decomposed including an effective peak–total angular factor $\overline{W}_{pt}$:
  $$S_{{\rm v}, j} = P(i\mid j)\,\overline{W}_{pt}\,\eta_{t, i} S_{\rm geom}.$$
* Then the intrinsic peak-to-total ratio $(P/T)_i = \eta_{p, i} / \eta_{t, i}$ is recovered via:
  $$\boxed{\left(\frac{P}{T}\right)_i = P(i\mid j)\,\overline{W}_{pt} \frac{S_i^{(\rm peak)}}{S_{{\rm v}, j}}.}$$
* **Consistency Requirement:** The angular factor $\overline{W}_{pt}$ for peak–total summing loss must be defined consistently with the peak–peak factor $\overline{W}_{pp}$ appearing in the coincidence activity formula $A = \frac{C_1 C_2}{Q} \frac{P_{12}}{P_1 P_2} \overline{W}_{pp}$. In the simplified module [`Probability/DetectorCrossSectionDuality.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Probability/DetectorCrossSectionDuality.lean), $\overline{W}_{pt}$ is set to unity ($W = 1$). When angular correlations are retained, $\overline{W}_{pt}$ must multiply the ratio as derived above.

---

## 7. The Apollonian Bipolar Coordinate System

The Virtual Point Detector (VPD) model $r = d + d_0$ defines a static two-pole bipolar coordinate geometry:
* **Pole A (Source):** $(0, d)$ along the detector axis.
* **Pole B (Virtual Center):** $(0, -d_0)$ inside the detector volume.
* **Inter-Polar Separation:** $r_{AB} = d - (-d_0) = d + d_0$.
* **Quartic Linearizer:** $\Lambda(d) = Q(d)^{-1/4} = a(d + d_0) = a \cdot r_{AB}$.
* **Bipolar Coordinates:**
  $$\eta(P) = \ln\frac{|P - A|}{|P - B|}, \qquad \xi(P) = \angle APB.$$
  * Level sets of $\eta$ are Apollonian circles separating the poles.
  * The midline $\eta = 0$ is the perpendicular bisector plane at $x_m = (d - d_0)/2$.
  * Level sets of $\xi$ are circular arcs connecting Pole A and Pole B (streamlines).
* **Physical Boundary:** This geometry is a spatial representation of the inverse-distance scaling; it does not independently prove focusing, wave propagation, or an entropy-producing continuum dynamics without further microscopic transport modeling.

---

## 8. Verified Lean 4 Formalization Map

| File Path | Status | Formally Proved Scope |
| :--- | :--- | :--- |
| [`lean/InfoGeometry/Projective/WeylLogScaleBridge.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Projective/WeylLogScaleBridge.lean) | Verified | Scalar multiplicative action, log generator, group hom |
| [`lean/InfoGeometry/Probability/DetectorScaleInvariance.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Probability/DetectorScaleInvariance.lean) | Verified | Gauge zero-sum $\sum \widetilde{s}_j = 0$, $\prod e^{\widetilde{s}_j} = 1$, residual vanishing |
| [`lean/InfoGeometry/Probability/BinaryAitchisonMoments.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Probability/BinaryAitchisonMoments.lean) | Verified | CLR transform, centered moments, Fisher variance |
| [`lean/InfoGeometry/Probability/BinaryAitchisonLogOdds.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Probability/BinaryAitchisonLogOdds.lean) | Verified | Metric relation $d\ell^2 = 2\,ds_{\rm A}^2$, log-odds geodesic |
| [`lean/InfoGeometry/Convex/BinaryBarrierCoordinateHessian.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Convex/BinaryBarrierCoordinateHessian.lean) | Verified | Barrier Hessian identity $b'' = 2 g_{\rm Aitchison} - 2 g_{\rm FR}$ |
| [`lean/InfoGeometry/Convex/BinaryBarrierSurprisal.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Convex/BinaryBarrierSurprisal.lean) | Verified | Dual readouts $b = \operatorname{tr} K$, $S = \operatorname{tr}(\rho K)$, self-concordance |
| [`lean/InfoGeometry/Geometry/BinaryLegendreEntropyFlow.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Geometry/BinaryLegendreEntropyFlow.lean) | Verified | Bernoulli Legendre contact, monotonic entropy flow $\dot{S} \ge 0$ |
| [`lean/InfoGeometry/Thermo/BinaryEntropyMetriplectic.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Thermo/BinaryEntropyMetriplectic.lean) | Verified | Concrete GENERIC system, energy conservation, entropy production |
| [`lean/InfoGeometry/Modular/FiniteSimplexModularTime.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Modular/FiniteSimplexModularTime.lean) | Verified | $\sigma_t$ automorphism group, $-i[K, A]$ generator, frequency $\omega = \theta$ |
| [`lean/InfoGeometry/Nuclear/ApollonianBipolarField.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Nuclear/ApollonianBipolarField.lean) | Verified | Two poles $A, B$, separation $r_{AB}$, linearizer vanishing at $-d_0$ |
| [`lean/InfoGeometry/Probability/DetectorCrossSectionDuality.lean`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Probability/DetectorCrossSectionDuality.lean) | Verified | Activity cancellation, $(P/T)_i$ recovery formula under explicit hypotheses |

---

## 9. Slide Presentation Alignment (`conference.pdf`)

* **Slide 13 ([`virtual_benchmark.tex`](file:///home/goutev/Varna/presentation/60Co/New%20Project/slides/main/virtual_benchmark.tex)):** Virtual equivalent disk diameters ($65.8\text{ mm}$ for Canberra GC5019 vs $65.7\text{ mm}$ factory; $66.9\text{ mm}$ for ORTEC GEM50 vs $64.1\text{--}68\text{ mm}$ crystal).
* **Slide 37 ([`log_transport.tex`](file:///home/goutev/Varna/presentation/60Co/New%20Project/slides/main/log_transport.tex)):** Ensemble geometric-mean baseline, median shifts, and the exact CLR coordinate connection ($\prod_j e^{\widetilde{s}_j} = 1$).
* **Slides 145–150 ([`advanced_foundations.tex`](file:///home/goutev/Varna/presentation/60Co/New%20Project/slides/backup/advanced_foundations.tex)):** Complete Apollonian 10 cm detector vector diagram and bipolar field streamlines.
* **Slides 160–163 ([`simplex_extension.tex`](file:///home/goutev/Varna/presentation/60Co/New%20Project/slides/backup/simplex_extension.tex)):** Metric table (Fisher-Rao, Aitchison, Dikin barrier), surprisal dual readouts ($b(p) = \operatorname{tr} K$ vs $S(p) = \operatorname{tr}(\rho K)$), and the metriplectic/modular flows.

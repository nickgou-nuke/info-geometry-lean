# Split-Octonion Chiral Lightcone, De Witt Split, and Krein Monodromy Synthesis

> Status: `canonical geometric & thermodynamic reference`
> Version: 1.0.0
> Date: 2026-08-14

This document formalizes the exact geometric, operator-algebraic, and thermodynamic mechanics of the Split-Octonions ($\mathbb{O}_s$), the De Witt / Peirce split ($1 + 3$ planes), the Souriau-Vinberg statistical cone, the parabolic apex monodromy $(0, 1, \infty)$, and the Hestenes-Krein rotor calculus.

---

## 1. Split-Octonions $\mathbb{O}_s$, Zorn Vector Matrices, and the De Witt Split

In the algebra of split-octonions $\mathbb{O}_s$, the norm quadratic form has signature $(4,4)$. In the Zorn vector matrix representation:
$$Z = \begin{pmatrix} a & \mathbf{u} \\ \mathbf{v} & b \end{pmatrix}, \qquad a, b \in \mathbb{R}, \quad \mathbf{u}, \mathbf{v} \in \mathbb{R}^3$$
with non-associative multiplication:
$$\begin{pmatrix} a_1 & \mathbf{u}_1 \\ \mathbf{v}_1 & b_1 \end{pmatrix} \begin{pmatrix} a_2 & \mathbf{u}_2 \\ \mathbf{v}_2 & b_2 \end{pmatrix} = \begin{pmatrix} a_1 a_2 + \mathbf{u}_1 \cdot \mathbf{v}_2 & a_1 \mathbf{u}_2 + b_2 \mathbf{u}_1 - \mathbf{v}_1 \times \mathbf{v}_2 \\ b_1 \mathbf{v}_2 + a_2 \mathbf{v}_1 + \mathbf{u}_1 \times \mathbf{u}_2 & b_1 b_2 + \mathbf{v}_1 \cdot \mathbf{u}_2 \end{pmatrix}$$

### The 8-Dimensional Chiral Lightcone
$$\boxed{N(Z) = \det(Z) = ab - \mathbf{u} \cdot \mathbf{v} = 0}$$

### De Witt / Peirce Decomposition into Four 2D Planes ($1 + 3$)
With splitting idempotent $j_0$ ($j_0^2 = +1$) and Peirce projectors $e_1 = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}, e_2 = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$:
1. **Longitudinal Hyperbolic Lightcone Axis ($u_+, u_-$):**
   $$u_+ = a, \quad u_- = b \quad \Longrightarrow \quad ds_0^2 = du_+ du_-$$
2. **Three Transverse Hypercomplex / Phase Planes ($k = 1, 2, 3$):**
   $$(u_k, v_k) \in \mathbb{R}^2 \quad \Longrightarrow \quad ds_k^2 = -du_k dv_k$$
   Total decomposition:
   $$N(Z) = \underbrace{u_+ u_-}_{\text{longitudinal time axis}} - \underbrace{\sum_{k=1}^3 u_k v_k}_{\text{3 transverse spatial planes}} = 0$$

```text
                   u₊ (Axis to +∞)
                   ▲
                   │     /  Lightcone N(Z) = 0
                   │    /   ab - u·v = 0
                   │   /
                   │  /   [3 transverse planes (uₖ, vₖ)]
                   │ /    Spin cross-section: S² × S²
                   │/
   ────────────────┼────────────────► u₋ (Axis to -∞)
                  /│
                 / │
                /  │
               /   │  Apex (Origin: Z = 0)
              /    │  Parabolic Monodromy & Krein Jump
```

---

## 2. Nilpotent Generators $\sigma_k^\pm$ and Spin Algebra Soldering

On the lightcone, the transverse directions are governed by nilpotent step operators:
$$\sigma_k^+ = \begin{pmatrix} 0 & \mathbf{e}_k \\ 0 & 0 \end{pmatrix}, \qquad \sigma_k^- = \begin{pmatrix} 0 & 0 \\ \mathbf{e}_k & 0 \end{pmatrix} \qquad (k=1,2,3)$$
$$(\sigma_k^+)^2 = 0, \qquad (\sigma_k^-)^2 = 0, \qquad \{\sigma_k^+, \sigma_m^-\} = \delta_{km} I + \dots$$

* **Spin Algebra:** Commutators $[\sigma_k^+, \sigma_m^-]$ generate spatial rotations in $\mathfrak{su}(2) \subset \mathfrak{so}(3,1) \subset \mathfrak{g}_{2,2}$.
* **Spherical Cross-Section:** At constant slice $u_+ + u_- = 2E$, the cone projects to a spatial 2-sphere $S^2$ with spin operators $S_\pm = S_x \pm i S_y$.

---

## 3. Souriau-Vinberg Statistical Cone and Gaussian Information Thermodynamics

The lightcone $\mathcal{C}_8$ is a symmetric statistical cone with characteristic Massieu potential:
$$\psi(\beta) = -\ln N(\beta) = -\ln \big(\beta_+ \beta_- - \boldsymbol{\beta}_u \cdot \boldsymbol{\beta}_v\big)$$

* **Fisher-Souriau Metric:** $g_{AB}(\beta) = \frac{\partial^2}{\partial \beta^A \partial \beta^B} (-\ln N(\beta))$.
* **Gaussian Ensemble:** $p(Z | \beta) = \frac{1}{Z(\beta)} e^{-\langle \beta, Z \rangle}$ with covariance given by $g_{AB}$.
* **KMS Asymptotics:** On the boundary $N(\beta) \to 0$, the Souriau thermal flow $\sigma_t = e^{it \mathcal{K}}$ matches the Tomita modular flow at $\beta_c = \ln 2$.

---

## 4. Lightcone Projective Time, Parabolic Triad, and $(0, 1, \infty)$ Monodromy

Parametric time emerges along the projective rays:
$$\tau = \frac{1}{2} \ln \left(\frac{u_+}{u_-}\right)$$

### Mobius Triad:
1. **Hyperbolic (Dilation / Boost):** $H = u_+ \partial_+ - u_- \partial_-$ (modular scaling).
2. **Elliptic (Rotation / Spin):** $J = \sigma^+ - \sigma^-$.
3. **Parabolic (Lightlike Translations):** $N_+ = \sigma^+ = u_+ \partial_v$ (fixing the lightcone boundary).

### Monodromy around $(0, 1, \infty)$:
* $0$: Apex singularity (projector intersection $u_+ = 0$).
* $1$: KMS equilibrium / vacuum fixed point.
* $\infty$: Asymptotic null horizon.

Looping around the apex induces sheet-to-sheet winding across the Riemann surface of $\ln Z$:
$$\mathcal{M}_{0,1,\infty} : \Psi(e^{2\pi i} Z) = e^{2\pi i \mathcal{K}} \Psi(Z) = \Delta \Psi(Z)$$

---

## 5. Hestenes-Krein Operator Calculus and Krein Reflection

In the geometric algebra of Hestenes ($\mathrm{Cl}_{1,3}$ / $\mathrm{Cl}_{4,4}$) and Krein space theory:
$$[x, y]_\eta = \langle x, \eta y \rangle_{L^2}, \qquad \eta = J_{\mathrm{Krein}} = P_+ - P_-, \quad \eta^2 = I, \quad \eta^\dagger = \eta$$

### Krein Rotor Holonomy:
$$\mathcal{U}_\gamma = \mathcal{P} \exp \left( \oint_\gamma \Omega_{AB} \, \sigma^A \wedge \sigma^B \right)$$
$$\mathcal{U}_\gamma^\dagger \, \eta \, \mathcal{U}_\gamma = \eta \quad \text{($\eta$-unitarity)}$$
$$\mathcal{U}_\gamma = \underbrace{e^{i \Phi_{\text{Berry}}}}_{\text{compact spin phase}} \times \underbrace{e^{\Theta_{\text{boost}} J_{\text{Krein}}}}_{\text{hyperbolic rapidity / modular jump}}$$

---

## 6. Lean 4 Module Wire Correspondence

| Conceptual Layer | Formal Lean 4 Owner Module |
| :--- | :--- |
| **Octonionic Lightcone $ab - \mathbf{u}\cdot\mathbf{v} = 0$** | `lean/InfoGeometry/Canonical/SplitOctonionChiralPeirceSoldering.lean` |
| **De Witt $4$-Plane Metric $x_0 x_4 - \sum x_k x_{k+4}$** | `lean/InfoGeometry/Lie/SplitOctonionCircularWittForm.lean` |
| **$\sigma_\pm$ Soldering & Pauli Intertwining** | `lean/InfoGeometry/Canonical/CantorBernoulliPauliMatrixIntertwiner.lean` |
| **Souriau-Vinberg Thermodynamics** | `lean/InfoGeometry/Physics/SouriauAffineCasimirGradientBridge.lean` |
| **Tomita Modular Monodromy $\Delta = e^{-\mathcal{K}}$** | `lean/InfoGeometry/OperatorAlgebra/CantorBernoulliGNSModularTomitaBridge.lean` |
| **Projective Reciprocal Flow $(0,1,\infty)$** | `lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveReciprocalFlow.lean` |
| **Hestenes-Krein Rotors & $\eta$-Unitarity** | `lean/InfoGeometry/Physics/HestenesKreinOperatorCalculus.lean` |

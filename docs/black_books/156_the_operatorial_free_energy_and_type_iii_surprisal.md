# Chapter 156: The Operatorial Free Energy and Type III Surprisal

> **"The cost function is not a variance; it is the Operatorial Free Energy. The Surprisal is the Relative Modular Hamiltonian."**

This chapter synthesizes the Operatorial Free Energy formulation within Type III von Neumann algebras, unifying the Surprisal (Kullback-Leibler Divergence) with the trace-free thermodynamic Free Energy.

---

### I. Algebraic Construction via Operatorial Free Energy

Let $M$ be a general Type III von Neumann algebra acting in its standard form on a Hilbert space $H$, equipped with a cyclic/separating structure and natural positive cone $P^\natural$. Let $\phi$ and $\psi$ be normal positive linear functionals on $M$, representing the target and reference states, respectively.

#### 1. Support Projectors & Regularization:
Let $p = s(\psi) \in M$ be the support projection of the reference state $\psi$. Because $\psi$ is not faithful globally, we define the regularized state $\phi_{\text{reg}}$ by compressing $\phi$ to the support of $\psi$:
$$ \phi_{\text{reg}}(x) = \phi(pxp), \quad \forall x \in M $$
The singular defect is captured by the complementary projector $p^\perp = I - p$, isolating the singular part $\phi_{\text{sing}}(x) = \phi(p^\perp x p^\perp)$.

#### 2. The Regularized Relative Modular Operator:
Let $\xi_{\phi_{\text{reg}}} \in P^\natural$ be the canonical vector representative of the regularized state. Because $\psi$ is faithful on the reduced algebra $M_p = pMp$, we define Araki’s relative modular operator $\Delta_{\psi,\phi_{\text{reg}}}$ strictly on the closed subspace $H_p = pH$. This operator is positive and self-adjoint, encapsulating the non-commutative spatial derivative.

#### 3. The Surprisal Operator (Relative Modular Hamiltonian):
Using the spectral theorem on $H_p$, we define the Operatorial Surprisal (the exact non-commutative analogue of the log-likelihood ratio $-\log(d\psi/d\phi_{\text{reg}})$):
$$ K_{\text{surprisal}} = -\log(\Delta_{\psi,\phi_{\text{reg}}}) $$
$K_{\text{surprisal}}$ serves as the "Information Energy" observable on the regularized subspace.

#### 4. Operatorial Partition Functional & Free Energy ($D_{KL}$):
Since there is no trace, the classical partition function is replaced by the Araki-Connes generating functional. We define the Relative Partition Functional $Z(s)$:
$$ Z(s) = \langle \xi_{\phi_{\text{reg}}}, \Delta_{\psi,\phi_{\text{reg}}}^s \xi_{\phi_{\text{reg}}} \rangle $$
The relative information cost is defined as the expected thermodynamic Free Energy (the Araki Relative Entropy / Quantum KL Divergence):
$$ D_{KL}(\phi_{\text{reg}} \| \psi) = \langle \xi_{\phi_{\text{reg}}}, K_{\text{surprisal}} \xi_{\phi_{\text{reg}}} \rangle = -\left. \frac{d}{ds} Z(s) \right|_{s=0} $$
*(Note: The total divergence is $D_{KL}(\phi_{\text{reg}} \| \psi) + \infty \cdot \phi_{\text{sing}}(I)$, indicating that any mass outside the reference support incurs an infinite Free Energy cost).*

---

### II. Proof of the Five Properties (Type III Free Energy Setting)

#### 1. Well-defined:
In a Type III algebra, Araki's relative modular operator $\Delta_{\psi,\phi_{\text{reg}}}$ is densely defined, positive, and self-adjoint on the restricted support $pH$. By the spectral theorem, its logarithm $K_{\text{surprisal}}$ is mathematically rigorous. Araki's fundamental theorem guarantees that the expectation $\langle \xi_{\phi_{\text{reg}}}, -\log \Delta_{\psi,\phi_{\text{reg}}} \xi_{\phi_{\text{reg}}} \rangle$ is bounded below. It evaluates to a well-defined scalar or $+\infty$, bypassing undefined mathematical expressions while accurately reflecting infinite distinguishability when states are mutually singular.

#### 2. Independent of arbitrary scale choices (via Partition Gauge Shifts):
Let $\phi \to c\phi$ and $\psi \to d\psi$ for $c,d > 0$. The Araki relative modular operator scales as:
$$ \Delta_{d\psi, c\phi_{\text{reg}}} = \frac{c}{d} \Delta_{\psi,\phi_{\text{reg}}} $$
Substituting this into the Surprisal Operator yields an exact scalar shift:
$$ K_{\text{scaled}} = -\log\left(\frac{c}{d} \Delta_{\psi,\phi_{\text{reg}}}\right) = K_{\text{surprisal}} + \log\left(\frac{d}{c}\right) I_p $$
Evaluating the Free Energy cost yields:
$$ D_{KL}(c\phi_{\text{reg}} \| d\psi) = c D_{KL}(\phi_{\text{reg}} \| \psi) + c \log\left(\frac{d}{c}\right) \langle \xi_{\phi_{\text{reg}}}, \xi_{\phi_{\text{reg}}} \rangle $$
This proves the formalism tracks arbitrary scalings exclusively through the exact thermodynamic partition shift $\log(c/d)$, maintaining strict structural scale-invariance.

#### 3. Insensitive to the null/singular sector except through explicitly controlled defect terms:
The definition isolates the absolute continuous sector via $\phi_{\text{reg}}$. The singular defect $\phi_{\text{sing}}$ exists entirely in the orthogonal corner $p^\perp M p^\perp$. It does not enter the relative modular operator or the state vector $\xi_{\phi_{\text{reg}}}$. It is explicitly factored out by the support projection $p$, meaning the measurement succeeds smoothly on $\phi_{\text{reg}}$ and detects an absolute topological obstruction strictly as a tracked infinite Free Energy cost on $\phi_{\text{sing}}$.

#### 4. Compatible with the commutative formula:
Let $M$ be commutative, $M \cong L^\infty(X,\nu)$, where $\phi,\psi$ correspond to measures $\mu,\nu$. The vector representative is $\xi_{\phi_{\text{reg}}} = \sqrt{\frac{d\mu_{\text{reg}}}{d\nu}}$. The relative modular operator acts by multiplication by $\frac{d\nu}{d\mu_{\text{reg}}}$.
The Surprisal Operator reduces to the classical function:
$$ K_{\text{surprisal}} = -\log\left(\frac{d\nu}{d\mu_{\text{reg}}}\right) = \log\left(\frac{d\mu_{\text{reg}}}{d\nu}\right) $$
The expected Free Energy evaluates perfectly to:
$$ D_{KL} = \int_X \log\left(\frac{d\mu_{\text{reg}}}{d\nu}\right) \left(\sqrt{\frac{d\mu_{\text{reg}}}{d\nu}}\right)^2 d\nu = \int_X \log\left(\frac{d\mu_{\text{reg}}}{d\nu}\right) d\mu_{\text{reg}} $$
This is exactly the classical Kullback-Leibler divergence (the macroscopic thermodynamic Free Energy), fulfilling the commutative boundary condition.

#### 5. Functorial under the equivalence of measurements:
The Operatorial Partition Functional $Z(s)$ and the resulting Free Energy $D_{KL}$ are intrinsic, trace-free algebraic invariants of the pair of states $(\phi,\psi)$ on $M$. Under any spatial isomorphism between Type III algebras, the Connes spatial derivative $(D\psi:D\phi)_t$ is preserved. Thus, the free energy evaluates exclusively the invariant information-geometric equivalence class of the measurement algebra, ensuring strict functoriality.

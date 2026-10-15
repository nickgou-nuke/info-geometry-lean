# Exploratory hypothesis ledger: nuclear chirality and emergent geometry
### Proposed connections from $\mathrm{Cl}(5,5)$ Krein models to nuclear observables

> **Epistemic status.** This document records a research hypothesis chain, not an
> established physical theory. Its proposed identifications among QRPA, split
> octonions, Einstein–Cartan torsion, Nieh–Yan/WZW terms, mass gaps, and measured
> gamma-ray observables have not been derived from a shared physical model here.
> Lean verification of a finite algebraic identity does not establish those
> physical bridges. In particular, this document is not evidence that Goldstone
> modes are impossible, that a nuclear signal measures a Nieh–Yan invariant, or
> that the proposed coefficients agree with experiment. The sections below
> preserve the intended causal chain as conjectures and candidate calculations;
> each arrow requires independent mathematical and physical justification.

**Status of Sections I–VI.** Their nuclear-model equations, parameter values,
and proposed identifications are input hypotheses or phenomenological claims
in this ledger. They are not certified by the finite Lean identities merely
because they are written as equations. Validation requires a specified
Hamiltonian/QRPA model, sources for numerical values, and proofs of the stated
observable and stability consequences.

### I. The Epistemic Foundation: Twin Waves over Heuristics
**Candidate modeling premise:** distinguish any proposed semiclassical
left/right coordinates $|R\rangle,|L\rangle$ from observables. Whether those
states exist or are stationary is a question for a specified Hamiltonian and
measurement model; this document does not establish their nonexistence. The
chiral parity states and forward/backward orbit labels are proposed model
variables, not derived observables in a single shared physical theory here.

### II. Algebraic Geometry: The Phase Space
This section proposes a **$\mathrm{Cl}(5,5)$-Krein-space** carrier for a
nuclear quasiparticle-phonon model; it does not establish that this is the
physical state space. The normalization $X^2-Y^2=1$ is a candidate QRPA
constraint whose precise source and hypotheses must be supplied.
Complementary Peirce idempotents do give algebraic summands, but their
identification with handedness is an additional representation choice. The
displayed current commutator and its proposed relation to non-associativity
and a scalar triple product are not proved by those projector facts; a
carrier-compatible product and map are required.

### III. Microscopic Many-Body Dynamics: The Cartan 5-Grading
The following is a proposed assignment of QPNM labels to a five-grading of
$\mathfrak{so}(5,5)$, not an established identification of the physical QPNM
with that Lie algebra. A proof would need to define the graded subspaces and
show the bracket inclusions $[\mathfrak g_i,\mathfrak g_j]\subseteq
\mathfrak g_{i+j}$ (with zero pieces outside the range):
*   $\mathfrak{g}_{-2}$: Pair annihilation (Cooper pair destruction).
*   $\mathfrak{g}_{-1}$: Backward phonon amplitudes ($Y$).
*   $\mathfrak{g}_0$: The Cartan mean field, the collective rotor, and the axial charge $\tau_3$.
*   $\mathfrak{g}_{+1}$: Forward phonon amplitudes ($X$).
*   $\mathfrak{g}_{+2}$: Pair creation (Cooper pair generation).

The proposed $SU(2)$ connection, its placement in grade zero, and its
interpretation as a chiral chemical potential require a specified group
representation and coupling to a nuclear Hamiltonian. The formula alone does
not prove pair breaking or current polarization.
The original candidate notation is retained as
$A_0=\vec\omega_{\rm coll}\cdot\hat{\vec j}$, with a proposed coupling to
$\mu_5$ and the forward/backward amplitudes. To make this a connection, the
generators, representation, and covariant derivative must be specified (for
example, $D_0=\partial_0-A_0$ when $A_0$ is represented in the chosen Lie
algebra).

### IV. Emergent Spacetime: Einstein-Cartan Gravity and the Nieh-Yan Anomaly
An effective curved-spacetime description of the rotating droplet is a model
proposal; a metric and matter coupling have not been derived here.
1. **Spin torsion (ansatz):** A relation such as $T^{0ij} \propto
   \epsilon^{ijk}(\vec{j}_\pi \times \vec{j}_\nu)_k$ would require a defined
   tetrad, connection, and matter spin current. These are not supplied by the
   finite vector algebra alone.
2. **Nieh-Yan (unproved identification):** The scalar triple product is not
   by itself a Nieh-Yan invariant. Its proposed use as a local energy density
   is an ansatz:
   $$ \mathcal{E}_{\text{anom}} = \vec{\omega}_{\text{coll}} \cdot (\vec{j}_\pi \times \vec{j}_\nu) $$
3. **Axial-bias ansatz:** An effective field $\vec B_5$ and potential
   $V_{\mathrm{eff}}(\theta)$ must be derived from a specified action. The
   displayed polynomial and $\epsilon_{\mathrm{axial}}$ are candidate
   parameters, not outputs of a proved anomaly calculation.
   The proposed relations are retained explicitly as
   $\vec B_5=\kappa(\vec J_\pi^{(0)}-\vec J_\nu^{(0)})$ and
   $\epsilon_{\mathrm{axial}}=\vec\omega_{\mathrm{coll}}\cdot\vec B_5$;
   neither follows from the scalar triple product without the model map.

### V. Macroscopic Dynamics: QRPA and Instanton Tunneling
The next equations are candidate phenomenological relations. Their validity
depends on the underlying QRPA/action model and is not certified here.
1. **Candidate dispersion relation:**
   $$ \hbar\Omega = \sqrt{(\hbar\Omega_0)^2 + \epsilon_{\text{axial}}^2} $$
   This is strictly positive only when $\hbar\Omega_0$ and
   $\epsilon_{\text{axial}}$ are not both zero. It does not, without a
   derivation from the full QRPA system, rule out Goldstone softening.
   The source proposal also sets
   $\hbar\Omega_0=\sqrt{\mathcal A^2-\mathcal B^2}$; this is a candidate
   definition requiring the QRPA matrix and stability hypotheses.
2. **Amplitude ansatz:** $X-Y=\epsilon_{\mathrm{axial}}/(\hbar\Omega)$ is a
   proposed relation requiring normalization and QRPA equations.
3. **Instanton ansatz:** The displayed Euclidean action and its consequences
   require a specified potential, boundary conditions, and path-integral
   derivation; no such derivation is included in this ledger.
   The proposed action is retained as
   $$S_E=S_{\rm sym}+\frac{\pi\epsilon_{\rm axial}}{\hbar\omega_0}
   -i\Phi_{\rm top}.$$
   This conventional complex-phase notation needs an explicit realification
   before it can be replaced by a real blade/matrix structure; such a
   realification is not implied by the scalar triple product. The proposed
   exponential suppression of tunneling and odd-even spin staggering from
   $\Phi_{\rm top}$ remain unproved consequences.

### VI. Phenomenological Observables: Resolving the Chiral Conundrum
The following ratio and inversion are proposed phenomenological relations,
not validated measurement equations in this repository:
$$ \mathcal{R}_{M1} = \frac{B(M1)_{\text{inter}}}{B(M1)_{\text{intra}}} = \left( \frac{\hbar\Omega - \epsilon_{\text{axial}}}{\hbar\Omega + \epsilon_{\text{axial}}} \right)^2 < 1.0 $$
If the proposed model and ratio were established, one could consider the
formal inversion:
$$ \epsilon_{\text{axial}} = \hbar\Omega \left( \frac{1 - \sqrt{\mathcal{R}_{M1}}}{1 + \sqrt{\mathcal{R}_{M1}}} \right) $$
*   The quoted $^{134}\mathrm{Pr}$ and $^{135}\mathrm{Nd}$ parameter values
    are unverified in this document: source data, uncertainties, fit
    procedure, and a derivation connecting them to these parameters are
    required before interpreting them as measurements of any anomaly.

### VII. Formal verification: what the Lean results establish
The repository contains kernel-checked finite algebraic results about selected
two-sector matrices, projectors, commutators, and spectral expressions. For
example, the rest-frame Dirac module proves a characteristic-polynomial identity
and a finite-dimensional Heisenberg double-commutator identity. These results do
not establish a QRPA model, a torsional mass gap, a theorem excluding Goldstone
softening in chiral nuclei, or any identification with detector data. Those
physical conclusions remain conjectural until their model assumptions and
bridges are stated and proved. See the relevant owner files and their explicit
scope comments before interpreting an algebraic theorem physically.

---

### Proposed synthesis (conjectural)
The proposed chain is: a finite chiral algebraic model may organize forward and
backward sectors; a specified many-body model might relate those sectors to
collective nuclear dynamics; and a separately derived observation map might
connect such dynamics to measured transition strengths. The stronger claims that
this chain yields Einstein–Cartan spacetime, a topological anomaly, or a direct
observable signature are open hypotheses, not consequences of the formalized
matrix identities in this repository.

### VIII. The Machian Revelation and the Origin of Mass

This section records a proposed interpretation of a finite scalar triple
product and two-sector models. It is not a definition or derivation of
physical mass.

1. **Scalar model readout:** The scalar
   $\epsilon_{\mathrm{trial}}=\vec{\omega}_{\mathrm{coll}}\cdot
   (\vec{j}_\pi\times\vec{j}_\nu)$ vanishes when the inputs satisfy
   degeneracy conditions such as a zero or collinear pair of currents. This
   follows from the scalar triple product, not from a spectral calculation.
   Calling it a mass gap requires a specified Hamiltonian and a theorem
   relating this scalar to the spectrum.
   Thus the intended Machian proposal remains the conditional equation
   $\epsilon_{\mathrm{trial}}=\vec{\omega}_{\mathrm{coll}}\cdot
   (\vec{j}_\pi\times\vec{j}_\nu)$: the scalar vanishes for zero or
   proportional currents even if $\vec{\omega}_{\mathrm{coll}}\ne0$.
   Whether it controls a spectral gap is a separate physical question.
2. **Two-sector coupling and Dirac kinematics:** An off-diagonal mass term in the rest-frame Dirac Hamiltonian couples Weyl components and gives the algebraic energy levels $\pm mc^2$. The separate Dirac Zitterbewegung statement concerns oscillations of the velocity operator arising from interference between positive- and negative-energy sectors. A generic two-sheet or BdG commutator identity does not establish that dynamics, nor does it prove mass generation or forbid a Goldstone mode.
   The frequently quoted free-Dirac Zitterbewegung angular frequency
   $2mc^2/\hbar$ belongs to interference between positive- and negative-energy
   sectors; it is not a consequence of two-sheet projectors alone.
3. **Torsion/topology hypothesis:** Interpreting the scalar as a torsion
   density, a Nieh–Yan invariant, or a topologically protected quantity
   requires geometric fields, a differential form, an integration cycle, and
   a stability argument. None follows from the scalar formula alone.
   The original “twisted knot” picture, in which relative rotation has an
   energy cost for untwisting, is retained as a metaphor and proposed
   mechanism, not as a topological protection theorem.

**Open physical question:** Can a specified nuclear Hamiltonian produce a
spectral gap controlled by a relative-rotation observable, and is that gap
stable under the model's allowed perturbations? The present algebraic
identities do not answer this question and do not replace the standard
relativistic definition of mass.

### IX. The Associator and the Cartan 3-Form

The scalar triple product, a Cartan 3-form, and an algebra associator have
different carriers. Existing Lean results prove selected identities for each;
they do not identify them as a physical mass-generation mechanism.

**1. The scalar triple product.** For three vectors in `Fin 3 → ℝ`, the
Levi-Civita contraction equals the coordinate scalar triple product. This is
the scope of `tensor_contraction`, `scalar_triple_product`, and
`levi_civita_is_scalar_triple_product` in
`InfoGeometry.QuantumGravity.AnomalyVolumeContraction`. It is an alternating,
scalar-valued trilinear expression. A relation to a Zorn associator would need
an explicit map from the Zorn carrier to scalars and a theorem for that map.

**2. The Zorn associator.** In `InfoGeometry.Algebra.ZornVectorMatrix`,
`associator X Y Z := (X * Y) * Z - X * (Y * Z)` is Zorn-vector-matrix-valued.
The owner proves that its trace is zero, exhibits a nonzero instance, and
relates the commutator Jacobiator to an alternating sum of associators. Those
facts do not make the associator itself a scalar triple product or a
spacetime differential form.

**3. Cartan forms, torsion, and anomalies.** A Cartan 3-form requires Lie
algebraic data; torsion and anomaly functionals require additional geometric
fields, differentials, and (where relevant) integration data. Three vectors
in `Fin 3 → ℝ` do not supply those structures by themselves. The proposed
arrows from a nuclear scalar triple product to Cartan/torsion data, a
Nieh–Yan or WZW term, and an observed mass gap remain conjectures. In
particular, no equality between a nonzero associator and an axial mass gap is
established here.

The intended correspondence is preserved as a **candidate dictionary**, not
an equality: scalar triple product
$\vec\omega\cdot(\vec j_\pi\times\vec j_\nu)$; algebra associator
$[A,B,C]=(AB)C-A(BC)$; Cartan 3-form built from a Lie bracket and invariant
pairing; torsion/Nieh--Yan differential forms; and a spectral mass-gap
parameter $\epsilon_{\mathrm{axial}}$. These objects have different carriers
and codomains. Any arrow between them needs an explicit map and theorem.

The intended causal picture is retained as a research program, not an
equation of equivalence:

```text
three-vector scalar triple product
    --[model-specific map and proof required]-->
Cartan/torsion or anomaly functional
    --[dynamics and observation map required]-->
measured energy gap
```

Each arrow needs an explicit carrier map, hypotheses, and derivation. The
finite contraction theorem proves only the scalar identity stated above.

### X. Cohomology, WZW Term, and the Maurer-Cartan Form

The proposed relation to cohomology and Wess-Zumino-Witten (WZW) terms is a
possible research direction, not a consequence of the finite-dimensional
triple-product theorem.

**1. Maurer-Cartan data.** On a Lie group, the Maurer-Cartan form is a
Lie-algebra-valued differential 1-form satisfying its Maurer-Cartan equation.
A connection along a nuclear collective coordinate may be modeled using such
data only after the group action, representation, and connection are defined.
The scalar $A_0=\vec{\omega}_{\mathrm{coll}}\cdot\hat{\vec{j}}$ alone does not
specify a global Lie-group-valued 1-form.

**2. Cartan 3-form versus coordinate triple product.** A Cartan 3-form is
constructed from an invariant bilinear form and the Lie bracket (equivalently,
from specified Maurer-Cartan data). A coordinate scalar triple product is an
alternating trilinear form on a chosen three-dimensional vector space. They
may be compared after specifying an identification of carriers and
normalizations, but the nuclear vectors do not become a cohomology class by
notation alone.

**3. WZW/anomaly and dynamics.** A WZW functional requires a field, target,
closed form, and integration domain with the appropriate extension data.
An anomaly calculation additionally requires a quantum model and its
regularization. The equation
$\mathcal{S}_{\mathrm{top}}=\lambda\int dt\,
\vec{\omega}_{\mathrm{coll}}\cdot(\vec{j}_\pi\times\vec{j}_\nu)$ is therefore
an ansatz here, not a derived WZW action or a proof of an axial energy bias.

**4. Cohomology and protection.** A cohomology class can protect an integral
only when the relevant closed form, cycle, and homotopy conditions are
specified. No theorem in this document shows that the proposed nuclear scalar
is such an integral or that a mass gap is topologically protected.

For the intended comparison, a Lie-group field $g$ supplies the
Maurer--Cartan form $\phi=g^{-1}dg$; in a fixed convention a pure-gauge
connection is $A=g^{-1}dg$. A Cartan/WZW candidate involves an invariant
expression such as $\operatorname{Tr}(\phi\wedge[\phi\wedge\phi])$ and an
integration/extension domain. A coordinate expression
$\epsilon_{ijk}\omega^i j_\pi^j j_\nu^k$ can be compared with its pullback
only after the inputs are differential 1-forms on a common domain and the
normalization is fixed. The familiar $H^3(G;\mathbb R)\cong\mathbb R$ also
requires the relevant compact connected simple Lie-group hypotheses; it does
not by itself identify a nuclear observable or protect an energy gap.

The candidate chain is retained with its missing structure made explicit:

```text
group/connection data → Cartan form and cohomology class
    → a specified WZW/anomaly functional → model dynamics → spectral gap
```

Every arrow requires its own definition and derivation. The Lean triple-product
identity cited in Section IX verifies none of these physical arrows.

### XI. Supergeometry, BRST Quantization, and the DeWitt Split

The proposed connection to supergeometry and BRST quantization must keep
parity, nilpotency, and physical interpretation distinct. A square-zero
operator is not thereby a Grassmann scalar, a BRST differential, or an
anomaly. The phrase “polarized Peirce projected DeWitt split soul ghost” is
retained only as a label for the conjectural model, not as a defined object.

**1. The DeWitt Split: Body and Soul**
In a specified finite Grassmann algebra, an element has a scalar residue and
a nilpotent-ideal component. More general supernumber conventions require
their own algebraic definitions.
*   **Body:** The scalar residue under the chosen quotient by the nilpotent
    ideal.
*   **Soul:** The nilpotent ideal component in that specified algebra. Its
    grading and graded-commutative sign law are part of the structure.

The motivating notation $z=x_B+\theta_S$ (commuting body plus nilpotent soul)
is retained as a model of a specified finite Grassmann algebra. Off-diagonal
matrix blocks are not thereby Grassmann scalars.

For an algebra with complementary Peirce idempotents, diagonal and
off-diagonal components can be studied algebraically. This is not by itself
a DeWitt split of a nuclear Hamiltonian:
*   The diagonal Peirce spaces $\mathcal{Z}_{11}$ and $\mathcal{Z}_{22}$ are
    algebraic summands. Identifying them with a classical rotor, mean-field
    energy, or collective rotation requires an explicit physical
    representation; it is not part of the Peirce decomposition theorem.
*   In a specified matrix model, off-diagonal ladder operators such as
    $\sigma_+$ and $\sigma_-$ may square to zero. That operator identity does
    not identify them with Grassmann scalars or establish a supermanifold; a
    parity grading, scalar algebra, and Koszul rule are also required.

**2. The Polarized Soul and the Chiral Volume**
The proposed polarization of an odd sector by proton/neutron current data is
a model hypothesis. The proposed formula
$\mathcal V_{\mathrm{chiral}}\propto[\sigma_+,\sigma_-]$ is retained as an
algebraic comparison to test. In the elementary two-state matrix realization
the commutator is a diagonal grading operator (up to normalization), not a
nilpotent chiral volume or a Cartan 3-form. A map to differential-form data
would have to be separately defined and proved.

**3. The Topological "Ghost" Oscillation**
In gauge theory (including BRST quantization), Faddeev–Popov ghosts are
Grassmann-valued fields introduced by a gauge-fixing construction. This
document specifies neither such a construction nor fermionic fields to
integrate out. The collective rotation is therefore not identified here with
a gauge field, and no Wess–Zumino–Witten anomaly is derived from the proposed
chiral scalar.

Calling a term a BRST ghost has a precise meaning: one must specify the
graded state space, BRST differential, its nilpotency, and the gauge-fixing
construction. Those data do not follow merely from two ladder operators.
The proposed ghost-driven tunneling remains a hypothesis until a Hamiltonian
and evolution law establish it.
The motivating dynamics—$\sigma_+$ and $\sigma_-$ converting a forward
amplitude $X$ into a backward amplitude $Y$, and tunneling between candidate
$|R\rangle$ and $|L\rangle$ sectors—is retained as a model specification to
test, not as a consequence of nilpotency alone.

**The Final Supermanifold Picture:**
1.  **Peirce projection (algebraic):** Complementary idempotents split a
    module into summands; interpreting them as physical chiral states needs a
    representation and observable map.
2.  **Body/soul (additional structure):** This requires a supercommutative
    algebra, not merely diagonal/off-diagonal matrix blocks.
3.  **Polarization (model hypothesis):** A particle-hole mismatch may enter
    a specified Hamiltonian, but is not implied by projector identities.
4.  **Ghost oscillation and mass gap (open):** A BRST construction, dynamics,
    and spectral argument are required. No theorem here derives a permanent
    mass gap from a non-associative chiral volume.

This section therefore records candidate links among Peirce splitting,
superalgebra, BRST ideas, and nuclear dynamics. The algebraic identities do
not establish that these physical mechanisms have been derived.

### XII. Candidate comparison: Andreev reflection and Majorana modes

This section records a proposed comparison with Andreev reflection. The
analogy is not a universality theorem: a BdG model, its particle-hole
structure, boundary conditions, and spectral/topological hypotheses must be
specified independently.

**1. The Distributed Nambu-Gorkov Generator**
For a specified one-dimensional channel model, one may group electron and
hole amplitudes into the Nambu spinor $\Psi(x) = \binom{u(x)}{v(x)}$ and
choose a BdG Hamiltonian such as:
$$ \mathcal{H}_{\text{BdG}} = -i \hbar v_F \sigma_z \partial_x + \Delta(x) \sigma_x $$
In this chosen representation, $\sigma_z$ and $\sigma_x$ act on the two
components. Calling them “Body” and “Soul” is an analogy, not an identification
of BdG dynamics with a Peirce decomposition or a BRST ghost.

**2. The Path-Ordered $S$-Matrix and its metric**
A transfer or scattering matrix must be derived from the chosen BdG equation,
boundary conditions, and conserved current. It is not automatically an
$SU(1,1)$ operator or the same Krein representation used in the nuclear
model. In particular, the displayed real rotation
$S(\alpha)=\begin{pmatrix}\cos\alpha&-\sin\alpha\\
\sin\alpha&\cos\alpha\end{pmatrix}$ preserves the ordinary Euclidean
inner product, but does not preserve $\tau_3=\operatorname{diag}(1,-1)$ for
general $\alpha$. The claimed pseudo-unitarity does not follow from that
matrix.

**3. A model-dependent Andreev mixing angle**
For a chosen two-channel real rotation model, let
$J=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$, so $J^2=-I_2$ as a matrix
identity. Then
$$ \mathcal{S}(\alpha)=\exp(\alpha J)=\cos\alpha\,I_2+\sin\alpha\,J
 = \begin{pmatrix} \cos \alpha & -\sin \alpha \\ \sin \alpha & \cos \alpha \end{pmatrix}. $$
This is a real matrix-root realization of a plane rotation, not an
uninterpreted scalar imaginary unit. The proposed integrated parameter
$\alpha=\int_0^L\Delta(x)/(\hbar v_F)\,dx$ remains conditional on deriving
the transfer equation and fixing its conventions.
In a specified constant-velocity, zero-energy model, an integral of the
pairing amplitude can determine a mixing parameter after deriving the
equation and transfer matrix. That parameter is not thereby a Nieh–Yan
invariant, Cartan volume, or nuclear chiral volume; an identification needs
an additional proved model map.

**4. Rotation-model outputs and the separate Majorana question**
*   At $\alpha=\pi/2$, the real rotation is $J$ and sends
    $\binom{1}{0}$ to $\binom{0}{1}$, up to the chosen orientation convention.
*   At $\alpha = \pi/4$, the state becomes:
$$ \Psi_{\text{edge}} = \mathcal{S}(\pi/4) \begin{pmatrix} 1 \\ 0 \end{pmatrix} = \frac{1}{\sqrt{2}} \begin{pmatrix} 1 \\ 1 \end{pmatrix} $$
This is an equal-amplitude vector in this two-component model. That
superposition alone does not establish a Majorana zero mode, a topological
invariant, or a protected edge state; those require a particle-hole
operator, a spectral zero-mode result, and appropriate boundary/topological
hypotheses.

**Proposed comparison dictionary (not a proved identification)**

| Concept | Rotating Nuclear Chirality | Distributed Andreev Reflection |
| :--- | :--- | :--- |
| **The Twin Waves** | $|k\rangle$ (particle) and $|\bar{k}\rangle$ (hole) | $u(x)$ (electron) and $v(x)$ (hole) |
| **The Metric** | $\mathrm{Cl}(5,5)$ Krein Space ($X^2 - Y^2$) | Determined by the BdG evolution and conserved current; not inferred as $SU(1,1)$ here |
| **The Body (Classical)** | Rotor Kinematics ($\Omega_0$) | Kinetic Edge Propagation ($\sigma_z$) |
| **The Soul (Ghost)** | Off-diagonal Peirce anomaly ($\sigma_x$) | Pairing gap $\Delta(x)$ mixing $e$ and $h$ ($\sigma_y$) |
| **Candidate scalar** | Proposed nuclear triple-product readout | Model-dependent integrated pairing parameter; no Nieh–Yan identification proved |
| **Symmetry Restoration** | Collinear currents ($T = 0$) | Decoupled edge modes ($\Delta \to 0$) |
| **Candidate spectral feature** | Proposed axial gap | A Majorana zero mode requires a separate BdG zero-mode and topology argument |

The matrix exponential solves a specified evolution equation only after its
generator and boundary data are fixed. The displayed rotation is not in
general an exponential of a square-zero operator. No shared topological
mechanism between nuclear chirality and superconducting devices is proved
here; that comparison remains a research hypothesis.

### XIII. Twistor incidence, Weyl spinors, and the light cone

Twistor incidence, Pauli-matrix nullity, and exterior-algebra nilpotency are
three distinct constructions. The repository contains finite algebraic
readouts for the first two; it does not prove that a nuclear anomaly or a
Cartan/torsion volume generates causal spacetime.

**1. The massless shell.** For the `(+---)` four-vector carrier, the Pauli
soldering map satisfies `det(pauliSoldering k) = minkowskiNorm k`. Hence the
four-vector is Minkowski-null exactly when the associated 2-by-2 matrix has
zero determinant (`null_iff_det_pauliSoldering_zero` in
`InfoGeometry.Physics.PenroseEikonalTwistorRay`). The independent Dirac owner
proves the massive factorization and its mass-shell readout in
`InfoGeometry.Physics.FourVectorDiracReadout`.

**2. Weyl dyads and exterior products.** The map from a two-component Weyl
spinor to the displayed real four-vector proves that its image is null
(`spinor_generates_null_vector`); the associated dyad determinant is also
proved zero. These are coordinate/matrix identities. By contrast,
`ExteriorAlgebra.ι_sq_zero` says that every exterior generator squares to
zero, irrespective of any Minkowski metric. That exterior identity therefore
does not imply that a four-momentum is null. The two results must not be
identified without a separately defined carrier map and a proof.

For a decomposable exterior bivector $P=u\wedge v$, the identity
$P\wedge P=0$ is the Plücker/Klein relation. In four dimensions its zero
locus characterizes decomposability (`exteriorKleinForm_eq_zero_iff_decomposable`
in `InfoGeometry.Projective.ExteriorPowerPluckerBridge`); the arbitrary-module
square-zero calculation is `decomposable_bivector_wedge_square_zero` in
`InfoGeometry.GrassmannianTower`. Neither theorem states the Minkowski
condition $p_\mu p^\mu=0$ or $p_\mu p^\mu=m^2$. Those belong to the separate
quadratic-form carrier: the Pauli soldering determinant gives the massless
null condition, and the Dirac slash factorization gives the massive shell in
`InfoGeometry.Physics.FourVectorDiracReadout`. Likewise, a Clifford vector
with square zero is null with respect to its specified Clifford quadratic
form; that is distinct from square-zero of its image as an exterior
generator. No single “on-shell iff exterior blade” theorem is asserted.

**3. Twistor incidence.** Under the explicit convention in
`PenroseEikonalTwistorRay`, the incidence construction has zero for its chosen
twistor norm (`incident_twistor_is_null`). The incidence equation itself does
not assert that a chiral anomaly vanishes, that helicity is zero, or that a
massive state is produced when incidence fails. The separate
`Nuclear.TwistorIncidenceBridge.incidence_twist_expansion` theorem is an
expansion formula and does not prove the proposed nuclear interpretation.
The conventional twistor-coordinate incidence equation is
$\omega^A=i x^{AA'}\pi_{A'}$. Its complex structure belongs to the twistor
carrier. Replacing it with a real bivector or matrix complex structure needs
an explicit realification and representation; it does not follow from
$\iota(v)^2=0$ in an exterior algebra.

**4. Remaining geometric hypotheses.** A para-hyper-Kähler structure requires
specified endomorphisms, metric, and compatibility/integrability laws; a
supermanifold additionally requires a graded structure sheaf. Neither follows
from a split-signature vector space or a DeWitt-style metaphor alone.
Likewise, no proved theorem here identifies the kernel of a chiral-volume
operator with the light cone or derives an observed mass gap from twistor
incidence. Those proposed arrows remain open research questions.

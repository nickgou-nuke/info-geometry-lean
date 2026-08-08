# AST-style theorem/proposition extraction from downloaded PDFs

Total extracted items: `20`

## 10.1038_s42254-022-00516-5

### Result: `result`
- source file: `10.1038_s42254-022-00516-5.pdf.txt`
- lines: 545-642

```text
ant eigenvalue braids have three strands that together form a single point gap (Fig. 3h). It follows
that the parallel transport of a state must also cover three cycles around the order-3 EP to restore itself.
The Berry phase accumulated in the process is 2𝜋, as shown in the top panel of Fig. 3g. As in an order2 EP, this fractional winding behavior roots in the denominator of the eigenvector, and thus can be
determined from the critical exponents of phase rigidity. The blue and magenta lines in Fig. 3f are the
double-log plot of the phase rigidity and the detuning parameter near an order-2 and an order-3 EP,
respectively. Their slopes, namely the critical exponents, are 1/2 and 2/3 respectively, which reveals a
fundamental difference between them. It has been proved that the exponent is generally (𝑁 − 1)/𝑁
for an order-𝑁 EP95,96.
The rich topological characteristics of the order-3 EP are revealed by interrogating it in a
different subspace. For example, in Fig. 3d we plot the eigenvalue Riemann surfaces in the Λ-plane
with Θ = 0. At first sight, it appears that the middle state decouples from the other two, which is not
true because the phase rigidity of the middle state also vanishes at Λ = 0, as seen in the colormap in
Fig. 3d. Figure 3i shows the eigenvalue braids around the order-3 EP, in which the middle eigenvalue
(black) actually is linked with the other two, forming a Hopf link. This is a typical feature for an order2 EP, and it implies that the upper/bottom (middle) state can recover after only two (one) cycles around
the order-3 EP, which is clearly different from the situation in Fig. 3h. The Berry phases accumulated
in this process are 2𝜋 (𝜋) for the upper/bottom (middle) state, as shown in the bottom panel of Fig. 3g.
The critical exponent of phase rigidity is unity in the Λ-plane (the black line in Fig. 3f), which follows
a different (𝑁 − 1)/2 law for an order-𝑁 EP50,89,96. This dramatic difference between the Λ and Θ
planes highlights the unique hybrid nature of higher-order EPs, which is absent for order-2 EPs.
12
Because the evolution of non-Hermitian states is smoothly connected by spectral topology,
multi-state non-Hermitian systems are an excellent platform for realizing non-Abelian permutations
of states101–103. For example, the parallel transport around the blue (red) EA in Fig. 3a swaps states 2
and 3 (states 1 and 2), which is the consequence of a three-state unitary transformation captured by an
SO(3) group. These two operations can generate all possible state permutations in a three-state system,
which map to the dihedral group of order 3 – the smallest non-Abelian group103, whose characteristics
are attained by concatenating the generating operations in different orders, as shown in Fig. 3e. The
non-Abelian permutation also fundamentally distinguishes the possible topology of a two-statl nonHermitian system from a multi-state one.
Non-Hermitian band topology and skin effects. Band topology is one of the most successful
applications of topology in physics. The most salient feature of topological matter is the existence of
topological boundary modes (TBMs). The bulk-boundary correspondence states that every topological
bulk state has its characteristic TBMs104. As spectral topology plays no role in Hermitian systems,
band topology in Hermitian contexts only concerns the twisting of eigenvectors (wavefunctions) of
the bulk states. In contrast, the complex eigenvalues existing in non-Hermitian systems give rise to
spectral topology that also emerges in non-Hermitian periodic systems, manifested as the winding of
bands driven by crystal momentum. As such, band topology in non-Hermitian contexts expands to
include both spectral and wavefunction topology. However, these two layers of topology were initially
regarded as distinct aspects that do not interfere with each other. For example, in ref.
32
, the Chern
number, an invariant of wavefunction topology that can be computed from VWN (for example, the
Zak  ...
```

### Definition: `definition`
- source file: `10.1038_s42254-022-00516-5.pdf.txt`
- lines: 1475-1521

```text
is equivalent to the one introduced in “Complex eigenvalues and spectral topology,” but
here we focus on the disconnected spectral areas instead of the eigenvalue trajectory 𝐶𝐸 . Also, because
𝒌 takes value in the entire BZ, in dimension larger than 1, it is possible for a band to fill an entire
spectral area, as shown in the Figure below.
For a given point gap 𝐸̅𝑖 , choose one point 𝐸𝑟 ∈ 𝐸̅𝑖 that is invariant under all symmetries. Then
̃ = 𝐻 − 𝐸𝑟 , which belongs to the same symmetry class, and is
consider the new Hamiltonian 𝐻
invertible for all 𝒌 ∈ BZ. The latter is because the definition of point gap ensures that 𝐸0 does not
belong to any band, so that det(𝐻 − 𝐸𝑟 ) ≠ 0 . For any invertible square matrix, a unique polar
̃ (𝒌) = 𝑈(𝒌)𝑃(𝒌), where 𝑈(𝒌) is unitary and 𝑃(𝒌)is positive-definite
decomposition exists so that 𝐻
and Hermitian. The classification of 𝐻(𝒌) is then converted to the classification of 𝑈(𝒌), which is a
solved problem in the tenfold way. For example, consider a 1D one-band Hamiltonian 𝐸(𝑘), which
forms a loop in the complex plane, dividing the plane into the region outside 𝐸̅0 and the one inside 𝐸̅1.
̃ (𝑘) = 𝐸(𝑘) − 𝐸𝑟 . The polar decomposition goes 𝑈(𝑘) =
Choose any point 𝐸0 ∈ 𝐸̅0,1 we have 𝐻
𝐸(𝑘)−𝐸𝑟
|𝐸(𝑘)−𝐸𝑟 |
and 𝑃(𝑘) = |𝐸(𝑘) − 𝐸𝑟 | . The classification of 𝑈(𝑘) is just the winding number, so we
recover the EWN formula (Eq. (2)). Obviously, if
𝐸𝑟 ∈ 𝐸̅0 , then 𝒲𝐸 = 0 and for 𝐸𝑟 ∈ 𝐸̅1 , 𝒲𝐸 ≠ 0.
From this example, we see that the point gap
topology depends on the choice of the reference
point 𝐸𝑟 , but different choices of 𝐸𝑟 do not change
the point gap topology as long as 𝐸𝑟 belongs to the
same 𝐸̅𝑖 . In other words, the point-gap topology is
an extended version of spectral topology, which has
been discussed above. According to refs.
120,121
, in
1D, nontrivial spectral topology, i.e., the EWN, of
35
the point gap 𝐸̅𝑖 corresponds to the skin modes in the OBC spectrum. It is interesting to ask what point
gap topology corresponds to in higher dimensions. While some special cases have been discussed 176,
a general picture of bulk-edge correspondence has not been established.
36
```

## 10.1103_physrevb.99.201103

### Criterion: `criterion`
- source file: `10.1103_physrevb.99.201103.pdf.txt`
- lines: 23-94

```text
for their existence in non-Hermitian systems which, in contrast to previous formulations,
does not require specific tailoring to the system at hand. Our approach is intimately based on the
complex analytical properties of in-gap exceptional points, and gives a lower bound for the winding
number related to the vorticity of the energy Riemann surface. It also reveals that the topologically
nontrivial phase is partitioned into subregimes where the boundary mode’s decay length depends
differently on complex momenta roots.
The avenue of topological phases has reshaped our perspective on single-particle problems in condensed matter [1–3]. Unlike interacting many-body problems which
are seldom exactly solvable, single-particle problems are
often regarded as conveniently analytically tractable,
with quantum and classical realizations accessible on
equal formal footing [4–13]. This view, however, underestimates the richness and intricacies derived from
the parameter and phase space structure of the physical system [14], as well as the added complexity implied
by investigations of boundary terminations [15], external driving [16], and open systems beyond the realm of
Hermiticity [17].
Non-Hermiticity from either inherent gain/loss or nonreciprocity is particularly interesting, exhibiting several
exciting new phenomena. For instance, complex energy
bands can develop branch cuts terminating at so-called
exceptional points [18–25] that can coalesce to form exceptional rings [26–28], and bulk modes can morph into
boundary “skin” modes exhibiting an extensively large
boundary density of states [29, 30]. Non-Hermiticity profoundly affects topological localization in fascinating, yet
poorly understood ways. In a topologically non-trivial
Hermitian system, a boundary can only introduce a subextensive number of in-gap protected modes. The bulk
modes, being de-localized, remain largely undisturbed.
In contrast, in a non-Hermitian system, the entire spectrum of an arbitrary large system can be modified by
introducing a boundary, ostensibly violating the bulk
boundary correspondence (BBC) [20, 29–33].
As we shall elucidate, this seemingly counterintuitive
sensitivity to boundary conditions is a consequence of the
fundamental observation that non-reciprocal systems can
be driven into different regimes by local perturbations,
each characterized by its distinct exceptional points and
winding numbers. This is because non-reciprocity can localize all eigenmodes at the boundaries, including those
which, for periodic boundary conditions, would have been
assigned extended bulk modes. There are two types
of non-Hermitian boundary eigenmodes: Extensive skin
modes which are adiabatically connected to Hermitian
bulk modes through complex analytic continuation, and
sub-extensive topological boundary modes, which are, as
we will show, protected by a universal non-Hermitian
topological winding number criterion.
Recent attempts at characterizing these enigmatic nonHermitian boundary modes have not always been conclusive. Even after generalizing the Berry curvature
and Chern number to their biorthogonal non-Hermitian
analogs [23, 33–35], difficulties remain in choosing the
most appropriate and efficient quantities and contours
for capturing phase transitions [35]. While Refs. [29]
and [32] have identified jumps in the biorthogonal polarization as necessary conditions for topological phase
transitions, their sufficiency remains unclear beyond the
simplest models with nearest-neighbor hoppings. Since
non-reciprocity fundamentally alters the non-Bloch energy spectrum, the eigenmodes of generic models with
multiple non-reciprocal hopping ranges can only be understood through a systematic analysis of their complex
band structure. Quantitative predictions of the localization lengths and dispersions of skin modes are even more
elusive, with existing results restricted to numerical evidence or fine-tuned models where boundary modes can be
calculated exactly [30, 32, 33]. T ...
```

### Criterion: `Criterion`
- source file: `10.1103_physrevb.99.201103.pdf.txt`
- lines: 333-420

```text
for non-Hermitian topological phases – Besides
the continuum of skin boundary modes, there can also
exist isolated “topologically protected” boundary zero
modes. The general criterion for their existence, however,
must invariably differ in non-Hermitian systems from
that of Hermitian models, since the skin effect introduces
new decay length scales which manifest as additional singularities in the complex band structure. Below, we shall
derive a novel topological criterion (Eq. 11) for the most
intensely studied class of particle-hole (PH) symmetric
1D systems. It generalizes previously proposed invariants for non-Hermitian systems [29, 32, 35, 47], and is
straightforwardly applicable to models with arbitrarily
complicated non-Hermitian hoppings. Consider the most
generic PH symmetric 2-component Hamiltonian given
by H PH [{ra/b }; {pa/b }](z) =
!
Qp


)
√ i
0
z ra i a (z−a
0 a(z)
z ai
, (9)
=
Qp
)
b(z) 0
√ i
z rb i b (z−b
0
z ai
ik
where z = e and ai , bi are the complex roots of Laurent polynomials a(z), b(z), both of which can be rescaled
without changing the topology. In terms of OBC constraints (Eqs. 6), “topological” modes are special solutions where the boundary system described by Eqs. 6 is
not of full rank, such that the eigenmode weights cµ have
nonzero solutions despite |βµ | 6= |βν | for any pair µ, ν.
Rewriting Eqs. 6 as a matrix equation M c = 0, this condition for a topological mode translates to Det M = 0. As
meticulously derived in the supplement [44], this problem can be reformulated as the fundamental principle:
An isolated topological zero mode exists when the ra + rb
largest βµ s do not contain ra members from {a1 , ..., apa }
and rb members from {b1 , ..., bpb }. These conditions on
the zeros and poles of the Hamiltonian can also be recast [44] in terms of the windings
I
d(log g(z))
Wg (R) =
= #Zg (R) − #Pg , (10)
2πi
|z|=R
g = a, b, which counts the number of zeros #Zg (R) minus
the number of poles #Pg encircled by a circle |z| = R
of radius R ∈ R. Evidently, #Pg = pg − rg does not
depend on R, since the poles are always at z = 0. If
R is chosen such that |z| = R excludes the ra largest
roots of a(z), Wa (Ra ) = (pa − ra ) − #Pa = 0 when a
topological mode exists. The same |z| = R, however, is
not allowed to simultaneously exclude rb roots of b(z), for
that would cause the ra + rb excluded, i.e., largest roots,
to be partitioned into ra ai ’s and rb bi ’s. Hence when
Wa (R) = 0, we must have Wb (R) < 0, or vice versa.
Thus a topological boundary mode exists iff
∃ R ∈ (0, ∞)
such that Wa (R)Wb (R) < 0,
(11)
or, in terms of the energy surface vorticity and eigenmode
winding V (R), W (R) = (Wa (R) ± Wb (R))/2 [23, 29],
∃ R ∈ (0, ∞)
such that |V (R)| < |W (R)|.
(12)
(a)
(b)
FIG. 3: a) Phase diagram of Eq. 13 with γ = 1.2. Different colors represent regimes with topological mode decay rate −(log |β|)−1 determined by β = a1 , a2 , b1 or
b2 respectively. b) Illustration of how the ordering of
− log |β| solutions determine the phase along the dashed
line (t2 = 0.05) of a), with β = a1 , a2 , b1 and b2 solutions
colored red, light red, dark green and light green. From
```

### Criterion: `criterion 11`
- source file: `10.1103_physrevb.99.201103.pdf.txt`
- lines: 420-424

```text
, topological modes occur when no greenish
(redish) curve falls between two redish (greenish) curves,
with corresponding regimes colored as in a).
```

### Criterion: `Criterion 11`
- source file: `10.1103_physrevb.99.201103.pdf.txt`
- lines: 424-488

```text
or S18 is a main result of this work, implying that to have topological modes, we need to find
one value of R = e−κ such that Wa (R), Wb (R) are of
opposite signs. Based on the insight that the OBC spectrum remains invariant under imaginary flux pumping, it
does not rely on any specially tailored contour [29]. As
formulated in Eq. S18, it expresses vorticity as a lower
bound for eigenmode winding in the topological phase.
For instance, when the energy surface contains a branch
cut (V (R) = 1/2), topological modes require the winding
to be greater than 1/2, not 0 as in Hermitian cases.
To illustrate Eqs. 11 and S18, we apply it to a general
nearest neighbor (nn) hopping model which is already
beyond the models previously studied in the literature

0
t1 − γ + z + t2 /z
=
.
t1 + γ + 1/z + t2 z
0
(13)
Its phase diagram (Fig. 3a) contains a topological region
partitioned into four subregions, depending on whether
the zero mode decay length
−(log |β|)−1 is given by the
p
2
roots a1,2 =
p(−t1 − γ ± (t1 + γ) − 4t2 )/(2t2 ), or b1,2 =
2
(γ − t1 ± (t1 − γ) − 4t2 )/2. The decisive βµ is the
(ra +rb +1)th largest one [44] - not the one corresponding
to the imaginary gap (largest βµ ), which controls the
hopping decays [48, 49], as illustrated in Fig. 3b. For t2 =
0 in (13), criterion 11 reduces to previous formulations
of a topological criterion [29, 32, 45] |t21 − γ 2 | < 1 viz.
a1 = ∞, a2 = − t1 1+γ , b1 = γ − t1 and b2 = 0.
The fundamental advancement implied by criterion 11
lies in its logical sufficiency, convenience of use and general applicability to all two-component PH-symmetric
PH
Hnn
(z)

5
∗
FIG. 4: Application of criterion 11 to a more complicated
instance of (9) with pa = pb = 4 and ra = 3, rb = 2,
which is completely topologically characterized by the
roots of their a(z) and b(z) (purple and orange dots).
Non-contractible contours in the purple region (Wa > 0)
enclose at least qa +1 = pa −ra +1 = 2 purple roots, while
contours in the orange region (Wb < 0) enclose fewer
than qb + 1 = pb − rb + 1 = 2 orange roots. In a)/b), the
presence/absence of a zero mode corresponds to the presence/absence of an overlap region where Wa > 0 (purple)
and Wb < 0 (orange) simultaneously (i.e. Wa Wb < 0).
Hamiltonians after finding the zeros. As demonstrated
in Fig. 4 for Hamiltonians with generic complex nextnearest neighbor hoppings and multiple roots, whether
a zero mode exists depends on whether there exists a
ring where Wa > 0 and Wb < 0 simultaneously (or viceversa), i.e. where there are simultaneously less than ra
larger zeros of a(z) and less than rb smaller zeros of b(z).
```

### Result: `result`
- source file: `10.1103_physrevb.99.201103.pdf.txt`
- lines: 625-1801

```text
s Eqs. 1 and the discussion after Eq. 7 of the main text.
2. Pedagogical derivation of our topological criterion from first principles (Eqs. 11 and 12 of the main text).
PBC-OBC EVOLUTION THROUGH IMAGINARY FLUX
Imaginary flux threading argument and semi-OBCs
We treat a generic lattice system as a collection of 1D chains perpendicular to the open boundary, with coordinates
of the other dimensions taken as external parameters. Consider a 1D chain described by a Hamiltonian
H=
NR
X
X
n=−NL x;γδ
†
[Tn ]γδ ηx,γ
ηx+n,δ =
NR
X
XX
n=−NL
k
†
eikn [Tn ]γδ ηk,γ
ηk,δ ,
(S1)
γδ
such that hoppings across a displacement of n unit cells (i.e. sites) are given by the elements of the matrix Tn in the
†
†
and ηk,γ
are the creation operators of a γ-th sublattice
sublattice (internal component) basis indexed by γ, δ. ηx,γ
state at unit cell x and quasi-momentum k respectively. For brevity, we shall henceforth drop the sublattice indices.
We assume reasonably local hoppings, so NL , NR ∼ O(1). Under periodic/open boundary conditions (PBCs/OBCs),
the chain can be visualized as a ring with hoppings present/absent across its endpoints. Via Faraday’s law, we can
thread flux through this ring by shifting the momentum k via minimal coupling k → k + φ, where φ̇ is the rate
of change of flux which equals the induced (ficticious) electromagnetic field. Equivalently, this flux multiplies each
hopping with a phase factor viz. Tn → Tn einφ .
To relate this flux pumping with the boundary conditions (BCs), one performs a gauge transformation H → V −1 HV
with V = diag(e−iφ , e−2iφ , ..., e−ilφ ), l being the system length. This removes the phase from all the hoppings except
for those across the endpoints, which acquire a phase of e∓ilφ . Through this, we have managed to re-express BCs on
the boundary hoppings in terms of translationally-invariant fluxes.
We next construct an interpolation between PBCs and OBCs for studying how non-Hermitian skin modes arise.
For that, we have to first introduce the semi-open boundary condition (semi-OBC), which has the boundary hoppings
vanish in one direction but not the other. This is necessary because an imaginary flux component will always produce
a rescaling factor O(e±l Im φ ) that diverges with l at one of the boundaries. Without loss of generality, we set hoppings
Tn<0 |R from the right to the left boundary to zero, but preserve their reciprocal hoppings Tn>0 |L . As φ becomes
complex, Tn>0 |L will be rescaled by a factor of e−l Im φ . When Im φ = 0, we have perfect PBC in one direction; as
Im φ → ∞, we approach the OBC limit. Had the non-reciprocity be directed in the opposite direction, an identical
arguments holds with left and right sides switched, and φ ↔ φ∗ .
Hence, to find the spectrum of H(k) under the semi-OBC of Tn>0 |R = 0 and Tn>0 |L rescaled by a factor e−κl ,
which tends to the exact OBC when κl → ∞, we can perform the analytic continuation k → k + iκ. In other words,
we can simply diagonalize the translationally invariant analytic continuation of the original Hamiltonian (Eq. 1 of
the main text):
Hκ (k) = H(k + iκ),
(S2)
which possesses an identical spectrum as the semi-OBC system. Physically, (S2) implies that all the original PBC bulk
states must morph into left boundary modes with localization lengths κ−1 under e−κl boundary hopping suppression.
Furthermore, Hκ (k) ∀ κ forms an equivalence class of Hamiltonians with identical OBC spectra. Such macroscopic
condensation of modes onto one edge does not happen in Hermitian systems because semi-OBCs, being non-reciprocal,
S2
destroy hermiticity, and as such is a physically unrealistic proxy for OBC. But for the skin modes, OBCs and (correctly
chosen) semi-OBCs are essentially equivalent, since the BCs are only consequential at the boundary where the skin
mode is localized. Henceforth, we shall no longer distinguish OBCs from semi-OBCs.
Geometric argument for when skin mode evolution stops (Eq. 7 and subsequent arguments of the main text)
To intuitively under ...
```

## 10.1103_physrevlett.116.133903

### Result: `result`
- source file: `10.1103_physrevlett.116.133903.pdf.txt`
- lines: 307-567

```text
s can be proven analytically.)
To experimentally observe the fractional winding number, one can modulate the hopping amplitudes in time to
adiabatically sweep through the Brillouin zone (see Supplemental Material for details). An alternative approach
may be to use Bloch oscillations [33].
3
(b)
(a)
(c)
1
1.5
0.5
1
0
0.25
population
Im E
Re E
0.5
0
v=0.35.
0.5
0
-0.5
1
v=0.5.
0.5
0
-0.25
1
-1
-1
-0.5
0
0.5
1
v=0.65.
0.5
-0.5
-1.5
-1
-0.5
v/.
0
0.5
0
1
0
v/.
10
20
30
unit cell
FIG. 3. Chain with open boundaries, N = 30 unit cells, and r = 0.5γ. (a) Real and (b) imaginary parts of the spectrum. Red
lines follow the E = 0 eigenvalue. (c) Zero-energy eigenvector for different values of v.
Since a periodic chain has nontrivial topology, we next
investigate whether there are zero-energy edge states in a
chain with open boundaries. However, there is a problem:
Eq. (4) says that when one exceptional point is encircled,
Ek is gapless in both real and imaginary parts. This
is worrisome because it precludes the existence of zeroenergy edge states, which usually require a band gap.
Open boundary conditions.— Figure 3 shows the spectrum for an open chain. There are several remarkable
features of this spectrum:
• A gap opens up in the spectrum’s real part in the
vicinity of v = γ/2, dividing most of the eigenvalues
into two distinct bands [Fig. 3(a)].
• Within the band gap, there is an E = 0 eigenvalue,
which is twofold degenerate but defective [25]. This
eigenvalue is associated with an eigenvector and a
generalized eigenvector. Under time evolution, the
eigenvector dominates over the generalized eigenvector, so the latter is unimportant to the long-time
dynamics.
• The eigenvector for E = 0 is localized either on
the left edge (when v > 0) or the right edge (when
v < 0) [see Fig. 3(c)]. The edge state is protected
by chiral symmetry, and it appears when the gap
opens and disappears when the gap closes.
• For |v| ≥ γ/2, the spectrum is purely real
[Fig. 3(b)], i.e., PT symmetry is preserved, in contrast to a periodic chain [30].
Open chain: case of v = γ/2.— We discuss, in detail,
the case of v = γ/2, where H can be solved exactly. We
seek the eigenvalues of H, as well as their algebraic and
geometric multiplicities [25]. It is more convenient to deal
with H 2 , which is block upper triangular. It is easy to
show that the characteristic polynomial of H 2 is f (λ) =
λ2 (λ − r2 )2N −2 , which implies that H has eigenvalues
E = 0, r, −r with algebraic multiplicities 2, N − 1, N −
1, respectively. The Jordan normal form indicates that
the geometric multiplicities of all three eigenvalues are 1.
Thus, H is highly defective at v = γ/2. Note that the
eigenvalues are real.
The eigenvector for E = 0 is the edge state
u0 = (i, 1, 0, 0, . . .)T ,
(6)
in the basis α1 , β1 , α2 , β2 , . . .. So u0 is localized on the
left-most unit cell. It is its own chiral partner: Γu0 =
−u0 . Physically, this state has zero energy because of
destructive interference between the hopping and nonHermiticity.
The generalized eigenvector u00 for E = 0 is given by
Hu00 = u0 [25]:
u00

=
T
ir r2 ir2
2
r
, 0, − 2 , − 2 , 3 , 3 , . . .
.
γ
γ
γ γ γ
(7)
Since Hu00 = u0 , population in u00 is transferred to u0
during the time evolution. Note that u00 is also localized
on the left edge.
For v = −γ/2, H can be similarly solved: u0 and u00
are similar to Eqs. (6)–(7) but localized on the right.
Open chain: case of v 6= γ/2.— As v deviates from
γ/2, the bands are no longer degenerate, and the band
gap narrows and eventually closes. There is still a defective E = 0 eigenvalue because it is protected by chiral symmetry [Fig. 3(c)]. However, when the band gap
closes, the E = 0 eigenvalue splits into two distinct eigenvalues that join the upper and lower bands [Fig. 3(a)].
Strictly speaking, for finite N , the E = 0 eigenvalue
is defective only when v = γ/2. However, we find numerically that for a range of v around γ/2, H has one
vanishingly small singular value [25], which decreases ...
```

## 10.1103_physrevx.8.031079

### Principle: `principle`
- source file: `10.1103_physrevx.8.031079.pdf.txt`
- lines: 254-632

```text
s:
(I) Topological phases of non-Hermitian systems
can be understood as dynamical phases, where
Z2 ⊕ Z2 Z2 ⊕ Z2
not only the eigenstates but also the full complex
spectra should be taken into account;
(II) The non-Hermitian generalization of the concept of the band gap is the prohibition of touching
a base energy, which is typically zero but generally complex, in the spectrum.
We show that (I) and (II) are well justified both physically
and mathematically. On the basis of these two guiding principles, we find that a one-dimensional lattice with asymmetric
hopping amplitudes turns out to be the most prototypical example comparable to the quantum Hall insulator, in the sense
that an integer topological number can be defined without any
symmetry protection. This result gives an interesting topological interpretation to the emergent Anderson transition [113]
in the Hatano-Nelson model [114–116], which should otherwise be absent in one-dimensional Hermitian systems [117].
We also unveil a bulk-edge correspondence which is qualitatively different from the Hermitian case: There is a continuum
of (quasi-)edge modes in the semi-infinite space (open chain),
with the winding number being the degeneracy at a given base
energy. These findings answer the last two questions (iii) and
(iv) raised in the last paragraph.
Our guiding principles also enable a systematic application
of the K-theory [118], a technique widely used in classifying Hermitian topological systems [44, 46, 51], to the nonHermitian AZ classes, leading to a complete classification in
all spatial dimensions. We introduce a unitarization procedure
as a non-Hermitian generalization of band flattening, followed
by a Hermitianization procedure to represent the classifying
space as a Clifford-algebra extension [61]. The classification
problem turns out to be mathematically equivalent to that of
the Hermitian AZ classes with an additional chiral symmetry,
leading to a dramatically different periodic table as shown in
Table I. We identify the underlying topological numbers implied by the K-theory classification for all the non-Hermitian
AZ classes in one dimension. We also unveil a Z2 topological
index for zero-dimensional (anti-)P T -symmetric systems and
quantum channels. These results answer the first two questions (i) and (ii) raised above, and can further be generalized
to, e.g., systems with crystalline symmetries and especially to
P T -symmetric systems.
3
The remainder of the paper is organized as follows. In
Sec. II, we introduce the dynamical point of view regarding topological phases and justify the guiding principle (I).
In Sec. III, we first justify the guiding principle (II) and then
discuss the topological properties of non-Hermitian lattices in
one dimension, including the definition of the winding number, edge physics and experimentally observable signatures.
In Sec. IV, we employ the K-theory to achieve a complete
classification of non-Hermitian AZ classes in all dimensions,
as shown in Table I. The identification of topological numbers
and some topologically nontrivial examples in zero and one
dimensions are given in Sec. V. We conclude the paper with
an outlook in Sec. VI. Several technical details and an experimental implimentation on asymmetric hopping are relegated
to Appendices to avoid digressing from the main subjects.
II.
DYNAMICAL VIEWPOINT ON THE TOPOLOGICAL
PHASES
We begin by discussing how to define topological phases.
In a Hermitian system, a topological phase can be analyzed
from the many-body ground-state wave function |Ψi, which
can be mapped through the projector
X
P− =
|ϕj ihϕj |
(1)
Ej <EF
onto all the single-particle eigenstates |ϕj i = fj† |vaci below the Fermi energy EF for free fermions with |Ψi =
Q
( Ej <EF fj† )|vaci. Note that the spectrum plays no role here,
since the Hamiltonian H can be flattened by means of the projector (1) into 1 − 2P− [43–45] without closing the (band or
many-body) energy gap, as schematically illustrated in Fig. ...
```

### Principle: `principle`
- source file: `10.1103_physrevx.8.031079.pdf.txt`
- lines: 918-1671

```text
[119]
I
dz f 0 (z)
= Z − P,
(21)
|z|=1 2πi f (z)
where E = f (z) is the characteristic equation and Z (P ) denotes the number of zeros (poles) of f (z) in the area |z| <
1. Replacing z with eik , we find that the left-hand side of
Eq. (21) gives nothing but the winding number w introduced
in Eq. (6). A general form of the wave function can be writPZ
ten as ψj = l=1 cl zlj , where zl ’s are the zeros and cl ’s are
subject to P different constraints stemming from the inhomogeneity at the edge. These are straightforward generalizations
of Eqs. (19) and (20). As a result, there are Z − P = w-fold
degeneracies of edge states at E = 0, or generally at E = EB
if we replace f (z) with f (z) − EB in Eq. (21). Note that the
same analysis applies to single bands with negative winding
numbers by interchanging z and z −1 .
In a realistic one-dimensional system, such as a photonic
lattice [88], open boundaries always appear in pairs. In
the presence of two edges, only a one-dimensional part is
picked out from the edge-state continuum, making the topological degeneracy generally invisible for a given base energy. For example, the spectrum of an open chain described
by Eq. (7) with length L can be determined as En =
√
nπ
2 JL JR cos L+1
(n = 1, 2, ..., L) which distributes over an
√
√
interval (−2 JL JR , 2 JL JR ) on the real-energy axis in the
thermodynamic limit (see the red line in Fig. 4 (a)). A sudden change in the spectrum under different boundary conditions has also been found in Ref. [137]. Here, we can provide a topological understanding — the winding number (14)
should either vanish or become ill-defined in an open chain,
since the flux can always be gauged out and thus detH(Φ) is
Φ independent. Therefore, the spectrum no longer encircles
any base point inside the spectrum loop under the periodic
boundary condition. Since the spectrum should change continuously when the boundary hopping is gradually switched
on, the spectrum must be very sensitive to the boundary condition. Indeed, it is already shown in Ref. [137] that an exponentially small modification of the boundary condition can
lead to an order-one change in the spectrum.
As stated above, an energy eigenstate localized at the edge
of a semi-infinite space generally disappears if the system
size is finite. Nevertheless, quasi-edge modes may exist for
finite-size systems. By quasi-edge modes, we mean that they
are not genuine eigenstates, yet their dynamics look just like
eigenstates up to a time scale that increases with the system size and diverges in the thermodynamic limit. To investigate them, suppose that an edge state with energy E
for the semi-infinite condition is prepared in a finite lattice
with length L, whose spectrum does not include E. Then
the time evolution can be obtained to a good approximation
simply by multiplying e−iEt up to a time scale (at least) proportional to L (see Figs. 4(c) and (d)). Note that this quasieigenstate of a finite chain becomes exact in the semi-infinite
limit L → ∞. While a formal proof is available (see Appendix D), we can intuitively interpret this linear scaling as
a manifestation of the Lieb-Robinson bound [138] after a
boundary-condition quench roughly L sites away from the
edge mode, as illustrated in Fig. 4 (b). In the presence of
disorder, these quasi-edge modes stay robust, although they
are irregularly modified depending on the disorder configuration. As for on-site disorder in Eq. (7), the wave function of a
quasi-edge mode (if exist) at E can iteratively be determined
by ψj+1 = [(E − Vj )ψj − JR ψj−1 ]/JL . The lifetime upon
disorder average obeys the same linear scaling with respect to
(sufficiently large) L as the clean limit (see Fig. 4(f)).
The dramatic changes in the spectra for different boundary conditions has already been investigated in a purely mathematical context regarding non-Hermitian Toeplitz matrices
(i.e., the matrices satisfying Mjl = Mj−l ) and operators
[139]. A generalization of the conventional eigenv ...
```

### Theorem: `Theorem 1`
- source file: `10.1103_physrevx.8.031079.pdf.txt`
- lines: 1671-2442

```text
For an arbitrary invertible Hamiltonian H,
which has a unique polar√decomposition H = U P with U
being unitary and P = H † H being positive-definite and
Hermitian, we have H ' U .
This theorem is proved in Appendix G and applicable also to
crystalline symmetries. We provide two examples of unitarization from H to U in Fig. 6. According to this theorem,
it suffices to consider the classification of all the unitary matrices. Note that this result is consistent with band flattening
in the Hermitian case [43–45]. By diagonalizing a Hermitian
Hamiltonian as

H=V 
Λ+
p×p
0
0
Λ−
q×q

 V †,
(26)
−
where Λ+
p×p (Λq×q ) is the diagonal block of all the positive
(negative) energies, we find the polar decomposition to be
B.
K-theory and Clifford-algebra extension
The classification based on the homotopy equivalence is appropriate for a given Hilbert space, but is not so if the operations of inserting extra bands are also allowed. These operations are indeed possible in experiments of ultracold atoms,
where we can, for example, couple two or more individual
one-dimensional chains [147]. In this case, the correct classification should be carried out on the basis of the K-theory
[44, 46, 50, 51, 148], i.e., all we have to do is to figure out
the K-group of the map from the Brillouin zone M = T d (d:
spatial dimension) to a matrix space subject to specific symmetry requirements (but with no Hermiticity constraints). If
we are only interested in the strong topological numbers [44],
the manifold is M = S d .
It is worthwhile to sketch the basics of the K-theory, so as
to understand why it is compatible with band-inserting operations. The K-group is an Abelian group consisting of equivalence classes, denoted as [H0 , H1 ], of Hamiltonian pairs
(H0 , H1 ), where H0 and H1 act on the same Hilbert space.
For (H0 , H1 ), we define an addition structure as
(H0 , H1 ) + (H00 , H10 ) = (H0 ⊕ H00 , H1 ⊕ H10 ).
(28)
We also impose (H0 , H1 ) = (H00 , H10 ) if H0 ' H00 and
H1 ' H10 . To specify the equivalence classes, we require that
(H0 , H1 ) should be identified as (H0 ⊕ H, H1 ⊕ H) for all
H, i.e., [H0 ⊕ H, H1 ⊕ H] ≡ [H0 , H1 ]. By naturally defining
the addition between equivalence classes as
[H0 , H1 ] + [H00 , H10 ] = [H0 ⊕ H00 , H1 ⊕ H10 ],
(29)
we can deduce that they form an Abelian group, which is
called the K-group and denoted as K(M ), with zero element
[H, H] = 0 and the inverse of [H0 , H1 ] being [H1 , H0 ]. We
say that H0 and H1 belong to the same topological phase if
and only if [H0 , H1 ] = 0.
A crucial observation here is that although H0 ' H1 implies [H0 , H1 ] = 0, the converse is not true. A prototypical
example is the Hopf insulator [149] which is a two-band system in three dimensions and has no symmetry. While a Hopf
insulator differs homotopically from a trivial insulator by a
nonzero Hopf charge, it becomes trivial in the K-theory classification since we can insert additional bands into the system
to trivialize the homotopy from S 3 to the entire Hilbert space.
In other words, nontrivial topological phases emerge in class
A in three dimensions only if there are two bands.
11
While it is generally difficult to calculate the K-group, welldeveloped techniques are available if the Hamiltonian space
subjected to specific symmetry constraints is an extension of
a Clifford algebra [44], which is generated by a set of anticommutative elements {ej }nj=1 , i.e., ej ej 0 = −ej 0 ej for all
j 6= j 0 . If e2j = 1 for all j = 1, 2, ..., n, the algebra generated by {ej }nj=1 over the complex-number field C is called a
complex Clifford algebra C`n . If e2j = −1 for j = 1, 2, ..., p
(p ≤ n) and e2j = 1 for j = p + 1, p + 2, ..., n, the algebra
generated by {ej }nj=1 over the real-number field R is called a
real Clifford algebra C`p,q , where q = n − p. For a flattened
Hermitian Hamiltonian H, we naturally have H 2 = 1, which
can already be regarded as an element of a Clifford algebra
C`H generated by H and its two-fold symmetry operators (a ...
```

### Theorem: `Theorem 2`
- source file: `10.1103_physrevx.8.031079.pdf.txt`
- lines: 3519-3532

```text
Given D different wave functions |ψn i (n =
1, 2, ..., D) satisfying kH|ψn ik < 1 and |hψm |ψn i| < 2
D−1 for √
all m 6= n, there must be at least D different eigenstates of H † H with energies less than Eb = √ D1
.
1−(D−1)2
where ζl (l = 1, 2, ..., R) is the ml th zero of f (z) outside
|z| = 1. Recalling that z p f (z) is a polynomial with degree
PR
p + q, we have Z 0 ≡
l=1 ml = p + q − Z = q − w.
This result is consistent with directly applying the argument
```

### Principle: `principle`
- source file: `10.1103_physrevx.8.031079.pdf.txt`
- lines: 3532-3716

```text
to f (z −1 ), which has a single qth-order pole z = 0
inside the circle of |z| = 1, leading to
I
|z|=1
d
f (z −1 )
dz dz
= Z 0 − q.
2πi f (z −1 )
(C12)
Here we have used the fact that ζl−1 ’s are the zeros of f (z −1 )
inside the unit circle |z| = 1. Noting that the left-hand side in
Eq. (C12) can be shown to be the minus of that in Eq. (21) via
a change of the integration variable, we obtain Z 0 = q − w.
The initial condition
ψ0 = ψ1 = ... = ψq−1 = 0
(C13)
Proof.— We note that |ψn i’s are linearly independent. Otherwise, we can find cj ’s (j = 1, 2, ..., D) such that
PD
max1≤j≤D |cj | = |cj0 | > 0 and j=1 cj |ψj i = 0, leading to
the contradiction
|cj0 | = |cj0 hψj0 |ψj0 i| =
≤
X
j6=j0
X
j6=j0
cj hψj0 |ψj i
(C15)
|cj ||hψj0 |ψj i| < 2 (D − 1)|cj0 |  |cj0 |.
Therefore, denoting V0 ≡ span{|ψj i : j = 1, 2, ..., D}, we
have dimV0 = D. For an arbitrary |ψi ∈ V0 , which can
PD
PD
always be expressed as |ψi = j=1 cj |ψj i/k j=1 cj |ψj ik,
21
-1
we can bound kH|ψik from above as
-2
kH|ψik ≤
j=1 |cj |kH|ψj ik
PD
k j=1 cj |ψj ik
PD
1 j=1
< qP
D
j=1
<p
≤p
|cj
|2
−
〈lnλm 〉/ln10
PD
|cj |
∗
m6=n |cm cn hψm |ψn i|
P
1
1 − (D − 1)2
√
D1
PD
j=1
qP
W=5
-5
W=4
-6
W=3.5
-7
W=3
50
|cj |
D
j=1
100
150
200
L
|cj |2
FIG. 15. Finite-size scaling for the logarithmic-disorder-averaged
smallest singular value hln λm i of the Hatano-Nelson Hamiltonian
(11) with JL = 2, JR = 1 and complex disorder. Each point is
obtained from 2.5 × 105 disorder realizations.
Consequently, we have
TrV0 [H † H] < Eb2 ,
(C17)
where TrV0 [...] denotes the trace over the subspace V0 . Denoting Pg as the projector onto
√ the Hilbert subspace Vg spanned
by all the eigenstates of H † H with energies less than Eb ,
we can construct H 0 ≡ Eb2 (1 − Pg ) ≤ H † H, leading to
Eb2 (D
-4
(C16)
Eb
=√ .
D
1 − (D − 1)2
0
-3
Eb2
TrV0 [H ] =
− TrV0 [Pg ]) <
⇔ TrV0 [Pg ] = TrVg [P0 ] > D − 1,
(C18)
where P0 is the projector onto V0 . Since TrVg [P0 ] ≤
TrVg [1] = dimVg , which should be an integer, we finally obtain dimVg ≥ D. 
√
Now let us come back to the eigenvalue problem of H † H
for an open chain with length L. We can first work in the semiinfinite limit to determine a set of orthonormal zero modes
|φj i’s (j = 1, 2, ..., |w|) of H, and then truncate and normalize them on a finite chain, obtaining |ψj i’s. Note that |ψj i’s
are now not exact eigenstates of H, but the conditions of the
theorem proved above are satisfied, with 1 and 2 exponentially small in L, since the deviations stem from the exponential tail. According to the theorem, we can find at least
|w| eigenstates with exponentially small energies. We should
furthermore mention the impossibility to find the (|w| + 1)th
eigenstate with a small energy that eventually vanishes in the
thermodynamic limit; otherwise we will have at least |w| + 1
zero modes of H in a semi-infinite space, leading to a contradiction.
It is worthwhile to mention that the bulk-edge correspondence for class AIII (or BDI) alone can alternatively be proved
using the Callias index theorem [170] following Ref. [36].
However, it seems rather nontrivial whether a similar method
can be applied to a single off-diagonal block in a class AIII
Hamiltonian.
```

### Definition: `definition`
- source file: `10.1103_physrevx.8.031079.pdf.txt`
- lines: 4718-5122

```text
in the presence of zero modes, which are counted
as potentially P T -broken pairs. Note that unlike the chiral symmetry, a P T -symmetric Hamiltonian maintains the
P T -symmetry under the translation H → H + E for all
E ∈ R. The topological index given by Eq. (I6) can be
interpreted as whether a topological transition occurs at the
edge that changes the zero-dimensional Z2 index (discussed
in Sec. V A) when the boundary condition changes. Similar
to a Z2 topological insulator [5, 6], which has an odd number
of helical modes at the edge, a nontrivial P T -symmetric system in one dimension should exhibt an odd number of edgemode pairs, leading to s = −1. If there is additional particlehole symmetry, we can conclude that a system with s = −1
must have an odd number of pairs of P T -broken edge modes
with purely imaginary eigenenergies, and thus the system possesses at least one pair.
27
[1] D. J. Thouless, M. Kohmoto, M. P. Nightingale, and M. den
Nijs, “Quantized hall conductance in a two-dimensional periodic potential,” Phys. Rev. Lett. 49, 405 (1982).
[2] F. D. M. Haldane, “Nonlinear field theory of large-spin heisenberg antiferromagnets: Semiclassically quantized solitons of
the one-dimensional easy-axis néel state,” Phys. Rev. Lett. 50,
1153 (1983).
[3] F. D. M. Haldane, “Model for a quantum hall effect without landau levels: Condensed-matter realization of the ”parity
anomaly”,” Phys. Rev. Lett. 61, 2015 (1988).
[4] Xiao-Gang Wen, “Topological orders and edge excitations in
fractional quantum hall states,” Adv. Phys. 44, 405 (1995).
[5] C. L. Kane and E. J. Mele, “Quantum spin hall effect in
graphene,” Phys. Rev. Lett. 95, 226801 (2005).
[6] B. Andrei Bernevig, Taylor L. Hughes, and Shou-Cheng
Zhang, “Quantum spin hall effect and topological phase transition in hgte quantum wells,” Science 314, 1757 (2006).
[7] Markus König, Steffen Wiedmann, Christoph Brüne, Andreas
Roth, Hartmut Buhmann, Laurens W. Molenkamp, XiaoLiang Qi, and Shou-Cheng Zhang, “Quantum spin hall insulator state in hgte quantum wells,” Science 318, 766 (2007).
[8] M. Z. Hasan and C. L. Kane, “Colloquium: Topological insulators,” Rev. Mod. Phys. 82, 3045 (2010).
[9] Xiao-Liang Qi and Shou-Cheng Zhang, “Topological insulators and superconductors,” Rev. Mod. Phys. 83, 1057 (2011).
[10] C. W. J. Beenakker, “Random-matrix theory of majorana
fermions and topological superconductors,” Rev. Mod. Phys.
87, 1037 (2015).
[11] Ching-Kai Chiu, Jeffrey C. Y. Teo, Andreas P. Schnyder, and
Shinsei Ryu, “Classification of topological quantum matter
with symmetries,” Rev. Mod. Phys. 88, 035005 (2016).
[12] Xiao-Gang Wen, “Colloquium: Zoo of quantum-topological
phases of matter,” Rev. Mod. Phys. 89, 041004 (2017).
[13] Immanuel Bloch, Jean Dalibard, and Sylvain Nascimbène,
“Quantum simulations with ultracold quantum gases,” Nat.
Phys. 8, 267 (2012).
[14] Marcos Atala, Monika Aidelsburger, Julio T. Barreiro, Dmitry
Abanin, Takuya Kitagawa, Eugene Demler, and Immanuel
Bloch, “Direct measurement of the zak phase in topological
bloch bands,” Nat. Phys. 9, 795 (2013).
[15] Gregor Jotzu, Michael Messer, Rémi Desbuquois, Martin Lebrat, Thomas Uehlinger, Daniel Greif, and Tilman Esslinger,
“Experimental realization of the topological haldane model
with ultracold fermions,” Nature 515, 237 (2014).
[16] M. Aidelsburger, M. Lohse, C. Schweizer, M. Atala, J. T. Barreiro, S. Nascimbène, N. R. Cooper, I. Bloch, and N. Goldman, “Measuring the chern number of hofstadter bands with
ultracold bosonic atoms,” Nat. Phys. 11, 162 (2015).
[17] B. K. Stuhl, H.-I. Lu, L. M. Aycock, D. Genkina, and I. B.
Spielman, “Visualizing edge states with an atomic bose gas in
the quantum hall regime,” Science 349, 1514 (2015).
[18] M. Mancini, G. Pagano, G. Cappellini, L. Livi, M. Rider,
J. Catani, C. Sias, P. Zoller, M. Inguscio, M. Dalmonte, and
L. Fallani, “Observation of chiral edge states with neutral
fermions in synthetic hall ribbons,” Science 349, 1510 (2015).
[19] Zhan Wu, Long Zhang, Wei Sun, ...
```

## 10.1103_physrevx.9.041015

### Result: `result`
- source file: `10.1103_physrevx.9.041015.pdf.txt`
- lines: 145-663

```text
s are summarized as periodic tables III-IX. The crucial idea behind this topological classification is that the
complex-spectral-flattening procedures differ according
to the type of the complex-energy gap: a non-Hermitian
Hamiltonian can be flattened to a unitary matrix in the
presence of a point gap, whereas it can be flattened to a
3
Hermitian or an anti-Hermitian matrix in the presence of
a line gap (Fig. 2). The corresponding topological invariants are systematically obtained in Sec. IV C. We also
elucidate the non-Hermitian bulk-boundary correspondence in terms of our classification in Sec. V. Remarkably, whereas the conventional bulk-boundary correspondence can break down in generic non-Hermitian systems,
we demonstrate that it is restored by certain classes of
symmetry including parity-time symmetry and pseudoHermiticity. As a unique non-Hermitian feature, there
appear multiple topological structures in each symmetry class and each spatial dimension, which is illustrated
with an example in Sec. VI. As discussed in Sec. VII,
our classification describes the non-Hermitian topological
phases observed in recent experiments [145, 146, 148–
151, 153–157], which are not fitted into the previous
classification scheme [122]. Furthermore, our classification systematically predicts a new type of symmetryprotected topological lasers that support lasing helical
edge states and dissipative topological superconductors
that support nonorthogonal Majorana edge states. As
a crucial byproduct, our non-Hermitian theory also provides the topological classification of Hermitian and nonHermitian free bosons as shown in Sec. VIII. We conclude
this work in Sec. IX.
B.
Whereas a point gap and the corresponding topological classification were considered in Ref. [122], a
line gap was not considered there, and the present
work has developed the unified understanding of
complex-energy gaps. Importantly, the two types
of complex-energy gaps enrich non-Hermitian topological phases in a fundamental manner that has
no analogs to the Hermitian ones; non-Hermitian
topology strongly depends on the type of complexenergy gaps.
Our complete classification of non-Hermitian topological phases relies on these fundamental insights in nonHermitian physics. Crucially, although the previous classification [122] cannot correctly describe the recent experiments on non-Hermitian topological systems, the present
classification encompasses them because of the above fundamental insights into symmetry and energy gaps, as described in Sec. VII A. Moreover, our work systematically
predicts novel non-Hermitian topological phases that enable richer phenomena and functionalities due to the interplay of non-Hermiticity and topology. For example,
our theory predicts novel symmetry-protected topological lasers and dissipative topological superconductors, as
described in Secs. VII B and VII C.
Distinction from the previous work
The general theory in the present work supersedes and
encompasses the results in the previous work [122]. In
particular, this work provides the following fundamental
insights into symmetry and topology in non-Hermitian
physics:
• Symmetry ramification. — We discover that nonHermiticity ramifies symmetry due to the distinction between complex conjugation and transposition, which are equivalent for Hermitian Hamiltonians, as described in Sec. II. Consequently, we have
a lot of new non-Hermitian symmetries, culminating in the 38-fold symmetry beyond the celebrated
AZ symmetry in Hermitian physics. In particular, whereas a number of recent works including
Ref. [122] focused on symmetry in terms of complex conjugation (such as parity-time symmetry),
the crucial significance of the transposition symmetry has not been appreciated, and we have found
its special role, for instance, in symmetry-protected
topological lasers and dissipative superconductors.
• Complex-energy gaps and non-Hermitian topology. — The definition of an energy gap is nontrivial in non-Hermiti ...
```

### Definition: `Definition 1`
- source file: `10.1103_physrevx.9.041015.pdf.txt`
- lines: 952-1023

```text
(point gap) — A non-Hermitian Hamiltonian H (k) is defined to have a point gap if and only
if it is invertible (i.e., ∀ k det H (k) 6= 0) and all the
eigenenergies are nonzero (i.e., ∀ k E (k) 6= 0).
Under this definition, a gapless system possesses a
zero-energy state for some k. A point gap helps understand the localization-delocalization transition in nonHermitian systems in one dimension [13, 18, 122, 138]
that occurs due to the competition between disorder and
non-Hermiticity. Since one-dimensional Hermitian systems always show the Anderson localization, the delocalization is unique to non-Hermitian systems. Here, a topological invariant [i.e., the winding number in Eq. (42)]
can be assigned to a generic non-Hermitian system in
one dimension. In the Hatano-Nelson model (i.e., a
non-Hermitian extension of the one-dimensional Anderson model with asymmetric hopping) [13], wave functions
are delocalized (localized) and the system is metallic (insulating) if the winding number is nonzero (zero) [122].
Moreover, it has recently been reported that localization
(delocalization) of wave functions corresponds to the nontrivial (trivial) topology in a non-Hermitian quasicrystal
(Aubry-André-Harper model) [138].
B.
Line gap
A complex-energy line that serves as an obstacle in the
complex-energy plane can also be subject to restrictions
in the presence of symmetry, whereas such a line is arbitrary in the absence of symmetry. In particular, it should
be either the imaginary axis (Re E = 0) or the real axis
(Im E = 0) when symmetry imposes a real structure on
the complex spectrum. For instance, the real axis should
be considered when pairs of eigenenergies (E, E ∗ ) appear with TRS; the imaginary axis should be considered
when pairs of eigenenergies (E, −E ∗ ) appear with CS.
In contrast to the point gap, there are no restrictions in
the presence of SLS since SLS does not give the complex spectrum real structures [eigenenergies just come in
(E, −E) pairs]. Thus, it is convenient to choose the line
that determines the complex gap as the imaginary axis
(real gap) or the real axis (imaginary gap), which leads
to the precise definition of the line gap in the following:
Definition 2 (line gap) — A non-Hermitian Hamiltonian H (k) is defined to have a line gap in the real (imaginary) part of its complex spectrum [real (imaginary) gap]
if and only if it is invertible (i.e., ∀ k det H (k) 6= 0)
and the real (imaginary) part of all the eigenenergies is
nonzero [i.e., ∀ k Re E (k) 6= 0 (Im E (k) 6= 0)].
Under this definition of a real (imaginary) gap, a gapless system includes an eigenenergy with Re E (k) = 0
(Im E (k) = 0) for some k. Line gaps are employed explicitly in Refs. [102, 117, 126] and implicitly in many
other pieces of work, and characterize topologically protected boundary states, which were also observed in experiments [145, 146, 148–151, 153–155]. Remarkably,
topologically protected boundary states in Hermitian systems are immune to non-Hermiticity as long as a real gap
is open and relevant symmetry is respected, which is generally ensured by the nontrivial non-Hermitian topology
in terms of line gaps. Furthermore, the presence of an
imaginary gap has a significant influence on the nonequilibrium wave dynamics [126], although it has no counterparts in the Hermitian band theory.
IV.
TOPOLOGICAL CLASSIFICATION
We provide topological classification of non-Hermitian
insulators and superconductors according to all the 38
symmetry classes discussed in Sec. II and the two types of
the complex-energy gaps discussed in Sec. III. Here, nonHermitian Hamiltonians H0 (k) and H1 (k) are defined
to be topologically equivalent if and only if there exists a
family of non-Hermitian Hamiltonians Hλ (k) (0 ≤ λ ≤
1) that interpolates between them, i.e.,
Hλ=0 (k) = H0 (k) ,
Hλ=1 (k) = H1 (k)
(28)
with certain symmetries and a complex-energy gap for all
λ ∈ [0, 1]. Our strategy is to reduce this non-Hermitian
problem to the established topological classi ...
```

### Theorem: `Theorem 1`
- source file: `10.1103_physrevx.9.041015.pdf.txt`
- lines: 1047-1051

```text
(unitary flattening for point gaps) — If a
non-Hermitian Hamiltonian H (k) has a point gap, it can
be continuously deformed into a unitary matrix U (k)
while keeping the point gap and its symmetry [Fig. 2 (b)].
```

### Theorem: `Theorem 1`
- source file: `10.1103_physrevx.9.041015.pdf.txt`
- lines: 1051-1184

```text
reduces the topological classification of a
non-Hermitian Hamiltonian to that of a unitary matrix.
Furthermore, with the flattened unitary matrix U (k), we
have a flattened Hermitian matrix
!
0
U (k)
H̃ (k) :=
, H̃ 2 (k) = 1.
(29)
U † (k)
0
Here the presence of symmetry for the original nonHermitian Hamiltonian H (k) discussed in Sec. II imposes the following constraints on the extended Hermitian Hamiltonian H̃ (k):
!
T± 0
−1
∗
T̃± H̃ (k) T̃± = ±H̃ (−k) , T̃± :=
; (30)
0 T±
−1
C˜± H̃ ∗ (k) C˜±
= ±H̃ (−k) , C˜± :=
Γ̃H̃ (k) Γ̃
S̃ H̃ (k) S̃
−1
−1
η̃ H̃ (k) η̃
0 C±
C± 0
!
= −H̃ (k) , Γ̃ :=
0 Γ
Γ 0
!
= −H̃ (k) , S̃ :=
S 0
0 S
−1
= H̃ (k) , η̃ :=
0 η
η 0
!
; (31)
;
(32)
;
(33)
!
.
Moreover, H̃ (k) respects additional CS (SLS):
!
1 0
−1
ΣH̃ (k) Σ = −H̃ (k) , Σ :=
.
0 −1
(34)
(35)
Importantly, there exists a one-to-one correspondence between a unitary matrix U (k) and an extended Hermitian
matrix H̃ (k) that satisfies Eq. (35) [122, 227], and hence
topology of H (k) can also be captured by the extended
Hermitian Hamiltonian H̃ (k). Therefore, the topological
classification of a non-Hermitian Hamiltonian H (k) with
a point gap and symmetry reduces to that of a Hermitian
Hamiltonian that respects symmetry given by Eqs. (30)(35), which was already obtained in Refs. [206–208, 213].
In this manner, the periodic tables under point gaps are
11
obtained as Tables III-IX. Notably, a similar theorem was
proved in Ref. [122]. However, it is not applicable in the
presence of C± , and Theorem 1 in the present work is a
nontrivial generalization of the theorem in Ref. [122].
Let us consider class DIII as an example (Table IV).
The original non-Hermitian Hamiltonian H (k) respects
both TRS and PHS:
T+ H ∗ (k) T+−1 = H (−k) , T+ T+∗ = −1;
C− H
T
−1
(k) C−
= −H (−k) ,
∗
C− C−
= +1.
(36)
(37)
As a result, the extended and flattened Hermitian Hamiltonian H̃ (k) respects TRS described by Eq. (30) with
∗
T̃+ T̃+∗ = −1 and PHS described by Eq. (31) with C˜− C˜−
=
+1, as well as additional CS (SLS) described by Eq. (35).
Therefore, the topological classification of the original
non-Hermitian Hamiltonian reduces to that of the Hermitian Hamiltonian in class DIII with additional CS that
commutes with TRS and anticommutes with PHS. The
topology of such Hermitian Hamiltonians is characterized
by the classifying space R4 [213].
B.
Hermitian flattening for line gaps
```

### Theorem: `Theorem 2`
- source file: `10.1103_physrevx.9.041015.pdf.txt`
- lines: 1184-1219

```text
also reduces the topological classification
of a non-Hermitian Hamiltonian to that of a Hermitian
matrix [206–208, 213]. Here, we note that topology of an
anti-Hermitian Hamiltonian H (k) [i.e, H † (k) = −H (k)]
under an imaginary gap is equivalent to that of a Hermitian Hamiltonian iH (k) under a real gap [126]. The
periodic tables under line gaps are also obtained as Tables III-IX.
Let us again consider class DIII as an example (Table IV). The original non-Hermitian Hamiltonian H (k)
respects both TRS and PHS as Eqs. (36) and (37), respectively. In the presence of a real gap, H (k) can be
flattened to a Hermitian Hamiltonian H̄ (k) that belongs
to class DIII, which is characterized by the classifying
space R3 [206–208]. In the presence of an imaginary
gap, on the other hand, H (k) can be flattened to an antiHermitian Hamiltonian H̄ (k) that respects Eqs. (36) and
(37). Importantly, the topology of H̄ (k) is equivalent to
¯ (k) := iH̄ (k), which respects Hermiticity and
that of H̄
¯ (−k) , T T ∗ = −1;
¯ ∗ (k) T −1 = −H̄
T+ H̄
+ +
+
−1
T
∗
¯
¯
C− H̄ (k) C− = −H̄ (−k) , C− C−
= +1.
(38)
(39)
In contrast to the unitary flattening for point gaps,
the flattening procedure changes for line gaps. In fact, a
non-Hermitian Hamiltonian can be flattened into a Hermitian matrix in the presence of a real gap and an antiHermitian matrix in the presence of an imaginary gap.
This property is guaranteed by the following theorem (see
```

### Theorem: `Theorem 2`
- source file: `10.1103_physrevx.9.041015.pdf.txt`
- lines: 1225-3943

```text
(Hermitian flattening for line gaps) — If
a non-Hermitian Hamiltonian H (k) has a line gap in
the real (imaginary) part of its complex spectrum [real
(imaginary) gap], it can be continuously deformed into a
Hermitian (an anti-Hermitian) matrix while keeping the
line gap and its symmetry [Fig. 2 (c)].
Thus, the non-Hermitian Hamiltonian H (k) under an
imaginary gap reduces to the Hermitian Hamiltonian
¯ (k) that respects the two antiunitary symmetries as
H̄
Eqs. (38) and (40). The topology of such Hermitian
Hamiltonians is characterized by the classifying space
C0 [213].
¯ ∗ (k) C −1 = −H̄
¯ (−k) , C C ∗ = +1.
C− H̄
− −
−
(40)
12
TABLE III. Topological classification table for non-Hermitian systems in the complex AZ symmetry class. Non-Hermitian
topological phases are classified according to the AZ symmetry class, the spatial dimension d, and the definition of complexenergy point (P) or line (L) gaps. The subscript of L specifies the line gap for the real or imaginary part of the complex spectrum.
AZ class
A
AIII
Gap
P
L
P
Lr
Li
Classifying space
C1
C0
C0
C1
C0 × C0
d=0
0
Z
Z
0
Z⊕Z
d=1
Z
0
0
Z
0
d=2
0
Z
Z
0
Z⊕Z
d=3
Z
0
0
Z
0
d=4
0
Z
Z
0
Z⊕Z
d=5
Z
0
0
Z
0
d=6
0
Z
Z
0
Z⊕Z
d=7
Z
0
0
Z
0
TABLE IV. Topological classification table for non-Hermitian systems in the real AZ symmetry class. Non-Hermitian
topological phases are classified according to the AZ symmetry class, the spatial dimension d, and the definition of complexenergy point (P) or line (L) gaps. The subscript of L specifies the line gap for the real or imaginary part of the complex spectrum.
AZ class
AI
BDI
D
DIII
AII
CII
C
CI
Gap
P
Lr
Li
P
Lr
Li
P
L
P
Lr
Li
P
Lr
Li
P
Lr
Li
P
L
P
Lr
Li
Classifying space d = 0 d = 1 d = 2 d = 3 d = 4 d = 5 d = 6 d = 7
R1
Z2
Z
0
0
0
2Z
0
Z2
R0
Z
0
0
0
2Z
0
Z2
Z2
R2
Z2
Z2
Z
0
0
0
2Z
0
R2
Z2
Z2
Z
0
0
0
2Z
0
R1
Z2
Z
0
0
0
2Z
0
Z2
R2 × R2
Z2 ⊕ Z2 Z2 ⊕ Z2 Z ⊕ Z
0
0
0
2Z ⊕ 2Z
0
R3
0
Z2
Z2
Z
0
0
0
2Z
R2
Z2
Z2
Z
0
0
0
2Z
0
R4
2Z
0
Z2
Z2
Z
0
0
0
R3
0
Z2
Z2
Z
0
0
0
2Z
C0
Z
0
Z
0
Z
0
Z
0
R5
0
2Z
0
Z2
Z2
Z
0
0
R4
2Z
0
Z2
Z2
Z
0
0
0
R6
0
0
2Z
0
Z2
Z2
Z
0
R6
0
0
2Z
0
Z2
Z2
Z
0
R5
0
2Z
0
Z2
Z2
Z
0
0
R6 × R6
0
0
2Z ⊕ 2Z
0
Z2 ⊕ Z2 Z2 ⊕ Z2 Z ⊕ Z
0
R7
0
0
0
2Z
0
Z2
Z2
Z
R6
0
0
2Z
0
Z2
Z2
Z
0
R0
Z
0
0
0
2Z
0
Z2
Z2
R7
0
0
0
2Z
0
Z2
Z2
Z
C0
Z
0
Z
0
Z
0
Z
0
13
TABLE V. Topological classification table for non-Hermitian systems in the real AZ† symmetry class. Non-Hermitian
topological phases are classified according to the AZ† symmetry class, the spatial dimension d, and the definition of complexenergy point (P) or line (L) gaps. The subscript of L specifies the line gap for the real or imaginary part of the complex spectrum.
AZ† class
†
AI
BDI†
D†
DIII†
AII†
CII†
C†
CI†
Gap
P
L
P
Lr
Li
P
Lr
Li
P
Lr
Li
P
L
P
Lr
Li
P
Lr
Li
P
Lr
Li
Classifying space d = 0 d = 1 d = 2 d = 3 d = 4 d = 5 d = 6 d = 7
R7
0
0
0
2Z
0
Z2
Z2
Z
R0
Z
0
0
0
2Z
0
Z2
Z2
R0
Z
0
0
0
2Z
0
Z2
Z2
R1
Z2
Z
0
0
0
2Z
0
Z2
R0 × R0
Z⊕Z
0
0
0
2Z ⊕ 2Z
0
Z2 ⊕ Z2 Z2 ⊕ Z2
R1
Z2
Z
0
0
0
2Z
0
Z2
R2
Z2
Z2
Z
0
0
0
2Z
0
R0
Z
0
0
0
2Z
0
Z2
Z2
R2
Z2
Z2
Z
0
0
0
2Z
0
R3
0
Z2
Z2
Z
0
0
0
2Z
C0
Z
0
Z
0
Z
0
Z
0
R3
0
Z2
Z2
Z
0
0
0
2Z
R4
2Z
0
Z2
Z2
Z
0
0
0
R4
2Z
0
Z2
Z2
Z
0
0
0
R5
0
2Z
0
Z2
Z2
Z
0
0
R4 × R4
2Z ⊕ 2Z
0
Z2 ⊕ Z2 Z2 ⊕ Z2 Z ⊕ Z
0
0
0
R5
0
2Z
0
Z2
Z2
Z
0
0
R6
0
0
2Z
0
Z2
Z2
Z
0
R4
2Z
0
Z2
Z2
Z
0
0
0
R6
0
0
2Z
0
Z2
Z2
Z
0
R7
0
0
0
2Z
0
Z2
Z2
Z
C0
Z
0
Z
0
Z
0
Z
0
TABLE VI. Topological classification table for non-Hermitian systems in the complex AZ symmetry class with sublattice
symmetry (SLS). Non-Hermitian topological phases are classified according to the AZ symmetry class with additional SLS,
the spatial dimension d, and the definition of complex-energy point (P) or line (L) gaps. The subscript of L specifies the
line gap for the real or imaginary part of the complex spectrum. The subscript of S± specifies the commutation (+) or
anticommutation (−) relation to chiral symmetry: ΓS± = ±S± Γ.
SLS
AZ class
S+
AIII
S
A
S−
AIII
Gap
P
Lr
Li
Classifying space
C1
C1 × C1
C1 × C1
d=0
0
0
0
d=1
Z
Z⊕Z
Z⊕Z
d=2
0
0
0
d=3
Z
Z⊕Z ...
```

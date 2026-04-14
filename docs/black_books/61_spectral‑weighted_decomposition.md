# Spectral‑weighted decomposition as a singular KAN/polar theory with kernel quarantine

## Executive summary

Your repo’s “spectral‑weighted decomposition” doctrine is best understood as a **singular, graded, operator‑first replacement** for the clean global diagonal/polar/KAN decompositions one has for well‑behaved (invertible, diagonalizable, positive) operators. The distinguishing feature is that you are formalising *two different kinds of data*—“spectral shape” and “Weyl/scale gauge”—while simultaneously enforcing a canonical separation between **active** vs **apex/kernel** spectral support.

A tight mathematical analogue exists in several mature domains:

- **Kernel/apex quarantine** is precisely what the **Drazin inverse and its associated projector** are designed to do: isolate the nilpotent/zero‑mode (“generalised kernel”) sector from the invertible sector, canonically. citeturn1search4turn7search0  
- **Active lane split** into **elliptic/phase** versus **hyperbolic/boost/squeezing** is exactly the structure behind the **Bloch–Messiah (Euler) decomposition** and the **Iwasawa/KAN** decompositions for symplectic (Bogoliubov) transformations: passive rotations (phase) + active squeezes (boost) + unipotent shear (often interpretable as “mismatch/anomaly”). citeturn1search5turn8search2turn1search6  
- **Spectral shape + Weyl/scale gauge** is mirrored by **log‑det / trace split** divergences (e.g. log‑det Bregman divergences / Stein loss) and by the information‑geometric viewpoint on scale invariance (e.g. Itakura–Saito type divergences). citeturn11search1turn11search4  
- **Frequency splitting without global time** is algebraically encoded by **Tomita–Takesaki modular theory**: the modular operator \(\Delta\), its logarithm, and modular flow derived from \((\mathcal M,\Omega)\), plus wedge/boost identifications in Bisognano–Wichmann. citeturn4search6turn3search2turn5search4  

What you correctly identify as missing is a **capstone theorem** that states (in one place) that the Drazin/Moore–Penrose/projector/Bogoliubov apparatus provides *the* canonical singular replacement for global diagonal/polar/KAN decomposition—complete with:  
(i) active vs kernel splitting,  
(ii) elliptic vs hyperbolic vs nilpotent factorisation on the active sector, and  
(iii) scale/Weyl gauge separation from shape invariants.

The remainder of this report outlines how such a theorem can be stated rigorously, which constituent steps are already classical theorems, and which steps remain “repo‑programme” (i.e. require conditions and proof engineering).

## The doctrine formalised as operator data plus gauge

### State/operator content as “shape + gauge”
Your slogan  
\[
\text{state/operator data}=\text{spectral shape}+\text{Weyl/scale gauge}
\]
is not merely philosophical: it matches a standard mathematical pattern in which one separates:

- **shape invariants**: eigenvalue ratios, singular values, symplectic eigenvalues, or more generally spectral measures modulo scale;  
- **scale/gauge**: an overall normalisation (determinant, trace, modular scaling, cocycle) that changes under a “Weyl” or “representation” choice.

A canonical finite-dimensional illustration is: for a positive definite matrix \(A\in\mathrm{SPD}(n)\), one can separate
\[
A = (\det A)^{1/n}\;\tilde A,\qquad \det \tilde A=1,
\]
where \((\det A)^{1/n}\) is a pure **scale** and \(\tilde A\) is **shape**. This is exactly the algebraic shadow of log‑det divergences that split into trace-like and \(\log\det\)-like components. citeturn11search1turn11search6  

In operator algebra contexts where \(\det\) is unavailable (type III), the role of “scale” is taken over by modular/cocycle data (Section “Modular …”). citeturn3search2turn4search2  

### Active lane ⊕ apex/kernel lane as Drazin-style support decomposition
Your “active spectral lane ⊕ apex/kernel lane” is mathematically modelled by separating an operator \(A\) into:

- a part where \(A\) is effectively invertible (active dynamics), and  
- a part where \(A\) is nilpotent/defective/zero‑mode (apex/kernel).

The Drazin inverse does exactly that. For a square matrix/operator \(A\), define the index \(k\) by stabilisation of ranks (finite-dimensional) and the Drazin inverse \(A^D\) by the identities (see below). The key point for your doctrine is the canonical idempotent
\[
P_{\text{act}}:=A A^D,
\]
which is a projector onto an “active” range along a “defect” nullspace (precise statement depends on the index). citeturn1search4  

This is precisely the kind of canonical “kernel quarantine” your description demands: it is not an ad hoc split but an invariantly defined projector extracted from \(A\)’s algebraic structure. citeturn1search4turn7search0  

### Inside the active lane: elliptic/phase ⊕ hyperbolic/boost/chiral
On the active sector, the “elliptic vs hyperbolic” split is an instance of **Cartan/KAK** and **Iwasawa/KAN** logic for Lie groups, and of **polar decompositions** for operators:

- “elliptic/phase” corresponds to unitary/orthogonal‑like pieces (compact subgroup \(K\));  
- “hyperbolic/boost/squeeze” corresponds to positive diagonal/Cartan subgroup \(A\);  
- “nilpotent/shear/mismatch” corresponds to unipotent \(N\).

This becomes extremely concrete in the symplectic/Bogoliubov setting, where you literally get factorisations into rotations + squeezes + shears. citeturn1search5turn8search2  

```mermaid
flowchart LR
  A[Operator/state object] --> B[Kernel quarantine]
  A --> C[Active sector]
  B --> BD[Drazin / MP projectors]
  C --> C1[Elliptic / phase]
  C --> C2[Hyperbolic / boost]
  C --> C3[Nilpotent / mismatch]
  C1 --> K[Compact K action (rotations)]
  C2 --> H[Cartan A action (squeezes)]
  C3 --> N[Unipotent N action (shears)]
  K --> G[Gauge: Bogoliubov/Weyl representative changes]
  H --> G
  N --> G
  G --> Inv[Invariants: shape weights + scale/Weyl data]
```

## Rigorous decomposition theorems that match your lanes

This section lists “known theorems” that align almost one‑to‑one with the roles you attribute to Drazin/MP, projectors, phase/boost flows, and Bogoliubov transport.

image_group{"layout":"carousel","aspect_ratio":"16:9","query":["Bloch-Messiah decomposition optical interferometers squeezing diagram","Iwasawa decomposition symplectic matrix KAN schematic","Williamson theorem symplectic diagonalization covariance matrix illustration"],"num_per_query":1}

### Drazin inverse and the canonical active‑vs‑defect projector
A standard (and very usable) definition is:

- The index \(k=\mathrm{ind}(A)\) is the least \(k\ge 0\) such that \(\mathrm{rank}(A^{k+1})=\mathrm{rank}(A^k)\).  
- The Drazin inverse \(A^D\) is the unique matrix satisfying  
\[
A^{k+1}A^D=A^k,\qquad A^DAA^D=A^D,\qquad AA^D=A^DA.
\]
citeturn1search4  

A key structural statement (exactly aligned with your “active lane ⊕ kernel lane”) is that **\(AA^D\) is an idempotent projecting onto the stable range along the stable nullspace** (precise formulation uses \(A^k\)’s range and nullspace). citeturn1search4  

This is the canonical “apex/kernel is not the same kind of spectral weight” statement, expressed purely algebraically.

### Moore–Penrose / Penrose generalised inverse and principal idempotents
Your repo’s repeated use of Moore–Penrose projectors has a deep upstream source: entity["people","Roger Penrose","mathematical physicist"]’s 1955 paper introducing the generalised inverse via a system of equations, with applications including solving linear matrix equations and extracting “principal idempotent elements” and a “new type of spectral decomposition.” citeturn7search0  

This matters because “range/domain projectors” are not optional decorations: they are the invariant way to turn non-invertible operators into **partial isometries + positive parts + defect projections** in a manner compatible with your projector algebra approach. citeturn7search0turn1search4  

### Indefinite/Krein settings: why functional calculus becomes “weighted and conditional”
In a Krein setting (indefinite inner product with a fundamental symmetry), even the meaning of “spectral decomposition” can require additional hypotheses (definitisability, etc.). A concrete rigorous pointer is Kaltenbäck–Skrepek’s construction of a **spectral theorem / functional calculus** for tuples of commuting definitisable self-adjoint bounded operators on a Krein space, explicitly positioned as the “proper analogue” of spectral measures in Hilbert space. citeturn1search11  

This directly supports your “not naïve eigenvalues but spectral‑weighted decomposition theory” point: in indefinite settings, spectral calculus exists but is subtler, and one often needs to treat neutral/kernel sectors separately—exactly the kind of role your Drazin lane plays. citeturn1search11turn8search1  

### Polar decomposition and sign/involution factors in indefinite inner product spaces
A concrete “repo-aligned” polar/factorisation result appears in work on factorisations in indefinite inner product spaces: one can factor a nonsingular matrix into normal pieces including a unitary (phase-like), a self-adjoint with eigenvalues in the right half-plane (hyperbolic/positive-like), and a “normal involutory” factor with a neutral negative eigenspace (grading-like). citeturn8search4  

This kind of theorem is precisely the prototype of your \((J,\varepsilon,K)\) axis logic: phase, boost/positive, and involutory/grade are distinct structural “actors” in indefinite geometry. citeturn8search4  

### Bogoliubov/symplectic transport: Bloch–Messiah, Iwasawa/KAN, and Williamson
Your “diagonal representative + Bogoliubov rotation” intuition maps extremely cleanly onto the well‑developed Gaussian/symplectic toolkit:

- **Williamson normal form**: any real symmetric positive definite matrix can be symplectically diagonalised; its diagonal entries (“symplectic eigenvalues”) are invariants. citeturn0search3turn1search5  
- **Bloch–Messiah (Euler) decomposition**: any symplectic matrix can be decomposed into symplectic rotations (passive/phase) and squeezes (active/hyperbolic). A concrete formula is  
\[
M(\theta,d,\varphi)=R(\theta)\,Z(d)\,R(\varphi),
\]
with \(R(\cdot)\in \mathrm{Sp}(2n,\mathbb R)\cap \mathrm{SO}(2n)\) and \(Z(d)\) built from squeezing generators. citeturn1search6turn1search5  
- **Iwasawa/KAN for symplectic groups**: any symplectic matrix factors uniquely into \(K\cdot A\cdot N\), and there are explicit computational constructions (e.g. via Cholesky factorisation). citeturn8search2turn1search5  

This is already a rigorous, published “capstone theorem template” for the active lane split:

- **\(K\)** ↔ elliptic/phase flow,  
- **\(A\)** ↔ hyperbolic/boost/spectral weights (squeezing),  
- **\(N\)** ↔ shear/mismatch/anomaly lane.

Notably, this is exactly the pattern you describe: “same content, new representative under rotation/boost; preserve the right invariants under the right subgroup; interpret the remaining mismatch as anomaly/dilation data.” citeturn1search5turn8search2turn1search6  

Finally, if you need functional-analytic control for Bogoliubov transport in infinite-dimensional QFT contexts, implementability and representation change are governed by Shale–Stinespring-type conditions, with modern work extending implementability beyond the usual Hilbert–Schmidt criterion. citeturn6search0  

## Modular/relative modular operators as “spectral weight + Weyl gauge”

Here the argument becomes especially tight: Tomita–Takesaki theory shows how a state supplies a canonical “time flow” and hence a frequency split, while “gauge/scale” lives in cocycle/outer automorphism data rather than in eigenvalues alone.

### Tomita–Takesaki: modular flow as intrinsic time
A classical short statement (proved in many places) is:

Given a von Neumann algebra \(M\) with cyclic separating vector \(\xi_0\), the Tomita operator \(S\) has polar decomposition \(S=J\Delta^{1/2}\), where \(J\) is an antiunitary involution and \(\Delta\) is positive self-adjoint, and they satisfy:
\[
J M J = M',\qquad \Delta^{it} M \Delta^{-it}=M\quad(\forall t\in\mathbb R).
\]
This is stated explicitly in a well-known short-proof paper. citeturn4search6  

This is exactly why your repo’s “real Tomita core” feels like it is doing “frequency splitting without global spacetime”: modular time is an **operator-algebraic primitive** derived from \((M,\Omega)\), not from a background Hamiltonian. citeturn4search6turn3search2  

### Thermal time and Weyl/scale gauge as modular cocycle data
In the thermal time hypothesis, entity["people","Alain Connes","mathematician"] and entity["people","Carlo Rovelli","theoretical physicist"] argue that in generally covariant quantum theories, the physical time flow is state‑dependent and given by the modular automorphism group; moreover, a state‑independent notion of time can be associated to the outer automorphism class coming from Connes’ cocycle Radon–Nikodym theorem. citeturn3search2turn3search39  

This cleanly matches your “spectral shape + Weyl/scale gauge” split:

- “shape” ↔ spectral data of the modular Hamiltonian \(\log\Delta\) in the active sector (when meaningful),  
- “Weyl/scale gauge” ↔ changes of representative / cocycle data / outer modular class, not just raw eigenvalues. citeturn3search2turn4search2  

### Bisognano–Wichmann: wedge modularity makes the boost/hyperbolic lane concrete
The wedge case is the archetype where modular flow is geometrically a **boost**: the Bisognano–Wichmann programme ties modular operators of wedge algebras in vacuum to Lorentz boosts and CPT-like reflections, providing the canonical “hyperbolic/boost” interpretation of modular flow and the Unruh thermal structure. citeturn5search4turn5search6  

So, when your repo’s modular layer is described as aiming at “wedge/Unruh closure targets”, it is aligning with one of the most rigid and successful instances of “algebra → geometry → thermodynamics”. citeturn5search4turn3search2  

### Information‑geometry shadows: Itakura–Saito and log‑det divergences as shape vs gauge
Your mention of Itakura–Saito and generalised KL intuitions can be made mathematically sharp in a way that matches “spectral weight + Weyl gauge”:

- Kanamori’s work on **scale‑invariant divergences** treats the Itakura–Saito divergence as a canonical example originally used for power spectral density comparison, within a Bregman divergence framework. citeturn11search4turn11search0  
- A log‑det Bregman **matrix divergence** (“Stein’s loss”) has the exact decomposition you intuit:
\[
\mathcal D_{\log\det}(Q,W)=\mathrm{tr}(QW^{-1})-\log|QW^{-1}|-M,
\]
exhibiting a trace (shape/relative stretching) term and a log‑det (volume/scale) term. citeturn11search1  

That trace/log‑det split is arguably the cleanest finite-dimensional model of your repository phrase “spectral weight content” vs “volume shadow / Weyl gauge content”.

### Orientation flip and “σt versus σ−t”: why doubled-real structures help
Your repo’s “orientation flip law \(\delta\mapsto-\delta\)” has a strong external analogue: in the Jordan operator-algebra generalisation of modular theory, entity["people","Uffe Haagerup","mathematician"] and entity["people","Harald Hanche-Olsen","mathematician"] note that, working only with the Jordan product, one cannot distinguish \(\sigma_t^\varphi\) from \(\sigma_{-t}^\varphi\); they construct a canonical averaged one-parameter family that does generalise. citeturn5search44  

That is exactly the kind of phenomenon where a doubled-real ontology with internal axes (your \(J,\varepsilon,K\)) is not a matter of taste but a structural stabiliser: it encodes what is otherwise “sign-ambiguous” in purely commutative/Jordan data.

## The missing capstone theorem: a precise template and what is rigorous vs programme

Here is a mathematically precise “capstone theorem template” that matches your doctrine and can be apportioned into (A) already‑known theorems vs (B) genuine unification work.

### Capstone theorem template
Let \(A\) be a linear operator (matrix in finite dimensions; densely-defined in infinite dimensions) acting on a graded space with a fixed grading projector system \(P_\pm\) (your \(P_\pm\) correspond to \(P_\pm=\tfrac12(I\pm\varepsilon)\) in typical algebraic treatments). Assume \(A\) may be singular.

**Capstone statement (singular spectral–KAN decomposition).** Under explicit regularity hypotheses (below), there exist canonical projectors and factors such that:

1. (**Kernel quarantine**) There is a canonical idempotent \(P_{\mathrm{act}}\) extracted from \(A\) (Drazin and/or Moore–Penrose) such that  
   \[
   H = H_{\mathrm{act}}\oplus H_{\mathrm{ker}},\quad H_{\mathrm{act}}=\mathrm{ran}(P_{\mathrm{act}}),\quad H_{\mathrm{ker}}=\mathrm{ran}(I-P_{\mathrm{act}}),
   \]
   and \(A|_{H_{\mathrm{act}}}\) is invertible (or at least has controlled spectrum), while \(A|_{H_{\mathrm{ker}}}\) is nilpotent/defective.  
   In finite dimensions, \(P_{\mathrm{act}}=AA^D\) is exactly the Drazin projector onto the stable range along the stable nullspace. citeturn1search4  

2. (**Active sector KAN**) On \(H_{\mathrm{act}}\), \(A\) admits a factorisation into **elliptic/phase**, **hyperbolic/weights**, and **nilpotent/shear** pieces:
   \[
   A_{\mathrm{act}} = K\cdot A_{\text{hyp}}\cdot N
   \]
   where \(K\) lies in a compact‑type subgroup (phase/rotation), \(A_{\text{hyp}}\) lies in a positive diagonal Cartan subgroup (squeezing/boost), and \(N\) is unipotent (shear).  
   In the symplectic/Bogoliubov case, this is rigorously realised by Iwasawa/KAN and Bloch–Messiah decompositions. citeturn1search5turn8search2turn1search6  

3. (**Spectral shape + Weyl gauge**) There is a canonical separation of the “weight spectrum” of \(A_{\text{hyp}}\) into:
   - a **shape invariant** (e.g. eigenvalue ratios or symplectic eigenvalues), and  
   - a **scale invariant** represented by a central scaling (e.g. determinant/trace class quantity in finite settings, or modular cocycle/outer modular class in type III settings).  
   In finite‑matrix information geometry, the trace/log‑det decomposition in log‑det Bregman divergences provides an explicit model of this separation. citeturn11search1turn11search6  
   In algebraic QFT/von Neumann settings, modular/cocycle theory provides the state-dependent vs state-independent “time/scale” separation. citeturn3search2turn4search2  

4. (**Gauge of representative**) Under “Bogoliubov transport” (symplectic conjugations / metaplectic implementers / representation change), the invariants are preserved; the representative changes encode **Weyl gauge** rather than intrinsic shape, and the remaining mismatch is measured by explicit defect/anomaly operators (your “dilation gap”).  
   The feasibility and limits of implementing such transformations on a chosen Hilbert representation are governed by Shale–Stinespring-type conditions (or controlled extensions beyond them). citeturn6search0  

### Which components are already rigorous theorems?
The following blocks are already “classical theorem-grade” (with stable references):

- Drazin inverse identities and the projector interpretation of \(AA^D\). citeturn1search4  
- Penrose generalised inverse framework and use of idempotents / spectral decomposition ideas. citeturn7search0  
- KAN/Iwasawa‑type decompositions for symplectic matrices and explicit computational constructions. citeturn8search2turn1search5  
- Bloch–Messiah decomposition and its phase/squeeze/phase meaning. citeturn1search6turn1search5  
- Williamson normal form as canonical extraction of “symplectic spectral shape”. citeturn0search3turn1search5  
- Tomita–Takesaki theorem and modular flow. citeturn4search6turn4search2  
- Bisognano–Wichmann wedge modularity as boost/Unruh structure. citeturn5search4turn5search6  
- Functional calculus adaptations needed in Krein settings under definitisability assumptions. citeturn1search11  

### What remains “programme” (repo-capstone engineering)?
What is still nontrivial is knitting these ingredients into a single **graded, singular, doubled-real** theorem with controlled hypotheses:

- In indefinite/Krein settings, “spectral calculus” is delicate and typically requires definitisability and careful functional calculus; your repo’s “spectral-weighted” stance strongly suggests you must specify exactly which calculus (continuous vs Borel, bounded vs unbounded, definitisable vs general). citeturn1search11turn8search1  
- For singular operators, global KAN/polar decompositions do not automatically exist without conditions; your capstone theorem must state **when** the Drazin/MP split commutes appropriately with the KAN decomposition of the active part. citeturn1search4turn1search5  
- If part of the “Weyl gauge” is genuinely type III / outer modular data, translating “volume shadow” into a rigorous invariant requires specifying the operator-algebraic context (weights, standard form, cocycles). citeturn3search2turn4search0  

This is exactly where a “synthesis engine” earns its name: not by inventing new fundamental theorems, but by **stating the correct composite theorem with correct hypotheses, and proving the commuting diagrams** between Drazin projectors, modular flows, Bogoliubov gauges, and grading involutions.

## Next research tasks and formalisation targets

### High-value mathematical tasks (capstone theorem proof plan)
A workable route to the missing capstone theorem is to prove it first in the “Gaussian/symplectic finite” model, then lift:

1. **Finite symplectic prototype**: formalise that for a positive definite covariance-like matrix \(M\), Williamson gives a canonical diagonal \(D\) and the symplectic eigenvalues are invariants; then show that any symplectic change of representative factors as Bloch–Messiah (phase–squeeze–phase) and/or KAN. citeturn1search5turn8search2  
2. **Add singularity**: incorporate Drazin/MP to treat semidefinite or rank-deficient matrices, making the “apex lane” explicit and functorial under gauge actions. Use the projector facts about \(AA^D\) and Penrose’s idempotent perspective. citeturn1search4turn7search0  
3. **Lift to operator algebras**: replace determinant/trace by modular data: use Tomita–Takesaki to represent frequency splitting intrinsically; interpret “Weyl gauge” as cocycle/outer modular data in Connes–Rovelli’s sense. citeturn4search6turn3search2  
4. **Connect to wedge modularity**: target a Bisognano–Wichmann-like endgame where “hyperbolic/boost lane” matches modular flow on local algebras; treat “orientation flip” carefully (Jordan ambiguity shows why encoding the sign may require extra structure). citeturn5search4turn5search44  

### Lean formalisation targets (small table)
Below is a minimal, “thick surface first” formalisation ladder aligned with what you described (projectors + generalised inverses + flows + pairings):

| Formalisation target | Minimal theorem surface to prove | Why it is a capstone prerequisite |
|---|---|---|
| Drazin projector calculus | \(AA^D\) is a projector onto stable range along stable nullspace; functoriality under similarity. citeturn1search4 | This *is* your apex/kernel separation, made canonical. |
| Moore–Penrose / Penrose idempotents | Penrose equations ⇒ range/kernel projectors; “principal idempotents” extraction patterns. citeturn7search0 | Provides canonical range/domain projectors and mismatch measures. |
| Symplectic KAN + Bloch–Messiah | State and prove \(S = KAN\) and \(S = RZR\) for symplectic matrices; identify phase vs squeeze. citeturn1search5turn8search2turn1search6 | This is the cleanest formal instance of your elliptic/hyperbolic split. |
| Modular core | \(S=J\Delta^{1/2}\), \(JMJ=M'\), \(\Delta^{it}M\Delta^{-it}=M\); define \(\log\Delta\) where allowed. citeturn4search6turn4search2 | Supplies a canonical “frequency split” from algebra+state. |
| Log‑det / Itakura–Saito divergences | Prove trace/logdet decomposition and scale invariance statements in the finite SPD setting. citeturn11search1turn11search4 | Packages “shape vs scale” as a reusable lemma family. |

### How this relates back to palatial twistor goals
You are effectively building the operator-algebraic infrastructure that Palatial/bi‑twistor programmes gesture at: shift the primitive layer from “manifold points” to “operator algebra with canonical involutions, flows, and projectors.” Penrose’s palatial twistor theory explicitly proposes a non-commutative holomorphic “twistor Heisenberg algebra” to overcome a chiral obstruction (googly). citeturn9search0turn9search5  

Your capstone theorem, once proved, would be a precise operator‑theoretic analogue of the key twistor ambition: **replace global geometric diagonalisation (which fails in the presence of singularities and gauge) by canonical projector + generalised inverse + transport decompositions**, all while keeping “frequency/time” and “helicity/chirality” from being conflated at the foundational level. citeturn9search5turn3search2
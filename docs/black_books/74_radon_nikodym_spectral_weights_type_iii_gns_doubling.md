# Radon–Nikodym derivatives as normal forms for spectral weights, with Type III / GNS “doubling” and spectral comparison ideas

## Executive summary

Radon–Nikodym (RN) derivatives are best understood as a **normal-form mechanism**: they turn “one weight relative to another” into an explicit *density* object. In the commutative case this density is a function \(f=\frac{d\nu}{d\mu}\); in the noncommutative case (von Neumann algebras) it becomes a **positive operator affiliated with the algebra (or a canonical cocycle/relative modular object)**. citeturn7view4turn5view1turn29view0turn28view0

Tomita–Takesaki theory provides the operator-algebraic “normal form” behind thermal equilibrium: from a cyclic separating GNS vector \(\Omega\) one obtains the **modular conjugation** \(J\) and **modular operator** \(\Delta\) via a polar decomposition \(S=J\Delta^{1/2}\), and \(\Delta^{it}\) yields the modular automorphism group. This modular structure is precisely where noncommutative RN derivatives live (e.g. Connes’ cocycle derivative \((D\varphi:D\psi)_t\)). citeturn5view5turn28view0turn30view0

For Type III von Neumann algebras (no semifinite trace), weights and modular theory are not optional: they are the replacement for “densities w.r.t. a trace”. Connes’ invariants and the (Connes–Takesaki) **flow of weights** expose a canonical “scale” structure (trace-scaling actions on a core algebra), which is the cleanest rigorous analogue of your “Weyl gauge scale” language. citeturn26view1turn28view0turn26view0turn14view3

Your Lean sketch (a doubled/Krein space, modular mirror \(J\)-like maps, KMS factors \(e^{-\omega/2}\), and an “active lane” projector) can be read as an abstracted version of (i) **standard form** \((M,H,J,P)\) and (ii) **thermofield double / Araki–Woods doubling** of GNS representations for KMS states. In existing mathlib, classical RN derivatives are already formalised, and von Neumann algebras exist at the definitional level, but GNS and Tomita–Takesaki modular theory are largely not yet formalised; in practice, a **finite-dimensional (matrix) modular theory** layer plus a “standard-form skeleton” is the realistic route. citeturn7view4turn7view3turn32view0turn5view3turn26view3turn27view0turn27view1

## RN derivatives for von Neumann weights as a noncommutative normal form

### Weights as “noncommutative measures”

A (normal, semifinite, faithful) weight \(\varphi\) on a von Neumann algebra \(M\) is the noncommutative counterpart of a \(\sigma\)-finite measure: it assigns “mass” to positive elements and yields an \(L^2\)-type completion. citeturn6view4turn26view1 In the commutative case, this perspective is literal: von Neumann algebras generalise measure theory, and the classical RN theorem is already implemented in mathlib (`rnDeriv`, `withDensity_rnDeriv_eq`). citeturn26view1turn7view4

### Pedersen–Takesaki: RN derivatives are affiliated positive operators

The foundational noncommutative RN theorem of entity["people","Gert K. Pedersen","operator algebraist; rn weights"] and entity["people","Masamichi Takesaki","operator algebraist; modular theory"] (Acta Math., 1973) constructs new weights from an initial faithful normal semifinite weight \(\varphi\) and a positive self-adjoint operator \(h\) affiliated with \(M\), producing derived weights of the form \(\varphi(h\cdot)\) (or symmetrically \(\varphi(h^{1/2}\,\cdot\,h^{1/2})\)). In particular, they emphasise that under modular/KMS-type invariance assumptions, such a weight can be written in that “density-operator” form with **\(h\) unique** (up to the appropriate notion of affiliation/commutation). citeturn5view0turn5view1turn5view2turn28view0

This is the precise noncommutative analogue of \(\nu=f\mu\): the “density” is no longer a function but an *affiliated operator*.

### Vaes and Connes cocycle derivatives: RN data can be expressed as a cocycle along modular flow

entity["people","Stefaan Vaes","operator algebraist; rn theorem"] generalises Pedersen–Takesaki by allowing **relative invariance** and by expressing the RN relationship via Connes’ cocycle derivative \([D\psi:D\varphi]_t\) together with an affiliated positive operator \(\delta\) (and an invariance factor \(\lambda\)). He states that one constructs weights \(\varphi(\delta^{1/2}\,\cdot\,\delta^{1/2})\) under modular covariance and that, conversely, weights whose modular groups commute (or are relatively invariant) arise this way, with uniqueness of the affiliated data encoded by the cocycle relation. citeturn29view0turn28view0

This explains the RN–normal-form slogan at operator level:

- **commutative:** RN derivative \(f\) is a density against a base measure; citeturn7view4  
- **von Neumann:** RN derivative is an affiliated operator \(\delta\) and/or a canonical **unitary cocycle** \((D\varphi:D\psi)_t\) intertwining modular dynamics. citeturn29view0turn28view0  

## Standard form, GNS doubling, and the “twin-wave” picture

Your phrases “twin wave representation”, “paired spectral spinors”, and “paired Krein/Kremer pairs” are **not standard terminology in operator algebra**, so the link depends on an interpretation. The most mathematically canonical interpretive match is:

- “paired objects” \(\approx\) the **modular pair** \((J,\Delta)\) from Tomita–Takesaki; or the **left/right commuting representations** \(M\) and \(M'\) on a standard form Hilbert space. citeturn5view5turn5view3  
- “spectral spinors” \(\approx\) vectors in the **natural cone** \(P\) representing weights/states in standard form. citeturn5view3turn26view3turn5view4  

### Haagerup standard form: a canonical normal form for the representation itself

entity["people","Uffe Haagerup","operator algebraist; standard form"] introduces the **standard form** as a quadruple \((M,H,J,P)\) where \(M\) acts on \(H\), \(J\) is a conjugate-linear isometric involution, and \(P\subseteq H\) is a self-dual cone, satisfying:

- \(J M J = M'\) (commutant duality),
- \(J\xi=\xi\) for \(\xi\in P\) (fixed-point “real positivity”),
- \(a\,J a\,J\,P\subseteq P\) for \(a\in M\), plus a centre compatibility condition. citeturn5view3turn26view3

Haagerup also stresses **uniqueness** of standard form up to a unique unitary implementing *-isomorphisms. This is a strong “normal form” principle: it’s a canonical arena where “left” and “right” (commutant) are simultaneously present. citeturn5view3turn26view3

In your Lean code, the role of a “mirror” `modular_j` and a “balanced” condition resembles the standard-form condition \(J\xi=\xi\) on the natural cone (or a close variant after identifying your doubled/Krein space with a standard-form Hilbert space). citeturn5view3turn26view3

### Tomita–Takesaki: the modular pair \((J,\Delta)\) is the canonical “paired normal form”

Given a von Neumann algebra \(M\subseteq B(H)\) and a cyclic separating vector \(\Omega\), define the densely defined anti-linear operator \(S_0(A\Omega)=A^*\Omega\). Its closure has polar decomposition
\[
S = J\Delta^{1/2} = \Delta^{-1/2}J,
\]
where \(J\) is the (antiunitary) modular conjugation and \(\Delta\) is the positive self-adjoint modular operator; \(\Delta^{it}\) implements the modular automorphism group. citeturn5view5turn30view0

This is exactly the place where “spectral theorem normal form” enters: \(\Delta\) is self-adjoint, so \(\Delta^{it}\) exists by functional calculus, and the modular dynamics is built from this spectral calculus. citeturn5view5turn30view0

### Doubling / “twin wave”: thermofield double and Araki–Woods as explicit GNS-type doubles

Two standard “doubling” constructions in the literature make your code’s “two partitures” and \(e^{-\omega/2}\) factors feel extremely close to established models.

**Thermofield double (TFD).** entity["people","Edward Witten","physicist; tfd and type iii"] describes TFD as taking \(\rho^{1/2} \propto e^{-\beta H/2}\) and *regarding it as a vector in the tensor product of two copies of the Hilbert space*, i.e. a purification on a doubled space. He explicitly notes that in the infinite-volume limit the naturally generated von Neumann algebra is Type III and that time translations become outer automorphisms. citeturn27view0

This matches your code-level choice `kms_correlation := exp(-ω/2)` at the level of “half-Boltzmann” amplitudes: TFD weights appear with \(\beta/2\) in the exponent precisely because the purified vector is \(\rho^{1/2}\). citeturn27view0

**Araki–Woods representation.** entity["people","Christian Gérard","mathematician; kms araki-woods"] presents the Araki–Woods representation as a realisation of the GNS representation for a KMS state on a Weyl algebra on a **doubled Hilbert space** (Fock space over \(h\oplus \bar h\)), explicitly giving the representation and KMS state structure. citeturn27view1

So, in rigorous operator-algebra terms, “twin wave representation” can be read as: **choose a KMS state, take its GNS representation, and (often) realise it explicitly on a doubled Hilbert space so that left/right (or tilde/non-tilde) structures become manifest**. citeturn27view0turn27view1turn30view1

## Type III factors and the modular “scale” as a Weyl-like gauge datum

### Type III means “no semifinite trace”, hence weights become structural

Takesaki highlights a defining feature: a von Neumann algebra \(M\) is Type III if it does not admit a non-trivial semifinite normal trace, and the absence of traces historically made Type III algebras appear “pathological” until modular theory clarified their structure. citeturn26view1turn28view0

This is the operator-algebraic reason your “spectral weights” are central in Type III contexts: in Type I/II settings, densities can often be expressed w.r.t. a trace; in Type III settings, **weights + modular dynamics replace traces**. citeturn26view1turn28view0turn5view0

### Connes invariants and the scale group \(S(M)\)

entity["people","Alain Connes","mathematician; type iii factors"] defines invariants (notably \(S(M)\)) tied to modular theory and uses them to split Type III factors into \(\mathrm{III}_0\), \(\mathrm{III}_\lambda\) \((0<\lambda<1)\), and \(\mathrm{III}_1\), with \(S(M)\) behaving like a subgroup of \(\mathbb R_+^\times\) capturing modular scaling information. citeturn26view0turn26view2

This is the mathematically precise anchor for your “Weyl gauge scale” instinct: modular theory canonically produces a **multiplicative scale set** (or flow) describing how weights transform under modular automorphisms. citeturn26view0turn28view0

### Core decomposition and trace-scaling flow: a canonical “scale bundle”

A particularly transparent “scale normal form” appears in Takesaki’s summary: each \(M\) gives rise to a **core** \(\widetilde M\) with a faithful semifinite normal trace \(\tau\) and a one-parameter automorphism group \(\{\theta_s\}\) such that
\[
\tau\circ \theta_s = e^{-s}\tau,
\]
and one recovers \(M\) as a fixed-point algebra and as a crossed product (\(M \cong \widetilde M \rtimes_\theta \mathbb R\), in the form he sketches). citeturn28view0

Interpreting \(\theta_s\) as a “Weyl rescaling” is reasonable at the level of intuition: it is literally a **trace-scaling gauge** action on the core, and “scale” is not auxiliary data but part of the canonical decomposition of Type III structure. citeturn28view0turn26view0

For practical modelling, this suggests that “compare spectra/scales” can mean comparing:

- spectra of modular operators \(\Delta_\varphi\),
- Connes cocycles \((D\varphi:D\psi)_t\),
- or the induced flows/invariants like \(S(M)\) / flow of weights, depending on how coarse a notion of equivalence you want. citeturn28view0turn29view0turn26view0turn14view3

## Spectral theorem, relative modular spectra, and “proximities” from spectral divergences

### The spectral theorem enters twice: functional calculus for \(\Delta\), and spectral decompositions for comparison

Modular theory uses the spectral theorem (functional calculus) in an essential way: \(\Delta\) is positive self-adjoint, hence \(\Delta^{it}\) makes sense and yields the modular automorphism group, and this is already presented explicitly in expository modular texts. citeturn5view5turn30view0

The “paired modular objects” viewpoint becomes even sharper with **relative modular operators**: operator-algebraic relative entropy and Connes cocycles are spectral objects attached to a pair of states/weights.

### Relative modular operator and Araki(-Uhlmann) relative entropy as a canonical spectral distance for weights

entity["people","Dénes Petz","mathematician; quantum entropy"] states that for faithful normal states \(\varphi,\omega\) on a von Neumann algebra \(M\), relative entropy can be defined using the **relative modular operator** \(\Delta(\varphi,\omega)\); if \(\Omega\) is the vector representative of \(\omega\) in the natural cone \(P\), then
\[
S(\varphi,\omega) = -\langle \log \Delta(\varphi,\omega)\,\Omega,\ \Omega\rangle.
\]
citeturn5view4

This is the rigorous operator-algebraic analogue of “compare spectra and scales”: relative entropy is literally a function of the spectrum of a (relative) modular operator. It lives naturally in Type III settings because it is defined without needing a trace. citeturn5view4turn28view0

### Itakura–Saito and log-det divergences as “spectral” comparison templates

If your goal is to define geometric “interaction/proximity” measures by comparing *spectra* (as you suggest with “Itakura–Saito wise”), there is a clean ladder of increasing noncommutativity:

1. **Scalar / diagonal case:** the Itakura–Saito divergence on \(\mathbb R^n_{++}\) is
   \[
   d_{\mathrm{IS}}(y,x)=\sum_i\left(\frac{y_i}{x_i}-\log\frac{y_i}{x_i}-1\right),
   \]
   and is explicitly used to compare power spectra in signal processing. citeturn21view0turn22view2

   A key structural property is its **scale invariance** in each component (it depends on ratios \(y_i/x_i\)); this matches your “gauge scale” intuition at the level of a divergence invariant under uniform amplitude rescaling. citeturn21view0

2. **Matrix / SPD case:** a standard matrix analogue is the log-det (Burg/Stein) divergence
   \[
   D_{\log\det}(X,Y)=\operatorname{tr}(X Y^{-1})-\log\det(XY^{-1})-n,
   \]
   which is again a spectral function of the eigenvalues of \(XY^{-1}\). citeturn22view1turn22view2

3. **Von Neumann algebra case:** Araki-style relative entropy replaces “\(\log\det\)” with “\(\log \Delta\)” and uses the relative modular operator rather than \(XY^{-1}\), preserving the core idea: compare two “densities” by a logarithmic spectral functional of their relative object. citeturn5view4turn29view0turn28view0

So, mathematically, “compare spectra and scales” can be made precise by choosing *which* spectral object you compare:

- For finite matrices, compare eigenvalues of \(XY^{-1}\) (log-det family) or use quantum relative entropy; citeturn22view2  
- For general von Neumann algebras, compare the spectrum of the relative modular operator \(\Delta(\varphi,\omega)\), or equivalently use Araki/Petz-style formulas and Connes cocycles. citeturn5view4turn29view0turn28view0

### Where your “active lane projector” fits: support projections and spectral cutting

Your Lean code uses a Drazin-based “active projector” \(\Pi_{\mathrm{act}} = A A^D\) to isolate an “active lane”. In modular theory the direct analogue is the **support projection** \(s(\varphi)\) of a weight/state and the passage to the reduced algebra \(M_{s(\varphi)}\), the locus where modular dynamics makes sense and where the weight is faithful. Takesaki states that the modular automorphism group \(\{\sigma_t^\varphi\}\) is defined on the reduced algebra \(M_{s(\varphi)}\) determined by the support projection \(s(\varphi)\). citeturn28view0

Conceptually: both Drazin projectors and support projections are **spectral cutters**, isolating the part of the structure that is dynamically/invertibly accessible (invertible part away from the “kernel”/singular horizon). citeturn28view0turn5view0

## A Lean (mathlib) formalisation angle for your architecture

You mentioned `InfoGeometry.Krein.DoubledSpace`, modular involutions, and Drazin operators, and you pasted Lean code with a doubled space, a modular mirror, and KMS-inspired factors. Without inspecting your repository (unspecified), the most realistic formalisation path is to separate **what mathlib already has** from what must be built.

### What mathlib already supports

- **Classical Radon–Nikodym theorem for measures** is formalised (`rnDeriv`, `withDensity_rnDeriv_eq`, etc.). citeturn7view4  
- **Von Neumann algebras exist as definitions** (abstract `WStarAlgebra` and concrete `VonNeumannAlgebra`), with an explicit note that major equivalence projects remain. citeturn7view3  

### What is currently missing or very incomplete

A public Lean4 noncommutative geometry status slide deck notes that **GNS construction from a state on a C\(^*\)-algebra is not in mathlib**, and functional calculus for self-adjoint operators is only partial in the ecosystem they survey. citeturn32view0

That aligns with expectations: fully formalising (i) weights, (ii) affiliated operators, (iii) Tomita–Takesaki modular theory, and (iv) Pedersen–Takesaki / Connes RN theorems is a major programme.

### Practical recommendation: a staged “normal forms” formalisation that matches your code

A robust path—compatible with your doubled-space/KMS design—looks like:

1. **Finite-dimensional “laboratory”: \(M_n(\mathbb C)\) modular theory.**  
   Use matrices and the Hilbert–Schmidt space as the GNS Hilbert space. For a faithful state \(\omega(A)=\mathrm{tr}(\rho A)\) with \(\rho>0\), modular objects are explicit:
   - \(\Delta_\rho(X)=\rho\,X\,\rho^{-1}\),
   - \(J(X)=X^*\),
   - relative modular operator becomes \(\Delta_{\rho|\sigma}\) built from \(\rho\) and \(\sigma\).  
   This finite-dimensional picture is directly consistent with the KMS discussion and with the “\(\rho^{1/2}\)” thermofield double vector idea. citeturn30view1turn27view0turn22view2

2. **Abstract “standard form skeleton” (your doubled/Krein space as a proxy).**  
   Axiomatise something like Haagerup standard form: a typeclass/structure containing \((M,H,J,P)\) and the standard-form laws \(JMJ=M'\), \(J\xi=\xi\) for \(\xi\in P\), etc. This exactly matches the style of your `IsBalanced` property if you interpret “balanced spectral spinors” as lying in a \(J\)-fixed positive cone. citeturn5view3turn26view3

3. **Noncommutative RN layer as a *specification* first, not a construction.**  
   Represent RN derivatives by a predicate capturing Vaes/Pedersen–Takesaki-style statements:
   - existence/uniqueness of \(\delta\) affiliated with \(M\),
   - cocycle condition for \([D\psi:D\varphi]_t\),
   - covariance w.r.t. modular automorphisms. citeturn29view0turn28view0turn5view0turn5view1  
   Early on, you can instantiate this predicate only in the finite-dimensional matrix model.

4. **Spectral proximity layer (Itakura–Saito / log-det / relative entropy).**  
   Implement spectral divergences for:
   - vectors/diagonal spectra (Itakura–Saito),
   - SPD matrices (log-det divergence),
   - then connect (in the finite-dimensional vN model) to relative entropy as a spectral functional of the relative modular operator. citeturn21view0turn22view2turn5view4  

### Dependency flowchart for a Lean roadmap

```mermaid
flowchart TD
  A[Measure RN theorem in mathlib] --> B[Finite-dimensional matrix states as densities ρ]
  B --> C[Explicit modular objects: J, Δ on Hilbert–Schmidt space]
  C --> D[Finite-dimensional KMS & thermofield-double vector ρ^(1/2)]
  C --> E[Relative modular operator Δ(φ,ω)]
  E --> F[Araki/Petz relative entropy as spectral functional]
  B --> G[SPD/log-det and Itakura–Saito divergences for spectra]
  D --> H[Abstract doubled-space API (your DoubledSpace) as a standard-form skeleton]
  H --> I[Abstract standard form axioms (M,H,J,P)]
  I --> J[Noncommutative RN spec: cocycles & affiliated δ (Pedersen–Takesaki / Vaes)]
```

This plan explicitly respects the fact that full Jordan/functional-calculus-heavy von Neumann algebra machinery is not currently “out of the box” in mathlib, while still letting you build a rigorous internal theory aligned with your architecture.

### Table: where the RN/normal-form mechanisms live

| Context | “Object being compared” | RN derivative object (normal form) | Existence status | High-value references |
|---|---|---|---|---|
| Classical measure theory | \(\nu\ll\mu\) | \(f=\frac{d\nu}{d\mu}\), \(\nu=f\mu\) | Yes under Lebesgue decomposition hypotheses | mathlib RN theorem docs citeturn7view4 |
| Semifinite von Neumann algebra (trace available on a core / or \(B(H)\)) | weights \(\psi \le C\varphi\) etc. | affiliated positive operator \(h\) giving \(\psi=\varphi(h\cdot)\) / \(\varphi(h^{1/2}\cdot h^{1/2})\) | Yes under Pedersen–Takesaki hypotheses | Pedersen–Takesaki RN theorem citeturn5view0turn5view1 |
| General von Neumann algebra (incl. Type III) | weights/states and their modular groups | Connes cocycle derivative \((D\varphi:D\psi)_t\) and (when available) affiliated \(\delta\) with modular covariance | Exists as modular data; “density w.r.t trace” generally not available in Type III | Takesaki modular/cocycle summary citeturn28view0; Vaes RN theorem citeturn29view0 |
| Standard form / GNS “twin wave” | representations of \(M\) plus commutant \(M'\) | standard form \((M,H,J,P)\), turning weights into vectors (“spectral spinors”) | Standard form exists and is unique (theory-level); formalisation in Lean is largely future work | Haagerup standard form citeturn5view3turn26view3 |
| Thermal/KMS doubling (TFD, Araki–Woods) | KMS states ↔ cyclic separating vectors in doubled space | purified vector \(\rho^{1/2}\) in \(H\otimes H\), or doubled Fock representation | Yes in operator-algebraic/QSM frameworks | Witten on TFD and Type III citeturn27view0; Gérard on Araki–Woods citeturn27view1 |

## Suggested sources with URLs (copy/paste list)

```text
Mathlib (classical RN theorem):
https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.html

Mathlib (von Neumann algebra definitions):
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/VonNeumannAlgebra/Basic.html

Pedersen–Takesaki (Acta Math. 1973) – noncommutative RN theorem for weights:
https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6142-11511_2006_Article_BF02392262.pdf

Haagerup (Math. Scand. 1975) – standard form of von Neumann algebras:
https://www.mscand.dk/article/viewFile/11606/9622

Vaes (J. Operator Theory 2001) – RN theorem for von Neumann algebras (commuting/relatively invariant weights):
https://jot.theta.ro/jot/archive/2001-046-003/2001-046-003-002.pdf

Takesaki (short notes) – modular automorphism group, Connes cocycle derivative, core decomposition:
https://www.ms.u-tokyo.ac.jp/~yasuyuki/pre-takesaki.pdf

Summers (arXiv 2005) – Tomita–Takesaki modular theory overview:
https://arxiv.org/pdf/math-ph/0511034

Petz (CMP 1988) – relative entropy via relative modular operator and natural cone:
https://math.bme.hu/~petz/pdf/35variational.pdf

Witten (arXiv 2021/2022) – thermofield double as ρ^{1/2} in doubled Hilbert space; Type III discussion:
https://arxiv.org/pdf/2112.11614

Gérard–Jäkel (Araki–Woods representation for KMS states, GNS on a doubled space):
https://www.imo.universite-paris-saclay.fr/~christian.gerard/publis/rel-kms3.pdf

Itakura–Saito divergence (arXiv 2011, explicit formula):
https://arxiv.org/pdf/1106.4198

Bregman/log-det/IS as spectral divergences (course notes):
https://www.seas.ucla.edu/~vandenbe/236C/lectures/bregman.pdf

Lean4 NCG status slide noting “GNS construction … No” in mathlib:
https://www.cirm-math.fr/RepOrga/3196/Slides/4-Stephan.pdf
```

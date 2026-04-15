# Radon–Nikodym derivatives and normal forms

## Executive summary

The most direct “link” between the Radon–Nikodym theorem and various *normal-form* ideas is that Radon–Nikodym derivatives provide the **coordinate change / density transform** that turns an abstract object (a measure, a spectral measure, or a weight on an operator algebra) into a **canonical representation relative to a chosen reference**. In commutative measure theory this is literally “\(\nu = f\,\mu\)” for \(\nu\ll\mu\). citeturn0search0turn1view0

In spectral theory (the normal-form theory for **normal/self-adjoint operators**), the “multiplication form” of the spectral theorem represents an operator as multiplication by the coordinate function in an \(L^2(\mu)\)-space. Changing the generating vector changes the representing measure by an explicit Radon–Nikodym factor (often \(|g|^2\)). citeturn2view1turn2view0

In von Neumann algebra theory, **noncommutative Radon–Nikodym theorems** (e.g. Pedersen–Takesaki and later generalisations) express one weight/functional in terms of another via a **unique positive operator** (the “Radon–Nikodym derivative” in the noncommutative sense), giving a powerful normal-form parametrisation of weights. citeturn1view1turn1view3turn1view2

## Radon–Nikodym as a canonical normal form for measures

Let \((X,\Sigma)\) be a measurable space, and let \(\mu,\nu\) be \(\sigma\)-finite measures with \(\nu\ll\mu\). The Radon–Nikodym theorem states that there exists a measurable \(f\ge 0\) such that
\[
\nu(A)=\int_A f\,d\mu\quad\text{for all }A\in\Sigma,
\]
and \(f\) is unique \(\mu\)-almost everywhere; \(f\) is written \(d\nu/d\mu\). citeturn0search0turn1view0

This is a genuine **normal form** statement:
- “\(\nu\) is absolutely continuous with respect to \(\mu\)” becomes “\(\nu\) is *multiplication by a density* \(f\) against a fixed base measure \(\mu\).” citeturn0search0turn1view0

The canonical aspect becomes even clearer via the **Lebesgue decomposition theorem**, which splits a measure into an absolutely continuous part and a singular part, uniquely. In many spectral-theory texts this is refined further into the triple decomposition
\[
\mu=\mu_{\mathrm{ac}}+\mu_{\mathrm{cs}}+\mu_{\mathrm{pp}}
\]
(absolutely continuous, singular continuous, and pure point). This is a “normal form” for measures relative to Lebesgue measure and the atomic/continuous dichotomy. citeturn1view0turn2view0

## Spectral theorem normal forms and where Radon–Nikodym enters

### Multiplication representation

A core normal-form theorem for (bounded) self-adjoint or normal operators on a Hilbert space is the **spectral theorem**, which represents the operator on a suitable invariant subspace as multiplication by the real variable on an \(L^2\)-space. One standard construction (especially in physics/maths notes) proceeds by associating a **scalar spectral measure** \(\mu_\psi\) to a vector \(\psi\) and the operator \(A\). citeturn2view0turn2view1

Concretely, in the “multiplication form” described in the spectral theorem notes you can define the cyclic subspace
\[
H_\psi := \overline{\{f(A)\psi : f\in \mathcal S(\mathbb R)\}}
\]
and obtain a unitary \(U_\psi : H_\psi \to L^2(\mathbb R,d\mu_\psi)\) such that (on \(H_\psi\))
\[
U_\psi A U_\psi^{-1} = (f\mapsto x f(x)).
\]
citeturn2view1turn2view0

This *is* a “normal form”: instead of handling \(A\) abstractly, you handle multiplication by \(x\).

### Radon–Nikodym derivatives between spectral measures

Here is the key RN link: if you replace the cyclic vector \(\psi\) by \(g(A)\psi\), the associated spectral measures change by a Radon–Nikodym density.

In the spectral theorem notes one finds the explicit relation
\[
d\mu_{g(A)\psi} = |g|^2\, d\mu_\psi,
\]
i.e. \(\mu_{g(A)\psi}\ll \mu_\psi\) and
\[
\frac{d\mu_{g(A)\psi}}{d\mu_\psi} = |g|^2 \quad (\mu_\psi\text{-a.e.}).
\]
citeturn2view1turn2view0

So in the multiplication-picture, “changing vectors” corresponds to changing the measure by a Radon–Nikodym factor, and the unitary map between the two \(L^2\)-models involves multiplication by \(\sqrt{d\mu'/d\mu}\) (up to phase conventions). This is exactly the same structural role RN derivatives play in ordinary measure theory: they describe the change of density between equivalent measure representations. citeturn0search0turn2view1

### Normal-form decompositions of spectrum via measure decompositions

Once you have spectral measures \(\mu_\psi\), the Lebesgue decomposition yields canonical “types” (ac / singular continuous / pure point). The spectral theorem notes build corresponding invariant subspaces \(H_{\mathrm{ac}}, H_{\mathrm{cs}}, H_{\mathrm{pp}}\) and decompose the spectrum accordingly. citeturn2view0turn1view0

This shows a second strong link: Radon–Nikodym/Lebesgue decomposition is the measure-theoretic tool used to produce a **canonical decomposition** (“normal form”) of a normal operator’s spectral behaviour. citeturn2view0turn1view0

### Relation to finite-dimensional “normal forms”

If \(A\) is a *normal matrix* (unitarily diagonalizable), the spectral measure is purely atomic (a finite sum of Dirac masses at eigenvalues). In that finite-dimensional setting, Radon–Nikodym derivatives between spectral measures reduce to **ratios of point-masses** on eigenvalues (when the support matches), i.e. a discrete density. This is the finite analogue of the \(|g|^2\) density above. citeturn2view1turn2view0

By contrast, for **Jordan normal form** of general (possibly non-normal) matrices, Radon–Nikodym is not the natural tool; the natural analytic tool there is the holomorphic/functional calculus for Jordan blocks or the algebraic minimal polynomial machinery. citeturn25search0turn26view0

## Noncommutative Radon–Nikodym theorems as normal forms for weights

In von Neumann algebra theory, there is a powerful family of “noncommutative Radon–Nikodym theorems” that generalise densities \(d\nu/d\mu\) to *operators*.

One classical perspective (visible already in entity["people","Alfons Van Daele","mathematician; vN weights"]’s work) is: given a faithful normal state/weight \(\varphi\) on a von Neumann algebra \(M\), and another normal positive functional/weight \(\psi\) “dominated” by \(\varphi\), one can represent \(\psi\) using a **unique** element/operator \(h\) in \(M\) (or affiliated with \(M\)) satisfying \(0\le h\le 1\) and a suitable identity such as \(\psi(x)=\varphi(hx+xh)/2\) on a dense domain (with strengthened forms under stronger hypotheses). citeturn1view2

At a more structural level, the Pedersen–Takesaki Radon–Nikodym theorem (as summarised in entity["people","Stefaan Vaes","mathematician; vN algebra"]’s paper) describes when one normal semifinite faithful weight can be written as \(\varphi(\cdot\,\delta)\) or \(\varphi(\delta^{1/2}\,\cdot\,\delta^{1/2})\) for a strictly positive operator \(\delta\) affiliated with a suitable fixed-point algebra for the modular automorphism group. citeturn1view3turn1view1

This is a **normal form** statement in the same sense as the commutative RN theorem:

- commutative case: \(\nu = f\mu\) with \(f = d\nu/d\mu\);  
- noncommutative case: \(\psi = \varphi(\cdot\,h)\) (or a symmetric variant) with \(h\) the Radon–Nikodym derivative operator, uniquely determined under the theorem’s hypotheses. citeturn1view3turn1view2

## How this connects back to “normal forms” for inverses and functional calculus

If your earlier interest in “normal forms” comes from matrix/operator inverses (e.g. the Drazin inverse discussion), the spectral theorem viewpoint gives a very clean bridge:

- For a normal/self-adjoint operator \(A\), many generalised inverses are realised as **Borel functional calculus** \(f(A)\). In the multiplication model, \(f(A)\) is literally multiplication by \(f(x)\). citeturn2view1turn2view0  
- The Drazin inverse (in settings where it exists) can often be expressed by choosing a function like
  \[
  f(\lambda)=\begin{cases}
  1/\lambda,& \lambda\neq 0,\\
  0,& \lambda=0,
  \end{cases}
  \]
  combined with the appropriate spectral idempotent at \(0\); Koliha’s idempotent formula \(a^D=(a+p)^{-1}(1-p)\) is the Banach-algebra analogue of “invert off the \(0\)-part”. citeturn18search0turn2view0  
- When you change the representing measure (by changing the cyclic vector), the Radon–Nikodym derivative \(|g|^2\) tells you exactly how the \(L^2\)-models relate, but the operator \(A\) (and hence constructions like \(f(A)\)) remains unitarily equivalent. citeturn2view1turn2view0turn0search0  

In short: **Radon–Nikodym derivatives are the mechanism that makes spectral-theoretic “normal forms” stable under changes of representation**, and noncommutative Radon–Nikodym theorems play the same role for weights/functional normal forms in von Neumann algebras. citeturn2view1turn1view3turn1view2

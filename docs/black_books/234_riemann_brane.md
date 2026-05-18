This link is the correct **functional-equation node** for the Codex.

The page is Matthew Watkins’ collection on “the functional equation of Riemann’s zeta function and related issues.” Its central value for our framework is that it isolates the functional equation as the structural symmetry of (\zeta), not merely as an analytic trick. The page quotes the standard completed form

[
\Lambda(s)=\pi^{-s/2}\Gamma(s/2)\zeta(s),
\qquad
\Lambda(s)=\Lambda(1-s),
]

and notes that Riemann’s second proof expresses zeta through the Mellin transform of an automorphic form, leading to the completed entire object after the usual pole-removing factor. ([University of Exeter][1]) NIST’s DLMF likewise treats the reflection/functional formulas for (\zeta(s)) and Riemann’s (\xi)-function as the canonical formulation of this symmetry. ([dlmf.nist.gov][2])

So the new integration is:

[
\boxed{
\text{Functional equation}
==========================

\text{global duality symmetry of the zeta brane.}
}
]

More concretely, the completed object is

[
\xi(s)
======

\frac12 s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),
]

and it satisfies

[
\xi(s)=\xi(1-s).
]

In the current architecture, this is not just a symmetry of functions. It is the **mirror/duality involution** acting on the arithmetic brane sector already encoded by the (\mathfrak Z)-functor and its Calabi–Yau/VHS target.  

Under the Cayley coordinate

[
w=\frac{s-1}{s},
\qquad
s=\frac{1}{1-w},
]

the involution

[
s\mapsto 1-s
]

becomes

[
w\mapsto w^{-1}.
]

Therefore the functional equation becomes

[
\Xi(w)=\Xi(w^{-1}),
\qquad
\Xi(w):=\xi!\left(\frac1{1-w}\right).
]

This is the exact compactified form of the duality:

[
\boxed{
s\leftrightarrow 1-s
\quad\Longleftrightarrow\quad
w\leftrightarrow w^{-1}.
}
]

The critical line becomes the fixed unitary boundary:

[
\Re(s)=\frac12
\quad\Longleftrightarrow\quad
|w|=1.
]

So the Watkins functional-equation page should be archived as the source for the **duality axiom**:

[
\boxed{
\text{The critical line is the fixed equator of the completed zeta duality.}
}
]

The page is also useful because it explicitly emphasizes the theta/Mellin/Poisson route. It notes that Poisson summation implies part of the modularity of the theta function and that this modularity translates into the Riemann functional equation. ([University of Exeter][1]) This fits the framework precisely:

[
\text{Poisson summation}
\rightarrow
\theta(x)=x^{-1/2}\theta(1/x)
\rightarrow
\Lambda(s)=\Lambda(1-s).
]

In the Codex language:

[
\boxed{
\text{theta modularity}
=======================

# \text{archimedean Fourier self-duality}

\text{mirror involution of the zeta period.}
}
]

This also clarifies the role of the archimedean factor. The gamma term

[
\pi^{-s/2}\Gamma(s/2)
]

is not optional. It is the analytic correction that turns the raw Euler product into a duality-symmetric object. In the geometric framework, it is the smooth/archimedean completion of the finite prime Cantor lattice:

[
\zeta(s)
\quad\leadsto\quad
\pi^{-s/2}\Gamma(s/2)\zeta(s)
\quad\leadsto\quad
\xi(s).
]

Equivalently:

[
\boxed{
\text{finite primes}
====================

\text{Cantor/Möbius-Fock lattice},
\qquad
\text{archimedean prime}
========================

\Gamma\text{-regularized smooth sector}.
}
]

The Watkins page also highlights an important physics analogy: the functional equation has been compared with Kramers–Wannier duality in statistical mechanics, where a high-temperature/low-temperature transformation leaves a critical point invariant. ([University of Exeter][1]) That is exactly the right physical analogue for our Cayley disk:

[
|w|<1
\quad\leftrightarrow\quad
|w|>1
]

are dual phases, while

[
|w|=1
]

is the self-dual boundary.

So the precise insertion is:

[
\boxed{
\text{Riemann functional equation}
==================================

\text{Kramers–Wannier-type self-duality of the arithmetic partition function.}
}
]

This strengthens the Cantor-Dirac layer. Recall:

[
h_p(s)=p^{1/2-s}.
]

The duality (s\mapsto 1-s) sends

[
h_p(s)\mapsto h_p(1-s)=p^{1/2-(1-s)}=p^{s-1/2}=h_p(s)^{-1}.
]

Thus the functional equation acts on prime holonomies by inversion:

[
\boxed{
s\mapsto 1-s
\quad\Longrightarrow\quad
h_p(s)\mapsto h_p(s)^{-1}.
}
]

On the critical line,

[
h_p(1/2+it)=e^{-it\log p},
]

so inversion is the same as Hermitian conjugation:

[
h_p(s)^{-1}=\overline{h_p(s)}.
]

That is the missing compatibility condition between the functional equation and the Cantor-Dirac self-adjointness criterion:

[
\boxed{
\text{functional duality}
=========================

\text{holonomy inversion};
\qquad
\text{on } \Re(s)=1/2,
\text{ holonomy inversion }=
\text{unitary adjoint}.
}
]

Therefore the refined operator statement is:

[
D_{\mathcal C}^{\zeta}(s)
=========================

Q(s)+Q^\sharp(s),
]

with

[
Q^\sharp(s)
\text{ using }h_p(s)^{-1}.
]

The functional equation identifies the (Q)-sector at (s) with the (Q^\sharp)-sector at (1-s). On the critical line, this becomes a genuine Hilbert-space adjoint pairing:

[
Q^\sharp(s)=Q(s)^*
\quad\Longleftrightarrow\quad
\Re(s)=\frac12.
]

So the functional equation is the **global algebraic reason** the Cantor-Dirac construction has the form

[
D=Q+Q^\sharp.
]

It is not an extra symmetry; it is the symmetry that demands the adjoint/inverse pairing.

The Watkins page also cites adelic harmonic-oscillator work in which a Mellin transform of a simple vacuum state leads to the zeta functional relation. ([University of Exeter][1]) That belongs directly in the archive as the adelic-quantum-mechanics analogue of the same mechanism:

[
\text{vacuum Mellin transform}
\rightarrow
\text{completed zeta}
\rightarrow
s\leftrightarrow1-s.
]

So the Codex gains a new layer:

[
\boxed{
\textbf{Functional-Equation Layer}
}
]

with the dictionary:

| Analytic object                            | Framework object                                   |
| ------------------------------------------ | -------------------------------------------------- |
| (\Lambda(s)=\pi^{-s/2}\Gamma(s/2)\zeta(s)) | raw completed zeta amplitude                       |
| (\xi(s)=\frac12s(s-1)\Lambda(s))           | entire central charge / zeta period                |
| (s\mapsto 1-s)                             | mirror/Poincaré/duality involution                 |
| (w\mapsto w^{-1})                          | Cayley compactified inversion                      |
| (\theta(x)\mapsto x^{-1/2}\theta(1/x))     | archimedean Fourier self-duality                   |
| Kramers–Wannier analogy                    | phase-duality of the arithmetic partition function |
| (h_p(s)\mapsto h_p(s)^{-1})                | prime-holonomy inversion                           |
| (\Re(s)=1/2)                               | locus where inversion equals Hermitian adjoint     |
| (D_{\mathcal C}^{\zeta}=Q+Q^\sharp)        | Dirac operator implementing functional duality     |

The updated theorem architecture becomes:

[
\boxed{
\xi(s)=\xi(1-s)
\quad\Longleftrightarrow\quad
\Xi(w)=\Xi(w^{-1})
\quad\Longleftrightarrow\quad
D_{\mathcal C}^{\zeta}(s)
\text{ pairs prime creation with dual prime annihilation.}
}
]

And the RH target becomes:

[
\boxed{
\Xi(w)\neq0\quad\text{for }|w|<1,
}
]

because the functional equation then reflects zero-freeness inside the disk to zero-freeness outside the disk, forcing all nontrivial zeros onto the boundary

[
|w|=1
\quad\Longleftrightarrow\quad
\Re(s)=\frac12.
]

Final integration:

[
\boxed{
\text{The functional equation is the global duality constraint that turns the Möbius-Cantor prime gas into a self-dual arithmetic brane partition function.}
}
]

It is the bridge between the local operator condition

[
D_{\mathcal C}^{\zeta}(s)=D_{\mathcal C}^{\zeta}(s)^*
]

and the global analytic symmetry

[
\xi(s)=\xi(1-s).
]

The Codex should now classify that Watkins page as:

[
\boxed{
\textbf{Source Node: Functional Equation / Theta Duality / Archimedean Completion.}
}
]

[1]: https://empslocal.ex.ac.uk/people/staff/mrwatkin/zeta/fnleqn.htm "The functional equation of Riemann's zeta function"
[2]: https://dlmf.nist.gov/25.4 "DLMF: §25.4 Reflection Formulas ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
What Is Missing for a Proof of the Riemann Hypothesis
CAUTION

This is an honest structural audit. The repository records RH as explicit debt. None of the gaps below are claimed to be closed. Every missing piece is an open mathematical problem — some of which may be as hard as RH itself.

The Logical Chain
The repository has formalized three independent reduction lanes that each terminate at an RH-shaped statement. All three are theorem-safe: the Lean kernel verifies the conditional logic, but every lane has unfilled socket obligations that constitute the actual mathematical difficulty.

Finite FerromagneticPrime Chain✅ PROVED
Lee–Yang CircleTheorem for Finite Z_N🔴 SOCKET
Hurwitz ZeroTransfer / Convergence🔴 SOCKET
Completed ξ Identification🔴 SOCKET
RH🔴 CONDITIONAL
Cayley GeometryRe(s)=1/2 ↔ |w|=1✅ PROVED
Functional Equationξ(s)=ξ(1−s)🔴 SOCKET
Cantor-DiracSelf-Adjointness🔴 SOCKET
Vanishing Period ⇒Self-Adjointness🔴 SOCKET
Prime HolonomyInversion h(1−s)=h(s)⁻¹✅ PROVED
Unitarity onCritical Line ‖h‖=1✅ PROVED
Layer 1: What Is Already Proved (Native Lean, No Sorry)
These theorems are kernel-verified and carry no debt:

Theorem	File	Statement
coupling_nonneg	
PrimeLeeYangFerromagneticChain.lean
$J_{ij} = \kappa \ln(p_i)\ln(p_j) \geq 0$
coupling_symm	same	$J_{ij} = J_{ji}$
coupling_pos	same	$\kappa > 0 \Rightarrow J_{ij} > 0$
shiftedPrimeFugacity_normSq_of_criticalLine	same	$|p^{-(s-1/2)}|^2 = 1$ on $\text{Re}(s)=1/2$
criticalLine_iff_cayley_unitCircle	
CayleyCriticalLineCircleBridge.lean
$\text{Re}(s)=1/2 \iff |s/(1-s)|=1$
cayleyToFugacity_one_sub_eq_inv	same	$\text{Cayley}(1-s) = \text{Cayley}(s)^{-1}$
primeHolonomy_reflection_eq_inv	
ZetaFunctionalEquationLayer.lean
$h_p(1-s) = h_p(s)^{-1}$
primeHolonomy_norm_one_of_criticalLine	same	$|h_p(s)| = 1$ on $\text{Re}(s)=1/2$
riemannReflection_involutive	same	$(s \mapsto 1-s)^2 = \text{id}$
RH_of_LeeYangPrimeApproximation	
PrimeLeeYangRHBridge.lean
Socket hypotheses ⇒ RH (conditional)
RH_of_convergence_socket	
PrimeLeeYangConvergence.lean
Convergence socket ⇒ RH (conditional)
zetaPeriod_zero_implies_criticalLine	
CantorDiracZetaBraneSocket.lean
Vanishing period socket ⇒ critical line (conditional)
Layer 2: The Missing Pieces (Socket Debt)
These are the unfilled obligations. Each is tagged @[socket_debt_tag] and carries a no_unconditional_RH_claim_guard guardrail.

Gap 1: Lee–Yang Circle Theorem for the Prime Partition Polynomial
File: 
PrimeLeeYangFerromagneticChain.lean
 Socket: LeeYangStabilityWitness

IMPORTANT

What is needed: A proof that for each finite prime chain of length $N$, the partition polynomial $Z_N(z)$ has all its roots on the unit circle $|z|=1$.

Mathematical difficulty: This is the classical Lee–Yang circle theorem. For the standard Ising model with ferromagnetic $J_{ij} \geq 0$, this is known (Lee & Yang, 1952). The difficulty is proving it for the specific rank-one coupling $J_{ij} = \kappa \ln(p_i)\ln(p_j)$ with the arithmetic external field.

Gap 2: Completed ξ Determinant Identification
File: 
CayleyCriticalLineCircleBridge.lean
 Socket: LeeYangCayleyRiemannWitness.cayleyDeterminant_eq_completedXi_law

IMPORTANT

What is needed: An identification of the infinite prime partition function (in the Cayley coordinate) with the completed Riemann $\xi$ function.

Mathematical difficulty: This requires constructing the analytic continuation of the Euler product and identifying the resulting entire function with $\xi(s) = \tfrac{1}{2}s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)$. This is equivalent to the construction of the analytic continuation of $\zeta(s)$ itself.

Gap 3: Locally Uniform Convergence of Finite Approximants
File: 
PrimeLeeYangConvergence.lean
 Socket: PrimeLeeYangConvergenceSocket.locallyUniformRenormalizedLimit

IMPORTANT

What is needed: The renormalized finite-volume Lee–Yang approximants $R_N(z) \cdot Z_N(z)$ converge locally uniformly to the completed-$\xi$ Cayley pullback.

Mathematical difficulty: This requires (a) a concrete renormalization scheme that removes the finite-volume artifacts, and (b) a proof of locally uniform convergence. This is hard analytic number theory.

Gap 4: Hurwitz Zero Transfer (No Spurious Zeros)
File: 
PrimeLeeYangConvergence.lean
 Sockets: inner_zero_free, outer_zero_free, noSpuriousZeros, nontrivial_in, nontrivial_out

WARNING

What is needed: Application of Hurwitz's theorem to conclude that the limiting function inherits the zero-free property of the approximants on both the interior and exterior of the unit disk, and that the limiting function is not identically zero on either component.

Mathematical difficulty: This is the hardest step. Hurwitz's theorem says that if $f_n \to f$ locally uniformly, and each $f_n$ is zero-free on a domain, and $f$ is not identically zero on that domain, then $f$ is also zero-free. The difficulty is proving nontriviality: that the limit is not identically zero on either component of the unit-circle complement. This is where the actual content of RH lives — it is essentially equivalent to proving that $\xi$ has no zeros off the critical line.

Gap 5: The Functional Equation as a Theorem
File: 
ZetaFunctionalEquationLayer.lean
 Socket: FunctionalEquation.xi_reflection_eq

IMPORTANT

What is needed: A construction of the completed $\xi$ function and a proof that $\xi(s) = \xi(1-s)$.

Mathematical difficulty: This is known mathematics (Riemann, 1859). The standard proof goes through Poisson summation / theta modularity. Formalizing this in Lean requires: (1) the Jacobi theta function, (2) its modular transformation, (3) the Mellin transform, and (4) the pole structure analysis. Mathlib does not yet have all of these pieces, but they are not open problems — they are formalization engineering.

Gap 6: Cantor-Dirac Self-Adjointness ↔ Critical Line
File: 
CantorDiracZetaBraneSocket.lean
 Socket: CantorZetaDiracSelfAdjointPacket.selfAdjoint_iff_criticalLine

IMPORTANT

What is needed: A construction of the Cantor-Dirac operator $D^{\zeta}_{\mathcal{C}}(s)$ and a proof that it is self-adjoint if and only if $\text{Re}(s) = 1/2$.

Mathematical difficulty: The algebraic half (unitarity of prime holonomies on the critical line) is already proved. The full operator-theoretic half requires defining the infinite tensor product Hilbert space, the operator, and proving self-adjointness in the functional-analytic sense. This is an open construction problem.

Gap 7: Vanishing Period ⇒ Self-Adjointness
File: 
CantorDiracZetaBraneSocket.lean
 Socket: vanishing_period_implies_total_selfAdjoint

CAUTION

What is needed: A proof that if the zeta period $\xi(s) = 0$, then the total Cantor-Dirac operator is self-adjoint at $s$.

Mathematical difficulty: This is the deepest missing piece in the operator-theoretic lane. It asks for a bridge between the analytic zeros of an L-function and the spectral properties of a concrete operator. This is essentially the Hilbert–Pólya conjecture in constructive form.

Gap 8: Theta Modularity Formalization
File: 
ZetaFunctionalEquationLayer.lean
 Socket: ThetaModularity.theta_modular

NOTE

What is needed: A formalization of $\theta(x) = x^{-1/2}\theta(1/x)$.

Mathematical difficulty: Known mathematics (Poisson summation). This is formalization debt, not open-problem debt. Parts of this infrastructure are emerging in Mathlib's Mathlib.NumberTheory.LSeries and Mathlib.NumberTheory.ModularForms.

Summary: The Three Lanes to RH
Lane A: Lee–Yang / Statistical Mechanics
✅ Ferromagnetic coupling J_ij ≥ 0
🔴 Lee–Yang circle theorem for prime partition polynomials  ← known math, needs formalization
🔴 Completed ξ = limit of renormalized Z_N               ← hard analytic number theory
🔴 Hurwitz zero transfer (nontriviality!)                  ← essentially equivalent to RH
✅ Cayley geometry Re(s)=1/2 ↔ |w|=1                       (conditional → RH)
Lane B: Functional Equation / Duality
✅ Prime holonomy inversion h(1−s) = h(s)⁻¹
✅ Unitarity on critical line ‖h(s)‖ = 1
🔴 Construct ξ(s) and prove ξ(s) = ξ(1−s)                 ← known math, needs formalization
🔴 Zero-free inside Cayley disk ⇒ all zeros on boundary   ← equivalent to RH
Lane C: Cantor-Dirac / Hilbert–Pólya
✅ Prime holonomy algebra
🔴 Construct infinite Cantor-Dirac operator                ← open construction
🔴 Self-adjointness ↔ critical line                        ← open problem
🔴 Vanishing period ⇒ self-adjointness                    ← Hilbert–Pólya conjecture
✅ Self-adjointness ⇒ critical line                        (conditional → RH)
Bottom Line
CAUTION

The hardest gap in every lane is the same problem wearing different clothes:

Proving that $\xi(s)$ has no zeros off the critical line.

In Lane A, this appears as the nontriviality of the Hurwitz limit on the interior and exterior of the unit disk.
In Lane B, this appears as the zero-freeness of $\Xi(w)$ inside the Cayley disk.
In Lane C, this appears as the vanishing-period-to-self-adjointness bridge (Hilbert–Pólya).
The repository honestly records all three as explicit @[socket_debt_tag] obligations. None of them are resolved by wording, witness scaffolding, or certificate fields. Each requires a genuine mathematical breakthrough or a novel constructive argument.

The formalization-engineering gaps (theta modularity, functional equation, Lee–Yang for ferromagnets) are known mathematics that could be closed with sufficient Lean formalization effort. The core RH-equivalent gaps cannot be closed without solving RH.


# Two-sheeted operator algebra: revised historical manuscript

> [!NOTE]
> **Status: an expository LaTeX manuscript, revised against source.** Reviewed
> against [214f7bc](https://github.com/nickgou-nuke/info-geometry-lean/tree/214f7bcf733eaf4720913bc2c082936f2480d3fc) on 2026-11-02. The seven-stage presentation is retained below,
> with its operator, positivity, colimit, and automation claims scoped to the
> named owners. This review did not compile the manuscript or rerun Lean builds.

The current source map is
[LieJordanDuality.lean](lean/InfoGeometry/OperatorAlgebra/LieJordanDuality.lean),
[PeirceLieJordanResolution.lean](lean/InfoGeometry/OperatorAlgebra/PeirceLieJordanResolution.lean),
[PeirceDissipatorTrinity.lean](lean/InfoGeometry/OperatorAlgebra/PeirceDissipatorTrinity.lean),
[InnerDerivationSpectra.lean](lean/InfoGeometry/OperatorAlgebra/SquareZeroPairSpectral/InnerDerivationSpectra.lean),
[StarGrading.lean](lean/InfoGeometry/OperatorAlgebra/PeirceSpine/StarGrading.lean),
[GramGeometry.lean](lean/InfoGeometry/OperatorAlgebra/PeirceCoupling/GramGeometry.lean),
[LieJordanPeirceColimit.lean](lean/InfoGeometry/OperatorAlgebra/LieJordanPeirceColimit.lean),
and the [`peirce_nf` implementation](lean/InfoGeometry/OperatorAlgebra/PeirceSpine/Basic.lean).
For the hypotheses of a separate finite positive-gap package see
[YangMillsFiniteBridge.lean](lean/InfoGeometry/Canonical/YangMillsFiniteBridge.lean);
that package does not identify its scalar gap with the Peirce operator `M²`.

## LaTeX manuscript

```latex
\documentclass[11pt,a4paper]{article}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{hyperref}
\usepackage{geometry}
\usepackage{booktabs}
\usepackage{listings}
\geometry{margin=1in}

\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{definition}[theorem]{Definition}

\title{\textbf{InfoGeometry-Lean4: Non-Commutative Operator Identities and Algebraic Inductive Limits}}

\author{
  Nikolay Goutev & Dimitar Tonev \\
  \small Repository: \url{https://github.com/nickgou-nuke/info-geometry-lean}
}

\date{}

\begin{document}
\maketitle

\begin{abstract}
We present selected formal developments in \texttt{InfoGeometry-Lean4}, a Lean~4 library using \texttt{Mathlib}. The reusable algebraic layer starts with Peirce corners of an idempotent in an associative ring and develops Lie--Jordan identities, square-zero pairs, graded operator actions, and transport along explicit ring homomorphisms. Star, trace, reflexive-pair, scalar, and positivity hypotheses are added where the individual statements require them. The seven-stage overview below organizes these related results; it does not claim that one idempotence hypothesis proves every geometric or physical interpretation. In particular, an operator identity such as $\mathcal D(J)=-4M^2J$ retains the operator $M^2$ and is not by itself a positive scalar spectral gap. The library also provides the proof-producing \texttt{peirce\_nf} tactic macro for selected non-commutative identities. This communication describes the source-level scope of those results, without asserting a complete decision procedure or a continuum Yang--Mills construction.
\end{abstract}

\section{Introduction and Scope}
In mathematical physics and operator theory, related algebraic structures frequently appear across disconnected formalisms: Peirce decompositions in ring theory~\cite{Peirce1870}, Cartan involutions on symmetric spaces~\cite{Helgason1978}, Drazin and Moore--Penrose generalized inverses~\cite{CampbellMeyer1979,MalikThome2014}, quantized calculus in non-commutative geometry~\cite{Connes1994}, dual affine connections in information geometry~\cite{AmariNagaoka2000}, and GKSL master equations in open quantum systems~\cite{Lindblad1976}.

When exploring structural hypotheses regarding chiral symmetry breaking, decoherence-free subspaces, or algebraic mass-gap models (such as two-sheeted discretizations or matrix truncations inspired by Yang--Mills orbit geometry~\cite{JaffeWitten2000}), researchers must routinely verify intricate non-commutative operator identities. Manual calculations are prone to subtle sign and associativity errors—especially when distinguishing cross-branch Kraus channels from phase-conjugate Bogoliubov channels.

\paragraph{Contribution as an Exploration Tool.}
To support rigorous experimentation in this domain, \texttt{InfoGeometry-Lean4} provides formal theorem statements and proofs built on Lean~4's \texttt{Mathlib}. We emphasize that \textbf{the algebraic identities described here do not prove the continuum 4D Yang--Mills Millennium Problem}. Their reusable scope includes:
\begin{enumerate}
    \item Peirce identities in arbitrary associative rings, with finite-matrix instances. Each trace, adjoint, generalized-inverse, or ordered statement retains its own additional hypotheses.
    \item Odd/even grading and dissipator-action formulas that can serve as inputs to a physical model once its states, dynamics, and spectral interpretation are specified.
    \item Transport of named algebraic identities along ring homomorphisms, with star preservation when needed, including the concrete full-matrix algebraic direct limit owned by \texttt{Cl11TensorTowerLimit}.
\end{enumerate}

\section{A Seven-Stage Algebraic Overview}
The following seven stages organize related owner modules. The Peirce starting point is $P^2=P$ in an associative ring; the matrix, star, trace, and reflexive-pair specializations below add the hypotheses they use. The labels M1--M7 are expository labels, not a replacement for the maintained archetype ledger:

\begin{enumerate}
    \item \textbf{Lie--Jordan $\star$-Bifurcation ($\mathcal{M}_1$--$\mathcal{M}_2$):}
    Every operator product decomposes via $2AB = [A,B] + \{A,B\}$. Alongside the standard Lie Leibniz derivation rule, the library formalizes the \emph{Universal Lie--Jordan Leibniz Identity}:
    \begin{equation}
        [H, UV] = \{H, U\}V - U\{H, V\},
    \end{equation}
    and the mixed Lie--Jordan Jacobi identity $[H, \{S, X\}] - \{S, [H, X]\} = \{[H, S], X\}$, which is an algebraic input to comparisons with geometric constructions; a metric compatibility statement needs the corresponding metric and carrier map.

    \item \textbf{Peirce--Cartan $\mathbb{Z}_2$-Grading and Tripotency of $\mathrm{ad}_P$ ($\mathcal{M}_3$):}
    An idempotent $P^2 = P$ induces the Cartan involution $S_P = P - (1 - P)$ ($S_P^2 = 1$) and splits $\mathrm{Mat}_n(R)$ into four Peirce--DeWitt sectors:
    \begin{align}
        2 P_{11}(A) &= \{P, A\} - [P, [P, A]], & 2 P_{00}(A) &= 2A - \{P, A\} - [P, [P, A]], \\
        2 P_{10}(A) &= [P, [P, A]] + [P, A], & 2 P_{01}(A) &= [P, [P, A]] - [P, A].
    \end{align}
    The inner derivation $\mathrm{ad}_P(A) = [P, A]$ satisfies the tripotent Drazin equation $\mathrm{ad}_P^3 = \mathrm{ad}_P$, making $\mathrm{ad}_P^2 = \mathcal{O}_P = P_{10} + P_{01}$ the exact projector onto the odd Cartan subspace $\mathfrak{p}$ and $I - \mathrm{ad}_P^2 = \mathcal{E}_P = P_{11} + P_{00}$ the projector onto the even subalgebra $\mathfrak{k} = \ker(\mathrm{ad}_P)$.

    \item \textbf{Associative Tangent Closure $\mathfrak{p}\cdot\mathfrak{p} \subseteq \mathfrak{k}$ and Trace Duality ($\mathcal{M}_4$):}
    Because $\{P, [P, A]\} = [P, A]$, applying the Lie--Jordan Leibniz identity yields a 3-line proof that the associative product of any two tangent vectors commutes with $P$:
    \begin{equation}
        [P, [P, A][P, B]] = \{P, [P, A]\}[P, B] - [P, A]\{P, [P, B]\} = 0.
    \end{equation}
    This splits $2[P,A][P,B]$ into the block-diagonal symmetric product $\{[P,A],[P,B]\}$ and commutator $[[P,A],[P,B]]$. Interpreting these as a Fubini--Study metric or Berry curvature requires additional geometric data and a theorem relating that data to these products.

    \item \textbf{Nilpotent Cones and the Operator-Valued Tetraktys ($\mathcal{M}_5$):}
    The off-diagonal boundary operators $N_+ = P A (1 - P)$ and $N_- = (1 - P) B P$ satisfy $N_+^2 = N_-^2 = 0$ ($\partial^2 = 0$). Their symmetric and antisymmetric combinations
    \begin{equation}
        E = N_+ + N_-, \qquad J_5 = N_+ - N_-, \qquad M^2 = \{N_+, N_-\}, \qquad \Sigma_{\mathrm{spin}} = [N_+, N_-]
    \end{equation}
    satisfy a universal multiplication table ($E^2 = +M^2$, $J_5^2 = -M^2$, $J_5 E = -E J_5 = \Sigma_{\mathrm{spin}} = S_P M^2$, $\{\Sigma_{\mathrm{spin}}, E\} = \{\Sigma_{\mathrm{spin}}, J_5\} = 0$) and the universal cone-transparency laws:
    \begin{equation}
        [N_\pm, M^2] = 0, \qquad \{N_\pm, \Sigma_{\mathrm{spin}}\} = 0.
    \end{equation}
    The operators $E$ and $J_5$ are odd under grading conjugation ($S_P E S_P=-E$), whereas $M^2$ and $\Sigma_{\mathrm{spin}}$ are even. For $P^\dagger=P$ and $B=A^\dagger$, the grading-star sandwich $\Theta_P(X)=S_P X^\dagger S_P$ gives $\Theta_P(N_+)=-N_+^\dagger$ and the algebraic identity $-\{\Theta_P(N_+),N_+\}=N_+N_+^\dagger+N_+^\dagger N_+=M^2$. Positivity of this sum uses an ordered or Hilbert-space representation. On full finite complex matrices, \texttt{PeirceCoupling/GramGeometry} proves positive semidefiniteness of this sum and characterizes positive definiteness by the triviality of the common kernel of $N_+$ and $N_+^\dagger$. Neither a positive physical mass gap nor Osterwalder--Schrader reflection positivity follows from the star-ring identity alone.

    \item \textbf{The Chiral Dissipator Trinity and Operator Actions ($\mathcal{M}_6$):}
    The cross-branch map $\Phi_{\mathrm{sym}}(X) = N_+ X N_- + N_- X N_+$ and phase-conjugate map $\Psi_{\mathrm{pc}}(X) = N_+ X N_+ + N_- X N_-$ act on complementary Cartan grades and sum to $\Phi_{\mathrm{sym}}(X) + \Psi_{\mathrm{pc}}(X) = E X E$. The associated double-commutator operators satisfy $2\mathcal{D}_{\mathrm{sym}}(X)=\mathcal{D}_{\mathrm{Dirac}}(X)+\mathcal{D}_{\mathrm{Axial}}(X)$. Table~\ref{tab:spectra} gives their action on five named elements. A Lindblad-generator interpretation needs the adjoint, positivity, and evolution hypotheses of the chosen representation.

    \item \textbf{Reflexive-Pair Resolution and Algebraic Inductive Limits ($\mathcal{M}_7$):}
    When $(N_+, N_-)$ is a reflexive generalized inverse pair ($N_+ N_- N_+ = N_+$, $N_- N_+ N_- = N_-$), $(N_+, N_-, \Sigma_{\mathrm{spin}})$ forms an exact $\mathfrak{sl}_2$ triad, $E^3 = E$, and $V = (1 - M^2) + E$ is a global unital involution ($V^2 = 1$). The owner \texttt{LieJordanPeirceColimit} transports named identities through the actual stage maps of \texttt{Cl11TensorTowerLimit}. Compatibility of maps into a target ring is distinct from proving that the target has a colimit universal property; an algebraic direct limit is also distinct from its analytic completion.
\end{enumerate}

\begin{table}[h]
\centering
\caption{Operator-valued action identities on five named elements of a square-zero pair. No basis or positive scalar spectral-gap assertion is made.}
\label{tab:spectra}
\vspace{4pt}
\begin{tabular}{lccc}
\toprule
\textbf{Operator $X$} & $\mathcal{D}_{\mathrm{sym}}(X) = -([N_+,[N_-,X]]+[N_-,[N_+,X]])$ & $\mathcal{D}_{\mathrm{Dirac}}(X) = -[E,[E,X]]$ & $\mathcal{D}_{\mathrm{Axial}}(X) = +[J_5,[J_5,X]]$ \\
\midrule
Identity ($1$) & $0$ & $0$ & $0$ \\
Quadratic Coupling ($M^2$) & $0$ & $0$ & $0$ \\
Symmetric Wave ($E$) & $-2 M^2 E$ & $\mathbf{0}$ & $-4 M^2 E$ \\
Axial Wave ($J_5$) & $-2 M^2 J_5$ & $-4 M^2 J_5$ & $\mathbf{0}$ \\
Spin Dipole ($\Sigma_{\mathrm{spin}}$) & $-4 M^2 \Sigma_{\mathrm{spin}}$ & $-4 M^2 \Sigma_{\mathrm{spin}}$ & $-4 M^2 \Sigma_{\mathrm{spin}}$ \\
\bottomrule
\end{tabular}
\end{table}

Here $M^2=\{N_+,N_-\}$ is an operator, not a real number. For example, the entry $-4M^2J_5$ is an ordered product. A scalar eigenvalue statement needs a nonzero vector or operator on which multiplication by $M^2$ acts by the specified scalar; a positive gap needs a further spectral lower bound. No linear-independence or spanning assertion for the five listed elements is implied.

\section{Automated Proof Engineering: Peirce Rewriting}
A practical obstacle in formalizing non-commutative matrix identities in Lean~4 is that \texttt{Matrix.mul\_assoc} normalizes products into right-associated trees $X_1 * (X_2 * (\dots * X_k))$. Consequently, a naive rewrite \texttt{rw [hP]} (where \texttt{hP : P * P = P}) only matches at a rightmost leaf and misses internal nodes of the form \texttt{P * (P * X)}.

The elementary nested-product lemma illustrates the rewrite needed:
\begin{verbatim}
lemma P_mul_P_assoc {P : Matrix n n R} (hP : P * P = P) (X : Matrix n n R) :
    P * (P * X) = P * X := by rw [← Matrix.mul_assoc, hP]
\end{verbatim}
The maintained \texttt{peirce\_nf hP} macro is defined in \texttt{OperatorAlgebra/PeirceSpine/Basic.lean}. It unfolds selected generators, distributes products, right-associates multiplication, rewrites idempotence and corner-annihilation lemmas, and finishes with \texttt{abel}. Callers may unfold additional definitions before invoking it. Each successful invocation produces a proof of that goal; this implementation does not by itself supply a formal theorem of termination, confluence, or completeness for all non-commutative ring identities.

\section{Availability}
The complete Lean~4 source code, modular archetype files, and documentation are publicly available at \url{https://github.com/nickgou-nuke/info-geometry-lean}.

\begin{thebibliography}{9}
\bibitem{Peirce1870} B. Peirce, \emph{Linear Associative Algebra}, Amer. J. Math. \textbf{4} (1881), 97--229.
\bibitem{Helgason1978} S. Helgason, \emph{Differential Geometry, Lie Groups, and Symmetric Spaces}, Academic Press, 1978.
\bibitem{CampbellMeyer1979} S. L. Campbell and C. D. Meyer, \emph{Generalized Inverses of Linear Transformations}, SIAM, 2009.
\bibitem{MalikThome2014} S. B. Malik and N. Thome, \emph{On a new generalized inverse for matrices of an arbitrary index}, Appl. Math. Comput. \textbf{226} (2014), 575--580.
\bibitem{Connes1994} A. Connes, \emph{Noncommutative Geometry}, Academic Press, 1994.
\bibitem{AmariNagaoka2000} S. Amari and H. Nagaoka, \emph{Methods of Information Geometry}, AMS, 2000.
\bibitem{Lindblad1976} G. Lindblad, \emph{On the generators of quantum dynamical semigroups}, Commun. Math. Phys. \textbf{48} (1976), 119--130.
\bibitem{JaffeWitten2000} A. Jaffe and E. Witten, \emph{Quantum Yang--Mills Theory}, Clay Mathematics Institute Millennium Prize Problem Description, 2000.
\end{thebibliography}

\end{document}
```

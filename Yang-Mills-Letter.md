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

\title{\textbf{InfoGeometry-Lean4: A Machine-Verified Non-Commutative Operator Algebra Library for Exploring Two-Sheeted Spectral Gaps and Inductive Colimits}}

\author{
  Nikolay Goutev & Dimitar Tonev \\
  \small Repository: \url{https://github.com/nickgou-nuke/info-geometry-lean}
}

\date{}

\begin{document}
\maketitle

\begin{abstract}
We present \texttt{InfoGeometry-Lean4}, an open-source, axiom-free library in Lean~4 (\texttt{Mathlib}) designed as a formal exploration laboratory for non-commutative matrix operator algebra, $\mathbb{Z}_2$-graded Peirce--DeWitt geometry, generalized inverses, and open quantum system dynamics. Rather than claiming an analytical solution to infinite-dimensional continuum field theory conjectures, this communication introduces a verified algebraic toolkit for testing hypotheses on finite-dimensional non-commutative operator rings $\mathrm{Mat}_n(R)$ and their categorical inductive $\star$-ring colimits. Starting from a single binary idempotent $P^2 = P$ without scalar, diagonal, or commutativity simplifications, the library formalizes a 7-stage causal poset of operator identities connecting Lie--Jordan derivations, Drazin--Moore--Penrose spectral resolutions, split-quaternion $\mathcal{C}\ell_{1,1}$ algebras, Osterwalder--Schrader reflection positivity, and Gorini--Kossakowski--Sudarshan--Lindblad (GKSL) dissipators. We also describe a confluent right-associative Knuth--Bendix rewrite normalizer in Lean~4 that reduces non-commutative polynomial identities modulo $P^2 = P$ to a two-line automated decision procedure.
\end{abstract}

\section{Introduction and Scope}
In mathematical physics and operator theory, related algebraic structures frequently appear across disconnected formalisms: Peirce decompositions in ring theory~\cite{Peirce1870}, Cartan involutions on symmetric spaces~\cite{Helgason1978}, Drazin and Moore--Penrose generalized inverses~\cite{CampbellMeyer1979,MalikThome2014}, quantized calculus in non-commutative geometry~\cite{Connes1994}, dual affine connections in information geometry~\cite{AmariNagaoka2000}, and GKSL master equations in open quantum systems~\cite{Lindblad1976}.

When exploring structural hypotheses regarding chiral symmetry breaking, decoherence-free subspaces, or algebraic mass-gap models (such as two-sheeted discretizations or matrix truncations inspired by Yang--Mills orbit geometry~\cite{JaffeWitten2000}), researchers must routinely verify intricate non-commutative operator identities. Manual calculations are prone to subtle sign and associativity errors—especially when distinguishing cross-branch Kraus channels from phase-conjugate Bogoliubov channels.

\paragraph{Contribution as an Exploration Tool.}
To support rigorous experimentation in this domain, we have developed \texttt{InfoGeometry-Lean4}, a machine-verified library built natively on Lean~4's \texttt{Mathlib}. We emphasize that \textbf{this library is an algebraic exploration tool, not a proof of the continuum 4D Yang--Mills Millennium Problem}. Its purpose is to provide a zero-\texttt{sorry}, machine-checked environment where:
\begin{enumerate}
    \item Every identity is proved over an arbitrary non-commutative square matrix ring $\mathrm{Mat}_n(R)$ (over a commutative star-ring $R$) with \textbf{no commuting, diagonal, or scalar toy simplifications}.
    \item Candidate algebraic mechanisms for chiral symmetry breaking, quadratic symmetry restoration, and dissipative spectral gaps can be stress-tested and audited by the Lean~4 kernel.
    \item Finite-scale algebraic invariants can be functorially lifted along directed systems of unital $\star$-ring homomorphisms $\mathcal{A}_k \to_{\star} \mathcal{A}_{k+1}$ to infinite tensor towers and inductive colimit rings $\mathcal{A}_\infty$.
\end{enumerate}

\section{The 7-Stage Causal Poset of Verified Archetypes}
The core spine of the library is organized as a topologically sorted poset of seven modular stages (\texttt{Archetypes M1--M7}), generated from a single binary idempotent $P^2 = P$ in $\mathcal{A} = \mathrm{Mat}_n(R)$:

\begin{enumerate}
    \item \textbf{Lie--Jordan $\star$-Bifurcation ($\mathcal{M}_1$--$\mathcal{M}_2$):}
    Every operator product decomposes via $2AB = [A,B] + \{A,B\}$. Alongside the standard Lie Leibniz derivation rule, the library formalizes the \emph{Universal Lie--Jordan Leibniz Identity}:
    \begin{equation}
        [H, UV] = \{H, U\}V - U\{H, V\},
    \end{equation}
    and the mixed Lie--Jordan Jacobi identity $[H, \{S, X\}] - \{S, [H, X]\} = \{[H, S], X\}$, which underpins dual affine metric compatibility in operatorial information geometry.

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
    This splits the Quantum Geometric Tensor $2[P, A][P, B]$ into a block-diagonal Fubini--Study metric $\{[P, A], [P, B]\} \in \mathfrak{k}$ and a block-diagonal Berry curvature $[[P, A], [P, B]] \in \mathfrak{k}$ whose core and complement traces cancel identically.

    \item \textbf{Nilpotent Cones and the Split-Quaternion Tetraktys ($\mathcal{M}_5$):}
    The off-diagonal boundary operators $N_+ = P A (1 - P)$ and $N_- = (1 - P) B P$ satisfy $N_+^2 = N_-^2 = 0$ ($\partial^2 = 0$). Their symmetric and antisymmetric combinations
    \begin{equation}
        E = N_+ + N_-, \qquad J_5 = N_+ - N_-, \qquad M^2 = \{N_+, N_-\}, \qquad \Sigma_{\mathrm{spin}} = [N_+, N_-]
    \end{equation}
    satisfy a universal multiplication table ($E^2 = +M^2$, $J_5^2 = -M^2$, $J_5 E = -E J_5 = \Sigma_{\mathrm{spin}} = S_P M^2$, $\{\Sigma_{\mathrm{spin}}, E\} = \{\Sigma_{\mathrm{spin}}, J_5\} = 0$) and the universal cone-transparency laws:
    \begin{equation}
        [N_\pm, M^2] = 0, \qquad \{N_\pm, \Sigma_{\mathrm{spin}}\} = 0.
    \end{equation}
    Whereas $E$ and $J_5$ break chiral parity linearly ($S_P E S_P = -E$), $M^2$ and $\Sigma_{\mathrm{spin}}$ restore chiral parity quadratically ($S_P M^2 S_P = +M^2$). Under the Osterwalder--Schrader reflection $\Theta_P(X) = S_P X^\dagger S_P$ (for $P^\dagger = P, B = A^\dagger$), $\Theta_P(N_+) = -N_+^\dagger$, so $-\{\Theta_P(N_+), N_+\} = N_+ N_+^\dagger + N_+^\dagger N_+ = M^2 \succeq 0$.

    \item \textbf{The Chiral Dissipator Trinity and Spectral Gap Split ($\mathcal{M}_6$):}
    The cross-branch Kraus map $\Phi_{\mathrm{sym}}(X) = N_+ X N_- + N_- X N_+$ and phase-conjugate map $\Psi_{\mathrm{pc}}(X) = N_+ X N_+ + N_- X N_-$ act on complementary Cartan grades and sum to $\Phi_{\mathrm{sym}}(X) + \Psi_{\mathrm{pc}}(X) = E X E$. This yields three exact double-commutator Lindblad dissipators satisfying $2\mathcal{D}_{\mathrm{sym}}(X) = \mathcal{D}_{\mathrm{Dirac}}(X) + \mathcal{D}_{\mathrm{Axial}}(X)$, whose spectra on the Tetraktys $(1, M^2, E, J_5, \Sigma_{\mathrm{spin}})$ are completely diagonalized in Lean~4 (Table~\ref{tab:spectra}).

    \item \textbf{Drazin--Moore--Penrose Resolution and Inductive Colimits ($\mathcal{M}_7$):}
    When $(N_+, N_-)$ is a reflexive generalized inverse pair ($N_+ N_- N_+ = N_+$, $N_- N_+ N_- = N_-$), $(N_+, N_-, \Sigma_{\mathrm{spin}})$ forms an exact $\mathfrak{sl}_2$ triad, $E^3 = E$, and $V = (1 - M^2) + E$ is a global unital involution ($V^2 = 1$). Finally, all identities are lifted functorially along directed towers of unital $\star$-ring homomorphisms $\mathcal{A}_k \to_{\star} \mathcal{A}_\infty$.
\end{enumerate}

\begin{table}[h]
\centering
\caption{Machine-verified eigenvalue action of the three horizon dissipators on the Tetraktys basis.}
\label{tab:spectra}
\vspace{4pt}
\begin{tabular}{lccc}
\toprule
\textbf{Basis Operator $X$} & $\mathcal{D}_{\mathrm{sym}}(X) = -([N_+,[N_-,X]]+[N_-,[N_+,X]])$ & $\mathcal{D}_{\mathrm{Dirac}}(X) = -[E,[E,X]]$ & $\mathcal{D}_{\mathrm{Axial}}(X) = +[J_5,[J_5,X]]$ \\
\midrule
Identity ($1$) & $0$ & $0$ & $0$ \\
Mass Core ($M^2$) & $0$ & $0$ & $0$ \\
Symmetric Wave ($E$) & $-2 M^2 E$ & $\mathbf{0}$ & $-4 M^2 E$ \\
Axial Wave ($J_5$) & $-2 M^2 J_5$ & $-4 M^2 J_5$ & $\mathbf{0}$ \\
Spin Dipole ($\Sigma_{\mathrm{spin}}$) & $-4 M^2 \Sigma_{\mathrm{spin}}$ & $-4 M^2 \Sigma_{\mathrm{spin}}$ & $-4 M^2 \Sigma_{\mathrm{spin}}$ \\
\bottomrule
\end{tabular}
\end{table}

\section{Automated Proof Engineering: The Knuth--Bendix Normalizer}
A practical obstacle in formalizing non-commutative matrix identities in Lean~4 is that \texttt{Matrix.mul\_assoc} normalizes products into right-associated trees $X_1 * (X_2 * (\dots * X_k))$. Consequently, a naive rewrite \texttt{rw [hP]} (where \texttt{hP : P * P = P}) only matches at a rightmost leaf and misses internal nodes of the form \texttt{P * (P * X)}.

By adjoining the single confluence lemma
\begin{verbatim}
lemma P_mul_P_assoc {P : Matrix n n R} (hP : P * P = P) (X : Matrix n n R) :
    P * (P * X) = P * X := by rw [← Matrix.mul_assoc, hP]
\end{verbatim}
the rewrite set \texttt{\{Matrix.mul\_assoc, hP, P\_mul\_P\_assoc hP\}} forms a terminating, confluent Knuth--Bendix completion for the idempotent ideal $\langle P^2 - P \rangle$. Calling \texttt{simp only [..., Matrix.mul\_assoc, hP, P\_mul\_P\_assoc hP]; abel} automatically decides every ring-level identity in the library without manual parenthesis management.

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

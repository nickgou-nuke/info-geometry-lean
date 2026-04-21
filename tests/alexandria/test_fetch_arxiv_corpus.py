from tools.alexandria.fetch_arxiv_corpus import tex_to_text


def test_tex_to_text_preserves_theorem_equation_and_labels() -> None:
    tex = r"""
    \documentclass{article}
    \newcommand{\junk}[1]{#1}
    \begin{document}
    \title{Ignored}
    \begin{abstract}
    We prove a Fisher--Onsager statement.
    \end{abstract}
    \section{Main Results}
    \begin{theorem}[Souriau Fisher]\label{thm:souriau}
    Let $I_{ij}$ be the covariance matrix. Then $\sigma \ge 0$.
    \end{theorem}
    \begin{equation}\label{eq:entropy}
    \sigma = X^T L X
    \end{equation}
    \begin{proof}
    This follows from \eqref{eq:entropy}.
    \end{proof}
    \end{document}
    """

    text = tex_to_text(tex, title="main.tex")

    assert "# main.tex" in text
    assert "## Abstract" in text
    assert "## Main Results" in text
    assert "## Theorem: Souriau Fisher [label:thm:souriau]" in text
    assert "$I_{ij}$" in text
    assert "[equation:eq:entropy]" in text
    assert "$$\n\\sigma = X^T L X\n$$" in text
    assert "## Proof" in text
    assert "[ref:eq:entropy]" in text
    assert "\\newcommand" not in text


def test_tex_to_text_strips_figure_tikz_scaffolding() -> None:
    tex = r"""
    \begin{document}
    \section{Geometry}
    Text before.
    \begin{figure}
    \begin{tikzpicture}
    \draw (0,0) -- (1,1);
    \end{tikzpicture}
    \caption{Noise}
    \end{figure}
    Text after with \emph{operatorial} content and \cite{Souriau1970}.
    \end{document}
    """

    text = tex_to_text(tex, title="paper.tex")

    assert "## Geometry" in text
    assert "Text before." in text
    assert "Text after with operatorial content" in text
    assert "[cite:Souriau1970]" in text
    assert "tikzpicture" not in text
    assert "\\draw" not in text
    assert "caption" not in text.lower()

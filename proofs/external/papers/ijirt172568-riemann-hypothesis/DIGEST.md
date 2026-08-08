# Digest — IJIRT172568_PAPER.pdf

Source: `/home/goutev/Desktop/symmetry/par/IJIRT172568_PAPER.pdf`

## Bibliographic note

- Title: *Exploring New Insights into the Riemann Hypothesis*
- Authors: Nandini C S, Rashmi S
- Venue metadata in PDF: IJIRT, Volume 6 Issue 2, July 2019, ISSN 2349-6002

## Core content

The paper is a high-level survey of the Riemann Hypothesis and adjacent themes:

1. Riemann zeta function `ζ(s)` initially by the Dirichlet series for `Re(s)>1`.
2. Analytic continuation and functional equation are cited.
3. Trivial zeros at negative even integers and non-trivial zeros in the critical strip are described.
4. RH is stated: non-trivial zeros lie on `Re(s)=1/2`.
5. Prime Number Theorem and RH-improved prime-counting error terms are discussed.
6. Average prime gaps are said to grow like `log p_n`.
7. Random Matrix Theory / GUE / Wigner-Dyson spacing statistics are presented as evidence/analogy.
8. Computational verification of many zeros is mentioned as evidence, not proof.

## Theorem-honesty audit

The PDF’s “Theorem 1” is not a proof of RH; it restates RH and cites evidence/functional-equation symmetry.  Functional-equation symmetry gives pairing around the critical line, not that every zero is fixed by that symmetry.

The PNT, average gap, and GUE claims are analytic/asymptotic/statistical results and should be socketed unless imported from a serious analytic number theory library.

The formalization therefore records:

- proved finite algebraic consequences and definitions;
- explicit sockets for analytic continuation, functional equation, PNT, RH, average-gap asymptotics, and GUE spacing;
- a verified CPT fixed-line identity via the existing Lean theorem `MajoranaPrimonSpectralBridge.cpt_fixed_point_iff_critical_line`.

## Formal artifacts

- Lean: `proofs/IJIRTRiemannDigest.lean`
- SymPy witness: `proofs/ijirt_riemann_digest.py`

The Lean module intentionally does **not** prove RH, PNT, GUE statistics, or analytic continuation. It exposes them as typed assumptions/sockets and proves only finite/algebraic checks around them.

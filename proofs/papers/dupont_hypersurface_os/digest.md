# Dupont Hypersurface Orlik-Solomon Model Digest

Paper:
Clément Dupont, "The Orlik-Solomon model for hypersurface arrangements",
Annales de l'Institut Fourier 65 (2015), no. 6, 2507-2545.
arXiv:1302.2103.

Local files:

```text
papers/dupont_hypersurface_os/1302.2103.pdf
papers/dupont_hypersurface_os/The_Orlik-Solomon_model_for_hypersurface_arrangements.tex
papers/dupont_hypersurface_os/1302.2103.txt
```

## Main Relevance

Ordinary Orlik-Solomon algebras compute hyperplane arrangement complements.
Our `D=4` non-isotropic problem is not a hyperplane arrangement; it is a
hypersurface arrangement of quadrics.  Dupont's model is the appropriate
replacement.

## Model Spine

For a smooth projective complex variety `X` and a hypersurface arrangement `L`,
Dupont defines:

```latex
M_q^n(X,L)
=
\bigoplus_{S\in \mathscr S_{q-n}(L)}
H^{2n-q}(S)(n-q)\otimes A_S(L).
```

The product is:

```latex
M_q^n(X,L)\otimes M_{q'}^{n'}(X,L)
\to
M_{q+q'}^{n+n'}(X,L).
```

The differential is:

```latex
d:M_q^n(X,L)\to M_q^{n+1}(X,L),
```

and its stratum component uses a Gysin morphism:

```latex
H^{2n-q}(S)(n-q)
\to
H^{2n-q+2}(S')(n-q+1).
```

The comparison theorem identifies:

```latex
\operatorname{gr}^W H^\bullet(X\setminus L)
\cong
H^\bullet(M^\bullet(X,L)).
```

## Formalized Locally

Lean:

```text
proofs/DupontHypersurfaceOSModel.lean
```

SymPy:

```text
proofs/dupont_hypersurface_os_model.py
```

Formalized genuine lemmas:

```latex
(2n-q)+(2n'-q') = 2(n+n')-(q+q')
```

```latex
(n-q)+(n'-q') = (n+n')-(q+q')
```

```latex
2(n+1)-q = 2n-q+2
```

```latex
(n+1)-q = (n-q)+1
```

```latex
q-(n+1)=q-n-1.
```

Remaining as sockets:

1. verification that our compactified quadric boundary is a hypersurface arrangement;
2. computation of all relevant strata cohomology;
3. computation of Gysin maps;
4. identification of `gr^W H` with the point-count/E-polynomial data.

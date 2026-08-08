# math/9801114 Digest

Paper: Toshinori Oaku and Nobuki Takayama, "An algorithm for de Rham cohomology groups of the complement of an affine variety via D-module computation" (`arXiv:math/9801114v1`).

Local inputs:
- PDF: `/home/goutev/Desktop/symmetry/par/9801114v1.pdf`
- TeX source: `papers/math9801114/ot2.tex`
- Extracted PDF text: `papers/math9801114/9801114v1.txt`

## Core Theorem

For a nonzero polynomial `f in Q[x1, ..., xn]`, with

```latex
X = \mathbb{C}^n,\qquad Y = V(f),\qquad U = X \setminus Y,
```

the groups

```latex
H^k(U,\mathbb{C}_U)
```

are computable for every `k`.

## Algorithm 1.2 Spine

The paper's constant-sheaf algorithm is:

```latex
\mathbb{Q}[x,1/f] \simeq A_n/I
```

as a left Weyl-algebra module, then:

```latex
J = I|_{x_i \mapsto -\partial_i,\ \partial_i \mapsto x_i}
```

then compute a free resolution of `A_n/J` of length `n+1`, and finally compute the cohomology of

```latex
A_n/(x_1A_n+\cdots+x_nA_n)\otimes_{A_n} A_n^{p_{-k}}.
```

The comparison theorem identifies the resulting integration/restriction computation with the sheaf cohomology of the complement.

## Weyl Algebra Atom

The Weyl algebra has generators `x_i, partial_i` with

```latex
\partial_i x_j = x_j \partial_i + \delta_{ij}.
```

The introductory one-variable example uses

```latex
p = (x-u)(x-v)\partial_x - a(x-v) - b(x-u).
```

The formal Fourier transform gives

```latex
\widehat p =
x\partial_x^2
+ ((u+v)x + 2+a+b)\partial_x
+ uvx + u+v+av+bu.
```

The indicial / b-polynomial atom is

```latex
b(s)=s(s-a-b).
```

## Formalization Map

Lean:
- `proofs/OakuTakayamaDModuleDeRham.lean`
- Defines the D-module algorithm sockets.
- Proves the small `b(s)` root facts.
- Records the normal-form coefficients of `\widehat p`.

SymPy:
- `proofs/oaku_takayama_dmodule_de_rham.py`
- Implements a small normal-ordered `A_1` Weyl algebra.
- Checks the Fourier transform of `p`.
- Checks the roots of `b(s)=s(s-a-b)`.

Connection to repo:
- `proofs/NonIsoConf3OrlikSolomon.lean` models a finite Orlik-Solomon complement skeleton.
- `OakuTakayamaDModuleDeRham.lean` is the general D-module computation socket for affine complement cohomology beyond the formal OS model.

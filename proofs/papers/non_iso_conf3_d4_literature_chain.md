# Non-Isotropic `Conf_3(C^4)` Literature And Lemma Chain

Goal:

```latex
U_4 =
\{(a,b)\in \mathbb C^4\times\mathbb C^4
  \mid q(a)q(b)q(a-b)\neq 0\}.
```

## Literature Anchors

1. **Oaku--Takayama, arXiv:math/9801114**
   General D-module algorithm for de Rham cohomology of affine hypersurface complements.
   Correct but computationally expensive.

2. **Clément Dupont, "The Orlik-Solomon model for hypersurface arrangements", arXiv:1302.2103 / Ann. Inst. Fourier 65 (2015)**
   The right replacement for ordinary hyperplane Orlik-Solomon in our case.
   It gives a global OS-type model for complements of hypersurface arrangements using logarithmic forms, strata, and weight filtrations.

3. **Deligne mixed Hodge/logarithmic forms**
   Supplies the comparison framework: logarithmic forms and weight filtrations compute complement cohomology after suitable compactification/normal-crossing control.

## Corrected Generator Picture

For one quadric complement in `C^4`,

```latex
\mathbb C^4 \setminus \{q=0\},
```

the map `q` to `C^*` exposes two visible classes:

```latex
\alpha = d\log q,\qquad \deg(\alpha)=1,
```

and a quadric-fiber class

```latex
\beta,\qquad \deg(\beta)=3.
```

So for three pairs the first corrected candidate uses:

```latex
\alpha_{12},\alpha_{23},\alpha_{13}\quad \deg=1,
```

and

```latex
\beta_{12},\beta_{23},\beta_{13}\quad \deg=3.
```

## Alpha Relation

The Arnold-Orlik-Solomon alpha relation is:

```latex
\alpha_{12}\alpha_{23}
- \alpha_{12}\alpha_{13}
+ \alpha_{23}\alpha_{13}
=0.
```

This is formalized in:

```text
proofs/NonIsoConf3QuadricD4Model.lean
proofs/non_iso_conf3_quadric_d4_model.py
```

## Point-Count Lemma Chain

For odd finite fields, the computational fingerprint is:

```latex
\#U_4(\mathbb F_p)
=p^2(p-1)^2(p+1)(p^3-2p^2-p+3).
```

The current lemma chain is:

```latex
Z(p)=\#\{v\in\mathbb F_p^4\mid q(v)=0\}
    =p(p^2+p-1),
```

```latex
S(p)=\#\{v\mid q(v)\neq 0\}
    =p(p-1)^2(p+1),
```

```latex
B(p)=\#\{(a,b)\mid q(a)\neq0,\ q(b)\neq0,\ q(a-b)=0\}
    =p^2(p-1)^2(p+1)(p^2-2),
```

and therefore

```latex
\#U_4(\mathbb F_p)=S(p)^2-B(p).
```

Formalized in:

```text
proofs/NonIsoConf3QuadricD4PointCount.lean
proofs/non_iso_conf3_quadric_d4_point_count.py
```

## Remaining Sockets

To turn the point-count fingerprint into the final cohomology ring, we still need:

1. point count for all odd prime powers, not just sampled primes;
2. purity / mixed Tate comparison;
3. identification of compact-support E-polynomial;
4. Poincare duality or a recovery theorem for ordinary cohomology;
5. beta/Gysin interaction relations in the hypersurface-arrangement model.

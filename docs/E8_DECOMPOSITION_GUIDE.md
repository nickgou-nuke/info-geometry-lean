# E₈ Decomposition Guide: $\mathfrak{e}_8 \cong \mathfrak{so}(16) \oplus S^+_{16}$

This document provides a mathematically rigorous explanation of the decomposition of the
248-dimensional exceptional Lie algebra $E_8$ under its maximal compact subalgebra $D_8$ ($\mathfrak{so}(16)$),
detailing how the root vectors and weight systems are constructed.

---

## 1. Lie Algebra Dimensions and Branching

Under the maximal subgroup $\text{Spin}(16)$, the adjoint representation of $E_8$ decomposes as:
$$\text{adj}(E_8) \cong \text{adj}(\mathfrak{so}(16)) \oplus S^+_{16}$$

Evaluating the dimensions yields:
$$248 = 120 + 128$$

where:
*   $\text{adj}(\mathfrak{so}(16))$ is the 120-dimensional adjoint representation of $\mathfrak{so}(16)$
    (corresponding to the 112 roots of $D_8$ plus the 8 Cartan generators).
*   $S^+_{16}$ is the 128-dimensional positive Weyl (chiral) spinor representation of $\text{Spin}(16)$.

---

## 2. Root System Construction

Let $\{e_1, e_2, \dots, e_8\}$ be the standard orthonormal basis of $\mathbb{R}^8$ with the standard
inner product $\langle e_i, e_j \rangle = \delta_{ij}$.

### A. The 112 Roots of $\mathfrak{so}(16)$
The root system of $D_8$ ($\mathfrak{so}(16)$) consists of all vectors of the form:
$$\pm e_i \pm e_j \quad (1 \le i < j \le 8)$$

The number of such root vectors is:
$$4 \times \binom{8}{2} = 4 \times 28 = 112$$

Adding the 8 dimension-spanning Cartan generators of the Cartan subalgebra $\mathfrak{h} \subset \mathfrak{so}(16)$
gives the total dimension:
$$112 + 8 = 120$$

### B. The 128 Weights of the Weyl Spinor $S^+_{16}$
The weights of the positive Weyl spinor representation of $D_8$ are given by:
$$\frac{1}{2} \sum_{i=1}^8 \epsilon_i e_i$$

where $\epsilon_i \in \{\pm 1\}$ and the product of the signs is positive (even number of minus signs):
$$\prod_{i=1}^8 \epsilon_i = 1$$

The number of such weight vectors is:
$$2^{8-1} = 128$$

### C. The Full 240 Root System of $E_8$
Combining the $112$ roots of $\mathfrak{so}(16)$ and the $128$ spinor weights yields the $240$ non-zero roots
of $E_8$:
$$\Phi(E_8) = \left\{ \pm e_i \pm e_j \right\} \cup \left\{ \frac{1}{2} \sum_{i=1}^8 \epsilon_i e_i \text{ where } \prod_{i=1}^8 \epsilon_i = 1 \right\}$$

Together with the 8 Cartan generators of $E_8$, they form the 248 dimensions of the Lie algebra.

---

## 3. $\mathbb{Z}_2$-Grading & Witten Index

We define a $\mathbb{Z}_2$-grading $\Gamma$ on $E_8$ by setting:
*   $\Gamma = +1$ (Bosonic) on the adjoint part $\mathfrak{so}(16)$ (dimension 120).
*   $\Gamma = -1$ (Fermionic) on the spinor part $S^+_{16}$ (dimension 128).

The Witten index (or graded index) of this Lie algebra structure is:
$$W = \text{Tr}(\Gamma) = \text{dim}(\mathfrak{so}(16)) - \text{dim}(S^+_{16}) = 120 - 128 = -8$$

This explains the role of the graded index value of $-8$ as a topological invariant of the
split $E_8$ root lattice.

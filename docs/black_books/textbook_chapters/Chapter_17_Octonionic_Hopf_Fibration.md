# Section 17: Octonion Algebra and the Octonionic Hopf Fibration: A Rigorous Exposition

This section provides a mathematically rigorous exposition of octonion algebra and the octonionic Hopf fibration, focusing on clear definitions, properties, and a detailed verification of the Hopf map.

## 17.1 Octonion Algebra ($\mathbb{O}$)

**Definition 17.1.1: Octonion Algebra**
The octonions ($\mathbb{O}$), also known as Cayley numbers, form an 8-dimensional non-associative division algebra over the real numbers $\mathbb{R}$. As a vector space over $\mathbb{R}$, $\mathbb{O}$ is spanned by a basis $\{e_0, e_1, e_2, e_3, e_4, e_5, e_6, e_7\}$, where $e_0$ is the real unit and $e_1, \ldots, e_7$ are imaginary units. An octonion $o \in \mathbb{O}$ is expressed as:
$$o = o_0 e_0 + o_1 e_1 + o_2 e_2 + o_3 e_3 + o_4 e_4 + o_5 e_5 + o_6 e_6 + o_7 e_7, \quad o_i \in \mathbb{R}$$
Typically, $e_0$ is identified with the real unit $1$, so we write:
$$o = o_0 + \sum_{i=1}^{7} o_i e_i$$

**Axiom 17.1.1: Multiplication Rules for Octonion Units**
The multiplication in $\mathbb{O}$ is determined by the following rules:
*   **Identity Element:** $e_0 e_i = e_i e_0 = e_i$
*   **Square of Imaginary Units:** $e_i^2 = -e_0 = -1$
*   **Multiplication Table from Fano Plane:**
    $$\begin{aligned} e_1 e_2 &= e_3, \quad e_2 e_3 = e_1, \quad e_3 e_1 = e_2 \\ e_1 e_4 &= e_5, \quad e_4 e_5 = e_1, \quad e_5 e_1 = e_4 \\ e_1 e_7 &= e_6, \quad e_7 e_6 = e_1, \quad e_6 e_1 = e_7 \\ e_2 e_4 &= e_6, \quad e_4 e_6 = e_2, \quad e_6 e_2 = e_4 \\ e_2 e_5 &= e_7, \quad e_5 e_7 = e_2, \quad e_7 e_2 = e_5 \\ e_3 e_4 &= e_7, \quad e_4 e_7 = e_3, \quad e_7 e_3 = e_4 \\ e_3 e_6 &= e_5, \quad e_6 e_5 = e_3, \quad e_5 e_3 = e_6 \end{aligned}$$
*   **Anticommutativity:** $e_i e_j = -e_j e_i$ for distinct $i,j \ge 1$.

**Definition 17.1.2: Conjugation and Norm in $\mathbb{O}$**
The conjugate of an octonion $o$ is defined as $\bar{o} = o_0 - \sum_{i=1}^{7} o_i e_i$.
The norm squared is a real number defined by $|o|^2 = o\bar{o} = \bar{o}o = o_0^2 + \sum_{i=1}^{7} o_i^2$.

**Theorem 17.1.1: Non-Associativity and Alternativity of $\mathbb{O}$**
Octonion multiplication is non-associative. For example, $(e_1 e_2)e_5 = e_3 e_5 = -e_6$, but $e_1(e_2 e_5) = e_1 e_7 = e_6$.
However, octonions are **alternative**, satisfying $a(ab) = (aa)b$, $a(bb) = (ab)b$, and $(ab)a = a(ba)$.

**Theorem 17.1.2: Division Algebra Property**
For any non-zero octonion $o$, there exists a unique inverse $o^{-1} = \frac{\bar{o}}{|o|^2}$.
By Hurwitz's Theorem, the only normed division algebras over the real numbers are $\mathbb{R}, \mathbb{C}, \mathbb{H}, \mathbb{O}$.

## 17.2 Octonionic Hopf Fibration ($S^{15} \to S^8$)

**Definition 17.2.1: 15-Sphere ($S^{15}$) as Octonion Pairs**
The 15-sphere, $S^{15}$, is defined as the set of pairs of octonions $(o_1, o_2)$ such that $|o_1|^2 + |o_2|^2 = 1$.

**Definition 17.2.2: Octonionic Hopf Map ($h: S^{15} \to S^8$)**
The octonionic Hopf map is defined by:
$$h(o_1, o_2) = (2o_1\bar{o}_2, |o_1|^2 - |o_2|^2)$$

**Theorem 17.2.1: The Hopf Map maps $S^{15}$ to $S^8$**
To prove that $h$ maps to $S^8$, we compute the squared norm of the image:
$$\begin{aligned} |h(o_1, o_2)|^2 &= |2o_1\bar{o}_2|^2 + (|o_1|^2 - |o_2|^2)^2 \\ &= 4|o_1|^2|o_2|^2 + |o_1|^4 - 2|o_1|^2|o_2|^2 + |o_2|^4 \\ &= (|o_1|^2 + |o_2|^2)^2 = 1^2 = 1 \end{aligned}$$
Thus, $h(o_1, o_2)$ lies perfectly on $S^8$.
For each point on $S^8$, the fiber is homeomorphic to the 7-sphere $S^7$.

## 17.3 Connection to Exceptional Lie Groups

**Theorem 17.3.1: Exceptional Lie Groups**
The automorphism group of the octonions is the exceptional Lie group $G_2$. The isometry group of $\mathbb{O}P^1$ is $F_4$. The largest exceptional Lie group $E_8$ can be constructed using octonions.

**Theorem 17.3.2: Emergence of Gauge Groups**
When a complex structure is fixed in the octonions (selecting $e_7$ as the complex imaginary unit), the $Spin(9)$ group that acts on the octonionic Hopf fibration contains a subgroup that preserves this structure. This subgroup is isomorphic to:
$$SU(3) \times SU(2) \times U(1) / \mathbb{Z}_6$$
which perfectly corresponds to the gauge group of the Standard Model of particle physics.

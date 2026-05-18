# On rationality of  $W$ -algebras

Victor G. Kac*† and Minoru Wakimoto‡§

Dedicated to Bertram Kostant on his  $80^{\mathrm{th}}$  birthday.

Abstract: We study the problem of classification of triples  $(\mathfrak{g},f,k)$ , where  $\mathfrak{g}$  is a simple Lie algebra,  $f$  its nilpotent element and  $k\in \mathbb{C}$ , for which the simple  $W$ -algebra  $W_{k}(\mathfrak{g},f)$  is rational.

# 0 Introduction

A vertex algebra  $V$ , used to construct a rational conformal field theory, must satisfy at least the following three conditions:

(a)  $\mathrm{V}$  has only finitely many irreducible representations  $\{M_j\}_{j \in J}$ ,  
(b) the normalized characters  $\chi_{j}(\tau) = \mathrm{tr}_{\mathrm{M}_{\mathrm{j}}}\mathrm{e}^{2\pi \mathrm{i}\tau (\mathrm{L}_{0} - \mathrm{c} / 24)}$  converge to holomorphic functions on the complex upper half-plane  $\mathbb{C}^+$ ,  
(c) the functions  $\{\chi_j(\tau)\}_{j\in J}$  span an  $SL_2(\mathbb{Z})$  -invariant space.

A vertex algebra  $V$  is called rational if it satisfies these three properties. Recall that any semisimple vertex operator algebra, i.e. a vertex operator algebra for which any representation is completely reducible, is rational (see [Z], [DLM]). However, it is unclear how to verify this condition for vertex algebras, considered in the present paper.

It is well known that lattice vertex algebras, associated to even positive definite lattices, are rational (and semisimple as well). A simple Virasoro vertex algebra is rational (and semisimple as well) iff its central charge is of the form  $c = 1 - \frac{6(p - p')^2}{pp'}$ , where  $p, p'$  are relatively prime integers, greater than 1 (which are central charges of the so-called minimal models [BPZ]). A simple affine vertex algebra  $V_{k}(\mathfrak{g})$ , attached to a simple Lie algebra  $\mathfrak{g}$  is rational (and semisimple as well) iff its level  $k$  is a non-negative integer. (Simplicity of a vertex operator algebra is a necessary, but by far not sufficient, condition of semisimplicity.)

It follows from [KW1], Theorems 3.6 and 3.7, and [KW2], Remark 4.3(a), that for a rational

$k$  of the form

$$
(0. 1) \quad k = - h ^ {\vee} + \frac {p}{u}, \text {w h e r e} (p, u) = 1, u \geq 1, (u, \ell) = 1 (\text {r e s p .} = \ell), p \geq h ^ {\vee} (\text {r e s p .} \geq h),
$$

where  $h$  is the Coxeter number,  $h^{\vee}$  is the dual Coxeter number and  $\ell (= 1,2$  or 3) is the "lacety" of  $\mathfrak{g}$ , the normalized character of the vertex algebra  $V_{k}(\mathfrak{g})$  is a modular function (conjecturally, these are all  $k$  with this property). It was shown in [KW1], Theorem 3.6, that for these  $k$  with  $(u,\ell) = 1$  the affine Lie algebra  $\widehat{\mathfrak{g}}$  has a finite set of irreducible highest weight modules  $\{M_j\}_{j\in J}$  (called admissible), whose regularized normalized characters  $\chi_j(\tau ,z) = \mathrm{tr}_{\mathrm{M_j}}\mathrm{e}^{2\pi \mathrm{i}\tau (\mathrm{L_0} - c / 24) + z}, z\in \mathfrak{g}$ , span an  $SL_2(\mathbb{Z})$ -invariant space (if  $(u,\ell) = \ell$ , then one has only  $\Gamma_0(\ell)$ -invariance, see [KW2], Remark 4.3(a)). Conjecturally, these  $\widehat{\mathfrak{g}}$ -modules extend to  $V_{k}(\mathfrak{g})$  and are all of its irreducible modules (this conjecture was proved in [AM] for  $\mathfrak{g} = s\ell_2$ ). Thus,  $V_{k}(\mathfrak{g})$  for  $k$  of the form (0.1) with  $(u,\ell) = 1$  satisfy the properties (a) and (c) of rationality, but property (b) fails for some  $j\in J$  since  $\chi_j(\tau ,z)$  may have a pole at  $z = 0$ , unless  $k$  is a non-negative integer.

In the present paper we study the problem of rationality of simple  $W$ -algebras  $W_{k}(\mathfrak{g},f)$ , which is a family of vertex algebras, depending on  $k \in \mathbb{C}$ , attached to a simple Lie algebra  $\mathfrak{g}$  and a nilpotent element  $f$  of  $\mathfrak{g}$  (rather its conjugacy class) [KRW], [KW3]. More precisely, we need to analyze for which triples  $(\mathfrak{g},f,k)$  the  $W_{k}(\mathfrak{g},f)$ -modules, obtained by the quantum Hamiltonian reduction from admissible modules of level  $k$  over the affine Lie algebra  $\widehat{\mathfrak{g}}$ , have convergent characters, as the modular invariance property is preserved by this reduction. We call such  $f$  an exceptional nilpotent and such  $k$  an exceptional level.

The most well studied case of  $W$ -algebras is that corresponding to the principal nilpotent element  $f$  (a special case of which for  $\mathfrak{g} = s\ell_2$  is the Virasoro vertex algebra). It follows from [KW1] and [FKW] that for principal  $f$  the exceptional levels  $k$  are given by

$$
k = - h ^ {\vee} + \frac {p}{u}, \text {w h e r e} (p, u) = 1, p \geq h ^ {\vee}, u \geq h, (u, \ell) = 1. \tag {0.2}
$$

We expect that for the principal nilpotent  $f$ , (0.2) are precisely the values of  $k$ , for which  $W_{k}(\mathfrak{g},f)$  is a semisimple vertex algebra.

Surprisingly, beyond the principal nilpotent, there are very few exceptional nilpotents. We conjecture that there exists an order-preserving map of the set of non-principal exceptional nilpotent orbits of  $\mathfrak{g}$  to the set of positive integers, relatively prime to  $\ell$  and smaller than  $h$ , such that the corresponding integer  $u$  is the only denominator of an exceptional level  $k = -h^{\vee} + p / u$ , where  $p \geq h^{\vee}$  and  $(u,p) = 1$ .

Note that  $f = 0$  is an exceptional nilpotent, corresponding to  $u = 1$ , since in this case  $W_{k}(\mathfrak{g},0)$  is the simple affine vertex algebra of level  $k\in \mathbb{Z}_{+}$ .

We prove the above conjecture for  $\mathfrak{g} \simeq s\ell_n$ . In this case the above map is bijective to the set  $\{1,2,\ldots,h-1\}$ , and the exceptional nilpotent, corresponding to the positive integer  $u \leq h=n$ , is given by the partition  $n = u + \dots + u + s$ , where  $0 \leq s < u$ .

For an arbitrary simple  $\mathfrak{g}$  we give a geometric description of the exceptional pairs  $(k,f)$  in terms of  $\mathfrak{g}$  and its adjoint group.

We are grateful to K. Bauer, A. Elashvili and A. Premet for very useful discussions on nilpotent orbits, and to ESI and IHES for their hospitality. The results of the paper were reported at the Weizmann Institute in January 2007 and at a conference in Varna in June 2007.

# 1 Admissible modules over affine Lie algebras.

# 1.1 Description of the vacuum admissible weights. Let  $\widehat{\mathfrak{g}}$  be a (non-twisted) affine Lie algebra, associated to a simple finite-dimensional Lie algebra  $\mathfrak{g}$  [K1]. Recall that

$$
\widehat {\mathfrak {g}} = \mathfrak {g} \left[ t, t ^ {- 1} \right] \oplus \mathbb {C} K \oplus \mathbb {C} D
$$

with commutation relations:

$$
[ a t ^ {m}, b t ^ {n} ] = [ a, b ] t ^ {m + n} + m \delta_ {m, - n} (a | b) K,
$$

$$
[ D, a t ^ {m} ] = m a t ^ {m}, [ K, \widehat {\mathfrak {g}} ] = 0,
$$

where  $(\cdot |.)$  denotes the symmetric invariant bilinear form on  $\mathfrak{g}$ , normalized by the condition  $(\alpha |\alpha) = 2$  for long roots  $\alpha$ .

Recall that the bilinear form  $(.|\cdot)$  extends from  $\mathfrak{g}$  to a symmetric invariant bilinear form on  $\widehat{\mathfrak{g}}$  by letting

$$
\left(t ^ {m} a \mid t ^ {n} b\right) = \delta_ {m, - n} (a \mid b), (\mathfrak {g} [ t, t ^ {- 1} ] | \mathbb {C} K + \mathbb {C} D) = 0,
$$

$$
(K | K) = (D | D) = 0, \quad (K | D) = 1.
$$

Choose a Cartan subalgebra  $\mathfrak{h}$  of  $\mathfrak{g}$ , then

$$
\widehat {\mathfrak {h}} = \mathfrak {h} + \mathbb {C} K + \mathbb {C} D
$$

is an ad-diagonalizable subalgebra of  $\widehat{\mathfrak{g}}$ , called its Cartan subalgebra. Since the restriction of the bilinear form  $(\cdot|\cdot)$  to  $\widehat{\mathfrak{h}}$  is non-degenerate, we can (and often will) identify  $\widehat{\mathfrak{h}}^*$  with  $\widehat{\mathfrak{h}}$ , using this form. Given  $\alpha \in \widehat{\mathfrak{h}}$  such that  $(\alpha|\alpha) \neq 0$ , we denote  $\alpha^\vee = 2\alpha / (\alpha|\alpha)$ , unless otherwise specified.

Let  $\Delta \subset \mathfrak{h}^*$  be the set of roots of  $\mathfrak{g}$ , choose a subset of positive roots  $\Delta_{+}$ , and let  $\prod = \{\alpha_{1},\ldots ,\alpha_{r}\}$  be the set of simple roots, where  $r$  is the rank of  $\mathfrak{g}$ . Let  $\Delta_{+}^{\vee} = \{\alpha^{\vee}|\alpha \in \Delta_{+}\}$  be the set of positive coroots,  $\prod^{\vee} = \{\alpha_{1}^{\vee},\dots,\alpha_{r}^{\vee}\}$  the set of simple coroots of  $\mathfrak{g}$ . Define, as usual,  $\rho$  and  $\rho^{\vee}$  by:

$$
(\rho | \alpha_ {i} ^ {\vee}) = 1, \quad (\rho^ {\vee} | \alpha_ {i}) = 1, \quad i = 1, \ldots , r.
$$

Recall that the sets of roots  $\widehat{\Delta}$  and coroots  $\widehat{\Delta}^{\vee}$  of  $\widehat{\mathfrak{g}}$  are

$$
\widehat {\Delta} = \widehat {\Delta} ^ {\mathrm {r e}} \cup \widehat {\Delta} ^ {\mathrm {i m}}, \widehat {\Delta} ^ {\vee} = \widehat {\Delta} ^ {\vee , \mathrm {r e}} \cup \widehat {\Delta} ^ {\mathrm {i m}},
$$

where the sets of real roots and coroots are

$$
\widehat {\Delta} ^ {\mathrm {r e}} = \{\alpha + n K | \alpha \in \Delta , n \in \mathbb {Z} \}, \widehat {\Delta} ^ {\vee , \mathrm {r e}} = \{\alpha^ {\vee} | \alpha \in \widehat {\Delta} ^ {\mathrm {r e}} \},
$$

and the set of imaginary roots (resp. coroots) is

$$
\widehat {\Delta} ^ {\mathrm {i m}} = \left\{n K | n \in \mathbb {Z}, n \neq 0 \right\},
$$

the subsets of positive roots and coroots being:

$$
\widehat {\Delta} _ {+} ^ {\mathrm {r e}} = \Delta_ {+} \cup \{\alpha + n K | \alpha \in \Delta , n > 0 \}, \widehat {\Delta} _ {+} ^ {\vee , \mathrm {r e}} = \{\alpha^ {\vee} | \alpha \in \widehat {\Delta} _ {+} ^ {\mathrm {r e}} \},
$$

$$
\widehat {\Delta} _ {+} ^ {\mathrm {i m}} = \{n K | n > 0 \}, \widehat {\Delta} _ {+} = \widehat {\Delta} _ {+} ^ {\mathrm {r e}} \cup \widehat {\Delta} _ {+} ^ {\mathrm {i m}}, \widehat {\Delta} _ {+} ^ {\vee} = \widehat {\Delta} _ {+} ^ {\vee , \mathrm {r e}} \cup \widehat {\Delta} _ {+} ^ {\mathrm {i m}}.
$$

Recall that the sets of simple roots (resp. coroots) in  $\widehat{\Delta}_{+}$  (resp.  $\widehat{\Delta}_{+}^{\vee}$ ) then are:

$$
\widehat {\prod} = \{\alpha_ {0} = K - \theta , \alpha_ {1}, \ldots , \alpha_ {r} \}, \widehat {\prod} ^ {\vee} = \{\alpha_ {0} ^ {\vee} = K - \theta^ {\vee}, \alpha_ {1} ^ {\vee}, \ldots , \alpha_ {r} ^ {\vee} \},
$$

where  $\theta$  is the highest root in  $\Delta_{+}$ . The positive integers

$$
h = (\rho^ {\vee} | \theta) + 1 \text {a n d} h ^ {\vee} = (\rho | \theta^ {\vee}) + 1
$$

are called the Coxeter number and the dual Coxeter number of  $\mathfrak{g}$ , respectively.

Defining  $\widehat{\rho} = h^{\vee}D + \rho$ ,  $\widehat{\rho}^{\vee} = hD + \rho^{\vee} \in \widehat{\mathfrak{h}}$ , we have the usual formulas:

$$
\left(\widehat {\rho} \mid \alpha_ {i} ^ {\vee}\right) = 1, \left(\widehat {\rho} ^ {\vee} \mid \alpha_ {i}\right) = 1, i = 0, 1, \dots , r.
$$

Given  $\lambda \in \widehat{\mathfrak{h}}^*$ , let

$$
\widehat {\Delta} _ {\lambda} ^ {\vee} = \left\{\alpha^ {\vee} \in \widehat {\Delta} ^ {\vee} | (\lambda | \alpha^ {\vee}) \in \mathbb {Z} \right\}.
$$

Let  $\widehat{\Delta}_{\lambda+}^{\vee} = \widehat{\Delta}_{\lambda}^{\vee} \cap \widehat{\Delta}_{+}^{\vee}$  and let  $\widehat{\prod}_{\lambda}^{\vee}$  be the set of simple roots in  $\widehat{\Delta}_{\lambda+}^{\vee}$ .

Definition 1.1 ([KW1]). A weight  $\lambda \in \widehat{\mathfrak{h}}^*$  is called admissible if the following two conditions hold:

$$
\left(\lambda + \widehat {\rho} | \alpha^ {\vee}\right) \notin \{0, - 1, - 2, \dots \} f o r a l l \alpha^ {\vee} \in \widehat {\Delta} _ {+} ^ {\vee}, \tag {1.1a}
$$

$$
\text {t h e} \mathbb {Q} \text {- s p a n o f} \widehat {\Delta} _ {\lambda} ^ {\vee} \text {c o n t a i n s} \widehat {\Delta} ^ {\vee}. \tag {1.1b}
$$

We proved in [KW1] that the (normalized) character of an irreducible highest weight  $\widehat{\mathfrak{g}}$ -module with highest weight  $\lambda$  satisfies a modular invariance property if  $\lambda$  is an admissible weight (and conjectured that for no other  $\lambda$  this property holds). Admissible weights were completely classified in [KW1], and this classification will be used in the paper. The following proposition describes the "vacuum" admissible weights.

Proposition 1.1. For  $k \in \mathbb{C}$  the weight  $\lambda = kD$  is admissible if and only if  $k$  satisfies the following properties (a) and (b):

(a)  $k + h^{\vee} = \frac{p}{u}$ , where  $p, u \in \mathbb{N}$ ,  $(p, u) = 1$ ;  
(b) one of the following possibilities holds:

(i)  $(u,\ell) = 1$  and  $p\geq h^{\vee}$  (in this case  $\widehat{\prod}_{\lambda}^{\vee} = \{uK - \theta^{\vee},\alpha_{1}^{\vee},\ldots ,\alpha_{r}^{\vee}\}$ ),  
(ii)  $u\in \ell \mathbb{N}$  and  $p\geq h$  (in this case  $\widehat{\prod}_{\lambda}^{\vee} = \{uK - \theta_s^{\vee},\alpha_1^{\vee},\ldots ,\alpha_r^{\vee}\})$

Here  $\ell$  is the lacety of  $\mathfrak{g}$  (i.e.,  $\ell = 1$  for  $A - D - E$  types,  $\ell = 2$  for  $B - C - F$  types, and  $\ell = 3$  for  $G_{2}$ ), and  $\theta_{s}$  is the highest among short roots in  $\Delta_{+}$ .

Proof. Condition (1.1b) of admissibility implies that  $(\lambda + \widehat{\rho} | \alpha_i) \in \mathbb{Q}$  for all  $i = 0, 1, \ldots, r$ . This, together with (1.1a) for  $\alpha^\vee = nK$  implies (a).

Next, note that  $(\lambda + \widehat{\rho} | \alpha^{\vee}) = (\rho | \alpha^{\vee}) \in \mathbb{Z}$  if  $\alpha \in \Delta^{\vee}$ , hence  $\Delta^{\vee} \subset \Delta_{\lambda}^{\vee}$ . Since  $(\lambda + \widehat{\rho} | nK + \alpha^{\vee}) = n(k + h^{\vee}) + (\rho | \alpha^{\vee}) \in n_{u}^{p} + \mathbb{Z}$ , we see that  $(\lambda + \widehat{\rho} | nK + \alpha^{\vee}) \in \mathbb{Z}$  iff  $n \in u\mathbb{Z}$ . Therefore,  $\widehat{\Delta}_{\lambda}^{\vee} = \widehat{\Delta}_{\lambda}^{\vee,\mathrm{re}} \cup \widehat{\Delta}_{\lambda}^{\vee,\mathrm{im}}$ , where

$$
\widehat {\Delta} _ {\lambda} ^ {\vee , \mathrm {r e}} = \{n u K + \alpha^ {\vee} | n \in \mathbb {Z}, \alpha^ {\vee} \in \Delta^ {\vee} \} \cap \widehat {\Delta} ^ {\vee , \mathrm {r e}}, \widehat {\Delta} _ {\lambda} ^ {\vee , \mathrm {i m}} = \{n u K | n \in \mathbb {Z} \backslash \{0 \} \}.
$$

Thus, the  $\lambda$  in question is an admissible weight iff (1.1a) holds, i.e.,

$$
\left(\lambda + \widehat {\rho} \mid \alpha^ {\vee}\right) \in \mathbb {N} \text {f o r a l l} \alpha \in \widehat {\Delta} _ {\lambda , +} ^ {\vee}. \tag {1.2}
$$

Case (i):  $(u,\ell) = 1$ . In this case

$$
\widehat {\Delta} _ {\lambda} ^ {\vee , \mathrm {r e}} = \{n u K + \alpha^ {\vee} | n \in \mathbb {Z}, \alpha \in \Delta_ {\mathrm {l o n g}} \} \cup \{n \ell u K + \alpha^ {\vee} | n \in \mathbb {Z}, \alpha \in \Delta_ {\mathrm {s h o r t}} \},
$$

and the set of simple roots is  $\widehat{\prod}_{\lambda}^{\vee} = \{uK - \theta^{\vee},\alpha_{1}^{\vee},\ldots ,\alpha_{r}^{\vee}\}$

Hence condition (1.1a) is equivalent to  $(\lambda + \widehat{\rho} | uK - \theta^{\vee}) = u(k + h^{\vee}) - (h^{\vee} - 1) \in \mathbb{N}$ , i.e.,  $p - h^{\vee} \in \mathbb{Z}_{+}$ .

Case (ii):  $(u,\ell) = \ell$ . In this case

$$
\widehat {\Delta} _ {\lambda} ^ {\vee , \text {r e}} = \left\{n u K + \alpha^ {\vee} | n \in \mathbb {Z}, \alpha^ {\vee} \in \Delta^ {\vee} \right\},
$$

hence  $\widehat{\prod}_{\lambda}^{\vee} = \{uK - \theta_s^{\vee},\alpha_1^{\vee},\ldots ,\alpha_r^{\vee}\}$ . Therefore, using that  $(\rho |\theta_s^\vee) = (\rho^\vee |\theta) = h - 1$ , condition (1.2) is equivalent to  $(\lambda +\widehat{\rho} |uK - \theta_s^\vee) = u(k + h^\vee) - (h - 1)\in \mathbb{N}$ , i.e.,  $p - h\in \mathbb{Z}_+$ .

1.2 Principal admissible weights. Recall the definition of the affine and extended affine Weyl groups. Let  $W \subset \operatorname{End} \mathfrak{h}$  be the Weyl group of  $\mathfrak{g}$  and extend it to  $\widehat{\mathfrak{h}}$  by letting  $w(K) = K$ ,  $w(D) = D$  for all  $w \in W$ . Let  $Q^{\vee} = \sum_{i=1}^{r} \mathbb{Z} \alpha_i^{\vee}$  be the coroot lattice of  $\mathfrak{g}$ , then  $P = \{\lambda \in \mathfrak{h}^* | (\lambda|\alpha) \in \mathbb{Z}\}$  for all  $\alpha \in Q^{\vee}\}$  is the weight lattice; note that  $Q^{\vee} \subset P \cap Q^*$ , where  $Q^* = \{\lambda \in \mathfrak{h} | (\lambda|\alpha) \in \mathbb{Z}\}$  for all  $\alpha \in Q\}$ . Given  $\alpha \in \mathfrak{h}$ , define the translation [K1]

$$
t _ {\alpha} (v) = v + (v | K) \alpha - (\frac {1}{2} | \alpha | ^ {2} (v | K) + (v | \alpha)) K, v \in \widehat {\mathfrak {h}},
$$

and for a subset  $L \subset \mathfrak{h}$ , let  $t_L = \{t_\alpha | \alpha \in L\}$ . The affine Weyl group  $\widehat{W}$  and the extended affine Weyl group  $\tilde{W}$  are defined as follows:

$$
\widehat {W} = W \ltimes t _ {Q ^ {\vee}}, \tilde {W} = W \ltimes t _ {Q ^ {*}},
$$

so that  $\widehat{W} \subset \tilde{W}$ . Recall that the group  $\tilde{W}_{+} = \{w \in \tilde{W} | w(\widehat{\prod}^{\vee}) = \widehat{\prod}^{\vee}\}$  acts transitively on orbits of  $\operatorname{Aut} \widehat{\prod}^{\vee}$  and simply transitively on the orbit of  $\alpha_{0}^{\vee}$ , and that  $\tilde{W} = \tilde{W}_{+} \ltimes \widehat{W}$ .

An admissible weight  $\lambda$  is called principal if  $\widehat{\Delta}_{\lambda}^{\vee}$  is isomorphic to  $\widehat{\Delta}^{\vee}$ . We describe below the set of all principal admissible weights.

For  $u\in \mathbb{N}$  let

$$
\widehat {S} _ {(u)} = \{u K - \theta^ {\vee}, \quad \alpha_ {1} ^ {\vee}, \ldots , \alpha_ {r} ^ {\vee} \}.
$$

Given  $y \in \tilde{W}$ , denote by  $\widehat{P}_{u,y}$  the set of all admissible weights  $\lambda$ , such that  $\widehat{\prod_{\lambda}^{\vee}} = y(\widehat{S}_{(u)})$ .

Let  $\widehat{P}$  (resp.  $\widehat{P}_{+}) = \{\lambda \in \widehat{\mathfrak{h}} |(\lambda |\alpha_{i}^{\vee})\in \mathbb{Z}$  (resp.  $\in \mathbb{Z}_+$ ) for all  $i = 0,\dots,r\}$  denote the sets of all integral (resp. dominant integral) weights. Given  $k\in \mathbb{C}$ , denote by  $\widehat{P}_{+}^{k}$ ,  $\widehat{P}_{u,y}^{k}$ , etc. the subsets of  $\widehat{P}_{+}$ ,  $\widehat{P}_{u,y}$ , etc., consisting of all elements of level  $k$  (recall that the level of  $\lambda$  is  $(\lambda |K)$ ).

Theorem 1.1 ([KW1]). (a)  $\widehat{P}_{u,y}^{k}\neq \emptyset$  iff the triple  $k,u,y$  satisfies the following three properties:

(i)  $(u,\ell) = 1$  (recall that  $\ell = 1,2$  or 3 is the lacety of  $\mathfrak{g}$ ),  
(ii)  $k + h^{\vee} = \frac{p}{u}$ , where  $p, u \in \mathbb{N}$ ,  $p \geq h^{\vee}$  and  $(p, u) = 1$ ,  
(iii)  $y(\widehat{S}_{(u)})\subset \widehat{\Delta}_{+}^{\vee}$

(b) If properties (i)-(iii) hold, then

$$
\widehat {P} _ {u, y} ^ {k} = \left\{y. (\Lambda + (k + h ^ {\vee} - p) D) | \Lambda \in \widehat {P} _ {+} ^ {p - h ^ {\vee}} \right\},
$$

where  $y.\lambda = y(\lambda + \widehat{\rho}) - \widehat{\rho}$  is the usual shifted action.

(c) The set of all principal admissible weights is  $\cup_{k,u,y}\widehat{P}_{u,y}^{k}$ , where  $(k,u,y)$  runs over all triples satisfying (i)-(iii).  
(d) Two non-empty sets  $\widehat{P}_{u,y}^{k}$  and  $\widehat{P}_{u',y'}^{k'}$  have a non-empty intersection iff they coincide, which happens iff  $k = k'$ ,  $u = u'$  and  $y(\widehat{S}_{(u)}) = y'(\widehat{S}_{(u)})$ .

Denote by  $Pr^k$  the set of all principal admissible weights of level  $k$ . Note that  $Pr^k = \widehat{P}_+^k + \mathbb{C}K$  if  $k \in \mathbb{Z}_+$ .

Proposition 1.2 ([FKW]). Let  $\Lambda \in \widehat{P}_{u,y}^{k}$ , where  $y = t_{\beta}\bar{y}$ , be a principal admissible weight. Then the following conditions are equivalent:

(i)  $(\lambda |\alpha)\notin \mathbb{Z}$  for all  $\alpha \in \Delta^{\vee}$  
(ii)  $y(\widehat{S}_{(u)})\subset \widehat{\Delta}_{+}^{\vee}\backslash \Delta_{+}^{\vee},$  
(iii)  $0 < - (\bar{y}^{-1}(\beta)|\alpha) < u$  for all  $\alpha \in \Delta_{+}$  
(iv)  $(\beta |\alpha)\notin u\mathbb{Z}$  for all  $\alpha \in \Delta$

A principal admissible weight, satisfying one of the equivalent properties (i)-(iv) of Proposition 1.2, is called non-degenerate. Given  $\bar{y} \in W$ , denote by  $\widehat{P}_{\bar{y}}^{k}$  the union of all  $\widehat{P}_{u,y}^{k}$  with  $y = t_{\beta}\bar{y}$ , where  $\beta$  satisfies the inequalities (iii) of Proposition 1.2. It follows from this proposition that the set of all non-degenerate principal admissible weights of level  $k$ , denoted by  $Prn^{k}$ , is the union of all  $\widehat{P}_{\bar{y}}^{k}$ :

$$
P r n ^ {k} = \bigcup_ {\bar {y} \in W} \widehat {P} _ {\bar {y}} ^ {k}.
$$

Proposition 1.3 ([KW2],[FKW]). (a)  $\widehat{P}_{\bar{y}}^{k} \neq \emptyset$  iff  $k$  satisfies conditions (0.2).

(b) Provided that (0.2) holds, two sets  $\widehat{P}_{\bar{y}}^{k}$  and  $\widehat{P}_{\bar{y}'}^{k}$  have a non-empty intersection iff they coincide, which happens iff  $\bar{y}^{-1}\bar{y}' \in W_{+}$ , where  $W_{+}$  is the image of  $\tilde{W}_{+}$  under the canonical map  $\tilde{W} \to W$ .  
(c) For  $\Lambda \in \widehat{P}_{\bar{y}}^{k}$  there exists a unique  $\beta$ , such that  $\Lambda = (t_{\beta}\bar{y})$ . ( $\Lambda^0 + (k + h^\vee - p)D$ ), where  $\Lambda^0 \in \widehat{P}_+^{p-h^\vee}$ ,  $p = u(k + h^\vee)$ . We let

$$
\varphi_ {\bar {y}} (\Lambda) = \left(\Lambda^ {0}, u D - \bar {y} ^ {- 1} (\beta) - \widehat {\rho} ^ {\vee}\right).
$$

This is a bijective map

$$
\varphi_ {\bar {y}}: \widehat {P} _ {\bar {y}} ^ {k} \to \widehat {P} _ {+} ^ {p - h ^ {\vee}} \times \widehat {P} _ {+} ^ {\vee u - h},
$$

the inverse map being

$$
\psi_ {\bar {y}} (\lambda , \mu) = \bar {y}. \lambda + (k + h ^ {\vee}) (D - \bar {y} (\mu + \hat {\rho} ^ {\vee})).
$$

(d) Given  $p, u \in \mathbb{N}$ , such that  $(p, u) = 1$ ,  $(\ell, u) = 1$ ,  $p \geq h^{\vee}$ ,  $u \geq h$ , define the set

$$
I _ {p, u} = \left(\widehat {P} _ {+} ^ {p - h ^ {\vee}} \times \widehat {P} _ {+} ^ {\vee u - h}\right) / \tilde {W} _ {+}
$$

(where  $w(\lambda, \mu) = (w(\lambda), w(\mu)), w \in \tilde{W}_+$ ). Then, letting

$$
\varphi (\Lambda) = \varphi_ {\bar {y}} (\Lambda) i f \Lambda \in \widehat {P} _ {\bar {y}} ^ {k},
$$

gives a well-defined map  $\varphi:Prn^{k}\to I_{p,u}$

(e) Elements  $\Lambda, \Lambda' \in Prn^k$  have the same image under the map  $\varphi$  iff  $\Lambda' = \bar{w} \cdot \Lambda$  for some  $\bar{w} \in W$ . In particular, all fibers of the map  $\varphi$  have cardinality  $|W|$ .

# 1.3 Characters of principal admissible  $\widehat{\mathfrak{g}}$ -modules, their modular transformations and asymptotics.

Introduce the following domain  $Y$  and coordinates  $(\tau, z, t)$  on  $Y$ :

$$
Y = \left\{\lambda \in \widehat {\mathfrak {h}} | \operatorname {R e} (\lambda | K) > 0 \right\} = \left\{(\tau , z, t) := 2 \pi i (- \tau D + z + t K) | \tau , t \in \mathbb {C}, \operatorname {I m} \tau > 0, z \in \mathfrak {h} \right\}.
$$

The product

$$
R _ {\widehat {\mathfrak {g}}} (v) = e ^ {(\widehat {\rho} | v)} \prod_ {\alpha \in \widehat {\Delta} _ {+} ^ {\mathrm {r e}}} (1 - e ^ {- (\alpha | v)}) \prod_ {j \in \mathbb {N}} (1 - e ^ {- j (K | v)}) ^ {r}
$$

converges to a holomorphic function on  $Y$ . Given  $\lambda \in Y - \widehat{\rho}$ , consider the series

$$
N _ {\lambda} (v) = \sum_ {w \in \widehat {W} _ {\lambda}} \epsilon (w) e ^ {(w (\lambda + \widehat {\rho}) | v)},
$$

where  $\widehat{W}_{\lambda}$  is the subgroup of  $\widehat{W}$ , generated by reflections  $r_{\alpha^{\vee}}$  (defined by  $r_{\alpha^{\vee}}(v) = v - (\alpha |v)\alpha^{\vee}$ ) in all real roots from  $\widehat{\Delta}_{\lambda}^{\vee}$ . This series converges to a holomorphic function on  $Y$ .

Let  $L(\lambda)$  denote the irreducible highest weight  $\widehat{\mathfrak{g}}$ -module with the highest weight  $\lambda \in \widehat{\mathfrak{h}}^*$ , and let

$$
\operatorname {c h} _ {L (\lambda)} (v) = \operatorname {t r} _ {L (\lambda)} \mathrm {e} ^ {v}, v \in \mathrm {Y},
$$

be its character. For a function  $F$  on the domain  $Y$  we shall often write  $F(\tau, z, t)$  in place of  $F(2\pi i(-\tau D + z + tK))$ .

Theorem 1.2 ([KW1]). (a) If  $\lambda$  is an admissible weight, then  $R_{\widehat{\mathfrak{g}}}\mathrm{ch}_{L(\lambda)}$  converges in the domain  $Y$  to the holomorphic function  $N_{\lambda}$ .

(b) Let  $\lambda = y$ .  $(\lambda^0 + (k + h^\vee - p)D) \in \widehat{P}_{u,y}^k$ , where  $\lambda^0 \in \widehat{P}_+^{p - h^\vee}$ . Define the following isometry  $\phi_{u,y}$  of  $\widehat{\mathfrak{h}}$ :

$$
\phi_ {u, y} (\alpha_ {i} ^ {\vee}) = y ^ {- 1} (\alpha_ {i} ^ {\vee}), \quad i = 1, \ldots , r, \phi_ {u, y} (D) = u y ^ {- 1} (D), \phi_ {u, y} (K) = u ^ {- 1} K.
$$

Then

$$
\operatorname {c h} _ {L (\lambda)} (v) = N _ {\lambda^ {0}} \left(\phi_ {u, y} (v)\right) / R _ {\widehat {\mathfrak {g}}} (v). \tag {1.3}
$$

Remark 1.1.  $\widehat{W}_{\lambda} = \phi_{u,y}^{-1}\widehat{W}\phi_{u,y}$ . Using this, one derives (1.3) from (a).

Define the normalized character

$$
\chi_ {L (\lambda)} (\tau , z, t) = e ^ {2 \pi i \tau s _ {\lambda}} \mathrm {c h} _ {L (\lambda)} (\tau , z, t), \tag {1.4}
$$

where

$$
s _ {\lambda} = \frac {| \lambda + \widehat {\rho} | ^ {2}}{2 (k + h ^ {\vee})} - \frac {| \widehat {\rho} | ^ {2}}{2 h ^ {\vee}},
$$

and  $k$  is the level of  $\lambda$ . Let  $D_{\widehat{\mathfrak{g}}}(\tau, z, t) = q^{|\widehat{\rho}|^2 / 2h^\vee} R_{\widehat{\mathfrak{g}}}(\tau, z, t)$  denote the denominator of  $\chi_{L(\lambda)}(\tau, z, t)$ . It satisfies the following well-known transformation formula [K1]:

$$
D _ {\widehat {\mathfrak {g}}} \left(- \frac {1}{\tau}, \frac {z}{\tau}, t - \frac {(z | z)}{2 \tau}\right) = (- i) ^ {| \Delta_ {+} |} (- i \tau) ^ {r / 2} D _ {\widehat {\mathfrak {g}}} (\tau , z, t). \tag {1.5}
$$

Note that  $\chi_{L(\lambda)} = \chi_{L(\lambda +aK)}$  for any  $a\in \mathbb{C}$ . For that reason, from now on we shall consider elements of  $Pr^{k}\mod \mathbb{C}K$ . There is a unique representative  $\lambda$  in each coset, such that  $\lambda (D) = 0$ . When writing  $(\lambda |\mu)$  for  $\lambda ,\mu \in Pr^k$ , we shall mean the scalar product of these representatives, in other words,  $(\lambda |\mu) = (\bar{\lambda} |\bar{\mu})$ , where the bar means the orthogonal projection of  $\widehat{\mathfrak{h}}$  to  $\mathfrak{h}$ . Note that, by the "strange formula" [K1], we have:

$$
s _ {\lambda} = \frac {(\bar {\lambda} + 2 \rho | \bar {\lambda})}{2 (k + h ^ {\vee})} - \frac {1}{2 4} \frac {k \dim \mathfrak {g}}{k + h ^ {\vee}}.
$$

From (1.3) and the transformation formula and asymptotics for characters of integrable  $\widehat{\mathfrak{g}}$ -modules we derived those for principal admissible modules.

Theorem 1.3 ([KW1]). Let  $\lambda = y.(\lambda^0 + (k + h^\vee - p)D) \in Pr^k$ , where  $k + h^\vee = p / u$ ,  $y = t_\beta \bar{y}$ ,  $\beta \in Q^*$ ,  $\bar{y} \in W$ ,  $\lambda^0 \in \widehat{P}_+^{p - h^\vee}$ . Then

$$
(a) \chi_ {L (\lambda)} \left(- \frac {1}{\tau}, \frac {z}{\tau}, t - \frac {(z | z)}{2 \tau}\right) = \sum_ {\lambda^ {\prime} \in P r ^ {k}} a (\lambda , \lambda^ {\prime}) \chi_ {L (\lambda^ {\prime})} (\tau , z, t),
$$

where

$$
\begin{array}{l} a (\lambda , \lambda^ {\prime}) = i ^ {| \Delta_ {+} |} u ^ {- r} (k + h ^ {\vee}) ^ {- r / 2} | P / Q ^ {\vee} | \epsilon (\bar {y} \bar {y} ^ {\prime}) e ^ {- 2 \pi i ((\lambda^ {0} + \rho | \beta^ {\prime}) + (\lambda^ {\prime 0} + \rho | \beta) + (k + h ^ {\vee}) (\beta | \beta^ {\prime}))} \\ \times \sum_ {w \in W} \epsilon (w) e ^ {- \frac {2 \pi i}{k + h ^ {\vee}} \left(w \left(\lambda^ {0} + \widehat {\rho}\right) \mid \lambda^ {\prime 0} + \widehat {\rho}\right)}. \\ \end{array}
$$

(b) As  $\tau \downarrow 0$ , we have for each  $z \in \mathfrak{h}$ , such that  $(\alpha | z) \notin \mathbb{Z}$  for all  $\alpha \in \Delta$ :

$$
\chi_ {L (\lambda)} (\tau , - \tau z, 0) \sim b (\lambda , z) e ^ {\frac {\pi i g ^ {(k)}}{1 2 \tau}},
$$

where

$$
{b (\lambda , z)} = {\epsilon (\bar {y}) u ^ {- r / 2} a (\lambda^ {0}) \prod_ {\alpha \in \Delta_ {+}} \sin \frac {\pi (z - \beta | \alpha)}{u} / \sin \pi (z | \alpha),}
$$

$$
a (\lambda^ {0}) = p ^ {- r / 2} | P / Q ^ {\vee} | ^ {- 1 / 2} \prod_ {\alpha \in \Delta_ {+}} 2 \sin \frac {\pi (\lambda^ {0} + \rho | \alpha)}{p},
$$

$$
g ^ {(k)} = \left(1 - \frac {h ^ {\vee}}{p u}\right) \dim \mathfrak {g}.
$$

# 2 Characters of  $W$ -algebras  $W_{k}(\mathfrak{g},f)$ .

2.1 Construction of simple vertex algebras  $W_{k}(\mathfrak{g},f)$ . First, recall the definition of the vertex algebra  $W_{k}(\mathfrak{g},f)$  [KRW], [KW3]. Let  $\mathfrak{g}$  be a finite-dimensional simple Lie algebra with the normalized invariant bilinear form as in Sec. 1.1, and let  $f$  be a nilpotent element of  $\mathfrak{g}$ . Include  $f$  in an  $s\ell_{2}$ -triple  $f,x,e$ , so that  $[x,e] = e$ ,  $[x,f] = -f$  and  $[e,f] = x$ . We have the eigenspace decomposition of  $\mathfrak{g}$  with respect to  $\operatorname{ad} x$ :

$$
\mathfrak{g} = \bigoplus_{j\in \frac{1}{2}\mathbb{Z}}\mathfrak{g}_{j}  .
$$

Let  $\mathfrak{g}_{\pm} = \oplus_{j > 0}\mathfrak{g}_{\pm j}$ , and let  $A_{\mathrm{ch}} = \mathfrak{g}_{+} + \mathfrak{g}_{-}$  with odd parity. The restriction of the bilinear form  $(\cdot |.)$  to  $A_{\mathrm{ch}}$  is non-degenerate and skew-supersymmetric (since it is symmetric before the change of parity). Denote by  $A_{\mathrm{ne}}$  the (even) vector space  $\mathfrak{g}_{1/2}$  with the non-degenerate skew-symmetric bilinear form

$$
\langle a, b \rangle = (f | [ a, b ]), \quad a, b \in \mathfrak {g} _ {1 / 2}.
$$

Introduce the following differential complex  $(\mathcal{C}^k (\mathfrak{g},f),d_0)$  , where

$$
\mathcal {C} ^ {k} (\mathfrak {g}, f) = V ^ {k} (\mathfrak {g}) \otimes F (\mathfrak {g}, f)
$$

is the tensor product of the universal affine vertex algebra of level  $k$  and  $F(\mathfrak{g},f) = F(A_{\mathrm{ch}})\otimes F(A_{\mathrm{ne}})$  is the tensor product of vertex algebras of free superfermions, based on  $A_{\mathrm{ch}}$  and  $A_{\mathrm{ne}}$ , and  $d_0$  is an odd derivation of the vertex algebra  $\mathcal{C}^k (\mathfrak{g},f)$ , such that  $d_0^2 = 0$ .

In order to define the differential  $d_0$ , choose a basis  $\{u_{\alpha}\}_{\alpha \in S_j}$  of each subspace  $\mathfrak{g}_j$  of  $\mathfrak{g}$ , and let  $S_{+} = \cup_{j > 0}S_{j}$ ,  $S = \cup_{j}S_{j}$ . Then  $\{u_{\alpha}\}_{\alpha \in S_{+}}$  is a basis of  $\mathfrak{g}_{+}$ , and we denote by  $\{u^{\alpha}\}_{\alpha \in S_{+}}$  the dual basis of  $\mathfrak{g}_{-}$ . Let  $\{\varphi_{\alpha},\varphi^{\alpha}\}_{\alpha \in S_{+}}$  be the corresponding basis of  $A_{\mathrm{ch}}$  and  $\{\phi_{\alpha}\}_{\alpha \in S_{1 / 2}}$  the corresponding basis of  $A_{\mathrm{ne}}$ . Consider the following odd field of the vertex algebra  $\mathcal{C}^k (\mathfrak{g},f)$ :

$$
{ d ( z ) } { = } { d ^ { \mathrm { s t } } ( z ) + \sum _ { \alpha \in S _ { + } } ( f | u _ { \alpha } ) \varphi ^ { \alpha } ( z ) + \sum _ { \alpha \in S _ { 1 / 2 } } : \varphi ^ { \alpha } ( z ) \phi _ { \alpha } ( z ) : , }
$$

where

$$
d ^ {\mathrm {s t}} (z) = \sum_ {\alpha \in S _ {+}}: u _ {\alpha} (z) \varphi^ {\alpha} (z): - \frac {1}{2} \sum_ {\alpha , \beta , \gamma \in S _ {+}} c _ {\alpha \beta} ^ {\gamma}: \varphi_ {\gamma} (z) \varphi^ {\alpha} (z) \varphi^ {\beta} (z):
$$

and  $c_{\alpha \beta}^{\gamma}$  are the structure constants of  $\mathfrak{g} : [u_{\alpha}, u_{\beta}] = \sum_{\gamma} c_{\alpha \beta}^{\gamma} u_{\gamma} (\alpha, \beta, \gamma \in S)$ . Then  $d_0 := \operatorname{Res}_z d(z)$  is an odd derivation of all products of the vertex algebra  $\mathcal{C}^k(\mathfrak{g}, f)$  and  $d_0^2 = 0$ .

The homology of the complex  $(\mathcal{C}^k (\mathfrak{g},f),d_0)$  is a vertex algebra, denoted by  $W^{k}(\mathfrak{g},f)$

We shall assume that  $k + h^{\vee} \neq 0$ . Then one can construct the following Virasoro field  $L(z)$  of  $\mathcal{C}^k(\mathfrak{g},f)$ , making the latter a conformal vertex algebra:

$$
L (z) = L ^ {\mathfrak {g}} (z) + \partial_ {z} x (z) + L ^ {\mathrm {c h}} (z) + L ^ {\mathrm {n e}} (z).
$$

Here  $L^{\mathfrak{g}}(z) = \frac{1}{2(k + h^{\vee})}\sum_{\alpha \in S}:u_{\alpha}(z)u^{\alpha}(z):$  is the Sugawara construction, and

$$
L ^ {\mathrm {c h}} (z) = \sum_ {\alpha \in S _ {+}} (\alpha (x): \partial_ {z} \varphi_ {\alpha} (z) \varphi^ {\alpha} (z): + (1 - \alpha (x)): \partial_ {z} \varphi^ {\alpha} (z) \varphi_ {\alpha} (z):),
$$

$$
L ^ {\mathrm {n e}} (z) = \frac {1}{2} \sum_ {\alpha \in S _ {1 / 2}}: \partial_ {z} \phi^ {\alpha} (z) \phi_ {\alpha} (z):,
$$

where  $\{\phi^{\alpha}\}$  is a basis of  $A_{\mathrm{ne}}$ , dual to  $\{\phi_{\alpha}\}$  with respect to the bilinear form  $\langle ., . \rangle$ .

With respect to  $L(z)$  the field  $d(z)$  is primary of conformal weight 1. In the language of  $\lambda$ -brackets, this means that  $[d_{\lambda}L] = \lambda d$ , hence  $d_0(L) = [d_\lambda L]|_{\lambda = 0} = 0$ . Thus, the homology class of  $L$  defines the Virasoro field  $L(z) = \sum_{n\in \mathbb{Z}}L_nz^{-n - 2}$  of the vertex algebra  $W^{k}(\mathfrak{g},f)$ , making it a conformal vertex algebra. Its central charge is given by the following formula [KW1]:

$$
c (\mathfrak {g}, f, k) = \dim \mathfrak {g} _ {0} - \frac {1}{2} \dim \mathfrak {g} _ {1 / 2} - \frac {1 2}{k + h ^ {\vee}} | \rho - (k + h ^ {\vee}) x | ^ {2}. \tag {2.1}
$$

Above and further on we identify the fields of a vertex algebra, like  $d(z), L(z), \ldots$ , with the corresponding states  $d, L, \ldots$ , via the field-state correspondence:  $a = a(z)|0\rangle|_{z=0}$ .

Let  $\mathfrak{g}^f$  be the centralizer of  $f$  in  $\mathfrak{g}$ . Then the  $\frac{1}{2}\mathbb{Z}$ -grading, induced on  $\mathfrak{g}^f$  from  $\mathfrak{g}$  is of the form

$$
\mathfrak {g} ^ {f} = \sum_ {j \in \frac {1}{2} \mathbb {Z} _ {+}} \mathfrak {g} _ {- j} ^ {f}.
$$

It was proved in [KW3] that the vertex algebra  $W^{k}(\mathfrak{g},f)$  is strongly generated by  $\dim \mathfrak{g}^f$  fields  $J^{\{a\}}(z)$ , where  $a$  runs over a basis of  $\mathfrak{g}^f$ , compatible with the above  $\frac{1}{2}\mathbb{Z}$ -grading, and  $J^{\{a\}}(z)$  has conformal weight  $1 + j$  if  $a \in \mathfrak{g}_{-j}$ .

Therefore the operator  $L_{0}$  is diagonalizable on  $W^{k}(\mathfrak{g},f)$  with spectrum in  $\frac{1}{2}\mathbb{Z}_{+}$  and finite-dimensional eigenspaces, the  $0^{\mathrm{th}}$  eigenspace being  $\mathbb{C}|0\rangle$ . Hence the vertex algebra  $W^{k}(\mathfrak{g},f)$  has a unique maximal ideal  $I$ , and  $W_{k}(\mathfrak{g},f) = W^{k}(\mathfrak{g},f) / I$  is a simple vertex algebra.

Given  $v \in \mathfrak{g}_0$ , the subspaces  $\mathfrak{g}_{+}$  (resp.  $\mathfrak{g}_{1/2}$ ) are ad  $v$ -invariant; let  $c_{\beta}^{\alpha}(v)$ ,  $\alpha, \beta \in S_{+(resp. 1/2)}$  be the matrix of ad  $v$  on  $\mathfrak{g}_{+}(\text{resp. } 1/2)$  in the basis  $\{u_{\alpha}\}_{\alpha \in S_{+(resp. 1/2)}}$ , i.e.,  $[v, u_{\beta}] = \sum_{\alpha} c_{\beta}^{\alpha}(v) u_{\alpha}$ . Define the following field:

$$
J ^ {\{v \}} (z) = v (z) + v ^ {\mathrm {c h}} (z) + v ^ {\mathrm {n e}} (z),
$$

where

$$
v ^ {\mathrm {c h}} (z) = \sum_ {\alpha , \beta \in S _ {+}} c _ {\beta} ^ {\alpha} (v): \varphi_ {\alpha} (z) \varphi^ {\beta} (z):, v ^ {\mathrm {n e}} (z) = - \frac {1}{2} \sum_ {\alpha , \beta \in S _ {1 / 2}} c _ {\beta} ^ {\alpha} (v): \phi_ {\alpha} (z) \phi^ {\beta} (z):.
$$

Lemma 2.1. (a) For any  $v \in \mathfrak{g}_0$ , we have

$$
d _ {0} ^ {\mathrm {s t}} (J ^ {\{v \}}) = 0.
$$

(b) Provided that  $v \in \mathfrak{g}_0^f$ , we have:

$$
d _ {0} (J ^ {\{v \}}) = 0.
$$

Proof. (b) was proved in [KRW], by making use of the  $\lambda$ -bracket calculus. The same proof gives (a).

![](images/33ae29496f5a21ce02da69aa91347934c3beaae58abca2d68242c7a93d9ad434.jpg)

2.2 Computation of the Euler-Poincaré characters in the Ramond sector. We studied in [KW4] the most general  $\sigma$ -twisted modules over  $W^{k}(\mathfrak{g},f)$ . From the point of view of modular invariance the most important case is the Ramond twisted one, when  $\sigma = \sigma_{R}$  is an automorphism of  $\mathfrak{g}$ , defined by  $\sigma_{R} = e^{2\pi i\operatorname{ad}x}$ .

Since  $\sigma_R$  is an inner automorphism of  $\mathfrak{g}$ , we can choose a Cartan subalgebra  $\mathfrak{h}$  of  $\mathfrak{g}$ , contained in  $\mathfrak{g}_0$ . Let  $\Delta \subset \mathfrak{h}^*$  be the set of roots, and let  $\Delta^j \subset \Delta$  be the set of roots of  $\mathfrak{h}$  in  $\mathfrak{g}_j$ .

A natural choice of a subset of positive roots in  $\Delta$  is  $\Delta_{+} = \Delta_{+}^{0}\cup (\cup_{j > 0}\Delta^{j})$ , where  $\Delta_{+}^{0}$  is a subset of positive roots of the root system  $\Delta^0$ .

However, we shall need another choice of a subset of positive roots, which will be denoted by  $\Delta_{+}^{\mathrm{new}}$ . First, we choose the element  $f$  to be a sum of root vectors, attached to roots  $\gamma_1,\ldots ,\gamma_s\in \Delta^{-1}$ , such that  $\mathfrak{h}^f\coloneqq \{h\in \mathfrak{h}|\gamma_i(h) = 0,\quad i = 1,\dots ,s\}$  is a Cartan subalgebra of  $\mathfrak{g}^f$ . Next, choose an element  $h_0\in \mathfrak{h}^f$  such that  $\alpha (h_0) = 0$  iff  $\alpha |_{\mathfrak{h}^f} = 0$  for  $\alpha \in \Delta$ . Since the restriction of any root from  $\Delta^{1 / 2}$  to  $\mathfrak{h}^f$  is not identically zero [EK], it follows that ad  $h_0|_{\mathfrak{g}_{1 / 2}}$  has no zero eigenvalues. Finally, let  $\Delta_0^0 = \{\alpha \in \Delta^0 |\alpha |_{\mathfrak{h}^f} = 0\}$  and let  $\Delta_{0, + }^{0}$  be a subset of positive roots in the root system  $\Delta_0^0$ . The new set of positive roots in  $\Delta$  is as follows:

$$
\Delta_ {+} ^ {\mathrm {n e w}} = \Delta_ {0, +} ^ {0} \cup \{\alpha \in \Delta | \mathrm {e i t h e r} \alpha (h _ {0}) > 0, \mathrm {o r} \alpha (h _ {0}) = 0 \mathrm {a n d} \alpha (x) <   0 \}.
$$

Since  $h_0 \in \mathfrak{h}^f$ ,  $\gamma_i(h_0) = 0$  for all  $i$ , hence all  $\gamma_i$  lie in  $\Delta_+^{\mathrm{new}}$ . Also, since all elements from  $\mathfrak{g}_0^f$  define symplectic endomorphisms of  $\mathfrak{g}_{1/2}$ ,  $\Delta_+^{1/2} := \Delta_+^{\mathrm{new}} \cap \Delta^{1/2}$  (resp.  $\Delta_-^{1/2} := (-\Delta_+^{\mathrm{new}}) \cap \Delta^{1/2}$ ) contains exactly half of the roots from  $\Delta^{1/2}$ . Thus  $\Delta_+^{\mathrm{new}}$  satisfies the properties, required in [KW3].

Let  $\widehat{\mathfrak{g}}^R = \oplus_{m\in \frac{1}{2}\mathbb{Z}}(\mathfrak{g}_{\bar{m}}\otimes t^m)\oplus \mathbb{C}K\oplus \mathbb{C}D$  be the  $\sigma_R$ -twisted affine Lie algebra [K1], where  $\mathfrak{g}_{\bar{m}} = \oplus_{j\in \bar{m}}\mathfrak{g}_j$ ,  $\bar{m}\in \frac{1}{2}\mathbb{Z} / \mathbb{Z}$  being the coset of  $m\in \frac{1}{2}\mathbb{Z}$ , and the commutation relations are given by the same formulas as for  $\widehat{\mathfrak{g}}$ . Note that both  $\widehat{\mathfrak{g}}^R$  and  $\widehat{\mathfrak{g}}$  lie in the affine Lie algebra  $\mathfrak{g}[t^{1 / 2},t^{-1 / 2}]\oplus \mathbb{C}K\oplus \mathbb{C}D$ , and, in fact, they are isomorphic,  $\widehat{\mathfrak{g}}$  being mapped to  $\widehat{\mathfrak{g}}^R$  by the element  $t^x$  of the group  $G(\mathbb{C}[t^{1 / 2},t^{-1 / 2}])$ . Note also that they share the same Cartan subalgebra  $\widehat{\mathfrak{h}}$ , and that  $\widehat{\Delta}^R = t_x(\widehat{\Delta})$  is the set of roots of  $\widehat{\mathfrak{g}}^R$ .

For each  $\alpha \in \Delta$  define the number

$$
s _ {\alpha} = - \alpha (x) \text {i f} \alpha \in \Delta_ {+} ^ {\text {n e w}}, = 1 - \alpha (x) \text {i f} \alpha \in - \Delta_ {+} ^ {\text {n e w}},
$$

and introduce the following set of positive roots in the set  $\widehat{\Delta}^R$  of roots of  $\widehat{\mathfrak{g}}^R$ :

$$
\widehat {\Delta} _ {+} ^ {R} = \left\{(n + s _ {\alpha}) K + \alpha | \alpha \in \Delta , n \in \mathbb {Z} _ {+} \right\} \cup \left\{n K | n \in \mathbb {N} \right\}.
$$

Let  $\Delta^{R}(\mathrm{resp.}\Delta_{+}^{R}) = \{-\alpha (x)K + \alpha |\alpha \in \Delta (\mathrm{resp.}\Delta_{+}^{\mathrm{new}})\} \subset \widehat{\Delta}^{R}(\mathrm{resp.}\widehat{\Delta}_{+}^{R}).$  Let  $\Delta_{+}^{R,j} = \{\alpha \in \Delta_{+}^{R}|(\alpha |x) = j\}$ . Let  $\Delta^{R,f}(\mathrm{resp.}\Delta_{+}^{R,f}) = \{\alpha \in \Delta^{R}(\mathrm{resp.}\Delta_{+}^{R})|\alpha |_{\mathfrak{h}^{f}} = 0\}$ .

Lemma 2.2. (a) There exists  $\bar{w} \in W$ , such that  $\widehat{\Delta}_{+}^{R} = t_{x}\bar{w}(\widehat{\Delta}_{+})$ .

(b)  $\Delta_{+}^{\mathrm{new}} = \bar{w} (\Delta_{+})$  
(c) If  $g \in \mathfrak{g}^f$ , then  $(x|g) = 0$ . Consequently,  $\mathfrak{h}^f \subset t_x\bar{w}(\mathfrak{h})$ .  
(d) Let  $\prod^{R}$  be the set of simple roots for  $\Delta_{+}^{R}$ . Then  $\Delta_{+}^{R,f} \cap \prod^{R}$  is the set of simple roots for  $\Delta_{+}^{R,f}$ .

Proof. Let  $\widehat{\prod}^R = \{\tilde{\beta}_i = s_{\beta_i}K + \beta_i|i = 0,1,\ldots ,r\}$ , where  $\beta_{i}\in \Delta$ , be the set of simple roots of  $\widehat{\Delta}_{+}^{R}$ . We have:  $K = \sum_{i}a_{i}\tilde{\beta}_{i}$ , where  $a_{i}$  are positive integers. Recall also that  $s_{\beta_i} = -\beta_i(x) + n_i$  where  $n_i = 0$  or  $1$ .

Since  $(x|K) = 0$ , it follows that:

$$
\sum_ {i} a _ {i} \beta_ {i} = 0 \mathrm {a n d} \sum_ {i} a _ {i} n _ {i} = 1.
$$

It follows from the second equation that there exists index  $i_0$  such that  $a_{i_0} = 1$  and  $n_i = \delta_{i,i_0}$ . Hence  $\{\beta_i\}_{i\neq i_0}$  is a set of simple roots for  $\Delta$  and  $\tilde{\beta}_i = -\beta_i(x)K + \beta_i = t_x\beta_i$  for all  $i\neq i_0$ . Hence there exists  $\bar{w}\in W$ , such that  $\{\beta_i\}_{i\neq i_0} = \bar{w} (\prod)$ , where  $\prod$  is the set of simple roots of  $\Delta_{+}$ . Therefore  $\{\tilde{\beta}_i\}_{i\neq i_0} = t_x\bar{w} (\prod)$  and hence  $\widehat{\Pi}^R = t_x\bar{w} (\widehat{\Pi})$ , where  $\widehat{\Pi}$  is the set of simple roots of  $\widehat{\Delta}_{+}$  proving (a).

By the proof of (a),  $\beta_{i}\in \Delta_{+}^{\mathrm{new}}$  if  $i\neq i_0$ . Hence, by the construction of  $\bar{w}$ , (b) follows.

Since  $x = [e, f]$ , we have:  $(x|g) = ([e, f]|g) = (e|[f, g]) = 0$  if  $g \in \mathfrak{g}^f$ , proving (c).

In order to prove (d), we need to show that if  $\alpha \in \Delta_{+}^{R,f}$  and  $\alpha = \beta +\gamma$  , where  $\beta ,\gamma \in \Delta_{+}^{R}$  then  $\beta ,\gamma \in \Delta_{+}^{R,f}$  . Evaluating at  $h_0$  , we have:  $0 = \alpha (h_0) = \beta (h_0) + \gamma (h_0)$  . But both summands on the right are non-negative, by definition of  $\Delta_{+}^{\mathrm{new}}$  and  $\Delta_{+}^{R}$  . Hence  $\beta (h_0) = \gamma (h_0) = 0$  and the restriction of  $\beta$  and  $\gamma$  to  $\mathfrak{h}^f$  is zero.

We have:  $\widehat{\Delta}_{+}^{R} = t_{x}\bar{w} (\widehat{\Delta}_{+})$ ,  $\Delta^R = t_x(\Delta)$ ,  $\Delta_{+}^{R} = t_{x}\bar{w} (\Delta_{+})$ . Let  $\widehat{\rho}^{R} = t_{x}\bar{w} (\widehat{\rho})$ ,  $\mathfrak{h}^R = t_x(\mathfrak{h})$ ,  $D^{R} = t_{x}(D)$ ,  $W^{R} = t_{x}Wt_{x}^{-1}$ ,  $\widehat{P}_+^{k,R} = t_x\bar{w} (\widehat{P}_+^k)$ ,  $Pr^{k,R} = t_x\bar{w} Pr^k$ , etc. Then  $\widehat{W}^{R} = W^{R}\ltimes t_{Q^{\vee ,R}}$  is the (affine) Weyl group of  $\widehat{\mathfrak{g}}^R$ ,  $\tilde{W}^{R} = W^{R}\ltimes t_{P^{R}}$  is the extended affine Weyl group,  $\widehat{\mathfrak{h}} = \mathfrak{h}^R +\mathbb{C}K + \mathbb{C}D^R$  is the "standard" decomposition of the Cartan subalgebra  $\widehat{\mathfrak{h}}$  of  $\widehat{\mathfrak{g}}^R$ , etc.

Consider the triangular decomposition  $\widehat{\mathfrak{g}}^R = \widehat{\mathfrak{n}}_+^R +\widehat{\mathfrak{h}} +\widehat{\mathfrak{n}}_+^R$ , corresponding to the set of positive roots  $\widehat{\Delta}_{+}^{R}$ , and let  $M$  be a highest weight  $\widehat{\mathfrak{g}}^R$ -module with highest weight vector  $v_{\Lambda}$ , annihilated by  $\widehat{\mathfrak{n}}_+^R$ , where  $\Lambda \in \widehat{\mathfrak{h}}^*$  has level  $k$ . By [GK2],  $R_{\widehat{\mathfrak{g}}^R ch_M}$  converges to a holomorphic function in  $Y_{+}$ , which extends to a holomorphic function in the domain  $Y$ .

The  $\widehat{\mathfrak{g}}^R$ -module  $M$  extends to a  $\sigma_R$ -twisted  $V^k (\mathfrak{g})$ -module by the map:

$$
e _ {\alpha} \mapsto e _ {\alpha} ^ {R} (z) := \sum_ {n \in (\alpha | x) + \mathbb {Z}} (e _ {\alpha} t ^ {n}) z ^ {- n - 1}, h \mapsto h ^ {R} (z) = \sum_ {n \in \mathbb {Z}} (h t ^ {n}) z ^ {- n - 1},
$$

where  $e_{\alpha}$  is a root vector of  $\mathfrak{g}$ , attached to  $\alpha \in \Delta$ , and  $h \in \mathfrak{h}$ . Likewise we have the  $\sigma_R$ -twisted  $F(\mathfrak{g},f)$ -module  $F^{R}(\mathfrak{g},f)$ , given by  $\varphi_{\alpha} \mapsto \varphi_{\alpha}^{R}(z) \coloneqq \sum_{n \in \alpha(x) + \mathbb{Z}} (\varphi_{\alpha} t^n) z^{-n-1}$ ,  $\varphi^{\alpha} \mapsto \varphi^{\alpha,R}(z) \coloneqq \sum_{n \in \alpha(x) + \mathbb{Z}} (\varphi^{\alpha} t^n) z^{-n-1}$ , and  $\phi_{\alpha} \mapsto \phi_{\alpha}^{R}(z) \coloneqq \sum_{n \in 1/2 + \mathbb{Z}} (\phi_{\alpha} t^n) z^{-n-1}$ , generated by the vacuum vector  $|0\rangle_R$ , subject to the conditions  $\varphi_{\alpha} t^n |0\rangle_R = \varphi^{-\alpha} t^{n-1} |0\rangle_R = \phi_{\alpha} t^n |0\rangle_R = 0$  if  $\alpha + nK \in \widehat{\Delta}_+^R$  [KW4]. We thus obtain the  $\sigma_R$ -twisted  $\mathcal{C}^k(\mathfrak{g},f)$ -module  $\mathcal{C}^R(M) = M \otimes F^R(\mathfrak{g},f)$ .

Introduce the charge decomposition

$$
\mathcal {C} ^ {R} (M) = \bigoplus_ {m \in \mathbb {Z}} \mathcal {C} _ {m} ^ {R} (M)
$$

by letting charge  $M = 0$ , charge  $|0\rangle_R = 0$ , charge  $\varphi_\alpha^R = 1$ , charge  $\varphi^{\alpha, R} = -1$ , charge  $\phi_\alpha^R = 0$ . The most important  $\sigma_R$ -twisted fields of  $C^R(M)$  are:

$$
\begin{array}{l} d \mapsto d ^ {R} (z) = \sum_ {n \in \mathbb {Z}} d _ {n} ^ {R} z ^ {- n - 1}, L \mapsto L ^ {R} (z) = \sum_ {n \in \mathbb {Z}} L _ {n} ^ {R} z ^ {- n - 2}, \\ J ^ {\{h \}} \mapsto J ^ {\{h \}, R} (z) = \sum_ {n \in \mathbb {Z}} J _ {n} ^ {\{h \}, R} z ^ {- n - 1} \qquad (h \in \mathfrak {h}). \\ \end{array}
$$

Since  $(d_0^R)^2 = 0$ , we obtain a complex  $(\mathcal{C}^R (M),d_0^R)$ , where  $d_0^R:\mathcal{C}_m^R (M)\to \mathcal{C}_{m - 1}^R (M)$ . The homology of this complex is canonically a  $\sigma_R$ -twisted  $W^{k}(\mathfrak{g},f)$ -module

$$
H ^ {R} (M) = \bigoplus_ {m \in \mathbb {Z}} H _ {m} ^ {R} (M),
$$

where all  $H_{m}^{R}(M)$  are submodules (see [KW4] for details).

Recall [KRW] that with respect to  $L_0$  the fields  $e_{\alpha}(z), h(z), \varphi_{\alpha}(z), \varphi^{\alpha}(z), \phi_{\alpha}(z)$  have conformal weights  $1 - \alpha(x)$ ,  $1, 1 - \alpha(x)$ ,  $\alpha(x)$  and  $\alpha(x) = 1/2$ , respectively. Writing the corresponding twisted fields in the form  $a(z) = \sum_{n} a_n z^{-n - \Delta_a}$ , where  $\Delta_a$  is the conformal weight of  $a(z)$ , we obtain:

$$
e _ {\alpha} ^ {R} (z) = \sum_ {n \in \mathbb {Z}} e _ {\alpha , n} z ^ {- n - 1 + \alpha (x)}, h ^ {R} (z) = \sum_ {n \in \mathbb {Z}} h _ {n} z ^ {- n - 1}, \varphi_ {\alpha} ^ {R} (z) = \sum_ {n \in \mathbb {Z}} \varphi_ {\alpha , n} z ^ {- n - 1 + \alpha (x)},
$$

$$
\varphi^ {\alpha , R} (z) = \sum_ {n \in \mathbb {Z}} \varphi_ {n} ^ {\alpha} z ^ {- n - \alpha (x)}, \quad \phi_ {\alpha} ^ {R} (z) = \sum_ {n \in \mathbb {Z}} \phi_ {\alpha , n} z ^ {- n - 1 / 2}.
$$

Lemma 2.3. Let  $v = v_{\Lambda} \otimes |0\rangle_R \in M \otimes F^R(\mathfrak{g}, f)$ . Then

$$
e _ {\alpha , n} v = 0 \text {i f} \alpha \in \Delta_ {+} ^ {\text {n e w}}, n \geq 0 \left(\text {r e s p .} \alpha \in - \Delta_ {+} ^ {\text {n e w}}, n > 0\right),
$$

$$
h _ {n} v = \delta_ {0, n} \Lambda (h) v i f h \in \mathfrak {h}, n \geq 0,
$$

$$
\varphi_ {\alpha , n} (o r \phi_ {\alpha , n}) v = 0 i f \alpha \in \Delta_ {+} ^ {\mathrm {n e w}}, n \geq 0 (r e s p. \alpha \in - \Delta_ {+} ^ {\mathrm {n e w}}, n > 0),
$$

$$
\varphi_ {n} ^ {\alpha} v = 0 \mathrm {i f} \alpha \in \Delta_ {+} ^ {\mathrm {n e w}}, n > 0 (\mathrm {r e s p .} \alpha \in - \Delta_ {+} ^ {\mathrm {n e w}}, n \geq 0).
$$

Proof. It follows from the fact that  $e_{\alpha,n}v = 0$ ,  $\varphi_{\alpha,n}v = 0$  and  $\phi_{\alpha,n}v = 0$  if  $n - \alpha(x) \geq s_{\alpha}$ , and  $\varphi_n^\alpha v = 0$  if  $n - \alpha(x) \geq -s_\alpha$  by the construction of  $\widehat{\Delta}_+^R$  and of  $F^R(\mathfrak{g},f)$ , see [KW3].

As usual, define the Euler-Poincaré character of  $H^{R}(M)$  by the following formula:

$$
\mathrm {c h} _ {H ^ {R} (M)} (\tau , z, t) = e ^ {2 \pi i k t} \sum_ {m \in \mathbb {Z}} (- 1) ^ {m} \mathrm {t r} _ {\mathrm {H} _ {\mathrm {m}} ^ {\mathrm {R}} (\mathrm {M})} \mathrm {q} ^ {\mathrm {L} _ {0} ^ {\mathrm {R}}} \mathrm {e} ^ {2 \pi \mathrm {i} \mathrm {J} _ {0} ^ {\{z \}, \mathrm {R}}},
$$

where  $q = e^{2\pi i\tau}$ ,  $\tau$  lies in the complex upper half plane  $\mathbb{C}^+$ ,  $t \in \mathbb{C}$  and  $z \in \mathfrak{h}^f$ .

By the Euler-Poincaré principle we have

$$
\operatorname {c h} _ {H ^ {R} (M)} (\tau , z, t) = \operatorname {c h} _ {\mathcal {C} ^ {R} (M)} (\tau , z, t) \text {f o r} \tau \in \mathbb {C} ^ {+}, z \in \mathfrak {h} ^ {f}, t \in \mathbb {C}.
$$

Unfortunately, the right-hand side converges only for generic  $z \in \mathfrak{h}$  and may diverge for all  $z \in \mathfrak{h}^f$ .

To get around this difficulty, we use a trick similar to the one employed in [FKW].

Definition 2.1. An element  $f$  of  $\mathfrak{g}$  is called a nilpotent element of principal type if  $f$  is a principal nilpotent element in the centralizer of  $\mathfrak{h}^f$  (equivalently, if  $\Delta_0^0 = \emptyset$ ).

Recall that in  $\mathfrak{g} = s\ell_{r + 1}$  all nilpotent elements are of principal type, but in general this is not the case due to existence of non-principal nilpotents  $f$  with  $\mathfrak{h}^f = 0$ .

Introduce a bigrading

$$
\mathcal {C} ^ {R} (M) = \bigoplus_ {m, n \in \frac {1}{2} \mathbb {Z}} \mathcal {C} _ {m, n},
$$

by letting

$$
\deg v _ {\Lambda} \otimes | 0 \rangle_ {R} = (0, 0), \quad \deg e _ {\alpha} t ^ {n} = (\alpha (x), - \alpha (x)), \quad \deg h t ^ {n} = (0, 0),
$$

$$
\deg \varphi_ {\alpha} t ^ {n} = (\alpha (x) - 1, - \alpha (x)) = - \deg \varphi^ {\alpha} t ^ {n}, \quad \deg \phi_ {\alpha} t ^ {n} = (0, 0),
$$

and introduce the ascending fibration

$$
F_{p} = \bigoplus_{\substack{m\leq p\\ n\in \frac{1}{2}\mathbb{Z}}}\mathcal{C}_{m,n},\quad p\in \frac{1}{2}\mathbb{Z}.
$$

It is clear that  $d_0^R: F_p \to F_{p+1}$ , hence we have the associated graded complex  $(\operatorname{Gr}\mathcal{C}^R(M) = \oplus_{p \in \frac{1}{2}\mathbb{Z}} F_p / F_{p-1/2}, \operatorname{Gr}d_0^R)$ . It is also clear that

$$
\operatorname {G r} d _ {0} ^ {R} = d _ {0} ^ {\mathrm {s t}, R}.
$$

We thus obtain a spectral sequence with the first term  $(E_1 = \mathrm{Gr}\mathcal{C}^R (M)$ $d_0^{\mathrm{st},R})$

First of all, we need to show that this spectral sequence converges. For this (and for computation of characters) we need the following commutation relations.

Lemma 2.4. (a) With respect to ad  $L_0^R$  all operators  $e_{\alpha,n}^R$ ,  $\varphi_{\alpha,n}^R$ ,  $\varphi_n^{\alpha,R}$  and  $\phi_{\alpha,n}^R$  are eigenvectors with eigenvalue  $-n$ .

(b) With respect to ad  $J_0^{\{h\}, R}$  with  $h \in \mathfrak{h}$  the operators  $e_{\alpha, n}^R$  and  $\varphi_{\alpha, n}^R$  have eigenvalue  $\alpha(h)$ , and  $\varphi_n^{\alpha, R}$  has eigenvalue  $-\alpha(h)$ .  
(c) With respect to ad  $J_0^{\{h\}, R}$  with  $h \in \mathfrak{h}^f$  (resp. to ad  $J_0^{\{x\}, R}$ ) the operators  $\phi_{\alpha, n}^R$  have eigenvalue  $\alpha(h)$  (resp. 0).

Proof. (a) follows from the fact that  $L_0^R$  is the energy operator, (b) is (2.11) from [KRW], the first part of (c) is (2.12) from [KRW] and the second part holds since  $x^{\mathrm{ne}}(z) = 0$ .

![](images/7b2ab2b7618504bf91dfb2ad19ab9bcc3cb24967d10a851f9b148c50b1890a9a.jpg)

The following lemma implies the convergence of our spectral sequence and the convergence of the Euler-Poincaré character of  $E_1$ .

Lemma 2.5. Let  $f$  be a nilpotent element of  $\mathfrak{g}$  of principal type. Then we can choose  $h' \in \mathfrak{h}^f$ , such that  $\alpha(h') > 0$  for all  $\alpha \in \Delta_+^{0,\mathrm{new}} = \Delta^0 \cap \Delta_+^{\mathrm{new}}$ .

(a) Common eigenspaces of  $L_0^R$ ,  $J_0^{\{h_0\}, R}$  and  $J_0^{\{h'\}, R}$  in  $F_p$  are finite-dimensional for each  $p \in \frac{1}{2}\mathbb{Z}$ .  
(b) Common eigenspaces of  $L_0^R$ ,  $J_0^{\{h_0\}, R}$ ,  $J_0^{\{h'\}, R}$  and  $J_0^{\{x\}, R}$  in  $E_1$  are finite-dimensional.

Proof. The space  $C^R (M)$  is obtained by applying to  $v_{\Lambda}\otimes |0\rangle_R$  products of some number of operators of the following form (see Lemma 2.3):

(1)  $e_{\alpha ,n}$  with  $\alpha \in \Delta_{+}^{\mathrm{new}}$ $n < 0$  
(2)  $e_{\alpha ,n}$  with  $\alpha \in -\Delta_{+}^{\mathrm{new}}$ $n\leq 0$  
(3)  $h_n$  with  $h \in \mathfrak{h}$ ,  $n < 0$ ,  
(4)  $\varphi_{\alpha ,n}$  with  $\alpha \in \Delta_+^{\mathrm{new}}$ $n <   0$  
(5)  $\varphi_{\alpha ,n}$  with  $\alpha \in -\Delta_{+}^{\mathrm{new}}$ $n\leq 0$  
(6)  $\phi_{\alpha ,n}$  with  $\alpha \in \Delta_+^{\mathrm{new}}$ $n < 0$  
(7)  $\phi_{\alpha ,n}$  with  $\alpha \in -\Delta_{+}^{\mathrm{new}}$ $n\leq 0$  
(8)  $\varphi_n^\alpha$  with  $\alpha \in \Delta_+^{\mathrm{new}}$ ,  $n \leq 0$ ,  
(9)  $\varphi_{n}^{\alpha}$  with  $\alpha \in -\Delta_{+}^{\mathrm{new}}$ $n < 0$

By Lemma 2.4(a), only application of the operators of the form,  $e_{-\alpha,0}$  with  $\alpha \in \Delta_+^{\mathrm{new}}$ ,  $\varphi_{-\alpha,0}$  with  $\alpha \in \Delta_+^{\mathrm{new}}$ ,  $\phi_{-\alpha,0}$  with  $\alpha \in \Delta_+^{\mathrm{new}}$ , and  $\varphi_\alpha^0$  with  $\alpha \in \Delta_+^{\mathrm{new}}$  may produce infinitely many states in an eigenspace of  $L_0^R$ . Furthermore, by Lemma 2.4(b), application of all these operators to an eigenvector of  $J_0^{(h_0),R}$  changes the eigenvalue by a non-positive quantity. Since  $\alpha(h_0) > 0$  for  $\alpha \in \Delta_+^{1/2}$ , we conclude that the operators  $\phi_{-\alpha,0}$  with  $\alpha \in \Delta_+^{\mathrm{new}}$  change the eigenvalue of  $J_0^{(h_0),R}$  by a negative quantity.

Furthermore, application of the operators  $e_{-\alpha,0}$  with  $\alpha \in \Delta_+^{0,\mathrm{new}}$  change the eigenvalue of  $J_0^{\{h'\},R}$  by a negative quantity  $-\alpha(h')$ .

Finally, application of the operators  $e_{-\alpha,0}$  with  $\alpha \in \Delta_+^{\mathrm{new}}$  either changes the eigenvalue of  $J_0^{\{h_0\},R}$  by a negative quantity or else does not change this eigenvalue, but changes the degree of the filtration (resp. the eigenvalue of  $J_0^{\{x\},R}$ ) by a positive quantity.

This proves both statements of the lemma.

![](images/f3a882b2bed20ff4737b7edfdf99eeb6c7fd1e214ca4c34119a3eb6ba86e2dc9.jpg)

Now we are in a position to compute the Euler-Poincaré character  $\mathrm{ch}_{H^R (M)}(\tau ,z,t)$ , where  $z\in \mathfrak{h}^f$ , assuming that  $f$  is a nilpotent element of principal type. From now on we shall assume that  $f$  is a nilpotent element of principal type, when talking about the Euler-Poincaré characters.

First, note that, by Lemma 2.5(a) our spectral sequence converges. Hence, by Lemmas 2.5(b) and 2.1(a), we have:

$$
\mathrm {c h} _ {H ^ {R} (M)} (\tau , z, t) = e ^ {2 \pi i k t} \lim _ {\epsilon \rightarrow 0} \sum_ {m \in \mathbb {Z}} (- 1) ^ {m} \mathrm {t r} _ {\mathcal {C} _ {\mathrm {m}} ^ {\mathrm {R}} (\mathrm {M})} \mathrm {q} ^ {\mathrm {L} _ {0} ^ {\mathrm {R}}} \mathrm {e} ^ {2 \pi \mathrm {i} \mathrm {J} _ {0} ^ {\{\mathrm {z} + \epsilon \mathrm {x} \}, \mathrm {R}}}.
$$

Since  $L_0^R = L_0^{\mathfrak{g},R} - x_0 + L_0^{\mathrm{ch},R} + L_0^{\mathrm{ne},R}$ , we obtain that the right-hand side is equal to the product of  $e^{2\pi ikt}$  and the following two expressions:

$$
I = \lim _ {\epsilon \rightarrow 0} \operatorname {t r} _ {\mathrm {M}} \mathrm {q} ^ {\mathrm {L} _ {0} ^ {\mathfrak {g}, \mathrm {R}} - \mathrm {x} _ {0}} \mathrm {e} ^ {2 \pi \mathrm {i} (\mathrm {z} + \epsilon \mathrm {x}) _ {0}},
$$

$$
{ I I } { = } { \operatorname* { l i m } _ { \epsilon \to 0 } \mathrm { s t r } _ { F ^ { R } ( \mathfrak { g } , f ) } q ^ { L _ { 0 } ^ { \mathrm { c h } , R } + L _ { 0 } ^ { \mathrm { n e } , R } } e ^ { 2 \pi i ( ( z + \epsilon x ) _ { 0 } ^ { \mathrm { c h } , R } + ( z + \epsilon x ) _ { 0 } ^ { \mathrm { n e } , R } ) } , }
$$

where str stands for the supertrace.

We let  $S_{+} = \Delta_{+} \backslash \Delta_{+}^{0}$  for short (which is consistent with our earlier notation).

Lemma 2.6. (a) The constants  $s_{\mathfrak{g}}$ ,  $s_{\mathrm{ne}}$  and  $s_{\mathrm{ch}}$ , introduced in [KW4], Proposition 3.2, for arbitrary  $\sigma$ , are given by the following formulas for  $\sigma = \sigma_R$ :

$$
s _ {\mathfrak {g}} = - \frac {k}{k + h ^ {\vee}} \sum_ {\alpha \in S _ {+}} \binom {s _ {\alpha}} {2}, s _ {\mathrm {n e}} = - \frac {1}{1 6} \dim \mathfrak {g} _ {1 / 2}, s _ {\mathrm {c h}} = (\rho | x) - \frac {h ^ {\vee}}{2} | x | ^ {2}.
$$

(b) The element  $\gamma' \in \mathfrak{h}^*$ , introduced in [KW4], Corollary 3.1, is given by the following formula for  $\sigma = \sigma_R$ :

$$
\gamma^ {\prime} = \sum_ {\alpha \in S _ {+}} s _ {\alpha} \alpha - \rho .
$$

Proof. Formula for  $s_{\mathfrak{g}}$  follows from [KW4], formula (3.9), using that

$$
\left( \begin{array}{c} s _ {- \alpha} \\ 2 \end{array} \right) = \left( \begin{array}{c} s _ {\alpha} \\ 2 \end{array} \right)
$$

(which follows from  $s_{\alpha} + s_{-\alpha} = 1$ ) and  $s_{\alpha} = 0$  if  $\alpha = \Delta_{+}^{0}$ .

Formula for  $s_{\mathrm{ne}}$  follows from that in [KW4], formula (3.10), since  $s_{\alpha} = \pm 1 / 2$  for  $\alpha \in \Delta_{\mp}^{1 / 2}$ .

Since  $s_{\alpha} = -\alpha(x)$  or  $1 - \alpha(x)$ , each summand in [KW4], formula (3.11) for  $s_{\mathrm{ch}}$ , equals  $\alpha(x)(1 - \alpha(x)) / 2$ . Hence  $s_{\mathrm{ch}} = \frac{1}{2}\sum_{\alpha \in S_+}\alpha(x) - \frac{1}{2}\sum_{\alpha \in S_+}\alpha(x)^2 = (\rho|x) - \frac{h^{\vee}}{2}|x|^2$ , proving (a).

Next, by definition, we have:  $\gamma' = \frac{1}{2} \sum_{\alpha \in S_+ \cup \Delta_+^0} (s_\alpha \alpha + s_{-\alpha}(-\alpha))$ . Since  $s_\alpha + s_{-\alpha} = 1$  and  $s_\alpha = 0$  if  $\alpha \in \Delta_+^0$ , we obtain:  $\gamma' = \sum_{\alpha \in S_+} s_\alpha \alpha - \frac{1}{2} \sum_{\alpha \in S_+ \cup \Delta_+^0} \alpha$ , proving (b).

![](images/f4b70fab92d49d1d71b828fdfc5bd3f2b030e896d35c2118f73b22cac3ad7df9.jpg)

Lemma 2.7. (a)  $\hat{\rho}^R = h^\vee D - \gamma' + (\sum_{\alpha \in S_+} \alpha(x)s_\alpha - \rho(x) + \frac{h^\vee}{2}|x|^2)K.$

(b)  $\frac{(\bar{\Lambda}|\bar{\Lambda} + 2\bar{\rho}^R)}{2(k + h^\vee)} + s_{\mathfrak{g}} = \frac{(\Lambda|\Lambda + 2\hat{\rho}^R)}{2(k + h^\vee)} - \Lambda(D)$  for any  $\Lambda \in \widehat{\mathfrak{h}}$ .

Proof. By [KW3], Corollary 3.2, we have:

$$
\widehat {\rho} ^ {R} = h ^ {\vee} D - \gamma^ {\prime} + a K \text {f o r s o m e} a \in \mathbb {C}.
$$

In order to compute  $a$ , recall that

$$
\widehat {\rho} ^ {R} = t _ {x} \bar {w} (\widehat {\rho}) = t _ {x} \bar {w} (h ^ {\vee} D + \rho) = h ^ {\vee} D + h ^ {\vee} x + \bar {w} (\rho) - (\frac {h ^ {\vee}}{2} | x | ^ {2} + (x | \bar {w} (\rho)) K.
$$

Comparing with the first formula for  $\widehat{\rho}^R$ , we get:

$$
- \gamma^ {\prime} = \bar {w} (\rho) + h ^ {\vee} x \text {a n d} a = - \frac {h ^ {\vee}}{2} | x | ^ {2} - (\bar {w} (\rho) | x).
$$

Hence  $a = \frac{h^{\vee}}{2} |x|^2 + (\gamma' |x)$ . Substituting  $\gamma'$  from Lemma 2.6(b), we obtain (a).

We have by definition and (a):

$$
\begin{array}{l} \Lambda = k D + \bar {\Lambda} + (\Lambda | D) K, \\ \hat {\rho} ^ {R} = h ^ {\vee} D + \bar {\hat {\rho}} ^ {R} + (\sum_ {\alpha \in S _ {+}} \alpha (x) s _ {\alpha} - \rho (x) + \frac {h ^ {\vee}}{2} | x | ^ {2}) K. \\ \end{array}
$$

Hence

$$
\frac {(\Lambda | \Lambda + 2 \widehat {\rho} ^ {R})}{2 (k + h ^ {\vee})} = \frac {(\bar {\Lambda} | \bar {\Lambda} + 2 \bar {\widehat {\rho}} ^ {R})}{2 (k + h ^ {\vee})} + \frac {k}{k + h ^ {\vee}} \left(\sum_ {\alpha \in S _ {+}} \alpha (x) s _ {\alpha} - \rho (x) + \frac {h ^ {\vee}}{2} | x | ^ {2}\right) + \Lambda (D).
$$

Adding to both sides  $s_{\mathfrak{g}}$  and using in the left-hand side the formula for  $s_{\mathfrak{g}}$ , given by Lemma 2.6(a), we obtain:

$$
\frac {(\Lambda | \Lambda + 2 \hat {\rho} ^ {R})}{2 (k + h ^ {\vee})} - \Lambda (D) = \frac {(\bar {\Lambda} | \bar {\Lambda} + 2 \hat {\rho} ^ {R})}{2 (k + h ^ {\vee})} + s _ {\mathfrak {g}} + \frac {k}{k + h ^ {\vee}} A,
$$

where  $A = \sum_{\alpha \in S_+} \left( \binom{s_\alpha}{2} + \alpha(x)s_\alpha \right) - \rho(x) + \frac{h^\vee}{2}|x|^2$ . By definition of  $s_\mathrm{ch}$  given by [KW4], formula (3.11), and the third formula of Lemma 2.6(a), we obtain that  $A = 0$ , proving (b).

![](images/9f31a58a3ed395203c186ce3fa02ee0cd7f1b4eb92586d7dde6e1e14321a55c7.jpg)

Lemma 2.8. (a) On the  $\widehat{\mathfrak{g}}^R$ -module  $M$  (with the highest weight  $\Lambda$ ) we have:

$$
L _ {0} ^ {\mathfrak {g}, R} = \frac {(\Lambda | \Lambda + 2 \widehat {\rho} ^ {R})}{2 (k + h ^ {\vee})} I _ {M} - D.
$$

(b) For  $z\in \mathfrak{h}^f$  we have:

$$
\begin{array}{l} I I = q ^ {s _ {\mathrm {c h}} + s _ {\mathrm {n e}}} e ^ {\pi i \sum_ {\alpha \in \Delta_ {1 / 2}} s _ {\alpha} \alpha (z) + 2 \pi i (\bar {\rho} ^ {R} (z) - \rho (z))} \\ \times \prod_{\alpha \in \widehat{\Delta}_{+}^{R}}(1 - e^{-2\pi i\alpha (z)})^{\mathrm{mult}\alpha}\prod_{j = 1}^{\infty}(1 - q^{j})^{-r}\prod_{\substack{\alpha \in \widehat{\Delta}_{+}^{R,\mathrm{re}}\\ \alpha (x) = 0, - 1 / 2}}(1 - e^{-2\pi i\alpha (z)})^{-1}, \\ \end{array}
$$

Proof. By [KW4], Proposition 3.2 and Corollary 3.2, we have:

$$
L _ {0} ^ {\mathfrak {g}, R} v _ {\Lambda} = \left(\frac {1}{2 (k + h ^ {\vee})} (| \bar {\Lambda} | ^ {2} + 2 (\bar {\Lambda} | \hat {\rho} ^ {R})) + s _ {\mathfrak {g}}\right) v _ {\Lambda}.
$$

Hence, by Lemma 2.7:

$$
L _ {0} ^ {\mathfrak {g}, R} v _ {\Lambda} = \left(\frac {(\Lambda | \Lambda + 2 \hat {\rho} ^ {R})}{2 (k + h ^ {\vee})} - \Lambda (D)\right) v _ {\Lambda}.
$$

Since  $L_0^{\mathfrak{g},R} = -D + \mathrm{const}$ , (a) follows.

By Lemmas 2.3, 2.4 and [KW4], Proposition 3.2 and Corollary 3.3, we have:

$$
I I = \lim  _ {\epsilon \rightarrow 0} q ^ {s _ {\mathrm {c h}} + s _ {\mathrm {n e}}} e ^ {2 \pi i \left(\frac {1}{2} \sum_ {\alpha \in \Delta^ {1 / 2}} s _ {\alpha} \alpha (z + \epsilon x) - (\rho - \bar {\hat {\rho}} ^ {R}) (z + \epsilon x)\right)} \mathrm {c h} _ {F ^ {R}} (\tau , z + \epsilon x),
$$

where

$$
\operatorname {c h} _ {F ^ {R}} (\tau , z + \epsilon x) = \prod_ {\substack {\alpha \in S _ {+} \\ n > - s _ {\alpha}}} \left(1 - q ^ {n} e ^ {2 \pi i \alpha (z + \epsilon x)}\right) \prod_ {\substack {\alpha \in S _ {+} \\ n > - s _ {- \alpha}}} \left(1 - q ^ {n} e ^ {- 2 \pi i \alpha (z + \epsilon x)}\right) \prod_ {\substack {\alpha \in \Delta^ {1 / 2} \\ n > - s _ {\alpha}}} \left(1 - q ^ {n} e ^ {2 \pi i \alpha (z + \epsilon x)}\right) ^ {- 1}.
$$

Hence

$$
\begin{array}{l} { I I } { = } { q ^ { s _ { \mathrm { c h } } + s _ { \mathrm { n e } } } e ^ { \pi i \sum _ { \alpha \in \Delta ^ { 1 / 2 } } s _ { \alpha } \alpha ( z ) + 2 \pi i ( \bar { \rho } ^ { R } - \rho ) ( z ) } } \\ \times \left(\prod_ {\substack {\alpha \in \widehat {\Delta} _ {+} ^ {R} \\ | \alpha (x) | \geq 1}} (1 - e ^ {- \alpha}) \prod_ {\substack {\alpha \in \widehat {\Delta} _ {+} ^ {R} \\ \alpha (x) = 1 / 2}} (1 - e ^ {- \alpha})\right) (- \tau D + z), \\ \end{array}
$$

which proves (b).

![](images/9d7997487970829781933e46e7f8d3fefbff135fdea845131a145ae1966dae74.jpg)

Lemma 2.9. (a)  $\sum_{\alpha \in \Delta^{1/2}} s_{\alpha} \alpha(z) = -\sum_{\alpha \in \Delta_{+}^{1/2}} \alpha(z)$  if  $z \in \mathfrak{h}^f$ .

(b) All the  $\mathfrak{g}_0^f$ -modules  $\mathfrak{g}_j$  are self-contragredient. In particular,  $\operatorname{tr}_{\mathfrak{g}_j} \operatorname{ad} a = 0$  for all  $a \in \mathfrak{g}_0^f$  and  $j \in \frac{1}{2}\mathbb{Z}$ , and  $\rho(z) = \frac{1}{2}\sum_{\alpha \in \Delta_+^0} \alpha(z)$  for  $z \in \mathfrak{h}^f$ .

Proof. (a) follows from the fact that  $s_{\alpha} = -1 / 2$  (resp.  $= 1 / 2$ ) if  $\alpha \in \Delta_{+}^{1 / 2}$  (resp.  $\Delta_{-}^{1 / 2}$ ).

In order to prove (b), note that the  $\mathfrak{g}_0^f$ - (even  $\mathfrak{g}_0$ -) modules  $\mathfrak{g}_j$  and  $\mathfrak{g}_{-j}$  are contragredient since they are paired by the invariant form  $(.|\cdot)$ . On the other hand,  $(\operatorname{ad} f)^{2j}$  gives an isomorphism of the  $\mathfrak{g}_0^f$ -modules  $\mathfrak{g}_j$  and  $\mathfrak{g}_{-j}$ .

![](images/f8759ba7c678e11f8872ec79974c7177222f3111598bcd9546649b3fe64ca6cb.jpg)

Lemma 2.10.  $\{\alpha|_{\mathfrak{h}^f} \mid \alpha \in \Delta_+^R, \alpha(x) = 1/2\} = \{\alpha|_{\mathfrak{h}^f} \mid \alpha \in \Delta_+^R, \alpha(x) = -1/2\}$ .

Proof. Recall that  $\Delta^{1/2} = \Delta_{+}^{1/2} \sqcup \Delta_{-}^{1/2}$  and  $s_{\alpha} = \mp 1/2$  if  $\alpha \in \Delta_{\pm}^{1/2}$ . Therefore, if  $\alpha \in \Delta_{\pm}^{1/2}$ , then  $\pm (\alpha - K/2) \in \Delta_{+}^{R}$ . On the other hand, by Lemma 2.9(b),  $\Delta_{+}^{1/2}|_{\mathfrak{h}^f} = -\Delta_{-}^{1/2}|_{\mathfrak{h}^f}$ , which proves the lemma.

![](images/de061b5513cc7961f8a90f7c7e069164bf4d9cc3e5404255fe7f3cbebe2087ff.jpg)

Note that the  $D$ -operator for the  $\sigma_R$ -twisted affine Lie algebra  $\widehat{\mathfrak{g}}^R$  is

$$
D ^ {R} := t _ {x} \bar {w} (D) = D + x - \frac {(x | x)}{2} K.
$$

Let

$$
R _ {\widehat {\mathfrak {H}} ^ {R}} = e ^ {\widehat {\rho} ^ {R}} \prod_ {\alpha \in \widehat {\Delta} _ {+} ^ {R}} (1 - e ^ {- \alpha}) ^ {\text {m u l t} \alpha}
$$

be the Weyl denominator for  $\widehat{\mathfrak{g}}^R$ . Using Lemmas 2.8 and 2.9, we can rewrite  $\mathrm{ch}_{H^R (M)}$  as follows (here and further  $z\in \mathfrak{h}^f$ ):

$$
\begin{array}{l} \begin{array}{l} (2. 2) \quad \operatorname {c h} _ {H ^ {R} (M)} (\tau , z, t) = q ^ {\frac {(\Lambda | \Lambda + 2 \hat {\rho} ^ {R})}{2 (k + h ^ {\vee})} - \frac {k}{2} (x | x) + s _ {\mathrm {c h}} + s _ {\mathrm {n e}}} e ^ {\pi i \left(\sum_ {\alpha \in \Delta^ {1 / 2}} s _ {\alpha} \alpha (z) - \sum_ {\alpha \in \Delta_ {+} ^ {0}} \alpha (z)\right)} e ^ {- 2 \pi i h ^ {\vee} t} \end{array} \\ \times \left(\frac{R_{\widehat{\mathfrak{g}}^{R}}\mathrm{ch}_{M}}{\prod_{j = 1}^{\infty}(1 - e^{-jK})^{r}\prod_{\substack{\alpha \in \widehat{\Delta}_{+}^{R,\mathrm{re}}\\ \alpha (x) = 0, - 1 / 2}}(1 - e^{-\alpha})}\right)(2\pi i(-\tau D^{R} + z + tK)). \\ \end{array}
$$

This formula makes sense since  $\alpha|_{\mathfrak{h}^f} \neq 0$  if  $\alpha(x) = 0$  because  $f$  is a nilpotent element of principal type, and  $\alpha|_{\mathfrak{h}^f} \neq 0$  if  $|\alpha(x)| = 1/2$  for any nilpotent  $f$  [EK].

Formula (2.2) implies the following corollary.

Corollary 2.1. The minimal eigenvalue of  $L_0^R$  on  $H^{R}(M)$  equals

$$
\frac {(\Lambda | \Lambda + 2 \widehat {\rho} ^ {R})}{2 (k + h ^ {\vee})} - (\Lambda | D ^ {R}) + s _ {\mathrm {c h}} + s _ {\mathrm {n e}} - \frac {k}{2} (x | x).
$$

All other eigenvalues are obtained from this by adding a positive integer.

By the general principles of conformal field theory, define the normalized Euler-Poincaré character by:

$$
\chi_ {H ^ {R} (M)} (\tau , z, t) = e ^ {- \frac {\pi i \tau}{1 2} c (\mathfrak {g}, f, k)} \mathrm {c h} _ {H ^ {R} (M)} (\tau , z, t).
$$

Using (2.1) and Lemma 2.6(a), we obtain:

$$
\begin{array}{l} - \frac {1}{2 4} c (\mathfrak {g}, f, k) + s _ {\mathrm {c h}} + s _ {\mathrm {n e}} - \frac {k}{2} | x | ^ {2} = - \frac {1}{2 4} (\dim \mathfrak {g} _ {0} + \dim \mathfrak {g} _ {1 / 2}) + \frac {| \rho | ^ {2}}{2 (k + h ^ {\vee})} \\ = - \frac {1}{2 4} \dim \mathfrak {g} ^ {f} + \frac {| \widehat {\rho} ^ {R} | ^ {2}}{2 (k + h ^ {\vee})}. \\ \end{array}
$$

(Recall that  $\dim \mathfrak{g}^f = \dim \mathfrak{g}_0 + \dim \mathfrak{g}_{1/2}$ .) Using this, we can rewrite (2.2) as follows:

$$
\chi_ {H ^ {R} (M)} (\tau , z, t) = \frac {B _ {\Lambda} (\tau , z , t)}{\psi (\tau , z , t)}, \tag {2.3}
$$

where

$$
B _ {\Lambda} (\tau , z, t) = q ^ {\frac {| \Lambda + \hat {\rho} ^ {R} | ^ {2}}{2 (k + h \vee)}} \left(R _ {\hat {\mathfrak {g}} ^ {R}} \mathrm {c h} _ {M}\right) \left(2 \pi i (- \tau D ^ {R} + z + t K)\right) \tag {2.4}
$$

is the numerator of the normalized character  $\chi_{M}$  of the  $\widehat{\mathfrak{g}}$ -module  $M$  (with highest weight  $\Lambda$  of level  $k$ ) and

$$
\begin{array}{l} \psi (\tau , z, t) = e ^ {2 \pi i h ^ {\vee} t} q ^ {\frac {1}{2 4}} \dim \mathfrak {g} ^ {f} e ^ {\pi i \sum_ {\alpha \in \Delta_ {+} ^ {R, 0} \cup \Delta_ {+} ^ {R, 1 / 2}} \alpha (z)} \\ \times \prod_{j = 1}^{\infty}(1 - q^{j})^{r}\prod_{\substack{\alpha \in \widehat{\Delta}_{+}^{R,\text{re}}\\ \alpha (x) = 0, - 1 / 2}}(1 - e^{2\pi i\alpha (\tau D^{R} - z)}). \\ \end{array}
$$

Using Lemma 2.10, we rewrite the last formula as

$$
\begin{array}{l} \psi (\tau , z, t) = e ^ {2 \pi i h ^ {\vee} t} q ^ {\frac {1}{2 4}} \dim \mathfrak {g} ^ {f} e ^ {\pi i \sum_ {\alpha \in \Delta_ {+} ^ {R, 0} \cup \Delta_ {+} ^ {R, 1 / 2}} \alpha (z)} \tag {2.5} \\ \times \prod_ {n = 1} ^ {\infty} (1 - q ^ {n}) ^ {r} \prod_ {\alpha \in \Delta_ {+} ^ {R, 0} \cup \Delta_ {+} ^ {R, 1 / 2}} (1 - q ^ {n - 1} e ^ {- 2 \pi i \alpha (z)}) (1 - q ^ {n} e ^ {2 \pi i \alpha (z)}). \\ \end{array}
$$

If  $\Lambda \in Pr^k$  and  $M = L(\Lambda)$ , the numerator  $B_{\Lambda}$  is explicitly known (see Theorem 1.2); in [KW1], §3 one can find an explicit expression in terms of theta functions:

$$
B _ {\Lambda} (\tau , z, t) = A _ {\Lambda^ {0} + \widehat {\rho}} (u \tau , \bar {y} ^ {- 1} (z + \tau \beta), \frac {1}{u} (t + (z | \beta) + \frac {\tau | \beta | ^ {2}}{2})), z \in \mathfrak {h} ^ {f},
$$

where  $A_{\lambda}(\tau, z, t) = \sum_{w \in W} \epsilon(w) \Theta_{w(\lambda)}(\tau, z, t)$  (cf. [K1], Chapter 13). Dividing and multiplying the right hand side of (2.3) by  $A_{\hat{\rho}^R}(u\tau, \bar{y}^{-1}(z + \tau \beta), \frac{1}{u}(t + (z|\beta) + \frac{\tau|\beta|^2}{2}))$ , we obtain:

$$
\chi_ {H ^ {R} \left(L (\Lambda)\right)} (\tau , z, t) = \chi_ {L ^ {R} \left(\Lambda^ {0}\right)} \left(u \tau , \bar {y} ^ {- 1} (z + \tau \beta), \frac {1}{u} (t + (z | \beta) + \frac {\tau | \beta | ^ {2}}{2})\right) \frac {C (\tau , z , t)}{\psi (\tau , z , t)}, \tag {2.6}
$$

where

$$
\begin{array}{l} C (\tau , z, t) = q ^ {\frac {u}{2 4} \dim \mathfrak {g}} e ^ {2 \pi i ((\rho^ {R} | \bar {y} ^ {- 1} (z + \tau \beta)) + \frac {h ^ {\vee}}{u} (t + (z | \beta) + \frac {\tau | \beta | ^ {2}}{2}))} \\ \times \prod_ {\alpha \in \widehat {\Delta} _ {+} ^ {R}} (1 - e ^ {- \alpha}) ^ {\mathrm {m u l t} \alpha} \big (u \tau , \bar {y} ^ {- 1} (z + \tau \beta), 0 \big). \\ \end{array}
$$

Remark 2.1. (a) Since  $\mathfrak{g}^f$  and  $\mathfrak{g}_0 + \mathfrak{g}_{1/2}$  are isomorphic as  $\mathfrak{h}^f$ -modules, we have:

$$
(1 - q ^ {n}) ^ {r} \prod_ {\alpha \in \Delta_ {+} ^ {R, 0} \cup \Delta_ {+} ^ {R, 1 / 2}} (1 - q ^ {n} e ^ {- 2 \pi i \alpha (z)}) (1 - q ^ {n} e ^ {2 \pi i \alpha (z)}) = \det _ {\mathfrak {g} ^ {f}} (1 - q ^ {n} e ^ {2 \pi i z}), z \in \mathfrak {h} ^ {f}.
$$

Let  $\rho^f (z) = \frac{1}{2}\sum_{\alpha \in \Delta_+^{R,0}\cup \Delta_+^{R,1 / 2}}\alpha (z), z\in \mathfrak{h}^f$ . Thus, formulas (2.3) - (2.5) mean that the quantum Hamiltonian reduction of the  $\widehat{\mathfrak{g}}^R$ -module  $M$  to the  $W_{k}(\mathfrak{g},f)$ -module  $H^{R}(M)$  does not change the numerator of its normalized character, but "reduces" its denominator, replacing  $\mathfrak{g}$  by  $\mathfrak{g}^f$ .

(b) The product in  $C(\tau, z, t)$  is equal to  $\prod_{\alpha \in \widehat{\Delta}_{\Lambda, +}^{R}} (1 - e^{-\alpha})^{\mathrm{mult}\alpha}(\tau, z, 0)$ . This follows from formula (2.11) below.

2.3 Modular invariance, asymptotics, conditions of vanishing and convergence of normalized Euler-Poincaré characters in the Ramond sector. Formula (2.5) can be rewritten again in terms of the Dedekind  $\eta$ -function  $\eta(\tau) = q^{1/24} \prod_{j=1}^{\infty} (1 - q^j)$  and the following modular function in  $\tau \in \mathbb{C}^+$ ,  $s \in \mathbb{C}$ :

$$
f (\tau , s) = e ^ {\frac {\pi i \tau}{6}} e ^ {\pi i s} \prod_ {n = 1} ^ {\infty} (1 - q ^ {n} e ^ {2 \pi i s}) (1 - q ^ {n - 1} e ^ {- 2 \pi i s}) \tag {2.7}
$$

as follows:

$$
\psi (\tau , z, t) = e ^ {2 \pi i h ^ {\vee} t} \eta (\tau) ^ {r} \prod_ {\alpha \in \Delta_ {+} ^ {R, 0} \cup \Delta_ {+} ^ {R, 1 / 2}} f (\tau , \alpha (z)). \tag {2.8}
$$

Lemma 2.11. (a) One has the following transformation properties:

$$
\eta \left(- \frac {1}{\tau}\right) = (- i \tau) ^ {1 / 2} \eta (\tau), f \left(- \frac {1}{\tau}, \frac {s}{\tau}\right) = - i e ^ {\pi i s ^ {2} / \tau} f (\tau , s).
$$

(b) As  $\tau \downarrow 0$ , one has:

$$
\eta (\tau) \sim (- i \tau) ^ {- 1 / 2} e ^ {- \pi i / 1 2 \tau}, f (\tau , - a \tau) \sim 2 (\sin \pi a) e ^ {- \pi i / 6 \tau}, a \in \mathbb {C}.
$$

Proof. By the Jacobi triple product identity, one has:

$$
\begin{array}{l} f (\tau , s) = \theta (\tau , s) / \eta (\tau), \text {w h e r e} \\ \theta (\tau , s) = e ^ {\pi i (\tau / 4 + s)} \prod_ {n = 1} ^ {\infty} (1 - q ^ {n}) (1 - q ^ {n} e ^ {2 \pi i s}) (1 - q ^ {n - 1} e ^ {- 2 \pi i s}) \\ = \sum_ {n \in \mathbb {Z}} (- 1) ^ {n - 1} e ^ {2 \pi i s (n - 1 / 2)} q ^ {(n - 1 / 2) ^ {2} / 2}. \\ \end{array}
$$

Now (a) follows from the transformation formula for theta-functions (see e.g. [K1], Chapter 13 for details).

(b) follows from formulas in (a) with  $\tau$  replaced by  $-1 / \tau$ .

Assuming that  $k\neq 0$  , define the following quadratic form on  $\mathfrak{h}^f$  ..

$$
Q (z) = \frac {k + h ^ {\vee}}{k} (z | z) - \frac {1}{k} \sum_ {\alpha \in \Delta_ {+} ^ {R, 0} \cup \Delta_ {+} ^ {R, 1 / 2}} \alpha (z) ^ {2}.
$$

Now we can prove a modular transformation formula for the normalized Euler-Poincaré characters  $\chi_{H^R (L(\Lambda))}$ , where  $\Lambda$  runs over the set  $Pr^{k,R}(\mod \mathbb{C}K)$  of all principal admissible weights of level  $k$  of the affine Lie algebra  $\widehat{\mathfrak{g}}^R$ . (The assumption that  $k\neq 0$  is not restrictive since  $Prn^{0,R}(\mathfrak{g},f) = \emptyset$  if  $f\neq 0$ .)

Theorem 2.1. For  $\Lambda \in Pr^{k,R}$  one has:

(a)  $\chi_{H^R (L(\Lambda))}\left(-\frac{1}{\tau},\frac{z}{\tau},t - \frac{Q(z)}{2\tau}\right) = (-i)^{\frac{1}{2} (\dim \mathfrak{g} - \dim \mathfrak{g}^f)}\sum_{\Lambda '\in Pr^{k,R}}a(\Lambda ,\Lambda ')\chi_{H^R (L(\Lambda'))}(\tau ,z,t),$  where  $a(\Lambda ,\Lambda^{\prime})$  is as defined in Theorem 1.3(a).

(b)  $\chi_{H^R (L(\Lambda))}(\tau +1,z,t) = e^{2\pi is_\Lambda^f}\chi_{H^R (L(\Lambda))}(\tau ,z,t),$  where  $s_\Lambda^f = \frac{|\Lambda + \widehat{\rho}^R|^2}{2(k + h^\vee)} -\Lambda (D^R) - \frac{1}{24}\dim \mathfrak{g}^f.$

Proof. Since  $B_{\Lambda} = \chi_{L(\Lambda)}D_{\mathfrak{g}^R}$ , we have from Theorem 1.3(a) and (1.4):

$$
B _ {\Lambda} \left(- \frac {1}{\tau}, \frac {z}{\tau}, t - \frac {(z | z)}{2 \tau}\right) = (- i) ^ {| \Delta_ {+} |} (- i \tau) ^ {r / 2} \sum_ {\Lambda^ {\prime} \in P r ^ {k, R}} a (\Lambda , \Lambda^ {\prime}) B _ {\Lambda^ {\prime}} (\tau , z, t).
$$

Hence

$$
\begin{array}{l} (2. 9) \qquad B _ {\Lambda} \left(- \frac {1}{\tau}, \frac {z}{\tau}, t - \frac {Q (z)}{2 \tau}\right) = (- i) ^ {| \Delta_ {+} |} (- i \tau) ^ {r / 2} e ^ {\frac {\pi i}{\tau} (k + h ^ {\vee}) ((z | z) - Q (z))} \\ \times \sum_ {\Lambda^ {\prime} \in P r ^ {k, R}} a (\Lambda , \Lambda^ {\prime}) B _ {\Lambda^ {\prime}} (\tau , z, t). \\ \end{array}
$$

Here we used also that the only dependence of  $B_{\Lambda}$  on  $t$  is the factor  $e^{2\pi i(k + h^{\vee})t}$ . On the other hand, using formula (2.8) for  $\psi (\tau ,z,t)$  and Lemma 2.11(a), we obtain:

$$
\begin{array}{l} \psi \left(- \frac {1}{\tau}, \frac {z}{\tau}, t - \frac {Q (z)}{2 \tau}\right) = (- i) ^ {\left| \Delta_ {+} ^ {R, 0} \cup \Delta_ {+} ^ {R, 1 / 2} \right|} e ^ {- \frac {\pi i h ^ {\vee}}{\tau} Q (z)} \tag {2.10} \\ \times e ^ {\frac {\pi i}{\tau} \sum_ {\alpha \in \Delta_ {+} ^ {R, 0} \cup \Delta_ {+} ^ {R, 1 / 2}} \alpha (z) ^ {2}} \psi (\tau , z, t). \\ \end{array}
$$

Now (a) follows from (2.3), (2.9), (2.10), the definition of  $Q(z)$  and the fact that  $\dim \mathfrak{g}^f = \dim \mathfrak{g}_0 + \dim \mathfrak{g}_{1/2} = 2|\Delta_+^0 \cup \Delta_+^{1/2}| + r$ .

(b) follows from (2.3), (2.4), (2.5).

Theorem 2.2. For the principal admissible weight  $\Lambda = (t_{\beta}\bar{y}).(\Lambda^0 +(k + h^\vee -p)D^R)\in Pr^{k,R}$ , where  $\bar{y}\in W^{R},\beta \in Q^{*,R}$ ,  $k + h^{\vee} = p / u$ ,  $\Lambda^0\in \widehat{P}_+^{p - h^\vee ,R}$ , one has for each  $z\in \mathfrak{h}^f$ , as  $\tau \downarrow 0$ :

$$
\mathrm {c h} _ {H ^ {R} (L (\Lambda))} (\tau , - \tau z, 0) \sim \epsilon (\bar {y}) u ^ {- r / 2} a (\Lambda^ {0}) A _ {\beta} (z) e ^ {\frac {\pi i}{1 2 \tau} (\dim \mathfrak {g} ^ {f} - \frac {h ^ {\vee}}{p u} \dim \mathfrak {g})},
$$

where

$$
A _ {\beta} (z) = \frac {\prod_ {\alpha \in \Delta_ {+} ^ {R}} 2 \sin \frac {\pi (\alpha | z - \beta)}{u}}{\prod_ {\alpha \in \Delta_ {+} ^ {R , 0} \cup \Delta_ {+} ^ {R , 1 / 2}} 2 \sin \pi (\alpha | z)}
$$

and  $a(\Lambda^0)$  is the constant defined in Theorem 1.3(b).

Proof. Using Lemma 2.2(b) and Lemma 2.11(b) we obtain from (2.8) and a similar formula for  $D_{\widehat{\mathfrak{g}}^R}$  (or (1.5)):

$$
D _ {\hat {\mathfrak {g}} ^ {R}} (\tau , - \tau z, 0) \sim (- i \tau) ^ {- r / 2} \prod_ {\alpha \in \Delta_ {+} ^ {R}} 2 \sin \pi (\alpha | z) e ^ {- \frac {\pi i}{1 2 \tau} \dim \mathfrak {g}},
$$

$$
\psi (\tau , - \tau z, 0)\sim (-i\tau)^{-r / 2}\prod_{\substack{\alpha \in \Delta_{+}^{R,0}\cup \Delta_{+}^{R,1 / 2}}}2\sin \pi (\alpha |z)e^{-\frac{\pi i}{12\tau}\dim \mathfrak{g}^{f}}.
$$

The asymptotics for the numerator of  $\mathrm{ch}_{H^R (L(\Lambda))}(\tau , - \tau z,0)$  follow from the first of these formulas and Theorem 1.3(b). Now Theorem 2.2 follows, using the second of these formulas.

![](images/ed72470a4543a1e2af432a3851868892d5d8ffe7ca1fa8b9c26dd0d9547492d8.jpg)

Given  $\Lambda \in \widehat{\mathfrak{h}}^*$ , let  $\Delta_{\Lambda}^{R} = \Delta^{R} \cap \widehat{\Delta}_{\Lambda}^{R}$ , and  $\Delta_{\Lambda, +}^{R} = \Delta_{+}^{R} \cap \widehat{\Delta}_{\Lambda}^{R}$ .

Lemma 2.12. Let  $\Lambda$  be as in Theorem 2.2. Then

$$
\left\{\alpha \in \Delta^ {R} | (\alpha | \beta) \in u \mathbb {Z} \right\} = \Delta_ {\Lambda} ^ {R}.
$$

Proof. Let  $\widehat{\Delta}_{(u)}^{R} = \{\gamma + nuK | \gamma \in \Delta^{R}, n \in \mathbb{Z}\} \cup \{unK | n \in \mathbb{Z}, n \neq 0\}$ , and note that

$$
\widehat {\Delta} _ {\Lambda} ^ {R} = t _ {\beta} \left(\widehat {\Delta} _ {(u)} ^ {R}\right). \tag {2.11}
$$

Let  $\alpha \in \Delta^R$  be such that  $(\alpha|\beta) = un$  for some  $n \in \mathbb{Z}$ . Then  $\alpha = t_{\beta} (\alpha + unK) \in t_{\beta}(\widehat{\Delta}_{(u)}^R) = \widehat{\Delta}_{\Lambda}^R$ , which proves that  $\alpha \in \Delta_{\Lambda}^{R}$ .

Conversely, if  $\alpha \in \Delta_{\Lambda}^{R}$ , then  $\alpha \in t_{\beta}(\widehat{\Delta}_{(u)}^{R})$ . Hence  $\alpha \in t_{\beta}(\gamma + nuK)$  for some  $n \in \mathbb{Z}$ ,  $\gamma \in \Delta^{R}$ , that is,  $\alpha = \gamma + (nu - (\beta|\gamma))K$ . Since  $\alpha \in \Delta^{R}$ , it follows that  $\alpha = \gamma$  and  $(\beta|\gamma) = nu$ .

![](images/7a86567d32474e4b9b0c287761884692cca2b321cbb0677932f47ce92b8e5017.jpg)

Theorem 2.3. (a) Let  $M$  be a restricted  $\widehat{\mathfrak{g}}^R$ -module, and assume that  $R_{\widehat{\mathfrak{g}}^R}\mathrm{ch}_M$  converges to a holomorphic function on  $Y$ . Then  $\mathrm{ch}_{H^R(M)}$  is identically zero iff there exists  $\alpha \in \Delta^R$ , such that

(i)  $\alpha |_{\mathfrak{h}^f} = 0 (\Rightarrow |\alpha (x)| \geq 1)$ ,  
(ii)  $R_{\widehat{\mathfrak{g}}^R}\mathrm{ch}_M$  vanishes on the hyperplane  $\alpha = 0$

(b) Let  $\Lambda$  be as in Theorem 2.2. Then  $\mathrm{ch}_{H^R (L(\Lambda))} = 0$  iff there exists  $\alpha \in \Delta^R$  such that:

(i)  $\alpha |_{\mathfrak{h}^f} = 0 (\Rightarrow |\alpha (x)|\geq 1),$  
(ii)  $(\alpha |\beta)\in u\mathbb{Z}$

(c) Let  $\Lambda$  be an admissible weight. Then  $\mathrm{ch}_{H^R (L(\Lambda))}$  is not identically zero iff  $\Delta_{\Lambda , + }^{R}\subset$ $\Delta_{+}^{R}\backslash \Delta^{R,f}$ , where  $\Delta^{R,f} = \{\alpha \in \Delta^{R}|\alpha |_{\mathfrak{h}^{f}} = 0\}$ .

Proof. (a) follows from the character formula (2.2). Condition (i) implies that  $|\alpha(x)| \geq 1$  since  $f$  is of principal type, hence  $\alpha|_{\mathfrak{h}^f} \neq 0$  for  $\alpha \in \Delta^0$ , and  $\alpha|_{\mathfrak{h}^f} \neq 0$  for  $\alpha \in \Delta^{\pm 1/2}$  for all  $f$  [EK].

In order to prove (b), note that by Theorem 1.2(a),  $R_{\widehat{\mathfrak{g}}^R}\mathrm{ch}_{L(\Lambda)}$  vanishes on the hyperplane  $\alpha = 0$  iff  $\alpha \in \widehat{\Delta}_{\Lambda}^{R}$ . Now Lemma 2.12 and (a) imply (b). Due to Theorem 1.2(a), (c) is an equivalent form of (a) in the case when  $M = L(\Lambda)$ , where  $\Lambda$  is an admissible weight.

![](images/33d761801059526c952cc6aa14cfa64f606ff63c7c98559319b776f5b37c70b0.jpg)

We call a weight  $\Lambda \in Pr^{k,R}$  nondegenerate for  $W^{k}(\mathfrak{g},f)$  if  $\mathrm{ch}_{H^R (L(\Lambda))}\neq 0$ , and denote the set of all such weights by  $Prn^{k,R}(\mathfrak{g},f)$ .

Given  $\Lambda \in \widehat{\mathfrak{h}}^*$  of level  $k$ , denote by  $h_\Lambda$  the eigenvalue of  $L_0^R$  on  $v_\Lambda \otimes |0\rangle$ . Then we have the eigenvalue decomposition with respect to  $L_0^R$ :

$$
H ^ {R} (L (\Lambda)) = \bigoplus_ {j \in h _ {\Lambda} + \mathbb {Z} _ {+}} H ^ {R} (L (\Lambda)) _ {j},
$$

hence the decomposition of the Euler-Poincaré characters:

$$
\mathrm {c h} _ {H ^ {R} (L (\Lambda))} = e ^ {2 \pi i k t} \sum_ {j \in h _ {\Lambda} + \mathbb {Z} _ {+}} q ^ {j} \varphi_ {\Lambda , j} (z),
$$

where  $\mathrm{ch}_{H^R (L(\Lambda))_j} = e^{2\pi ikt}q^j\varphi_{\Lambda ,j}(z)$ . It follows from Theorem 1.2(a) and formula (2.2) that, if  $\Lambda$  is an admissible weight for  $\widehat{\mathfrak{g}}^R$ , all functions  $\varphi_{\Lambda ,j}(z)$  are meromorphic on  $\mathfrak{h}^f$ , and for  $j = h_{\Lambda}$  we have  $(z\in \mathfrak{h}^f)$ :

$$
\varphi_ {\Lambda , h _ {\Lambda}} (z) = \frac {\sum_ {w \in W _ {\Lambda} ^ {R}} \epsilon (w) e ^ {2 \pi i (w (\Lambda + \rho^ {R}) - \rho^ {R} | z)}}{\prod_ {\alpha \in \Delta_ {+} ^ {R , 0} \cup \Delta_ {+} ^ {R , 1 / 2}} (1 - e ^ {- 2 \pi i (\alpha | z)})}.
$$

Definition 2.2. We say that  $\mathrm{ch}_{H^R (L(\Lambda))}$  is almost convergent if  $\lim_{z\to 0}\varphi_{\Lambda ,h_{\Lambda}}(z)|_{\mathfrak{h}^f}$  exists and is non-zero. (The first condition is necessary for the convergence of  $\mathrm{ch}_{H^R (L(\Lambda))}(\tau ,0,0)$ , and the second condition is sufficient for its non-vanishing.)

Theorem 2.4. Let  $\Lambda$  be an admissible weight for  $\widehat{\mathfrak{g}}^R$ . Then

(a)  $\operatorname{ch}_{H^R(L(\Lambda))}$  is almost convergent iff

(2.12)  $\{\alpha |_{\mathfrak{h}^f}\mid \alpha \in \Delta_{\Lambda , + }^R\} = \{m_\alpha \alpha |_{\mathfrak{h}^f}\mid \alpha \in \Delta_+^{R,0}\cup \Delta_+^{R,1 / 2}\}$  (counting multiplicities),

for some non-zero  $m_{\alpha} \in \mathbb{Q}$  (it is easy to show that  $m_{\alpha} > 0$ ).

(b)  $\varphi_{\Lambda ,h_{\Lambda}}(z)$  is not identically zero iff  $\mathrm{ch}_{H^R (L(\Lambda))}$  is not identically zero.

Proof. We rewrite the formula for  $\varphi_{\Lambda ,h_{\Lambda}}(z)$  as follows:

$$
\varphi_ {\Lambda , h _ {\Lambda}} (z) = \frac {\sum_ {w \in W _ {\Lambda} ^ {R}} \epsilon (w) e ^ {2 \pi i (w (\Lambda + \rho^ {R}) - \rho^ {R} | z)}}{\prod_ {\alpha \in \Delta_ {\Lambda , +} ^ {R}} (1 - e ^ {- 2 \pi i (\alpha | z)})} \frac {\prod_ {\alpha \in \Delta_ {\Lambda , +} ^ {R}} (1 - e ^ {- 2 \pi i (\alpha | z)})}{\prod_ {\alpha \in \Delta_ {+} ^ {R , 0} \cup \Delta_ {+} ^ {R , 1 / 2}} (1 - e ^ {- 2 \pi i (\alpha | z)})}.
$$

Since  $W_{\Lambda}^{R}$  contains all reflections in  $\alpha \in \Delta_{\Lambda, +}^{R}$  the first factor is holomorphic in  $z \in \mathfrak{h}^f$ , and, by the usual argument, its limit as  $z \to 0$  is equal to  $\prod_{\alpha \in \Delta_{\Lambda, +}^{R}} (\Lambda + \rho^{R}|\alpha) / (\rho^{R}|\alpha) \neq 0$ . (a) follows. (b) follows due to Theorem 2.3(c).

![](images/0bd70c1369cbd969bd325589b266fa71564eae3339e98cc3c93226db5215447c.jpg)

Corollary 2.2. A necessary condition of almost convergence of  $\mathrm{ch}_{H^R (L(\Lambda))}$ , where  $\Lambda$  is an admissible weight, is:

$$
| \Delta_ {\Lambda} ^ {R} | = | \Delta^ {0} \cup \Delta^ {1 / 2} |.
$$

2.4 Characters of the principal  $W$ -algebras. In this section we consider in detail the case when  $f$  is a principal nilpotent element of  $\mathfrak{g}$ . Recall that these are elements of an adjoint orbit, whose closure contains all nilpotent elements of  $\mathfrak{g}$ . Recall that in this case  $x = \rho^{\vee}$ ,  $\mathfrak{h}^f = 0$ ,  $\mathfrak{g}_0 = \mathfrak{h}$ , hence  $\Delta^0 = \emptyset$ , and  $\mathfrak{g}_{1/2} = 0$ , hence  $\Delta^{1/2} = \emptyset$ . Hence  $h_0 = 0$  and  $\Delta_{+}^{\mathrm{new}} = \bar{w}_0(\Delta_+)$  where  $\bar{w}_0$  is the longest element of  $W$ . Thus, the quantum Hamiltonian reduction, considered in this paper, coincides with the “-”-reduction of [KRW]. The corresponding  $W$ -algebra, called principal, will be denoted by  $W^{k}(\mathfrak{g})$ , and its simple quotient by  $W_{k}(\mathfrak{g})$ .

By results of Arakawa [A2], a non-zero  $W^{k}(\mathfrak{g})$ -module  $H^{R}(L(\Lambda))$  is irreducible and coincides with  $H^{0,R}(L(\Lambda))$ . Hence the Euler-Poincaré character  $\mathrm{ch}_{H^R (L(\Lambda))}$  is the character of this module. Hence  $\mathrm{ch}_{H^R (L(\Lambda))} = 0$  iff the  $W^{k}(\mathfrak{g})$ -module  $H^{R}(L(\Lambda))$  is zero. It follows from Proposition 1.2 and Theorem 2.3(c) that for a principal admissible weight  $\Lambda$  of  $\widehat{\mathfrak{g}}^R$  we have:

$$
H ^ {R} (L (\Lambda)) = 0 \text {i f f} (\Lambda | \alpha) \in \mathbb {Z} \text {f o r s o m e} \alpha \in \Delta^ {\vee}.
$$

The remaining principal admissible weights  $\Lambda$  are called non-degenerate and the corresponding  $W^{k}(\mathfrak{g})$ -modules  $H^{R}(L(\Lambda))$  are irreducible. By Proposition 1.3, the set of such  $\Lambda$ , denoted by  $Prn^{k,R}$ , is non-empty iff  $k$  satisfies conditions (0.2):

$$
k + h ^ {\vee} = p / u, \mathrm {w h e r e} p, u \in \mathbb {N}, (p, u) = 1, (\ell , u) = 1, p \geq h ^ {\vee}, u \geq h.
$$

It follows from [FKW] that the irreducible  $W^{k}(\mathfrak{g})$ -modules  $H^{R}(L(\Lambda))$  and  $H^{R}(L(\Lambda'))$  with  $\Lambda, \Lambda' \in Prn^{k,R} \cong Prn^{k}$  are isomorphic iff  $\varphi(\Lambda) = \varphi(\Lambda')$ , where

$$
\varphi : P r n ^ {k} \to I _ {p, u} = (\widehat {P} _ {+} ^ {p - h ^ {\vee}} \times \widehat {P} _ {+} ^ {\vee u - h}) / \tilde {W} _ {+}
$$

is the surjective map, defined in Proposition 1.3.

Formula (2.1) for the central charge of these  $W^{k}(\mathfrak{g})$ -modules becomes:

$$
c (k, \mathfrak {g}) = r - \frac {1 2 | u \rho - p \rho^ {\vee} | ^ {2}}{p u}.
$$

The normalized character of the irreducible  $W^{k}(\mathfrak{g})$ -module  $H^{R}(L(\Lambda))$ , parameterized by  $\varphi(\Lambda) = (\lambda, \mu) \in I_{p,u}$ , is given by the following formula [FKW]:

$$
\chi_ {\lambda , \mu} (\tau) = \eta (\tau) ^ {- r} \sum_ {w \in \widehat {W}} \epsilon (w) q ^ {\frac {p u}{2} | \frac {w (\lambda + \widehat {\rho})}{p} - \frac {\mu + \widehat {\rho} ^ {\vee}}{u} | ^ {2}},
$$

the minimal eigenvalue of  $L_0^R$  being

$$
h _ {\lambda , \mu} = \frac {1}{2 p u} (| u (\bar {\lambda} + \rho) - p (\bar {\mu} + \rho^ {\vee}) | ^ {2} - | u \rho - p \rho^ {\vee} | ^ {2}).
$$

It follows from Theorem 2.2 that, as  $\tau \downarrow 0$

$$
\chi_ {\lambda , \mu} (\tau) \sim (u p) ^ {- r / 2} | P / Q ^ {\vee} | ^ {- 1 / 2} \prod_ {\alpha \in \Delta_ {+}} 4 \sin \frac {(\lambda + \rho | \alpha)}{p} \sin \frac {(\mu + \rho^ {\vee} | \alpha)}{u}.
$$

A formula for modular transformations can be found in [FKW].

Conjecture PA. If  $\Lambda \in Prn^{k,R}$ , then the  $W^{k}(\mathfrak{g})$ -module  $H^{R}(L(\Lambda))$  is actually a  $W_{k}(\mathfrak{g})$ -module (defined, up to isomorphism, by  $\varphi(\Lambda)$ ), and these are all irreducible  $W_{k}(\mathfrak{g})$ -modules.

Conjecture PB. The vertex algebra  $W_{k}(\mathfrak{g})$  is semisimple iff  $k$  satisfies (0.2).

2.5 Conjectures. Consider the space of meromorphic functions in the domain  $Y$  with the following action of  $SL_2(\mathbb{Z})$ :

$$
(g \cdot \chi) (\tau , z, t) = \chi \left(\frac {a \tau + b}{c \tau + d}, \frac {z}{c \tau + d}, t - \frac {c (z | z)}{2 (c \tau + d)}\right), g = \left( \begin{array}{l l} a & b \\ c & d \end{array} \right) \in S L _ {2} (\mathbb {Z}).
$$

We call a function  $\chi$  from this space modular invariant if the  $\mathbb{C}$ -span of the set of all functions  $\{g\cdot \chi \}_{g\in SL_2(\mathbb{Z})}$  is finite-dimensional. It follows from Proposition 1.1 and the results of [KW1], Theorems 3.6 and 3.7, and [KW2], Remark 4.3(a), that the function  $\chi_{L(kD)}$  is modular invariant if  $k$  is of the form (0.1). Moreover, if  $k$  is of the form (0.1) with  $(u,\ell) = 1$ , then  $\chi_{L(\lambda)}$  is modular invariant for all  $\lambda \in Pr^k$ , simply because  $|Pr^{k}\mod \mathbb{C}K| < \infty$  and the  $\mathbb{C}$ -span of  $\{\chi_{L(\lambda)}|\lambda \in Pr^k\}$  is  $SL_2(\mathbb{Z})$ -invariant (cf. Theorems 1.1-1.3).

Conjecture A. If  $\chi_{L(kD)}$  is modular invariant, then  $k$  is of the form (0.1).

It has been established recently [GK2] that the character of any highest weight  $\widehat{\mathfrak{g}}$ -module of non-critical level  $k \neq -h^{\vee}$  is a meromorphic function in the domain  $Y$ . It follows from [GK1] that for non-critical  $k$ ,  $\chi_{L(kD)}$  can be modular invariant only for  $k = -h^{\vee} + p / u\ell$ , where  $(p, u) = 1, u \geq 1, p \geq 2$ . Thus, the first unknown case is  $\mathfrak{g} = sl_3$ ,  $k = -1$ .

# Conjecture B.

(a) If  $M$  is an irreducible highest weight  $\widehat{\mathfrak{g}}^R$ -module of level  $k$ , then  $H^{R}(M) = H_{0}^{R}(M)$ , and this is either an irreducible  $\sigma_{R}$ -twisted  $W^{k}(\mathfrak{g},f)$ -module, or zero.  
(b) Let  $W^{R,f} = \{w \in \widehat{W}^R | w|_{\mathbb{C}D^R + \mathfrak{h}^f} = Id\}$ . Suppose that  $H^R(L(\Lambda)) \neq 0$ . Then the  $\sigma_R$ -twisted  $W^k(\mathfrak{g}, f)$ -modules  $H^R(L(\Lambda))$  and  $H^R(L(\Lambda'))$  are isomorphic iff  $\Lambda' = y. \Lambda$  for some  $y \in W^{R,f}$ .

In the case when  $f$  is a principal (resp. "minimal" nilpotent), Conjecture B(a) was stated in [FKW] and [KRW], and was proved in [A2] and [A1] respectively.

The specific choice of  $\widehat{\Delta}_{+}^{R}$  (depending on our specific choice of  $\Delta_{+}^{\mathrm{new}}$ ) is very important. Indeed, if the property, given by 2.2(d) (guaranteed by our choice of  $\Delta_{+}^{\mathrm{new}}$ ), doesn't hold, then Conjecture B(a) fails, for example, when  $\mathfrak{g} = sp_4$  and  $f$  is a root vector, attached to a short root.

It follows from Conjecture B(a) and Theorem 2.4 that for an admissible  $\Lambda$ ,  $\mathrm{ch}_{H^R (L(\Lambda))}(\tau ,0,0)$  converges for all  $\tau \in \mathbb{C}^{+}$  and does not vanish iff  $\mathrm{ch}_{H^R (L(\Lambda))}$  is almost convergent.

Remark 2.2. It follows from Theorem 2.2 that if  $\Lambda \in Pr^{k,R}$  and  $k = -h^{\vee} + \frac{p}{u}$  is such that  $pu\dim \mathfrak{g}^f < h^\vee \dim \mathfrak{g}$ , then  $H^{R}(L(\Lambda)) = 0$ . Moreover, if  $pu\dim \mathfrak{g}^f = h^\vee \dim \mathfrak{g}$  and  $\Lambda \in Prn^{k,R}(\mathfrak{g},f)$ , then  $0 < \dim H^{R}(L(\Lambda)) < \infty$ , hence  $c(\mathfrak{g},f,k) = 0$ . Thus, we obtain the following generalization of the "strange" formula:

$$
| \rho - \frac {p}{u} x | ^ {2} = \frac {1}{1 2} \frac {p}{u} \left(\dim {\mathfrak {g}} _ {0} - \frac {1}{2} \dim {\mathfrak {g}} _ {1 / 2}\right).
$$

This formula holds for each exceptional pair  $f$ ,  $u$  (see Definition 2.3 below), and an integer  $p \geq h^{\vee}$ ,  $(u, p) = 1$ , such that  $pu \dim \mathfrak{g}^f = h^{\vee} \dim \mathfrak{g}$ .

Conjecture C. The set  $Prn^{k,R}(\mathfrak{g},f)$  is non-empty iff  $k$  is of the form (0.1), where  $u$  satisfies

$$
u > (\theta | x). \tag {2.13}
$$

Definition 2.3. A pair  $(k, f)$ , where  $k \in \mathbb{C}$  and  $f$  is a nilpotent element of  $\mathfrak{g}$ , is called exceptional if the Euler-Poincaré character  $\mathrm{ch}_{H^R(L(\Lambda))}$  of the  $W^k(\mathfrak{g}, f)$ -module  $H^R(L(\Lambda))$  is almost convergent for some principal admissible  $\widehat{\mathfrak{g}}^R$ -module of level  $k$ , and is either  $0$  or is almost convergent for all principal admissible  $\widehat{\mathfrak{g}}^R$ -modules of level  $k$ . In this case  $f$  is called an exceptional nilpotent of  $\mathfrak{g}$  and its adjoint orbit is called an exceptional nilpotent orbit, and  $k$  is called an exceptional level for  $f$  and its denominator  $u$  an exceptional denominator.

Recall that convergence of characters  $tr_{M}q^{L_{0} - c / 24}$  of all modules  $M$  over a vertex algebra  $V$  is a necessary condition of rationality of  $V$ . We conclude from the above discussion that, provided that Conjectures B and C hold, the vertex algebra  $W_{k}(\mathfrak{g},f)$  is rational iff the pair  $(k,f)$  is exceptional.

Conjecture D. The vertex algebra  $W_{k}(\mathfrak{g},f)$  is semisimple iff the pair  $(k,f)$  is exceptional.

Remark 2.3. Note that  $W^{k}(\mathfrak{g},0)$  (resp.  $W_{k}(\mathfrak{g},0)$ ) is isomorphic to the universal (resp. simple) affine vertex algebra  $V^{k}(\mathfrak{g})$  (resp.  $V_{k}(\mathfrak{g})$ ), and  $H^{R}(M)\cong M$  in this case ( $f = 0$ ). Hence the pair  $(k,0)$  is exceptional iff  $k\in \mathbb{Z}_{+}$ . Since  $Pr^{k} = \widehat{P}_{+}^{k}$  in this case and all  $V_{k}(\mathfrak{g})$ -modules with  $k\in \mathbb{Z}_{+}$  are  $\{L(\Lambda)\}_{\Lambda \in \widehat{P}_{+}^{k}\mod \mathbb{C}K}$  [FZ], we conclude that Conjecture C (resp. D) holds if  $f = 0$  and  $k\in \mathbb{Z}_{+}$  (resp.  $f = 0$ ). However, it is unknown whether Conjecture C holds if  $k$  is of the form (0.1) with  $u$  satisfying (2.13) and  $k\notin \mathbb{Z}_{+}$ , except for the case  $\mathfrak{g} = s\ell_2$  [AM]. E. Frenkel pointed out that the first part of Conjecture C follows from the special case  $f = 0$ .

Remark 2.4. In the case when  $f$  is a principal nilpotent of a simply laced simple Lie algebra, the normalized characters  $\chi_{\lambda,\mu}(\tau)$  of  $W^k(\mathfrak{g},f)$  coincide with those of the centralizer of  $V_k(\mathfrak{g})$  in the vertex algebra  $V_1(\mathfrak{g}) \otimes V_{k-1}(\mathfrak{g})$  [KW2]. Conjecture C in the case of simply laced  $\mathfrak{g}$  and principal nilpotent  $f$  would follow if the latter vertex algebra were isomorphic to  $W_k(\mathfrak{g},f)$ . However, apparently this isomorphism is an open problem.

2.6 Description of exceptional pairs, assuming positivity. The following theorem provides an easy way to check almost convergence under the assumption that all the coefficients of  $\mathrm{ch}_{H^R (L(\Lambda))}$  are non-negative (cf. Conjecture B(a)).

Theorem 2.5. Let  $\Lambda$  be an admissible weight for  $\widehat{\mathfrak{g}}^R$  and assume that all the coefficients of  $\mathrm{ch}_{H^R (L(\Lambda))}$  are non-negative. Then  $\mathrm{ch}_{H^R (L(\Lambda))}$  is almost convergent iff

$$
\Delta_ {\Lambda} ^ {R} \subset \Delta^ {R} \backslash \Delta^ {R, f} a n d | \Delta_ {\Lambda} ^ {R} | = | \Delta^ {0} \cup \Delta^ {1 / 2} |. \tag {2.14}
$$

Consequently, if these conditions hold, then the eigenspace of  $L_0^R$  with minimal eigenvalue is finite-dimensional.

Proof. In view of Theorems 2.3 and 2.4, and Corollary 2.2, it remains to prove that conditions (2.14) imply almost convergence. In view of the proof of Theorem 2.4, it suffices to prove the following simple lemma on rational functions.

Lemma 2.13. Let  $R(z_{1},\ldots ,z_{n}) = f(z_{1},\ldots ,z_{n}) / \prod_{(k_{1},\ldots ,k_{n})\in \mathbb{Z}_{+}^{n}\setminus \{0\}}(1 - z_{1}^{k_{1}}\ldots z_{n}^{k_{n}})^{m(k_{1},\ldots ,k_{n})}$ , where  $f$  is a polynomial,  $m(k_{1},\dots,k_{n})\in \mathbb{Z}_{+}$  and all but a finite number of them is 0. Suppose that all coefficients of the Taylor expansion of  $R(z_{1},\dots,z_{n})$  at  $z_{1} = \dots = z_{n} = 0$  are nonnegative, and  $R(z^{s_1},\dots,z^{s_n})$  has a removable singularity at  $z = 1$ , for some positive integers  $s_i$ . Then  $R(z_{1},\dots,z_{n})$  is a polynomial.

This lemma follows from a similar lemma in one variable.

Lemma 2.14. Let  $R(z) = f(z) / \prod_{j=1}^{N}(1 - z^j)^{m_j}$ , where  $f(z)$  is a polynomial in  $z$  and  $m_j \in \mathbb{Z}_+$ . Suppose that all coefficients of the Taylor expansion of  $R(z)$  at  $z = 0$  are non-negative and that  $R(z)$  has a removable singularity at  $z = 1$ . Then  $R(z)$  is a polynomial.

Proof. Let  $M = \sum_{j} m_{j}$ . We have:  $f(z) = (1 - z)^{M} f_{1}(z)$ , and  $\prod_{j=1}^{N} (1 - z^{j})^{m_{j}} = (1 - z)^{M} f_{2}(z)$ , where  $f_{1}(z)$  and  $f_{2}(z)$  are polynomials and the coefficients of  $f_{2}(z)$  are non-negative. Hence  $f_{1}(z) = R(z) f_{2}(z)$ . Since all coefficients of the Taylor expansion at  $z = 0$  of  $R(z)$  and  $f_{2}(z)$  are non-negative and  $f_{1}(z)$  is a polynomial, it follows that  $R(z)$  is a polynomial.

Using Theorem 2.5, we can give a description of exceptional pairs  $(k,f)$  in terms of the Lie algebra  $\mathfrak{g}$  and its adjoint group  $G$ . For this we need some lemmas.

Lemma 2.15. Let  $\Lambda$  be an admissible weight of  $\widehat{\mathfrak{g}}$  of level  $k = v / u$ , where  $u, v \in \mathbb{Z}$ ,  $u > 0$ ,  $(u, v) = 1$ . Suppose that

(i)  $(u,\ell) = 1$  
(ii) for each  $\alpha \in \Delta^{\vee}$  there exists  $m\in \mathbb{Z}$ , such that  $mK + \alpha \in \widehat{\Delta}_{\Lambda}^{\vee,\mathrm{re}}$ .

Then  $\Lambda$  is a principal admissible weight.

Proof. It follows from the classification of admissible weights in [KW1] that if  $\mathfrak{g}$  is simply laced (i.e.,  $\ell = 1$ ), then condition (ii) implies that  $\Lambda$  is principal admissible.

In the non-simply laced cases condition (ii) leaves only the following possibilities for  $\widehat{\prod}_{\Lambda}^{\vee}$  to be non-isomorphic to  $\widehat{\prod}^{\vee}$  [KW1] (we use the numeration of simple roots of  $\widehat{\mathfrak{g}}$  from the tables of [K1], Chapter 4):

$$
\widehat {\prod_ {\Lambda} ^ {\vee}} = \sigma_ {\alpha_ {0} ^ {\vee}} \widehat {\prod^ {\vee}} \mathrm {i f} \mathfrak {g} = B _ {r}, C _ {r}, F _ {4} \mathrm {o r} G _ {2}; \widehat {\prod_ {\Lambda} ^ {\vee}} = \sigma_ {\alpha_ {4} ^ {\vee}} \widehat {\prod^ {\vee}} \mathrm {i f} \mathfrak {g} = F _ {4}.
$$

But the denominator  $u$  of  $k$  can be computed by the formula  $\sum_{i=0}^{r} a_i^\vee \gamma_i = uK$ , where  $\widehat{\prod}_{\Lambda}^{\vee} = \{\gamma_0, \dots, \gamma_r\}$ , and we see by a case-wise inspection that in all cases  $u$  is divisible by  $\ell$ , a contradiction with (i).

![](images/27df968124b458ab529ae3fd10223583689b7177e390423cb4b00bd6c998cb24.jpg)

Lemma 2.16. Let  $\Lambda \in \mathfrak{h}$  and let  $u$  be a positive integer, satisfying the following conditions:

(i)  $(\Lambda + \rho |\alpha) \notin -\mathbb{Z}_{+}$  for all  $\alpha \in \Delta_{+}^{\vee}$ ,  
(ii)  $(\Lambda |\alpha)\in \frac{1}{u}\mathbb{Z}$  for all  $\alpha \in \Delta^{\vee}$

(iii)  $(u,\ell) = 1$

Then for a sufficiently large integer  $p$ , coprime to  $u$ ,  $\widehat{\Lambda} = (\frac{p}{u} - h^{\vee})D + \Lambda$  is a principal admissible weight (of level  $k = -h^{\vee} + p / u$ ).

Proof. Let  $p$  be a positive integer, coprime to  $u$ , such that  $p / u > (\Lambda + \rho | \alpha)$  for all  $\alpha \in \Delta^{\vee}$ . Then, clearly,  $\widehat{\Lambda}$  is an admissible weight. Furthermore,  $(\widehat{\Lambda} + \widehat{\rho} | j\ell K + \alpha) = j\ell p / u + (\Lambda + \rho | \alpha)$  and  $(\Lambda + \rho | \alpha) \in \frac{1}{u}\mathbb{Z}$  for each  $\alpha \in \Delta^{\vee}$ . Since  $(u, \ell p) = 1$ , for each  $\alpha \in \Delta^{\vee}$  there exist  $m_{\alpha}$ , such that  $m_{\alpha}\ell p / u + (\Lambda + \rho | \alpha) \in \mathbb{Z}$ , hence  $(\widehat{\Lambda} + \widehat{\rho} | m_{\alpha}\ell K + \alpha) \in \mathbb{Z}$ . Therefore, by Lemma 2.15,  $\widehat{\Lambda}$  is a principal admissible weight.

![](images/8893c849febb0cbe9ca2ecc100a648826e42d50e857e35b6040310e8d713b997.jpg)

Lemma 2.17. Let  $\Lambda \in \mathfrak{h}$  be such that  $e^{2\pi i\Lambda}$  is an element of order  $u$  in the adjoint group  $G$  of the Lie algebra  $\mathfrak{g}$ , where  $u$  is a positive integer, coprime to  $\ell$ . Then

(a)  $\Delta_{\Lambda}^{\vee} = \{\alpha^{\vee} := 2\alpha / (\alpha |\alpha)| \alpha \in \Delta_{\Lambda}\}$ , where  $\Delta_{\Lambda} = \{\alpha \in \Delta | (\Lambda |\alpha) \in \mathbb{Z}\}$ .  
(b) For a sufficiently large integer  $p$ , coprime to  $u$ , there exists a principle admissible weight  $\widehat{\Lambda}$  of level  $k = -h^{\vee} + p / u$ , such that  $\widehat{\Lambda}|_{\mathfrak{h}}$  is conjugate to  $\Lambda$  by the Weyl group  $W_{\Lambda}$  of  $Z_{\mathfrak{g}}(e^{2\pi i\Lambda})$  (the centralizer of  $e^{2\pi i\Lambda}$  in  $\mathfrak{g}$ ) and  $Z_{\mathfrak{g}}(e^{2\pi i\widehat{\Lambda}|_{\mathfrak{h}}}) = Z_{\mathfrak{g}}(e^{2\pi i\Lambda})$ .

Proof. Since  $e^{2\pi i \Lambda}$  has order  $u$ , we have:  $\alpha \in \Delta_{\Lambda}$  implies  $(\Lambda | \alpha) \in \mathbb{Z}$ ;  $\alpha \in \Delta \backslash \Delta_{\Lambda}$  implies  $(\Lambda | \alpha) \in \frac{1}{u} \mathbb{Z} \backslash \mathbb{Z}$ . Note also that  $\alpha^{\vee} = \alpha$  (resp.  $\ell \alpha$ ) if  $\alpha$  is a long (resp. short) root and  $(\Lambda | \alpha) \in \frac{1}{u} \mathbb{Z} \backslash \mathbb{Z}$  iff  $\ell(\Lambda | \alpha) \in \frac{1}{u} \mathbb{Z} \backslash \mathbb{Z}$ , since  $(u, \ell) = 1$ . These remarks prove (a).

In order to prove (b), note that  $Z_{\mathfrak{g}}(e^{2\pi i\Lambda}) = \mathfrak{h} + \sum_{\alpha \in \Delta_{\Lambda}} \mathfrak{g}_{\alpha}$ , and  $\Lambda$  is an integral weight of the semisimple part of  $Z_{\mathfrak{g}}(e^{2\pi i\Lambda})$  (due to (a)). Hence there exists  $w \in W_{\Lambda}$ , such that  $\Lambda' = w(\Lambda)$  has the property that  $(\Lambda'|\alpha) \in \mathbb{Z}_+$  for all  $\alpha \in \Delta_{\Lambda} \cap \Delta_+$ . Hence we have:  $(\Lambda' + \rho|\alpha) \in \mathbb{N}$  for all  $\alpha \in \Delta_{\Lambda}^{\vee} \cap \Delta_+^{\vee}$ , and  $(\Lambda'|\alpha) \in \frac{1}{u}\mathbb{Z} \backslash \mathbb{Z}$  for all  $\alpha \in \Delta^{\vee} \backslash \Delta_{\Lambda}^{\vee}$ . Then, by Lemma 2.16, there exists a positive integer  $p$ , coprime to  $u$ , such that  $\widehat{\Lambda'} := (-h^{\vee} + p / u)D + \Lambda'$  is a principal admissible weight of level  $k = -h^{\vee} + p / u$ . Since  $\Delta_{\Lambda'} = w(\Delta_{\Lambda}) = \Delta_{\Lambda}$ , because  $w \in W_{\Lambda}$ , we conclude that  $Z_{\mathfrak{g}}(e^{2\pi i\Lambda'}) = \mathfrak{h} + \sum_{\alpha \in \Delta_{\Lambda'}} \mathfrak{g}_{\alpha} = Z_{\mathfrak{g}}(e^{2\pi i\Lambda})$ , proving (b).

![](images/a2a75bb84c05684648784ddedd100a25106bb158daee04651278f46d8edf4f0b.jpg)

Given a nilpotent element  $f$  of the Lie algebra  $\mathfrak{g}$  and a positive integer  $u$ , coprime to  $\ell$ , let

$$
S _ {u, f} = \left\{s \in G | s ^ {u} = 1 \text {a n d} Z _ {\mathfrak {g}} (s) \cap Z _ {\mathfrak {g}} (\mathfrak {h} ^ {f}) = \mathfrak {h} \right\}.
$$

Theorem 2.6. Assume that all the coefficients of  $ch_{H^R (L(\Lambda))}$  are non-negative for all principal admissible weights for  $\widehat{\mathfrak{g}}^R$  of level  $k = -h^{\vee} + p / u$ , where  $u\geq 1$ ,  $p\geq h^{\vee}$ ,  $(u,p\ell) = 1$ . Let  $f$  be a nilpotent element of  $\mathfrak{g}$  of principal type. Then the pair  $(k,f)$  is exceptional iff:

(i)  $\dim Z_{\mathfrak{g}}(s)\geq \dim \mathfrak{g}^f$  for all  $s\in S_{u,f}$  
(ii)  $\dim Z_{\mathfrak{g}}(s) = \dim \mathfrak{g}^f$  for some  $s\in S_{u,f}$

Proof. Note that condition (c) of Theorem 2.3 of non-vanishing of  $\mathrm{ch}_{H^R(L(\Lambda))}$  is equivalent to the condition that the element  $s = e^{2\pi i\Lambda|_{\mathfrak{h}}}$  lies in  $S_{u,f}$  and satisfies (i). Also, by Theorem 2.5,  $\mathrm{ch}_{H^R(L(\Lambda))}$  is almost convergent iff  $s$  lies in  $S_{u,f}$  and satisfies (ii). Hence conditions (i) and (ii) are necessary for the pair  $(k,f)$  to be exceptional. Due to Lemma 2.17, these conditions are also sufficient if  $p$  is large enough. But it is clear from Theorems 2.3 and 2.4 that the pairs  $(-h^\vee + p / u, f)$  are exceptional for all  $p \geq h^\vee$  iff one of them is exceptional for some  $p \geq h^\vee$ .

![](images/9a24fe7fb191ed8ea287f498e213abe93046cba93a2d189871595292dc282407.jpg)

# 3 Exceptional pairs for  $\mathfrak{g} = s\ell_n$

3.1 Sheets in  $\mathfrak{g} = s\ell_{n}$ . Recall that the adjoint nilpotent orbits of  $\mathfrak{g} = s\ell_{n}$  are parameterized by partitions of  $n$ , and that the closure of the nilpotent orbit, corresponding to the partition  $m_{1} \geq m_{2} \geq \dots$ , contains the nilpotent orbit, corresponding to the partition  $n_{1} \geq n_{2} \geq \dots$ , iff  $m_{1} \geq n_{1}$ ,  $m_{1} + m_{2} \geq n_{1} + n_{2}, \ldots$  [CM]. Note also that all nilpotents of  $s\ell_{n}$  are of principal type.

In order to classify exceptional pairs we use the theory of sheets. Recall that a sheet in a simple Lie algebra  $\mathfrak{g}$  is an irreducible component of the algebraic variety in  $\mathfrak{g}$ , consisting of all adjoint orbits of fixed dimension. In the case of  $\mathfrak{g} = s\ell_n$  the description of sheets is especially simple.

Proposition 3.1. [Kr] Let  $f$  be a nilpotent element of  $s\ell_{n}$ , let  $m_{1} \geq m_{2} \geq \dots \geq m_{s} > 0$  be the corresponding partition of  $n$ , let  $m = m_{1}$  and let  $m_1^\prime \geq m_2^\prime \geq \dots \geq m_m^\prime > 0$  be the dual partition.

(a) The element  $f$  is contained in a unique sheet, which we denote by  $\mathrm{Sh}_f$ .  
(b) All the semisimple elements in  $\mathrm{Sh}_f$  are those diagonalizable matrices in  $s\ell_n$ , which have  $m$  distinct eigenvalues of multiplicities  $m_1', m_2', \ldots, m_m'$ . We denote the set of all semisimple elements in  $\mathrm{Sh}_f$  by  $\mathrm{Sh}_f^0$ .  
(c) The rank of the semisimple Lie algebra  $[\mathfrak{g}^h, \mathfrak{g}^h]$ , where  $h \in \mathrm{Sh}_f^0$  and  $\mathfrak{g}^h$  is the centralizer of  $h$ , is equal to  $n - m$ .

Proposition 3.2. Let  $\mathfrak{h}$  be the set of all diagonal matrices in  $\mathfrak{g} = s\ell_n$ , let  $f$  be as in Proposition 3.1 and assume that the centralizer  $\mathfrak{h}^f$  of  $f$  in  $\mathfrak{h}$  is the Cartan subalgebra of the reductive part of  $\mathfrak{g}^f$ . Let

$$
\Omega_ {f} = \left\{h \in \mathfrak {h} | \alpha (h) \neq 0 f o r a n y r o o t \alpha \in \mathfrak {h} ^ {*} o f s \ell_ {n}, s u c h t h a t \alpha | _ {\mathfrak {h} ^ {f}} = 0 \right\}.
$$

(a) If  $h \in \Omega_f$ , then  $\text{rank}[\mathfrak{g}^h, \mathfrak{g}^h] \leq n - m$  and  $\dim \mathfrak{g}^h \leq \dim \mathfrak{g}^f$ .  
(b) If  $h \in \Omega_f$  and rank  $[\mathfrak{g}^h, \mathfrak{g}^h] = n - m$ , then  $h \in \mathrm{Sh}_f$ . Moreover,  $\mathrm{Sh}_f^0 = W(\Omega_f \cap \mathrm{Sh}_f)$ , where  $W$  is the Weyl group.

Proof. We fill the boxes of the Young diagram of the partition  $m_{1} \geq m_{2} \geq \dots \geq m_{s}$  by the eigenvalues of  $h$  (in  $\mathbb{C}^n$ ). Then  $h \in \Omega_f$  iff the eigenvalues in each row are distinct. Moreover,  $h \in \Omega_f \cap \mathrm{Sh}_f$  iff, in addition, all eigenvalues in each column are equal. This proves (b), due

to Proposition 3.1(c). Now (a) follows since making eigenvalues of  $h$  in a column unequal and keeping  $h$  in  $\Omega_f$  can only decrease the rank of  $[\mathfrak{g}^h, \mathfrak{g}^h]$  and the dimension of  $\mathfrak{g}^h$ .

![](images/dea168203f4a2746c61943367bc3746ce26940d1746ac13ad0c271b83fa7882f.jpg)

Let  $\Delta \subset \mathfrak{h}^*$  be the set of roots of  $\mathfrak{g} = s\ell_n$ , and let  $f \in \mathfrak{g}$  be a nilpotent element as in Proposition 3.1. Let  $\Delta^f = \{\alpha \in \Delta | \alpha|_{\mathfrak{h}^f} = 0\}$ . We call  $\Phi \subset \Delta$  a root subsystem if  $\alpha \in \Phi$  implies  $-\alpha \in \Phi$  and  $\alpha, \beta \in \Phi$ ,  $\alpha + \beta \in \Delta$  implies  $\alpha + \beta \in \Phi$ . The dimension of the  $\mathbb{C}$ -span of  $\Phi$  in  $\mathfrak{h}^*$  is called the rank of  $\Phi$ . Note that for each  $h \in \mathfrak{h}$  the set of roots of  $\mathfrak{g}^h$  is a root subsystem, and its rank equals rank  $[\mathfrak{g}^h, \mathfrak{g}^h]$ ; moreover, all root subsystems of  $\mathfrak{g} = s\ell_n$  are thus obtained. Hence the above propositions can be translated in the language of root subsystems. Given a positive integer  $m$ , such that  $m \leq n$ , denote by  $f_m$  the nilpotent element, corresponding to the partition of  $n$  of the form  $m = m = \dots = m > s \geq 0$ .

Proposition 3.3. (a) If  $\Phi \subset \Delta \backslash \Delta^f$  is a root subsystem, then

$$
\operatorname {r a n k} \Phi \leq n - m \text {a n d} | \Phi | \leq \left| \Delta^ {0} \cup \Delta^ {1 / 2} \right|. \tag {3.1}
$$

(b) There exists a root subsystem  $\Phi \subset \Delta \backslash \Delta^f$ , such that in (3.1) one has equalities. In this case  $\Phi|_{\mathfrak{h}^f} = (\Delta^0 \cup \Delta^{1/2})|_{\mathfrak{h}^f}$ .  
(c) There exists a root subsystem  $\Phi \subset \Delta \backslash \Delta^f$  such that rank  $\Phi = n - m$ , but  $|\Phi| < |\Delta^0 \cup \Delta^{1/2}|$  iff  $f \neq f_m$ .  
(d) If  $f = f_{m}$  and  $\Phi \subset \Delta \backslash \Delta^{f}$  is a root subsystem of rank  $n - m$ , then  $|\Phi| = |\Delta^{0} \cup \Delta^{1/2}|$ .

Proof. Recall that

$$
\dim \mathfrak {g} ^ {f} = \dim \mathfrak {g} _ {0} + \dim \mathfrak {g} _ {1 / 2}, \dim \mathfrak {g} _ {0} = | \Delta^ {0} | + n - 1, \dim \mathfrak {g} _ {1 / 2} = | \Delta^ {1 / 2} |.
$$

Note that a root subsystem  $\Phi \subset \Delta \backslash \Delta^f$  is, up to  $W$ -conjugation, the set of roots of  $\mathfrak{g}^h$  with  $h \in \Omega_f$ . Hence, by Proposition 3.2(a),  $\operatorname{rank} \Phi \leq n - m$  and  $|\Phi| + n - 1 \leq |\Delta^0 \cup \Delta^{1/2}| + n - 1$ , proving (a). By Proposition 3.2(b), for  $h \in \mathrm{Sh}_f^0$  one has equalities in (3.1), proving the first part of (b). It follows from Proposition 3.2(b) that  $\mathrm{Sh}_f^0$  consists of semisimple elements  $h$ , for which  $\mathfrak{h}^f$  is conjugate to a Cartan subalgebra of  $[\mathfrak{g}^h, \mathfrak{g}^h]$  and the set of roots with respect to  $\mathfrak{h}^{f*}$  in  $[\mathfrak{g}^h, \mathfrak{g}^h]$  is the same. Since  $\mathrm{Sh}_f^0$  is dense in  $\mathrm{Sh}_f$ , we obtain the second part of (b).

In order to prove (c), denote by  $N_{m}$  the set of nilpotent matrices  $X$ , such that  $X^{m} = 0$  but  $X^{m-1} \neq 0$ . It is the same as to say that the first part of the partition, corresponding to  $X$ , equals  $m$ . Note that the adjoint orbit of  $f_{m}$  is dense in  $N_{m}$ . If  $f \neq f_{m}$ , then there exists an element  $f' \in N_{m}$ , such that the closure of the adjoint orbit of  $f'$  contains  $f$ . If we choose  $f'$  in the canonical Jordan form, then  $\mathfrak{h}^f \supset \mathfrak{h}^{f'}$ , hence  $\Omega_{f} \supset \Omega_{f'}$ . Taking  $h \in \mathrm{Sh}_{f'}^0 \subset \mathrm{Sh}_f^0$ , the root system  $\Phi$  of  $\mathfrak{g}^h$  will satisfy all requirements of (c).

If  $f$  is of the form, described in (c), then all orbits from  $N_{m}$  lie in the closure of the orbit of  $f$  and all semisimple  $h$  such that  $\text{rank } [\mathfrak{g}^h, \mathfrak{g}^h] = n - m$  lie in the sheets of the nilpotents, contained in  $N_{m}$ . Hence there is no  $h \in \mathfrak{h}$ , such that  $\text{rank } [\mathfrak{g}^h, \mathfrak{g}^h] = n - m$ , but  $\dim \mathfrak{g}^f > \dim \mathfrak{g}^h$ , proving (c). (d) follows from (a) and (c).

![](images/a4c35533c8ffadd3228bdf54eb1403731560767b20bf866538a78433f454557e.jpg)

# 3.2 The main theorems for  $s\ell_{n}$

Lemma 3.1. Let  $f$  be a nilpotent element of  $s\ell_{n}$ , and let  $m$  be the maximal part of the partition of  $n$ , corresponding to  $f$ . Let  $\Lambda \in Pr^{k,R}$  be such that  $\mathrm{ch}_{H^R (L(\Lambda))}$  does not vanish, where  $k = -n + \frac{p}{u}$ ,  $p,u\in \mathbb{N}$ ,  $(p,u) = 1$ ,  $p\geq n$ . Then  $m\leq u$ .

Proof. By definition, the root system  $\widehat{\Delta}_{\Lambda}^{R}$  is of type  $A_{n - 1}^{(1)}$ , hence

$$
\widehat {\prod_ {\Lambda} ^ {R}} = \{u _ {0} K + \gamma_ {0}, \ldots , u _ {n - 1} K + \gamma_ {n - 1} \},
$$

where

$$
\sum_ {i = 0} ^ {n - 1} u _ {i} = u, \quad u _ {i} \in \mathbb {Z} _ {+}. \tag {3.2}
$$

Note that  $\mathrm{rank}\Delta_{\Lambda}^{R} = |\{i|0\leq i\leq n - 1,u_{i} = 0\} |.$  From (3.2) we obtain

$$
\mathrm {r a n k} \Delta_ {\Lambda} ^ {R} \geq n - u. \tag {3.3}
$$

Since, by assumption,  $\mathrm{ch}_{H^R (L(\Lambda))}\neq 0$ , by Theorem 2.3(c),  $\Delta_{\Lambda}^{R}\subset \Delta^{R}\backslash \Delta^{R,f}$ . Hence, by Proposition 3.2(a),  $\mathrm{rank}\Delta_{\Lambda}^{R}\leq n - m$ . The lemma now follows from (3.3).

Theorem 3.1. Given a positive integer  $m \leq n$ , denote, as above, by  $f_{m}$  the nilpotent element of  $\mathfrak{g} = s\ell_{n}$ , corresponding to the partition of the form  $m = m = \dots = m > s \geq 0$ . Let

$$
k = k _ {p, m} = \frac {p}{m} - n \text {w h e r e} p \in \mathbb {Z}, p \geq n \text {a n d} (p, m) = 1.
$$

Then

(a)  $(k, f_m)$  is an exceptional pair, that is the following two properties hold:

(i)  $\operatorname{ch}_{H^R(L(\Lambda))}$  either vanishes or is almost convergent for each  $\Lambda \in Pr^{k,R}$ ;  
(ii) there exists  $\Lambda \in Pr^{k,R}$ , such that  $\mathrm{ch}_{H^R (L(\Lambda))}$  does not vanish.

(b) If  $k \neq k_{p,m}$  and  $m < n$ , then  $(k, f_m)$  is not an exceptional pair.

Proof. Let  $\Lambda \in Pr^{k,R}$  be a principal admissible weight of level  $k = \frac{p}{m} - n$ , such that  $\mathrm{ch}_{H^R(L(\Lambda))}$  does not vanish. It follows from (3.3) with  $u = m$ , that

$$
\operatorname {r a n k} \Delta_ {\Lambda} ^ {R} \geq n - m.
$$

Since, by our assumption,  $\mathrm{ch}_{H^R (L(\Lambda))}\neq 0$ , we have:  $\Delta_{\Lambda}^{R}\subset \Delta^{R}\backslash \Delta^{R,f}$ , by Theorem 2.3(c). Hence, by Proposition 3.2(a),  $\mathrm{rank}\Delta_{\Lambda}^{R}\leq n - m$ , and we conclude that  $\mathrm{rank}\Delta_{\Lambda}^{R} = n - m$ . But then by Proposition 3.3(b), we obtain that  $\Delta_{\Lambda}^{R}|_{\mathfrak{h}^{f}} = (\Delta^{0}\cup \Delta^{1 / 2})|_{\mathfrak{h}^{f}}$ . By Theorem 2.4, we conclude that  $\mathrm{ch}_{H^R (L(\Lambda))}$  is almost convergent, proving (i).

Due to Theorem 2.3(c) and Propositions 3.2(b) and 3.3(d), (ii) holds as well, proving (a).

Claim (b) follows from the following two statements:

(i) if  $u > m$ , then there exists  $\Lambda \in Pr^{k,R}$ , such that  $\Delta_{\Lambda}^{R} \subset \Delta^{R} \backslash \Delta^{R,f}$ ,  $|\Delta_{\Lambda}^{R}| < |\Delta^{0} \cup \Delta^{1/2}|$  (hence, by Corollary 2.2,  $\mathrm{ch}_{H^R(L(\Lambda))}$  is not almost convergent);  
(ii) if  $u < m$ , then  $\Delta_{\Lambda}^{R}\cap \Delta^{R,f}\neq \emptyset$  for any  $\Lambda \in Pr^{k,R}$  (hence by Theorem 2.3(c),  $\mathrm{ch}_{H^R (L(\Lambda))} = 0$ ).

In order to prove (i), let  $k' = k_{p,m}$ , so that  $(k', f_m)$  is an exceptional pair. Then, by Theorem 3.1, there exists  $\Lambda' \in Pr^{k',R}$  for which  $\mathrm{ch}_{H^R(L(\Lambda'))}$  almost converges. As before, we write  $\Lambda'$  in the following form:  $\Lambda' = (t_{\beta'} \bar{y}).(\Lambda^0 - (m - 1)\frac{p}{m} D^R)$ , where  $\bar{y} \in W^R$  is such that  $\bar{y}(\alpha_i^R) = \gamma_i$ ,  $(\beta'|\gamma_i) = -m_i'$  for  $i = 1, \ldots, n-1$  and  $\Lambda^0 \in \widehat{P}_+^{p-n}$ , so that we have  $\widehat{\prod_{\Lambda'}}^R = \{m_i'K + \gamma_i\}_{i=0,\ldots,n-1}$ . Let  $I_{\Lambda'} = \{i | 0 \leq i \leq n-1, m_i' = 0\}$ . Then  $\{\gamma_i\}_{i \in I_{\Lambda'}}$  is the set of simple roots of  $\Delta_{\Lambda'}^R \cap \Delta_+^R$ . Recall that the almost convergence of  $\mathrm{ch}_{H^R(L(\Lambda'))}$  implies:

$$
\Delta_ {\Lambda^ {\prime}} ^ {R} \cap \Delta^ {R, f} = \emptyset , | \Delta_ {\Lambda^ {\prime}} ^ {R} | = | \Delta^ {0} \cup \Delta^ {1 / 2} |.
$$

Now fix  $i_0 \in I_{\Lambda'}$  and define  $m_i$  for  $0 \leq i \leq n-1$  and  $\beta \in \sum_{i=1}^{n-1} \mathbb{R}\alpha_i^R$  by the following relations:

$$
m _ {i} = m _ {i} ^ {\prime} \text {i f} i \neq i _ {0}, m _ {i _ {0}} = u - m;
$$

$$
(\beta | \gamma_ {i}) = - m _ {i} \text {f o r} i = 1, \dots , n - 1.
$$

Then  $\Lambda = (t_{\beta}\bar{y}).(\Lambda^0 -(u - 1)\frac{p}{u} D^R)\in Pr^{k,R}$  with  $\widehat{\prod}_{\Lambda}^{R} = \{m_{i}K + \gamma_{i}\}_{i = 0,\dots,n - 1}$ . Since  $m_{i_0} > 0$ ,  $\prod_{\Lambda}^{R} = \prod_{\Lambda '}^{R}\setminus \{\gamma_{i_0}\}$ , hence

$$
\Delta_ {\Lambda} ^ {R} \subset \Delta_ {\Lambda^ {\prime}} ^ {R} \subset \Delta^ {R} \backslash \Delta^ {R, f} \mathrm {a n d} | \Delta_ {\Lambda} ^ {R} | <   | \Delta_ {\Lambda^ {\prime}} ^ {R} | = | \Delta^ {0} \cup \Delta^ {1 / 2} |,
$$

proving (i).

In order to prove (ii), let  $\Lambda \in Pr^{k,R}$ , where  $\widehat{\prod}_{\Lambda}^{R} = \{m_{i}K + \gamma_{i}\}_{i=0,\dots,n-1}$ . Then  $u = \sum_{i=0}^{n-1} m_{i} < m$  (by our assumption), hence  $\mathrm{rank} \Delta_{\Lambda}^{R} = |\{i|m_{i} = 0\}| \geq n - m + 1 > n - m$ . Therefore, by Proposition 3.3(a),  $\Delta_{\Lambda}^{R} \cap \Delta^{R,f} \neq \emptyset$ , proving (ii).

![](images/80cea02e7389256130d1199354e6b2059ee627ff2674f426101bb16691f62641.jpg)

Theorem 3.2. Let  $f$  be a nilpotent element of  $s\ell_{n}$ , different from any of the nilpotent elements  $f_{m}, 1 \leq m \leq n$ . Then  $(k, f)$  is not an exceptional pair for any  $k$ .

Proof. Let  $m$  be the largest part of the partition, corresponding to  $f$ , and suppose that  $(k, f)$  is an exceptional pair, where  $k = -n + \frac{p}{u}$ ,  $p, u \in \mathbb{N}$ ,  $(p, u) = 1$ ,  $p \geq n$ . Let  $\Lambda \in Pr^{k,R}$  be such that  $\mathrm{ch}_{H^R(L(\Lambda))}$  does not vanish. Then, by Lemma 3.1,

(3.4)

$$
m \leq u.
$$

By Proposition 3.3(c), there exists a root subsystem  $\Phi \subset \Delta^{R} \backslash \Delta^{R, f}$ , such that

$$
\mathrm {r a n k} \Phi = n - m, \quad | \Phi | <   | \Delta^ {0} \cup \Delta^ {1 / 2} |.
$$

Let  $\prod_{\Phi} = \{\beta_1, \ldots, \beta_{n - m}\}$ , be the set of simple roots of  $\Phi \cap \Delta_{+}^{R}$ , and extend  $\prod_{\Phi}$  to a set of simple roots  $\prod' = \{\gamma_1, \ldots, \gamma_{n - 1}\}$  of  $\Delta^{R}$ . Let  $\gamma_0 = -\sum_{i=1}^{n-1} \gamma_i$ , and define  $u_i \in \mathbb{Z}_+$  as follows (here we use (3.4)):  $u_0 = u - m + 1$ ,  $u_i = 1$  if  $\gamma_i \in \prod' \setminus \prod_{\Phi}$ ,  $u_i = 0$  if  $\gamma_i \in \prod_{\Phi}$ . Let  $\widehat{\prod}_{\Phi} = \{u_i K + \gamma_i | i = 0, \ldots, n - 1\} \subset \widehat{\Delta}_{+}^{R}$ , and let  $\Lambda$  be a principal admissible weight of level  $k$ , such that  $\widehat{\prod}_{\Lambda}^{R} = \widehat{\prod}_{\Phi}$ . Note that  $\Delta_{\Lambda}^{R} = \Phi$ . Hence  $|\Delta_{\Lambda}^{R}| < |\Delta^0 \cup \Delta^{1/2}|$ , and therefore, by Corollary 2.2,  $\mathrm{ch}_{H^{R}(L(\Lambda))}$  is not almost convergent.

3.3 Example of  $\mathfrak{g} = s\ell_3$ ,  $f = \text{minimal nilpotent}$ . In this case  $x = \frac{1}{2}\theta$ , where  $\theta = \alpha_{1} + \alpha_{2}$  is the highest root,  $\mathfrak{g}_0 = \mathfrak{h}$ , hence  $\Delta^0 = \emptyset$ , and  $\Delta^{1/2} = \{\alpha_1, \alpha_2\}$ . We choose  $h_0 = \alpha_1 - \alpha_2$ ; then  $\mathfrak{h}^f = \mathbb{C}h_0$ ,  $\Delta_+^{1/2} = \{\alpha_1\}$ ,  $\Delta_-^{1/2} = \{\alpha_2\}$ ,  $\Delta_+^{\text{new}} = \{\alpha_1, -\alpha_2, -\alpha_1 - \alpha_2\} = \bar{w}(\Delta_+)$ , where  $\bar{w} = r_2r_1$ . Therefore,

$$
\Delta_ {+} ^ {R} = t _ {x} (\Delta_ {+} ^ {\mathrm {n e w}}) = \left\{- \frac {1}{2} K + \alpha_ {1}, \frac {1}{2} K - \alpha_ {2}, K - \alpha_ {1} - \alpha_ {2} \right\},
$$

$$
\prod^ {R} = t _ {x} \bar {w} (\{\alpha_ {1}, \alpha_ {2} \}) = \{\alpha_ {1} ^ {R} := K - \alpha_ {1} - \alpha_ {2}, \alpha_ {2} ^ {R} := - \frac {1}{2} K + \alpha_ {1} \},
$$

$$
\widehat {\prod} ^ {R} = t _ {x} \bar {w} (\{\alpha_ {0}, \alpha_ {1}, \alpha_ {2} \}) = \{\alpha_ {0} ^ {R} := \frac {1}{2} K + \alpha_ {2}, \alpha_ {1} ^ {R}, \alpha_ {2} ^ {R} \}.
$$

We also have:

$$
\mathfrak {h} ^ {f} = \mathbb {C} \big (\alpha_ {1} ^ {R} + 2 \alpha_ {2} ^ {R} \big), \Delta_ {+} ^ {R, f} = \left\{\alpha_ {1} ^ {R} \right\}, \Delta_ {+} ^ {R, 0} = \emptyset , \Delta_ {+} ^ {R, 1 / 2} = \left\{\alpha_ {2} ^ {R} \right\}.
$$

Recall that the corresponding to  $f$  exceptional denominator is  $u = 2$ . Then (cf. Section 1.2):

$$
\widehat {S} _ {(2)} ^ {R} = \{2 K - \alpha_ {1} ^ {R} - \alpha_ {2} ^ {R}, \alpha_ {1} ^ {R}, \alpha_ {2} ^ {R} \},
$$

and the corresponding set of roots is

$$
\widehat {\Delta} _ {(2)} ^ {R} = \{2 n K + \alpha | \alpha \in \Delta^ {R}, n \in \mathbb {Z} \} \cup \{2 n K | n \in \mathbb {Z} \backslash \{0 \} \}.
$$

Consider all possible subsets  $t_\beta \bar{y}(\widehat{S}_{(2)})$  where  $\bar{y} \in W^R = t_x W t_x^{-1}$ ,  $\beta \in \mathbb{Z} \Lambda_1^R + \mathbb{Z} \Lambda_2^R$ ,  $\Lambda_i^R \in \mathfrak{h}^R = t_x(\mathfrak{h})$ ,  $(\Lambda_i^R | \alpha_j^R) = \delta_{ij}$ , satisfying the conditions

$$
t _ {\beta} \bar {y} (\widehat {S} _ {(2)} ^ {R}) \subset \widehat {\Delta} _ {+} ^ {R} \text {a n d} t _ {\beta} \bar {y} (\widehat {\Delta} _ {(u)} ^ {R}) \cap (\Delta^ {R, f} = \{\alpha_ {1} ^ {R} \}) = \emptyset .
$$

It is easy to see that there are two possibilities for such subsets:

$$
\widehat {\prod} ^ {\prime} = t _ {- \Lambda_ {1} ^ {R}} (\widehat {S} _ {(2)} ^ {R}) = \{K - \alpha_ {1} ^ {R} - \alpha_ {2} ^ {R}, K + \alpha_ {1} ^ {R}, \alpha_ {2} ^ {R} \} \mathrm {a n d} \widehat {\prod} ^ {\prime \prime} = r _ {\alpha_ {1} ^ {R}} (\widehat {\prod} ^ {\prime}).
$$

Since  $r_{\alpha_1^R} |_{\mathfrak{h}^f} = 1$ , it follows from formula (2.3) that  $\chi_{H^R(L(\Lambda))} = \chi_{H^R(L(\Lambda'))}$  if  $\Lambda'$  and  $\Lambda''$  are admissible weights, satisfying  $\Lambda'' + \widehat{\rho}^R = r_{\alpha_1^R} (\Lambda' + \widehat{\rho}^R)$ . Thus, it suffices to consider only the principal admissible weights  $\Lambda$ , such that  $\widehat{\prod}_{\Lambda}^R = \widehat{\prod}' = t_{-\Lambda_1^R} (\widehat{S}_{(2)}^R)$ .

Since  $u = 2$ ,  $p$  should be an odd integer  $\geq h^{\vee} = 3$ , and  $k = -3 + p / 2$ . All principal admissible weights  $\Lambda$  of level  $k$  with  $\widehat{\prod}_{\Lambda}^{R} = \widehat{\prod}'$  are

$$
\Lambda = t _ {- \Lambda_ {1} ^ {R}}. (\Lambda^ {0} - \frac {p}{2} D ^ {R}) = \Lambda^ {0} - \frac {p}{2} (\Lambda_ {1} ^ {R} + D ^ {R}) \mod \mathbb {C} K, \mathrm {w h e r e} \Lambda^ {0} \in \widehat {P} _ {+} ^ {p - 3, R}.
$$

Since  $\mathfrak{h}^f = \mathbb{C}\Lambda_2^R$ , we can write an arbitrary element of  $\mathfrak{h}^f$  as  $z\Lambda_2^R$ ,  $z\in \mathbb{C}$ . Since  $\dim \mathfrak{g}^f = 4$  and  $h^\vee = 3$ , we obtain from (2.5):

$$
\psi (\tau , z \Lambda_ {2} ^ {R}, t) = e ^ {6 \pi i t} \eta (\tau) \theta (\tau , z).
$$

Note that for  $\Lambda \in M_p \coloneqq \{\Lambda^0 - \frac{p}{2} (\Lambda_1^R + D^R) | \Lambda^0 \in \widehat{P}_+^{p-3,R}\}$  we have:

$$
\widehat {\Delta} _ {\Lambda} ^ {R} = \{2 n K \pm \alpha_ {2} ^ {R}, (2 n - 1) K \pm \alpha_ {1} ^ {R}, (2 n - 1) K \pm (\alpha_ {1} ^ {R} + \alpha_ {2} ^ {R}) | n \in \mathbb {Z} \} \cup \{2 n K | n \in \mathbb {Z} \backslash 0 \}
$$

(it is a root system with basis  $\widehat{\prod_{\Lambda}R}$ ), hence

$$
\widehat {\Delta} _ {\Lambda , +} ^ {R} | _ {\mathfrak {h} ^ {f}} = \left\{(n - 1) K + \alpha_ {2} ^ {R} | _ {\mathfrak {h} ^ {f}}, n K - \alpha_ {2} ^ {R} | _ {\mathfrak {h} ^ {f}} \mid n \in \mathbb {N} \right\} \cup \left\{n K | n \in \mathbb {N} \right\}.
$$

Since for principal admissible weights in  $M_p$  we have  $\bar{y} = 1$ ,  $\beta = -\Lambda_1^R$ , a straightforward calculation gives that in (2.6) we have

$$
C (\tau , z \Lambda_ {2} ^ {R}, t) / \psi (\tau , z \Lambda_ {2} ^ {R}, t) = e ^ {- 3 \pi i t}.
$$

Hence (2.6) for  $\Lambda \in M_p$  becomes:

$$
\chi_ {H ^ {R} (L (\Lambda))} (\tau , z \Lambda_ {2} ^ {R}, t) = e ^ {- 3 \pi i t} \chi_ {L ^ {R} (\Lambda^ {0})} (2 \tau , z \Lambda_ {2} ^ {R} - \tau \Lambda_ {1} ^ {R}, \frac {1}{2} (t + \frac {\tau - z}{3})).
$$

Since  $\dim \mathfrak{g} = 8$ ,  $\dim \mathfrak{g}^f = 4$  and  $\mathrm{ch}_{H^R (L(\Lambda))}$  for  $\Lambda \in Pr^{k,R}$  does not vanish only when  $\widehat{\prod}_{\Lambda}^{R}$  is  $\widehat{\prod}'$  or  $\widehat{\prod}''$ , and the latter two give equal contributions. Thus, Theorem 2.1 gives the following transformation formula for  $\Lambda \in M_p$ :

$$
\chi_ {H ^ {R} (L (\Lambda))} \left(- \frac {1}{\tau}, \frac {z \Lambda_ {2} ^ {R}}{\tau}, t - \frac {Q _ {p} (z)}{2 \tau}\right) = - 2 \sum_ {\Lambda^ {\prime} \in M _ {p}} a (\Lambda , \Lambda^ {\prime}) \chi_ {H ^ {R} (L (\Lambda^ {\prime}))} (\tau , z \Lambda_ {2} ^ {R}, t),
$$

where  $Q_{p}(z) = \frac{2p - 6}{3p - 18} z^{2}$ .

Finally, we compute asymptotics, using Theorem 2.2. It is easy to see that  $A_{\beta}(z\Lambda_2^R) = 2$  for  $\beta = -\Lambda_1^R$ . Hence we have for  $\Lambda \in M_p$ , as  $\tau \downarrow 0$ :

$$
\mathrm {c h} _ {H ^ {R} (L (\Lambda))} (\tau , - \tau z \Lambda_ {2} ^ {R}, 0) = a (\Lambda^ {0}) e ^ {\frac {\pi i}{1 2 \tau} 4 \left(1 - \frac {3}{p}\right)}.
$$

Remark 3.1. For  $\mathfrak{g} = s\ell_{n}$  and its exceptional pair  $(k = -n + \frac{p}{u},f = f_u)$ , where  $u\leq n$ , the "extra factor" in the character formula (2.6) is independent of  $z$ , and is given by the following formula:

$$
\frac {C (\tau , z , t)}{\psi (\tau , z , t)} = \pm a (t) q ^ {b} \left(\prod_ {j = 1} ^ {\infty} \frac {1 - q ^ {u j}}{1 - q ^ {j}}\right) ^ {s ^ {\prime} - 1} M (q),
$$

where  $\pm = (-1)^{j_{\Lambda}}$ ,  $a(t) = e^{2\pi in(u^{-1} - 1)t}$ ,  $b = (s - 1)(u - s - 1)(su - s^2 + u) / 24u$ ,  $s$  is the remainder of the division of  $n$  by  $u$ ,  $s' = \min \{s, u - s\}$ , and

$$
M (q) = \prod_ {i = 1} ^ {s ^ {\prime}} \left(\prod_ {j = 1} ^ {\infty} (1 - q ^ {(j - 1) u + i}) (1 - q ^ {j u - i})\right) ^ {s ^ {\prime} - i}.
$$

In particular, the "extra factor" is equal to  $\pm a(t)$  if  $s' = 1$ , and to  $\pm a(t)\eta(\tau) / \eta(u\tau)$  if  $s' = 0$ .

3.4 Conjectures. Let  $\mathfrak{g}$  be a simple Lie algebra, and denote by  $E_0$  the set of all non-principal exceptional nilpotent orbits of  $\mathfrak{g}$ . Let  $h$  be the Coxeter number of  $\mathfrak{g}$ , and let  $I_0$  denote the set of integers  $j$ , such that  $1 \leq j < h$  and  $(j,\ell) = 1$ , where  $\ell (= 1,2$  or 3) is the lacety of  $\mathfrak{g}$ .

Conjecture E. There exists an order-preserving map  $\varphi : E_0 \to I_0$ , such that all exceptional pairs  $(k, f)$ , for which  $f$  is not principal, are as follows:  $f$  lies in an orbit from  $E_0$ ,  $k = -h^{\vee} + \frac{p}{\varphi(f)}$ , where  $p \in \mathbb{Z}$ ,  $p \geq h^{\vee}$  and  $(p, \varphi(f)) = 1$ .

Recall that all adjoint nilpotent orbits of  $\mathfrak{g} = so_N$ ,  $N$  odd (resp.  $sp_N$ ,  $N$  even) are intersections of nilpotent orbits of  $s\ell_N$  with  $\mathfrak{g}$ , if they are non-empty, and these intersections are non-empty iff all even (resp. odd) parts of the corresponding partition of  $N$  have even multiplicity. In the case  $\mathfrak{g} = so_N$ ,  $N$  even, the answer is the same, as for  $\mathfrak{g} = so_N$ ,  $N$  odd, except that in cases when all parts of the partition are even, the intersection consists of two orbits, permuted by an outer automorphism of  $so_N$ , which we shall identify. Furthermore, a nilpotent orbit of  $\mathfrak{g} = so_N$  or  $sp_N$  is of principal type if either the multiplicities of all parts of the partition of  $N$  are even, or else one has respectively:

$\mathfrak{g} = sp_N$ , and exactly one even part has odd multiplicity,

$\mathfrak{g} = s o_N$ $N$  odd, and exactly one odd part has odd multiplicity,

$\mathfrak{g} = s o_N$ $N$  even, and exactly two distinct parts, one of which is 1, have odd multiplicity.

Conjecture F. Let  $\mathfrak{g}$  be  $so_N$  or  $sp_N$ . Let  $m$  be a positive integer, and denote by  $N_m$  the set of matrices  $\{X \in \mathrm{Mat}_N \cap \mathfrak{g} | X^m = 0\}$ , and let  $\varnothing_m$  be the adjoint orbit, open in  $N_m$  (such an orbit is unique if  $\mathfrak{g} \neq so_{4n}$  or  $m$  is odd). Denote by  $F_0$  the set of all non-principal adjoint orbits  $\varnothing_m$  of principal type with  $m$  odd. Then  $F_0 \subset E_0$  and  $\varphi(\varnothing_m) = m$  for  $\varnothing_m \in F_0$ .

# Conjecture G.

(a) If  $\mathfrak{g} = s o_{2n + 1}$  or  $sp_{4n + 2}$ , then  $E_0 = F_0$ .  
(b) If  $\mathfrak{g} = sp_{4n}$ , then  $E_0 = \{F_0, \varnothing_{2n,2n}\}$ , where  $\varnothing_{2n,2n}$  denotes the nilpotent orbit, corresponding to the partition  $4n = 2n + 2n$ , and  $\varphi(\varnothing_{2n,2n}) = 2n + 1$ .  
(c) If  $\mathfrak{g} = so_{2n}$ , then  $F_0$  consists of all exceptional nilpotent orbits  $\varnothing$  with  $\varphi(\varnothing)$  odd.

We checked conjectures E, F and G for  $N \leq 13$ .

Examples 3.1. (a)  $\mathfrak{g} = s o_8$ . Then  $E_0 = \{F_0, \varnothing_{3,2,2,1}\}$ , where  $\varnothing_{3,2,2,1}$  is the nilpotent orbit, corresponding to the partition  $8 = 3 + 2 + 2 + 1$ , and  $\varphi(\varnothing_{3,2,2,1}) = 2$ . (Note that  $\varnothing_{3,2,2,1}$  is not open in  $N_3$ .)

(b)  $\mathfrak{g} = s o_{10}$ . Then  $E_0 = \{F_0, \varnothing_{3,2,2,1,1,1}\}$ , and  $\varphi(O_{3,2,2,1,1,1}) = 2$ . (Note that  $\varnothing_{3,2,2,1,1,1}$  is not open in  $N_{3}$ .)  
(c)  $\mathfrak{g} = s o_{12}$ . Then  $E_0 = \{F_0, \emptyset_{5,3,3,1}, \emptyset_{3,2,2,2,2,1}, \emptyset_{3,2,2,1,1,1,1,1}\}$ , and  $\varphi(\emptyset_{5,3,3,1}) = 4$ ,  $\varphi(\emptyset_{3,2,2,2,2,1}) = \varphi(\emptyset_{3,2,2,1,1,1,1,1}) = 2$ . (Note that  $O_{5,3,3,1}$  is not open in  $N_5$  and  $\emptyset_{3,2,2,2,2,1}$ ,  $\emptyset_{3,2,2,1,1,1,1,1}$  are not open in  $N_3$ .)

(d)  $\mathfrak{g} = G_2$ . Then the only non-zero non-principal exceptional nilpotent orbit is the orbit  $\varnothing$  of a root vector  $e_{\alpha}$ , where  $\alpha$  is a short root, and  $\varphi(\varnothing) = 2$ . This is the simplest case when the extra factor in (2.6) does depend on  $z$ :

$$
\frac {C (\tau , z , t)}{\psi (\tau , z , t)} = e ^ {- 4 \pi i t} \frac {f (\tau , z)}{f (2 \tau , 2 z)},
$$

where  $f(\tau ,z)$  is defined by (2.7).

# 3.5 Corrections to [KRW] and [KW4].

1. The last sentence of Proposition 3.3 in [KW4] should be changed as follows (cf. Theorem 2.3 of the present paper):

Then  $\mathrm{ch}_{H^{\mathrm{tw}}(M)}(\tau, h)$  is not identically zero iff the character of the  $\widehat{\mathfrak{g}}^{\mathrm{tw}}$ -module  $M$  has a pole at all hyperplanes  $\alpha = 0$ , where  $\alpha$  are positive even real roots, satisfying the following three properties:

Similar change should be made in Theorem 3.2 of [KRW].

2. The first factor on the right of formula (3.14) in [KW4] should be replaced by the following expression:

$$
e ^ {2 \pi i \tau (\frac {\bar {\Lambda} | \bar {\Lambda} + \bar {\rho} ^ {\hat {t} w}}{2 (k + h ^ {\vee})} + s _ {\mathfrak {g}} + s _ {\mathrm {c h}} + s _ {\mathrm {n e}} + (\Lambda | \Lambda_ {0}))} e ^ {\pi i (\sum_ {\alpha \in S _ {1 / 2}} (- 1) ^ {p (\alpha)} s _ {\alpha} \alpha (h) - 2 \sum_ {\alpha \in S _ {+}} (- 1) ^ {p (\alpha)} s _ {\alpha} \alpha (h))}.
$$

3. The convergence of characters argument in the proof of Theorem 3.1 in [KRW] should be changed as in the proof of Section 2.2 of the present paper. In particular, one should add there the assumption that  $f$  is of principal type.

3.6 Appendix: on representations of  $W^{\mathrm{fin}}(\mathfrak{g},f)$ . The associative algebra  $W^{\mathrm{fin}}(\mathfrak{g},f)$  is obtained by quantum Hamiltonian reduction as follows [P], [GG]. Let  $\mathfrak{g}_{\geq 1} = \oplus_{j\geq 1}\mathfrak{g}_j$  and let  $\chi : \mathfrak{g}_{\geq 1}\to \mathbb{C}$  be a homomorphism, defined by  $\chi (a) = (f|a)$ . Extend  $\chi$  to a homomorphism  $\chi : U(\mathfrak{g}_{\geq 1})\to \mathbb{C}$  and let  $I_{\chi}\subset U(\mathfrak{g}_{\geq 1})$  be the kernel of  $\chi$ . The subspace  $I_{\chi}$  is invariant with respect to the adjoint action of  $\mathfrak{g}_{+}$ , hence the left ideal  $U(\mathfrak{g})I_{\chi}$  of  $U(\mathfrak{g})$  is ad  $\mathfrak{g}_{+}$ -invariant as well, and we let

$$
W ^ {\mathrm {f i n}} (\mathfrak {g}, f) = (U (\mathfrak {g}) / U (\mathfrak {g}) I _ {\chi}) ^ {\mathrm {a d} \mathfrak {g} _ {+}}.
$$

It is easy to check that the product on  $U(\mathfrak{g})$  induces a well-defined product on  $W^{\mathrm{fin}}(\mathfrak{g},f)$ . We thus obtain the finite  $W$ -algebra, associated to the pair  $(\mathfrak{g},f)$ .

For the purpose of representation theory it is more convenient to use an equivalent definition of  $W^{\mathrm{fin}}(\mathfrak{g},f)$ , similar to that of  $W^{k}(\mathfrak{g},f)$  (equivalence of these two definitions was proved in the appendix to [DK]). Let  $\operatorname{Cl}(\mathfrak{g},f)$  denote the Clifford-Weil algebra on the vector superspace  $A_{\mathrm{ch}} \oplus A_{\mathrm{ne}}$  with the bilinear form  $(.|.) \oplus \langle .|. \rangle$ . Let  $\mathcal{C}(\mathfrak{g},f) = U(\mathfrak{g}) \otimes \operatorname{Cl}(\mathfrak{g},f)$ , and introduce the following odd element of  $\mathcal{C}(\mathfrak{g},f)$ :

$$
d = \sum_ {\alpha \in S _ {+}} (u _ {\alpha} + (f | u _ {\alpha})) \varphi^ {\alpha} + \sum_ {\alpha \in S _ {1 / 2}} \varphi^ {\alpha} \phi_ {\alpha} - \frac {1}{2} \sum_ {\alpha , \beta , \gamma \in S _ {+}} c _ {\alpha , \beta} ^ {\gamma} \varphi_ {\gamma} \varphi^ {\alpha} \varphi^ {\beta}.
$$

(This element is obtained from  $d(z)$  in Section 2.1 by dropping  $z$  and the signs of normally ordered product.) Then  $d^2 = \frac{1}{2} [d,d] = 0$ , and we have [DK]:

$$
W ^ {\mathrm {f i n}} (\mathfrak {g}, f) = H \left(\mathcal {C} (\mathfrak {g}, f), \operatorname {a d} d\right).
$$

As in [KW3] or [DK], one proves that this homology is concentrated in  $0^{\mathrm{th}}$  degree with respect to the charge decomposition, defined by

$$
\operatorname {c h a r g e} u _ {\alpha} = \operatorname {c h a r g e} \phi_ {\alpha} = 0, \operatorname {c h a r g e} \varphi_ {\alpha} = - \operatorname {c h a r g e} \varphi^ {\alpha} = 1. \tag {3.6}
$$

Recall the construction of  $\Delta_{+}^{\mathrm{new}}\subset \Delta$  in Section 2.2, and let

$$
R _ {j} ^ {\pm} = \{\alpha \in \pm \Delta_ {+} ^ {\mathrm {n e w}} | \alpha (x) = j \}, R _ {> 0} ^ {+} = \cup_ {j > 0} R _ {j} ^ {+}, R _ {> 0} ^ {-} = \cup_ {j > 0} R _ {j} ^ {-}.
$$

Let  $S(\mathfrak{g}, f)$  denote the irreducible  $\operatorname{Cl}(\mathfrak{g}, f)$ -module, generated by the even vector  $|0\rangle$ , subject to the conditions:

$$
\phi_ {\alpha} | 0 \rangle = 0 \text {i f} \alpha \in R _ {1 / 2} ^ {+}, \varphi_ {\alpha} | 0 \rangle = 0 \text {i f} \alpha \in R _ {> 0} ^ {+} \varphi^ {\alpha} | 0 \rangle = 0 \text {i f} \alpha \in R _ {> 0} ^ {-}.
$$

As in Section 2.2, given a  $\mathfrak{g}$ -module  $M$ , we can construct the complex

$$
\left(\mathcal {C} (M) = M \otimes S (\mathfrak {g}, f), d\right).
$$

It is a  $\mathbb{Z}$ -graded  $\mathcal{C}(\mathfrak{g},f)$ -module  $\mathcal{C}(M) = \oplus_{j\in \mathbb{Z}}\mathcal{C}_j(M)$ , where this charge decomposition extends (3.6) by letting charge  $M = 0$ , charge  $|0\rangle = 0$ . We thus obtain for each  $j\in \mathbb{Z}$  a functor  $H_{j}$  from the category of  $\mathfrak{g}$ -modules to the category of  $W^{\mathrm{fin}}(\mathfrak{g},f)$ -modules, given by:

$$
H _ {j} (M) := H _ {j} (\mathcal {C} (M), d).
$$

As in Section 2.2, we prove the following proposition.

Proposition 3.4. Assume that  $f$  is a nilpotent element of principal type. Let  $M$  be a highest weight  $\mathfrak{g}$ -module with respect to  $\Delta_{+}^{\mathrm{new}}$ , so that  $\operatorname{ch}_M(h) = \frac{n_M(h)}{\prod_{\alpha \in \Delta_{+}^{\mathrm{new}}} (1 - e^{-\alpha(h)})}$ ,  $h \in \mathfrak{h}$ . Then the Euler-Poincaré character  $\operatorname{ch}_{H(M)}$  of the  $W^{\mathrm{fin}}(\mathfrak{g}, f)$ -module  $H(M) = \oplus_{j \in \mathbb{Z}} H_j(M)$  is given by:

$$
\operatorname {c h} _ {H (M)} (h) = \frac {n _ {M} (h)}{\prod_ {\alpha \in R _ {0} ^ {+} \cup R _ {1 / 2} ^ {+}} \left(1 - e ^ {- \alpha (h)}\right)}, \quad h \in \mathfrak {h} ^ {f}. \tag {3.7}
$$

We rewrite formula (3.7), using the Kazhdan-Lusztig formula for  $n_{L(w,\Lambda)}$ , where  $w \in W$  and  $\Lambda + \rho$  is an integral regular anti-dominant weight:

$$
n _ {L (w. \Lambda)} = \sum_ {y \in W} \epsilon (y) \epsilon (w) P _ {y, w} (1) e ^ {y. \Lambda}, \tag {3.8}
$$

where  $P_{y,w}(q)$  are the Kazhdan-Lusztig polynomials.

Since  $f$  is a nilpotent element of principal type it can be written as a sum of root vectors, attached to roots  $\gamma_1, \ldots, \gamma_s$ , where  $\gamma_i - \gamma_j \notin \Delta \cup \{0\}$  for  $i \neq j$ , and  $\gamma_i|_{\mathfrak{h}^f} = 0$ . Denote by  $W^f$  the subgroup of  $W$ , generated by reflections in the  $\gamma_i$ ,  $i = 1, \ldots, s$ .

Since  $e^{s.\lambda}|_{\mathfrak{h}^f} = e^\lambda |_{\mathfrak{h}^f}$  for  $s \in W^f$ , we obtain from (3.8):

$$
\begin{array}{l} n_{L(w.\Lambda)}|_{\mathfrak{h}^{f}} = \sum_{\substack{y\in W^{f}\setminus W\\ s\in W^{f}}}\epsilon (sy)\epsilon (w)P_{sy,w}(1)e^{(sy). \Lambda}|_{\mathfrak{h}^{f}} \\ = \sum_ {y \in W ^ {f} \backslash W} \epsilon (y) \epsilon (w) \sum_ {s \in W ^ {f}} \epsilon (s) P _ {s y, w} (1) e ^ {y. \Lambda} | _ {\mathfrak {h} ^ {f}}. \\ \end{array}
$$

We thus obtain the following proposition.

Proposition 3.5. Assume that  $f$  is a nilpotent element of principal type. Let  $\Lambda + \rho$  be an integral regular anti-dominant weight and  $L(w, \Lambda)$  an irreducible highest weight  $\mathfrak{g}$ -module with respect to  $\Delta_{+}^{\mathrm{new}}$ . Then

$$
\mathrm {c h} _ {H (L (w. \Lambda))} (h) = \frac {\sum_ {y \in W ^ {f} \backslash W} \epsilon (y) \epsilon (w) \tilde {P} _ {y , w} (1) e ^ {(y . \Lambda) (h)}}{\prod_ {\alpha \in R _ {0} ^ {+} \cup R _ {1 / 2} ^ {+}} \left(1 - e ^ {- \alpha (h)}\right)}, \quad h \in \mathfrak {h} ^ {f}, \tag {3.9}
$$

where  $\tilde{P}_{y,w}(q) = \sum_{s\in W^f}\epsilon (s)P_{sy,w}(q)$ .

The following conjecture is a "finite" analogue of Conjecture B.

# Conjecture H.

(a) If  $M$  is an irreducible highest weight  $\mathfrak{g}$ -module (with respect to  $\Delta_{+}^{\mathrm{new}}$ ), then  $H(M) = H_0(M)$ , and this is either an irreducible  $W^{\mathrm{fin}}(\mathfrak{g}, f)$ -module, or zero.  
(b) Suppose that  $f$  is of principal type and  $H(L(\Lambda)) \neq 0$ . Then the  $W^{\mathrm{fin}}(\mathfrak{g},f)$ -modules  $H(L(\Lambda))$  and  $H(L(\Lambda'))$  are isomorphic iff  $\Lambda' = y.\Lambda$  where  $y \in W^{f}$ .  
(c) All finite-dimensional irreducible  $W^{\mathrm{fin}}(\mathfrak{g},f)$ -modules are contained among the  $H_0(L(\Lambda))$ .

In the case when  $f$  is a principal nilpotent in a Levi subalgebra, it was conjectured in [DV] that the right-hand side of formula (3.9) gives the character of an irreducible highest weight  $W^{\mathrm{fin}}(\mathfrak{g},f)$ -module. Due to Proposition 3.5, this conjecture (in the more general case of a nilpotent element of principal type) follows from Conjecture H(a).

# References

[AM] D. Adamović and A. Milas, Vertex operator algebras associated to modular invariant representations for  $A_1^{(1)}$ , q-alg/9509025.  
[A1] T. Arakawa, Representation theory of superconformal algebras and the Kac-Roan-Wakimoto conjecture, Duke Math. J. 130 (2005), 435-478.  
[A2] T. Arakawa, Representation theory of  $W$ -algebras, Invent. Math. 169 (2007), 219-320.  
[BPZ] A.A. Belavin, A.M. Polyakov and A.M. Zamolodchikov, Infinite conformal symmetry in two-dimensional quantum field theory, Nucl. Phys. B241 (1984), 333-380.

[CM] D. Collingwood and W. McGovern, Nilpotent orbits in semisimple Lie algebras, Van Norstand Reinhold, NY, 1993.  
[DK] A. De Sole and V.G. Kac, Finite vs affine  $W$ -algebras, Japan. J. Math. 1 (2006), 137-261.  
[DLM] C. Dong, H. Li and G. Mason, Twisted representations of vertex operator algebras, Math. Ann. 310 (1998), 571-600.  
[DV] K. de Vos and P. van Dreil, The Kazhdan-Lusztig conjecture for finite  $W$ -algebras, Lett. Math. Phys. 35 (1995), 333-344.  
[EK] A.G. Elashvili and V.G. Kac, Classification of good gradings of simple Lie algebras, Amer. Math. Soc. Transl (2) vol 213 (2005), 85-104.  
[FKW] E. Frenkel, V.G. Kac and M. Wakimoto, Characters and fusion rules for  $W$ -algebras via quantized Drinfeld-Sokolov reduction, Comm. Math. Phys. 147 (1992) 295-328.  
[FZ] I. Frenkel and Y. Zhu, Vertex algebras associated to representations of affine and Virasoro algebras, Duke Math. J. 66 (1992), 123-168.  
[GG] W. Gan and V. Ginzburg, Quantization of Slodowy slices, IMRN 5 (2002), 243-255.  
[GH1] M. Gorelik and V.G. Kac, On simplicity of vacuum modules, Adv. Math. 211 (2007), 621-677.  
[GK2] M. Gorelik and V.G. Kac, Characters of highest weight modules over affine Lie algebras are meromorphic functions. IMRN(2007) arXiv:0704.2876  
[K1] V. G. Kac, Infinite-dimensional Lie algebras, 3rd edition, Cambridge University Press, 1990.  
[K2] V. G. Kac, Vertex algebras for beginners, Providence: AMS, University Lecture Notes, Vol. 10, 1996, Second edition, 1998.  
[KRW] V.G. Kac, S.-S. Roan and M. Wakimoto, Quantum reduction for affine superalgebras, Comm. Math. Phys., 241 (2003), 307-342.  
[KW1] V. G. Kac and M. Wakimoto, Classification of modular invariant representations of affine algebras, in Infinite-dimensional Lie algebras and groups, Advanced ser. in Math. Phys. vol.7, World Scientific, 1989, 138-177.  
[KW2] V. G. Kac and M. Wakimoto, Branching functions for winding subalgebras and tensor products, Acta Applicandae Math. 21 (1990), 3-39.  
[KW3] V.G. Kac and M. Wakimoto, Quantum reduction and representation theory of superconformal algebras, Adv. Math. 185 (2004), 400-458. Corrigendum, Adv. Math. 193 (2005), 453-455.  
[KW4] V.G. Kac and M. Wakimoto, Quantum reduction in the twisted case, in Progress in Math. 237 2005, 85-126.

[Kr] H. Kraft, Parametrisierung der Konjugationklassen in  $s\ell_{n}$ , Math. Ann. 234 (1978), 209-220.  
[P] A. Premet, Special transverse slices and their enveloping algebras, Adv. Math. 170 (2002), 1-55.  
[Z] Y. Zhu, Modular invariance of characters of vertex operator algebras, J. Amer. Math. Soc., 9 (1996), 237-302.
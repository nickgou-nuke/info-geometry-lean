# Mirror symmetry for circle compactified 4d  $\mathcal{N} = 2$  SCFTs

Peng Shan $^{a,b}$  Dan Xie $^{b}$  Wenbin Yan $^{a}$

a Yau Mathematics Science center, Tsinghua University, Beijing, 100084, China  
$^b$ Department of Mathematics, Tsinghua University, Beijing, 100084, China

ABSTRACT: We propose a mirror symmetry for 4d  $\mathcal{N} = 2$  superconformal field theories (SCFTs) compactified on a circle with finite size. The mirror symmetry involves vertex operator algebra (VOA) describing the Schur sector (containing Higgs branch) of 4d theory, and the Coulomb branch of the effective 3d theory. The basic feature of the mirror symmetry is that many representational properties of VOA are matched with geometric properties of the Coulomb branch moduli space. Our proposal is verified for a large class of Argyres-Douglas (AD) theories engineered from M5 branes, whose VOAs are W-algebras, and Coulomb branches are the Hitchin moduli spaces. VOA data such as simple modules, Zhu's algebra, and modular properties are matched with geometric properties like  $\mathbb{C}^*$ -fixed varieties in Hitchin fibers, cohomologies, and some DAHA representations. We also mention relationships to 3d symplectic duality.

# Contents

# 1 Introduction 1

# 2 4d  $\mathcal{N} = 2$  SCFTs from 6d SCFTs on a sphere 6

2.1 Basic constructions 6  
2.2 Coulomb branch as Hitchin moduli space 8  
2.3 Schur sector and W-algebra 12

# 3 Representation theory of admissible W-algebras 13

3.1 Principal admissible modules of  $V_{\kappa}(\mathfrak{g})$  14  
3.2 Representation theory of boundary admissible W-algebras 16

# 4 Coulomb branch and its  $\mathbb{C}^*$ -fixed points 18

4.1 More on Higgs bundles and Higgs fields 19  
4.2 Zero fibre of the Hitchin moduli space and the affine Springer fibre 20  
4.3 Counting fixed varieties 23

# 5 Mirror symmetry for circle compactified 4d  $\mathcal{N} = 2$  theory 26

5.1 Simple modules of W-algebra and fixed points 26

5.1.1 W-algebras at boundary admissible level 27  
5.1.2 Non-admissible W-algebras 30  
5.1.3 Formula for the number of fixed varieties 32

5.2 Conformal weights and momentum map 33  
5.3 Modular properties 34  
5.4 Zhu's  $C_2$  algebra and the cohomology ring 36  
5.5 Generalization to arbitrary  $f$  37  
5.6 Relation with 3d symplectic duality 38

# 6 Conclusion and outlook 39

# A Rank one SCFT 42

# B Twisted theory 46

# 1 Introduction

Mirror symmetry plays an important role in modern theoretical physics and mathematics as it connects a large number of disciplines including string theory, geometry, algebra, representation theory and etc. The two dimensional mirror symmetry [1] involves a pair of Calabi-Yau (CY) manifold  $X, \tilde{X}$  which can be used to define a pair of two dimensional

(2,2) superconformal field theories (SCFTs)  $\mathcal{T}(X)$  and  $\mathcal{T}(\check{X})$ . The statement is then that  $\mathcal{T}(X)$  and  $\mathcal{T}(\check{X})$  are dual in the infrared (IR)

$$
\mathcal {T} (X) \simeq \mathcal {T} (\check {X}). \tag {1.1}
$$

The basic feature of the mirror symmetry is that: the same physical quantities (such as prepotential) can be computed from different geometrical data of  $X$  or  $X^{\vee}$  [2], which leads to many interesting correspondences in mathematics. More importantly, things which are difficult to compute on one side might become easier by looking at its mirror.

Three dimensional  $\mathcal{N} = 4$  SCFTs also have similar mirror symmetric properties [3], which often involves two hyper-Kähler manifolds  $X$  and  $Y$  acting as moduli spaces of vacua of the 3d theory. The basic feature of 3d mirror symmetry discussed in [3] is that  $X$  (resp.  $Y$ ) can be realized either as the Higgs (resp. Coulomb) branch of one theory  $\mathcal{T}_1$  or the Coulomb (resp. Higgs) branch of another theory  $\mathcal{T}_2$ . Again, the manifold which is difficult to describe on one side may have a simpler description in its mirror. It was further realized in [4-7] that there are duality involving geometric properties of  $X$  and  $Y$ . For example, one can get an algebra  $\mathcal{A}_X$  through the quantization of  $X$  (and its resolution), and the representation theory of  $\mathcal{A}_X$  is closed related to the geometric property of  $Y$

$$
\mathcal {A} _ {X} \longleftrightarrow Y. \tag {1.2}
$$

This kind of duality is called symplectic duality [5, 6].

Now consider a four dimensional  $\mathcal{N} = 2$  SCFT compactified on a circle  $S^1$  with finite radius. One may wonder whether there is a similar mirror symmetry. The resulting 3d effective theory has a Coulomb branch  $\mathcal{M}_C$  which is a hyper-Kähler manifold admitting torus fibration [8], and a Higgs branch  $\mathcal{M}_H$  which is the same hyper-Kähler cone as that of the original 4d theory. In this case,  $\mathcal{M}_H$  and  $\mathcal{M}_C$  are rather different and one does not expect to find a dual theory which exchanges the role of  $\mathcal{M}_C$  and  $\mathcal{M}_H$ .

However, motivated by the symplectic duality interpretation of the 3d mirror symmetry, the analog of the mirror symmetry of circle compactified 4d theories might be formulated as an algebra/geometry duality. Indeed, there are strong evidence [9-11] that the algebra should be the vertex operator algebra (VOA) associated with the 4d theory [12] which indeed consists of Higgs branch operators as a subset [13-15], and the geometric side should be the Coulomb branch. Given an arbitrary 4d  $\mathcal{N} = 2$  SCFT  $\mathcal{T}$ , we propose the following mirror symmetry between the corresponding  $\mathrm{VOA}(\mathcal{T})$  and the Coulomb branch  $\mathcal{M}_C(\mathcal{T})$  of  $\mathcal{T}$  compactified on the circle

$$
\operatorname {V O A} (\mathcal {T}) \longleftrightarrow \mathcal {M} _ {C} (\mathcal {T}), \tag {1.3}
$$

with the dictionary summarized in table 1. Given a 4d  $\mathcal{N} = 2$  SCFT, it is in general difficult to know neither its associated VOA nor the Coulomb branch  $\mathcal{M}_C$ . However, in a series of previous works, both the corresponding VOA [13, 16-18] and the Coulomb branch of a large class of 4d  $\mathcal{N} = 2$  SCFTs [17, 19, 20] are known  $^1$ , so one can thoroughly study and check the mirror symmetry for this class of theories.

<table><tr><td>VOA(T)</td><td>MC(T)</td></tr><tr><td>Simple modules</td><td>C*-fixed varieties</td></tr><tr><td>Conformal weights</td><td>Critical values of moment maps</td></tr><tr><td>Zhu&#x27;s C2 algebra</td><td>Cohomology ring</td></tr><tr><td>Modular properties of space of characters</td><td>Modular properties of cohomology of C*-fixed varieties</td></tr></table>

Table 1: Dictionary between VOA(T) and  $\mathcal{M}_C(\mathcal{T})$  for a 4d  $\mathcal{N} = 2$  SCFT  $\mathcal{T}$  compactified on a circle.

This class of theories is engineered by compactification of a 6d  $(2,0)$  theory of type  $\mathbf{j} = \mathrm{ADE}$  on a sphere with a regular and an irregular singularity. For our interest, the irregular singularity is labelled by a rational number  $\nu = \frac{u}{m}$ . (see table 9 for allowed values), and the regular singularity is labelled by a nilpotent orbit of  $\mathbf{j}$ . It was found in [13, 16, 18] that the associated VOA is the W-algebra  $W_{-h^{\vee} + \frac{1}{\nu}}(\mathfrak{j},f)$ , and the associated  $\mathcal{M}_C$  is the Hitchin moduli space  $\mathcal{M}_{Hit}(\mathfrak{j},\nu ,(f^{\vee},c))$  with  $(f^{\vee},c)$  being the dual of  $f$  and  $c$  being a conjugacy class of the component group [41]. Therefore the mirror symmetry is the correspondence between the following two objects

$$
W _ {- h ^ {\vee} + \frac {1}{\nu}} (\mathrm {j}, f) \longleftrightarrow \mathcal {M} _ {H i t} (\mathrm {j}, \nu , (f ^ {\vee}, c)). \tag {1.4}
$$

One can also get non-simply laced W-algebra by doing outer automorphism twist around the singularity [17], and the pair of objects are

$$
W _ {- h ^ {\vee} + \frac {1}{n \nu}} (\mathfrak {g}, f) \longleftrightarrow \mathcal {M} _ {H i t} ((j, o), \nu , (f ^ {\vee}, c)). \tag {1.5}
$$

Here  $o$  is the outer automorphism of ADE Lie algebra  $\mathfrak{j}$  whose invariant Lie algebra is  $\mathfrak{g}^{\vee}$  (the Langlands dual of  $\mathfrak{g}$ ),  $n$  is the lacety of  $\mathfrak{g}$ , summarized in table 3. The simply laced case (1.4) can also be fit into (1.5) by noticing that  $\mathfrak{j} = \mathfrak{g} = \mathfrak{g}^{\vee}$  when  $\mathfrak{j}$  is simply laced and choosing  $o = \{1\}$ . The appearance of a Lie algebra and its Langlands dual on each side of the duality is a feature similar to many dualities of physical theories found before (For example, in 4d  $\mathcal{N} = 4$  SYM theories).

In the following we briefly explain how the representation aspects of VOA is related to geometric property of Coulomb branch in our particular class of examples. Part of the statements can be formulated rigorously and will be proved in a parallel math paper [42].

1. Simple modules in the category  $\mathcal{O}$  of VOA and  $\mathbb{C}^*$  fixed varieties of  $\mathcal{M}_C$ :

There is a bijection between the simple modules of  $W_{-h^{\vee} + \frac{1}{n\nu}}(\mathfrak{g},f)^4$  and the  $\mathbb{C}^*$ -fixed varieties of  $\mathcal{M}_{Hit}((\mathfrak{j},o),\nu ,(f^{\vee},c))$ . It was first observed in [9] for cases when 4d theories are  $(A_{N - 1},A_{M - 1})$  Argyres-Douglas (AD) theories with  $N$  and  $M$  coprime  $^5$ , then generalized to cases when the 4d theories are  $(A_{1},A_{N})$  and  $(A_{1},D_{N})$  AD

theories for  $N \in \mathbb{Z}_{>0}$  in [10]. To generalize this correspondence to arbitrary  $\mathfrak{g}$ ,  $\nu$  and  $f$ , a crucial observation is that the fixed varieties of Hitchin moduli spaces  $\mathcal{M}_{Hit}((\mathrm{j},o),\nu ,f^{\vee})$  are reduced to that of the affine Springer fibre of elliptic type, and there is a nice algebraic description of the latter. Using this description, we find a natural bijection between fixed varieties and simple modules of the corresponding affine Lie algebra when the level is boundary admissible<sup>6</sup>. This will be explained in [42]. For general W-algebras, it is conjectured in [43] that simple modules can be obtained from simple modules of the affine Lie algebra from BRST reduction. We explain also in loc. cit. that this reduction is the same as a reduction of fixed varieties on the Hitchin side. Moreover, our results also provide predictions for classifications of simple modules of non-admissible W-algebras.

2. Conformal weight and momentum map: One can compute the momentum map for a fixed point using the Morse theory on  $\mathcal{M}_C$ , and match this with the conformal weight of the corresponding VOA [9, 10]. In this work, we propose a general formula relating conformal weights of simple modules of  $W_{-h^{\vee} + \frac{1}{n\nu}}(\mathfrak{g},f)$  to the values of moment maps of  $\mathbb{C}^*$ -fixed points of  $\mathcal{M}_{Hit}((\mathfrak{j},o),\nu,(f^{\vee},c))$ .

3. Modular transformation and DAHA: The space of characters of simple modules of some VOA's admit modular property with respect to certain  $SL(2,\mathbb{Z})$  action. This was shown for admissible AKM [43] and W-algebras [44]. On the other hand, the cohomology of fixed varieties of  $\mathcal{M}_{Hit}((\mathfrak{j},o),\nu ,f^{\vee})$  gives a finite dimensional representation of double affine Hecke algebra (DAHA)[45, 46], and in some cases, it admits a projective action of  $SL(2,\mathbb{Z})$  which is compatible with corresponding automorphisms of DAHA [47]. For admissible W-algebras, we show in [42] that the  $SL(2,\mathbb{Z})$  representations on both sides coincide<sup>7</sup>. Our result also gives interesting insights on the modular property of non-admissible W-algebras.

4. Modular property and Coulomb branch index: The Coulomb branch index of a 4d theory on lens space  $L(k,1)$  times  $S^1$  can be computed using the Morse theory data on the fixed varieties of Coulomb branch. It was found in [10, 49] that the Coulomb branch index is related to the modular properties of the corresponding VOA. We will show that the same relation works for the admissible cases, which gives strong hint that such relation should work in general.

5. Zhu's  $C_2$  algebra and cohomology ring: There is a so-called Zhu's  $C_2$ -algebra associated with the VOA( $\mathcal{T}$ ) [50]. It provides important information on the representation theory. On the Hitchin side, one naturally have a cohomological ring. In the context of principal admissible W-algebra, we find that Zhu's  $C_2$  algebra is the same as the cohomology ring of  $\mathcal{M}_C(\mathcal{T})$ . In general, we would expect that the cohomology ring of  $\mathcal{M}_C(\mathcal{T})$  is isomorphic to the cohomology ring of  $\mathcal{M}_C(\mathcal{T})$ .

logical ring should be related to some algebra on the VOA side which characterizes simple modules.

6. Relation with 3d symplectic duality: One can take the radius of the compactification circle to zero to get a 3d  $\mathcal{N} = 4$  SCFT from the 4d theory  $\mathcal{T}$ . The Higgs branch  $\mathcal{M}_H^{3d}(\mathcal{T})$  of the 3d theory is the same as  $\mathcal{M}_H(\mathcal{T})$ , while the Coulomb branch  $\mathcal{M}_C^{3d}(\mathcal{T})$  is related to  $\mathcal{M}_C(\mathcal{T})$  in a less obvious way [51, 52]. The Higgs and Coulomb branch of 3d theory can also be described by its 3d mirror [53].  $\mathcal{M}_H^{3d}(\mathcal{T})$  and  $\mathcal{M}_C^{3d}(\mathcal{T})$  naturally forms a symplectic pair, and many known symplectic pairs can be obtained in this way. Moreover, a finite W-algebra can be found as the twisted Zhu's algebra of VOA( $\mathcal{T}$ ) [54], which is exactly the same algebra studied in the context of 3d symplectic duality. So from 4d perspective, the appearance of an algebra in the symplectic duality is natural.

We would like to add that there is one more interesting relation for the mirror pair: the character of VOA modules can be computed using the wall crossing data on  $\mathcal{M}_C(\mathcal{T})$  [23, 26, 55]. We would not discuss this duality in this paper, but hope to study it in the future.

Physical interpretation of mirror symmetry: Let us now justify the name of mirror symmetry, namely the Coulomb branch of circle compactified 4d theory  $\mathcal{T}_1$  is given by the Higgs branch of another theory  $\mathcal{T}_2$ . The crucial difference with respect to the 3d mirror is that  $\mathcal{T}_2$  has to be a five dimensional theory. Following the discussion in [52], one first compactifies the 6d theory on a Riemann surface  $\Sigma$  and then on a circle  $S^1$  to get a 4d  $\mathcal{N} = 2$  theory on a circle. On the other hand, by changing the order of compactification, one first gets a 5d maximal SYM in the low energy from the 6d theory. The Coulomb branch of original theory is then the Higgs branch of the 5d theory compactified on  $\Sigma$ . This leads to the description of the Coulomb branch of the 4d theory on a circle as the Hitchin moduli space by explicitly writing down the Higgs branch equation of motion of the 5d theory (figure 1).

The paper is organized as the following: in section 2, we review the classification of 4d  $\mathcal{N} = 2$  SCFTs from 6d (2,0) theory and the structure of their Coulomb and Higgs (Schur) branches. Section 3 reviews the representation theory of admissible W-algebras. Section 4 discusses the zero fiber of Hitchin moduli space, its relation to affine Springer fibre, and the computation of fixed varieties. Using the knowledge of previous sections, we finally check the dictionary of the mirror symmetry in table 1 which is the main focus of section 5. We will mainly provide examples and predictions here. Finally various generalizations are discussed in section 6.

![](images/2609f6c60424e38226e6d5293359c66eb3c5dd7d94578a1ceda7e325601e3c76.jpg)  
Figure 1: Left: One first compactify 6d (2,0) theory on a Riemann surface to get a 4d theory, and then on a circle to get an effective 3d theory; Right: One first compactify 6d (2,0) theory on a circle to get a 5d theory and then on a Riemann surface to get an effective 3d theory. The Coulomb branch of the theory on the left is given by the Higgs branch of the theory on the right.

# 2 4d  $\mathcal{N} = 2$  SCFTs from 6d SCFTs on a sphere

4d  $\mathcal{N} = 2$  theories has two kinds of moduli spaces of vacua: the Coulomb branch and the Higgs branch. The low energy effective theory of the Coulomb branch is solved by the Seiberg-Witten (SW) solution [56, 57]. Roughly speaking, the SW solution is given by a family of algebraic varieties fibered over a base manifold  $B$  which is the Coulomb branch of the 4d theory on flat space. If we further compactify 4d theory on a circle with finite radius  $R$ , the effective theory also has a Coulomb branch  $\mathcal{M}_C$  which is a hyper-Kähler manifold [8].  $\mathcal{M}_C$  is given by an abelian variety fibered over the base  $B$  in one of its complex structures.

In general, it is difficult to find the SW solution for an arbitrary 4d  $\mathcal{N} = 2$  theory. However, for models constructed using the 6d  $(2,0)$  theory, one can find SW solutions using Hitchin moduli spaces [58, 59]. Given a 6d  $(2,0)$  theory of type j, a Riemann surface  $\Sigma_{g,n}$  of genus  $g$  with  $n$  punctures, one obtains a  $4d\mathcal{N} = 2$  SCFT by compactification of the 6d theory on  $\Sigma_{g,n}$ , then the Coulomb branch of this 4d theory on  $S^1$  is the same as the moduli space of the Hitchin system on  $\Sigma_{g,n}$ . In the following section, we will review data required to specify the 4d theory when the Riemann surface is a sphere with one irregular and one regular punctures [17, 19, 20].

# 2.1 Basic constructions

One can engineer a large class of 4d  $\mathcal{N} = 2$  SCFTs by putting a 6d  $(2,0)$  theory of type  $\mathbf{j} = ADE$  on a sphere with an irregular singularity and a regular singularity [17, 19, 20, 58, 59] (figure 2). The Coulomb branch of this 4d  $\mathcal{N} = 2$  theory is captured by a Hitchin system with the following boundary conditions near the irregular singularities

$$
\Phi (z) = \left(\frac {T _ {k}}{z ^ {2 + \frac {k}{b}}} + \sum_ {- b \leq l <   k} \frac {T _ {l}}{z ^ {2 + \frac {l}{b}}} + \dots\right) d z. \tag {2.1}
$$

![](images/15ff9a2f99bbabba5696ffe4abc14c93a3a7303176cda9adf4637ce1b9749714.jpg)  
Figure 2: A 4d AD theory is constructed by putting a 6d  $(2,0)$  theory of type  $j$  on a sphere with one irregular singularity and one regular singularity. The irregular singularity is labeled by  $\Phi$ , see (2.1), and the regular singularity is labeled by  $f$ .

Here one first choose a  $\mathbb{Z} / b\mathbb{Z}$  grading (a positive principal grading) of Lie algebra j [60]

$$
j = \oplus_ {i \in \mathbb {Z} / b \mathbb {Z}} j _ {i / b}, \tag {2.2}
$$

then each  $T_{l}$  is a regular semi-simple element in  $\mathfrak{j}_{i / b}$ . Possible choices of the integer  $b$  for each  $\mathbf{j}$  are listed in table 2, and the integer  $k$  is greater than  $-b$ . Subsequent terms of the Higgs field are chosen such that they are compatible with the leading order term (essentially determined by the grading). We call them irregular punctures of  $\mathfrak{j}^b [k]$  type. This choice of irregular singularities ensures that the resulting 4d  $\mathcal{N} = 2$  theory has a  $U(1)_R$  symmetry and therefore superconformal. Theories constructed using only these irregular singularities can also be engineered by putting type IIB string theory on a three-dimensional singularity [61] as summarized in table 2. One can add another regular singularity which is labelled by an element  $f$  in a nilpotent orbit of  $\mathbf{j}^8$ . All in all the 4d theory in our consideration is specified by four labels  $< \mathrm{j}, b, k, f >$ , with  $\mathbf{j}$  labelling the type of 6d (2,0) SCFT,  $b, k$  specifying the irregular singularity, and  $f$  fixing the regular singularity.

To get non-simply laced flavor groups, we need to specify some outer-automorphism twist of ADE Lie algebra  $\mathfrak{j}$ . A systematic study of these AD theories was performed in [17]. Denoting by  $\mathfrak{g}^{\vee}$  the invariant algebra of  $\mathfrak{j}$  under the twist and  $\mathfrak{g}$  its Langlands dual. Outer-automorphisms and invariant algebras are summarized in table 3. The irregular singularity of regular semi-simple type is also classified in table 4 with the following form,

$$
\Phi (z) = \left(\frac {T ^ {t}}{z ^ {2 + \frac {k _ {t}}{b _ {t}}}} + \dots\right) d z. \tag {2.3}
$$

Here  $T^t$  is a semi-simple element of Lie algebra  $\mathfrak{g}^\vee$ , and the novel thing is that  $k_t$  can take half-integer value or in  $\frac{1}{3}\mathbb{Z}$  ( $\mathfrak{g} = G_2$ ) [17]. We could again add a twisted regular puncture labeled by a nilpotent orbit  $f$  of  $\mathfrak{g}$ . A 4d  $\mathcal{N} = 2$  theory is then determined by following data  $\boxed{<\mathrm{j},o,b_t,k_t,f>}$ , with  $\mathrm{j}$  labelling the type of 6d (2,0) SCFT,  $o$  being the

<table><tr><td>j</td><td>b</td><td>Singularity</td><td>Spectral curve at SCFT point</td><td>Δ[z]</td><td>μ</td></tr><tr><td>AN-1</td><td>N</td><td>x12+x22+x3N+zk=0</td><td>xN+zk=0</td><td>N/N+k</td><td>(N-1)(k-1)</td></tr><tr><td></td><td>N-1</td><td>x12+x22+x3N+x3zk=0</td><td>xN+xzk=0</td><td>N-1/N+k-1</td><td>N(k-1)+1</td></tr><tr><td>DN</td><td>2N-2</td><td>x12+x2N-1+x2x32+zk=0</td><td>x2N+x2zk=0</td><td>2N-2/2N+k-2</td><td>N(k-1)</td></tr><tr><td></td><td>N</td><td>x12+x2N-1+x2x32+zkx3=0</td><td>x2N+z2k=0</td><td>N/N+k</td><td>2k(N-1)-N</td></tr><tr><td>E6</td><td>12</td><td>x12+x23+x34+zk=0</td><td>x12+zk=0</td><td>12/12+k</td><td>6k-6</td></tr><tr><td></td><td>9</td><td>x12+x23+x34+zkx3=0</td><td>x12+x3zk=0</td><td>9/9+k</td><td>8k-6</td></tr><tr><td></td><td>8</td><td>x12+x23+x34+zkx2=0</td><td>x12+x4zk=0</td><td>8/8+k</td><td>9k-6</td></tr><tr><td>E7</td><td>18</td><td>x12+x23+x2x33+zk=0</td><td>x18+zk=0</td><td>18/18+k</td><td>7k-7</td></tr><tr><td></td><td>14</td><td>x12+x23+x2x33+zkx3=0</td><td>x18+x4zk=0</td><td>14/14+k</td><td>9k-7</td></tr><tr><td>E8</td><td>30</td><td>x12+x23+x35+zk=0</td><td>x30+zk=0</td><td>30/30+k</td><td>8k-8</td></tr><tr><td></td><td>24</td><td>x12+x23+x35+zkx3=0</td><td>x30+x6zk=0</td><td>24/24+k</td><td>10k-8</td></tr><tr><td></td><td>20</td><td>x12+x23+x35+zkx2=0</td><td>x30+x10zk=0</td><td>20/20+k</td><td>12k-8</td></tr></table>

Table 2: Three-fold isolated quasi-homogenous singularities of cDV type corresponding to the  $\mathfrak{j}^b [k]$  irregular punctures of the regular-semisimple type in [20]. These 3d singularity is very useful in extracting the Coulomb branch spectrum [61].  

<table><tr><td>j</td><td>A2N</td><td>A2N-1</td><td>DN+1</td><td>E6</td><td>D4</td></tr><tr><td>Outer-automorphism o</td><td>Z2</td><td>Z2</td><td>Z2</td><td>Z2</td><td>Z3</td></tr><tr><td>Invariant subalgebra g√</td><td>BN</td><td>CN</td><td>BN</td><td>F4</td><td>G2</td></tr><tr><td>Flavor symmetry g</td><td>C(1)N</td><td>BN</td><td>C(2)N</td><td>F4</td><td>G2</td></tr><tr><td>Lacety n</td><td>4</td><td>2</td><td>2</td><td>2</td><td>3</td></tr><tr><td>hθ</td><td>4N+2</td><td>4N-2</td><td>2N+2</td><td>18</td><td>12</td></tr></table>

Table 3: Outer-automorphisms of simple Lie algebras  $j$ , its invariant subalgebra  $\mathfrak{g}^{\vee}$  and flavor symmetry  $\mathfrak{g}$  from the Langlands dual of  $\mathfrak{g}^{\vee}$ .

outer automorphism twist,  $b_{t}$  and  $k_{t}$  together determining the irregular singularity, and finally  $f$  fixing the regular singularity.

Remark: The label  $f$  here is actually the so-called Nahm (Higgs) label. The actual boundary condition of the Higgs field  $\Phi$  around the regular singularity looks like

$$
\Phi (z) \sim \left(\frac {f ^ {\vee}}{z} + \dots\right) d z, \tag {2.4}
$$

where  $f^{\vee} \in \overline{\mathcal{O}}_{f^{\vee}}$ . The nilpotent orbit  $\mathcal{O}_{f^{\vee}}$  in  $\mathfrak{g}^{\vee}$  is the Spaltanstein dual of  $\mathcal{O}_f$ . More carefully, one also needs to specify a conjugacy class  $c$  in the component group for the Higgs field [62], which will be reviewed in section 4.

# 2.2 Coulomb branch as Hitchin moduli space

As discussed above, the Coulomb branch of the theory  $\mathcal{T}_{j,b,k,f}$  (resp.  $\mathcal{T}_{j,o,b_t,k_t,f}$ ) on a circle is specified by the Hitchin moduli space  $\mathcal{M}_{Hit}(\mathrm{j},\nu,(f^\vee,c))$  with  $\nu = \frac{k}{b} + 1$  (resp.

<table><tr><td>j/o</td><td>bt</td><td>SW geometry at SCFT point</td><td>Spectral curve at SCFT point</td><td>Δ[z]</td></tr><tr><td>A2N/Z2</td><td>2N+1</td><td>x12+x22+x2N+1+zk+1/2=0</td><td>x2N+1+zk+1/2=0</td><td>4N+2/4N+2k+3</td></tr><tr><td></td><td>2N</td><td>x12+x22+x2N+1+ xzk=0</td><td>x2N+1+ xzk=0</td><td>2N/k+2N</td></tr><tr><td>A2N-1/Z2</td><td>2N-1</td><td>x12+x22+x2N+ xzk+1/2=0</td><td>x2N+xzk+1/2=0</td><td>4N-2/4N+2k-1</td></tr><tr><td></td><td>2N</td><td>x12+x22+x2N+zk=0</td><td>x2N+zk=0</td><td>2N/2N+k</td></tr><tr><td>DN+1/Z2</td><td>N+1</td><td>x12+x2N+x2x32+x3zk+1/2=0</td><td>x2N+2+z2k+1=0</td><td>2N+2/2k+2N+3</td></tr><tr><td></td><td>2N</td><td>x12+x2N+x2x32+zk=0</td><td>x2N+2+x2zk=0</td><td>2N/k+2N</td></tr><tr><td>D4/Z3</td><td>4</td><td>x12+x23+x2x32+x3zk±1/3=0</td><td>x8+z2k±2/3=0</td><td>12/12+3k±1</td></tr><tr><td></td><td>6</td><td>x12+x23+x2x32+zk=0</td><td>x8+x2zk=0</td><td>6/6+k</td></tr><tr><td>E6/Z2</td><td>9</td><td>x12+x23+x34+x3zk+1/2=0</td><td>x12+x3zk+1/2=0</td><td>18/18+2k+1</td></tr><tr><td></td><td>12</td><td>x12+x23+x34+zk=0</td><td>x12+zk=0</td><td>12/12+k</td></tr><tr><td></td><td>8</td><td>x12+x23+x34+x2zk=0</td><td>x12+x4zk=0</td><td>8/8+k</td></tr></table>

Table 4: SW geometry of twisted theories at the SCFT point. Here we also list the scaling dimension of coordinate  $z$ . All  $k$ 's in this table are integer valued and the power of  $z$  coordinate in singularity is equal to  $k_{t}$  used in equation (2.3). For example, in the case  $(D_4,\mathbb{Z}_3,b_t = 4)$ ,  $k_{t}$  is  $k\pm \frac{1}{3}$ . The definition of  $k_{t}$  and  $b_{t}$  are slightly different from [63] but the ration  $k_{t} / b_{t}$  remains the same.

$\mathcal{M}_{Hit}((\mathrm{j},o),\nu ,(f^{\vee},c))$  with  $\nu = \frac{k_t}{b_t} +1$ . Given a solution  $\Phi (z)\in \mathcal{M}_{Hit}$ , its spectral curve

$$
\det (x - \Phi (z)) = 0 \tag {2.5}
$$

is identified with the SW curve. In certain cases, the spectral curve is equivalent to the mini-versal deformation of the singularity (listed in table 2 and 4). One can see that  $\mathcal{M}_{Hit}$  is fibered over  $B$  through the Hitchin map

$$
\mathcal {M} _ {H i t} \rightarrow B, \tag {2.6}
$$

where the base  $B$  is the moduli space of the spectral (SW) curve which is just the Coulomb branch of the 4d theory on flat spaces.

Properties of  $\mathcal{M}_{Hit}$  with  $f$  trivial were recently studied in [64]. One interesting information is the complex dimension of the base  $B$ , which is equal to the dimension of the fibre due to the property of hyper-Kähler manifold. Here we provide a way to compute  $\dim B$  from physics. Since coordinates of  $B$  are parameterized by vacuum expectation values (vev's) of 4d Coulomb branch operators, we can find  $\dim B$  by counting the number of 4d Coulomb branch operators. This can be done as following: the spectral curve takes the form  $f_{ADE}(x,y,z,w) + \sum a_i\phi_i(z) = 0$ , and the existence of  $\mathbb{C}^*$  action on  $\mathcal{M}_{Hit}$  ensures that one can define a  $\mathbb{C}^*$  action on the coordinates  $x,y,z,w$  by requiring that the spectral curve is homogeneous under the  $\mathbb{C}^*$  action and  $[x] + [z] = 1$ . From these, one can deduce the  $\mathbb{C}^*$  charge of the coordinate  $a_i$ . Those  $a_i$ 's with  $\mathbb{C}^*$  charge greater than 1 are identified as Coulomb branch operators, then  $\dim B$  is the number of such  $a_i$ 's.

Example 2.1. Consider a theory whose spectral curve is given by  $x^{2} + z^{5} + u_{1}z^{3} + u_{2}z^{2} + u_{3}z + u_{4} = 0$ . The  $\mathbb{C}^*$  charges are  $[x] = \frac{5}{7}, [z] = \frac{2}{7}$ , so the scaling dimensions of base coordinates are

$$
[ u _ {1} ] = \frac {4}{7}, [ u _ {2} ] = \frac {6}{7}, [ u _ {3} ] = \frac {8}{7}, [ u _ {4} ] = \frac {1 0}{7}, \tag {2.7}
$$

so there are two coordinates with  $\mathbb{C}^*$  charge greater than 1, then

$$
\dim B = 2. \tag {2.8}
$$

One can compute  $\dim B$  by the Milnor number of singularity. First, the dimension of the charge lattice of the Coulomb branch is  $2\dim B + \mathfrak{f}$ , where  $\mathfrak{f}$  is the rank of flavor symmetries. This dimension is the same as the Milnor number  $\mu$  of the singularity, so we have the formula [61, 65-67]

$$
\dim B = \frac {1}{2} (\mu - \mathfrak {f}). \tag {2.9}
$$

For a quasi-homogeneous singularity, one can assign a weight  $q_{i}$  for the  $i$ -th coordinate such that the weight of the singularity is one, then the Milnor number of the singularity is

$$
\mu = \prod_ {i} \left(1 - \frac {1}{q _ {i}}\right), \tag {2.10}
$$

which is always an integer. We then need to find out the number of mass parameters (those coordinates in the mini-versal deformations with scaling dimension one) which gives  $\mathfrak{f}$ .

Example 2.2. Consider the singularity which is given as  $x^{2} + y^{5} = 0$  with weight assignments  $(x, y) = (\frac{1}{2}, \frac{1}{5})$ , then the Milnor number is  $\mu = 4$ , and there is also no mass parameter, so

$$
\dim B = \mu / 2 = 2. \tag {2.11}
$$

In general, the dimension of  $B$  of the theory  $\mathcal{T}_{\mathrm{j},b,k,f}$  and  $\mathcal{T}_{\mathrm{j},o,b_t,k_t,f}$  are specified by the following formula:

- For the untwisted theory  $\mathcal{T}_{j,b,k,f}$

$$
\dim B = \frac {\left(h \frac {k}{b} - 1\right) \operatorname {r a n k} (\mathfrak {g}) - f _ {0}}{2} - \frac {\dim \mathcal {O} _ {p r i n}}{2} + \frac {\dim \mathcal {O} _ {f ^ {\vee}}}{2}. \tag {2.12}
$$

Here  $h$  is the Coxeter number for the Lie algebra  $\mathbf{j}$ .  $f_0$  is the number of mass parameters in irregular singularity [17, 68], and  $\dim \mathcal{O}_{prin}$  is the complex dimension of principal nilpotent orbit of  $\mathfrak{g}$  which is equal to  $\dim(\mathbf{j}) - \operatorname{rank}(\mathbf{j})$ .

For the twisted theory  $\mathcal{T}_{j,o,b_t,k_t,f}$

$$
\dim B = \frac {\left(h _ {\theta} \frac {k _ {t} ^ {\prime}}{b _ {t}} - 1\right) \operatorname {r a n k} (\mathfrak {g}) - f _ {0}}{2} - \frac {\dim \mathcal {O} _ {p r i n}}{2} + \frac {\dim \mathcal {O} _ {f ^ {\vee}}}{2}. \tag {2.13}
$$

Here  $k_{t}^{\prime} = nk_{t} + nb_{t}$  and  $n$  is the order of outer-outmorphism  $o$ .  $h_\theta$  is the twisted Coxeter number listed in the last line of 3.  $f_0$  is the number of mass parameters in irregular singularity [17, 68], and  $\mathcal{O}_{prin}$  is the principal nilpotent orbit of Lie algebra  $\mathfrak{g}^\vee$ .

The above formula is found by explicitly computing the graded Coulomb branch dimensions, see [63] for the derivation. We also give the explicit expression for  $\dim B$  when  $f$  is trivial or principal orbit.

- If  $f$  is trivial, the dimension of  $B$  is

$$
\dim B = \frac {\left(h _ {\theta} \frac {k _ {t} ^ {\prime}}{b _ {t}} - 1\right) \operatorname {r a n k} (\mathfrak {g}) - f _ {0}}{2}. \tag {2.14}
$$

This is the same as the result in [64].

- If  $f$  is principal, the dimension of  $B$  is given by

$$
\dim B = \frac {\left(h _ {\theta} \frac {k _ {t} ^ {\prime}}{b _ {t}} - h (\mathfrak {g} ^ {\vee}) - 1\right) \operatorname {r a n k} (\mathfrak {g}) - f _ {0}}{2}. \tag {2.15}
$$

In order to derive dimension formulae (2.12) and (2.13), we start with a non-twisted theory  $\mathcal{T}(\mathfrak{j},b,k,f)$ , and if there is irregular singularity only (i.e.  $f$  is chosen to be principal), the same theory can also be engineered by putting type IIB theory on a three-fold singularity which are listed in the third column of table 2. One can then compute  $\dim B$  using equation (2.9). The tables of  $\mu$  in each case can also be found in the last column of table I of [16] and we also reproduce them in the last column of table 2 for reader's convenience. Adding a regular singularity with Nahm label  $f$ , will change  $\dim B$  into

$$
\dim B = \frac {1}{2} \left(\mu - f _ {0}\right) + \frac {1}{2} \dim \mathcal {O} _ {f ^ {\vee}}. \tag {2.16}
$$

Finally one can check case by case that the Milnor number  $\mu$  for non-twisted cases can also be written uniformly as

$$
\mu = \left(h _ {\mathrm {j}} \frac {k}{b} + h _ {\mathrm {j}} - 1\right) \operatorname {r a n k} (\mathrm {j}) - \dim \mathcal {O} _ {p r i n} \tag {2.17}
$$

The dimension formula for twisted cases is a direct generalization of the untwisted one.

Example 2.3. When  $j = A_{N - 1}$ , the number  $b$  can be either  $N$  or  $N - 1$  as table 2. If there is no regular puncture, the corresponding 3-fold singularity is

$$
x ^ {2} + y ^ {2} + z ^ {N} + w ^ {k} = 0, \quad b = N
$$

$$
x ^ {2} + y ^ {2} + z ^ {N} + z w ^ {k} = 0, \quad b = N - 1 \tag {2.18}
$$

For  $b = N$ , the Milnor number  $\mu = (N - 1)(k - 1)$ . On the other hand, since  $h = N$ ,  $\mathrm{rank}(\mathrm{j}) = N - 1$  and  $\dim \mathcal{O}_{prin} = N^2 - N$ , we have

$$
\left(h _ {j} \frac {k}{b} + h _ {j} - 1\right) \operatorname {r a n k} (j) - \dim \mathcal {O} _ {p r i n} = (k - 1) (N - 1) = \mu . \tag {2.19}
$$

For  $b = N - 1$ , the Milnor number is  $\mu = N(k - 1) + 1$ , which also agrees with equation (2.17)

$$
\begin{array}{l} \left(h _ {\mathrm {j}} \frac {k}{b} + h _ {\mathrm {j}} - 1\right) \operatorname {r a n k} (\mathrm {j}) - \dim \mathcal {O} _ {p r i n} \tag {2.20} \\ = N k + (N - 1) ^ {2} - N (N - 1) = N (k - 1) + 1 = \mu . \\ \end{array}
$$

There is a different way of counting  $\dim B$  by using the fact that the dimension of the fibre is the same as the dimension of the base  $B$ . The dimension formula of the Hitchin fibre can also be found in math literature [46, 69, 70] for both untwisted and twisted cases, which is exactly the formula we found using physics arguments. This provides a cross check of (2.12) and (2.13).

# 2.3 Schur sector and W-algebra

The Higgs branch of a 4d  $\mathcal{N} = 2$  theory is given by a Hyper-Kähler manifold. Unlike the Coulomb branch, there are many  $\mathcal{N} = 2$  theories which do not have Higgs branch. However, all  $\mathcal{N} = 2$  theories do have a Schur sector, which includes the Higgs branch when exists. For general  $\mathcal{N} = 2$  theories especially strongly coupled theories, direct computations of Higgs (Schur) sector are very difficult. Luckily one can get a 2d VOA  $(\mathcal{T})$  from the Schur sector of a 4d  $\mathcal{N} = 2$  SCFT  $\mathcal{T}$  with the following properties [12]:

- There is a subalgebra  $V_{k_{2d}}(\mathfrak{g}_F)$  in  $\mathrm{VOA}(\mathcal{T})$ , where  $V_{k_{2d}}(\mathfrak{g}_F)$  is the simple quotient of the affine vertex algebra of the affine Kac-Moody (AKM) algebra  $\hat{\mathfrak{g}}_F$  at level  $k_{2d}$ , and  $\mathfrak{g}_F$  is the Lie algebra of 4d flavor symmetry  $G_F$ .  
- The 2d central charge  $c_{2d}$  and the level of the AKM algebra  $k_{2d}$  are related to the 4d central charge  $c_{4d}$  and the flavor central charge  $k_{F}$  as<sup>9</sup>

$$
c _ {2 d} = - 1 2 c _ {4 d}, \quad k _ {2 d} = - k _ {F}. \tag {2.21}
$$

- The (normalized) vacuum character of  $\mathrm{VOA}(\mathcal{T})$  is the 4d Schur index  $\mathcal{I}(q)$ . The growth function  $G$  of the vacuum character is related to 4d central charges by

$$
- 4 8 \left(a _ {4 d} - c _ {4 d}\right) = G \tag {2.22}
$$

- The associated variety  $X_{\mathrm{VOA}(\mathcal{T})}$  is the Higgs branch  $\mathcal{M}_H$  of  $\mathcal{T}$  [13-15].

If we can find the VOA for a given  $4\mathrm{d}\mathcal{N} = 2$  SCFT, then the Higgs (Schur) sector can be solved.

In general there is no systematical way to get  $\mathrm{VOA}(\mathcal{T})$  from a given  $\mathcal{T}$ , However, for our theory  $\mathcal{T}_{j,k,b,f}$  and  $\mathcal{T}_{j,o,k,b,f}$ , if the irregular singularity carries no flavor symmetry, the corresponding VOA are respectively the following W-algebra [13, 16-18]

$$
W _ {- h ^ {\vee} + \frac {b}{b + k}} (j, f), \tag {2.23}
$$

and

$$
W _ {- h ^ {\vee} (\mathfrak {g}) + \frac {1}{n} \frac {b _ {t}}{b _ {t} + k _ {t}}} (\mathfrak {g}, f). \tag {2.24}
$$

Here  $h^{\vee}$  is the dual Coxeter number of  $\mathfrak{j}$ ,  $h^{\vee}(\mathfrak{g})$  is the dual Coxeter number for  $\mathfrak{g}$ , and  $n$  is the lacety listed in table 3. The constraints on the irregular singularity  $\mathfrak{j}^b [k]$  which has no mass deformation are summarized in tables 5 and 6 [16, 72].

<table><tr><td>jb[k]</td><td>no mass</td><td>jb[k]</td><td>no mass</td></tr><tr><td>AN-1N[k]</td><td>(k,N)=1</td><td>AN-1N-1[k]</td><td>No solution</td></tr><tr><td>DN2N-2[k]</td><td>2N-2gcd(k,2N-2) even, gcd(k,2N-2) odd</td><td>DN[k]</td><td>Ngcd(k,N) even</td></tr><tr><td>E612[k]</td><td>k≠3n</td><td>E69[k]</td><td>k≠9n</td></tr><tr><td>E68[k]</td><td>No solution</td><td>E718[k]</td><td>k≠2n</td></tr><tr><td>E714[k]</td><td>k≠2n,n&gt;1</td><td>E830[k]</td><td>k≠30n</td></tr><tr><td>E824[k]</td><td>k≠24n</td><td>E820[k]</td><td>k≠20n</td></tr></table>

Table 5: Constraints on  $k$  so that irregular singularity denoted by  ${\mathrm{j}}^{b}\left\lbrack  k\right\rbrack$  has no mass deformation.  

<table><tr><td>j/o</td><td>bt</td><td>no mass</td></tr><tr><td>A2N/Z2</td><td>2N+1</td><td>4N+2gcd(4N+2,2k+1) even</td></tr><tr><td></td><td>2N</td><td>2Ngcd(2N,k) even</td></tr><tr><td>A2N-1/Z2</td><td>2N-1</td><td>4N-2gcd(4N-2,2k+1) even</td></tr><tr><td></td><td>2N</td><td>2Ngcd(2N,k) even</td></tr><tr><td>DN/Z2</td><td>N+1</td><td>2Ngcd(2k+1,2N) even</td></tr><tr><td></td><td>2N</td><td>2N-2gcd(k,2N-2), gcd(k,2N-2) even</td></tr><tr><td>D4/Z3</td><td>4</td><td>No constraint</td></tr><tr><td></td><td>6</td><td>k≠6n</td></tr><tr><td>E6/Z2</td><td>9</td><td>No constraint</td></tr><tr><td></td><td>12</td><td>k≠12n</td></tr><tr><td></td><td>8</td><td>k≠8n, k even</td></tr></table>

Table 6: Constraints  $k_{t}$  so that the twisted irregular singularity has no mass deformation.

From tables 2 and 4, one can see that given the irregular singularity  $j^b [k]$ , the allowed values of  $b$  is always smaller or equal to the dual Coxeter number  $h^\vee$  of  $\mathbf{j}$ . Also recall that a level of the W-algebra  $W_{\kappa}(\mathfrak{g},f)$  is called admissible if it has the form

$$
\kappa = - h ^ {\vee} + \frac {p}{q}, \quad p \geq h ^ {\vee}, q \in \mathbb {Z} _ {\geq 0}, \operatorname * {g c d} (p, q) = 1. \tag {2.25}
$$

When  $p = h^{\vee}$  the corresponding level is called boundary admissible. Then the W-algebra (2.23) and (2.24) are always boundary admissible or non-admissible.

# 3 Representation theory of admissible W-algebras

As mentioned in the introduction, the core correspondence of the mirror symmetry here is the bijection between simple modules and fixed points. In this section, we will review key information on the representation theory of W-algebras  $W_{\kappa}(\mathfrak{g},f)$  at boundary admissible level, which will provide crucial examples for our duality.

# 3.1 Principal admissible modules of  $V_{\kappa}(\mathfrak{g})$

Let  $\hat{\mathfrak{g}}$  be the (non-twisted) affine Lie algebra of  $\mathfrak{g}$ . Let us start from the representation theory of the simple VOA  $V_{\kappa}(\mathfrak{g})$  given by the unique simple quotient of the universal vertex algebra associated with  $\hat{\mathfrak{g}}$  at level  $\kappa$ . The level  $\kappa$  is called admissible if it has the following form [73]

$$
\kappa = - h ^ {\vee} + \frac {p}{u}, \quad p \geq h ^ {\vee}, u \in \mathbb {Z} _ {> 0}, \operatorname * {g c d} (p, u) = \operatorname * {g c d} (n, u) = 1. \tag {3.1}
$$

Here  $h^{\vee}$  is the dual Coxeter number of  $\mathfrak{g}$ . By [74], simple modules of  $V_{\kappa}(\mathfrak{g})$  at admissible level in the category  $\mathcal{O}$  of  $\hat{\mathfrak{g}}$  are the so-called admissible modules defined in [73]. Admissible modules have many properties similar to modules at integral levels, therefore are interesting objects in VOA research.

From now on, we fix  $\kappa$  to be the boundary admissible level, i.e.,

$$
\kappa = - h ^ {\vee} + \frac {h ^ {\vee}}{u}, \quad u \in \mathbb {Z} _ {> 0}, \operatorname * {g c d} (h ^ {\vee}, u) = \operatorname * {g c d} (n, u). \tag {3.2}
$$

In this case, the highest weight of admissible modules are given as follows. One first defines a set of affine coroots  $S_{u}$  depending on  $u$

$$
S _ {u} \equiv \{- \theta^ {\vee} + u \delta , \alpha_ {1} ^ {\vee}, \dots , \alpha_ {r} ^ {\vee} \}, \tag {3.3}
$$

where  $\theta^{\vee}$  is the coroot corresponding to the highest root  $\theta$  of  $\mathfrak{g}$ , and  $\delta$  is the imaginary root,  $\{\alpha_1^{\vee},\dots ,\alpha_r^{\vee}\}$  is the set of simple coroots of  $\mathfrak{g}$ . The set of admissible weights at level  $\kappa$  is given by

$$
\operatorname {A d m} _ {\kappa} = \left\{w. \left(\kappa \Lambda_ {0}\right) \mid w \in W _ {e x t}, w \left(S _ {u}\right) \subset \hat {\Delta} _ {+} ^ {\vee} \right\}, \tag {3.4}
$$

where  $W_{ext}$  is the extended affine Weyl group,  $\Lambda_0$  is the 0-th affine fundamental weight, and  $\hat{\Delta}_{+}^{\vee}$  is the set of positive real coroots. The dot action  $w.\Lambda$  is defined as

$$
w. \Lambda \equiv w (\Lambda + \hat {\rho}) - \hat {\rho}, \tag {3.5}
$$

with  $\hat{\rho} = \sum_{i=0}^{r} \Lambda_i$  being the affine Weyl vector. Here  $\Lambda_i$ 's are affine fundamental weights of  $\hat{\mathfrak{g}}$  and  $r = \mathrm{rank}\mathfrak{g}$ . Moreover,  $w.(k\Lambda_0) = w'(k\Lambda_0)$  if and only if  $w^{-1}w'(S_u) = S_u$ . Let

$$
W _ {u} = \left\{w \in W _ {\text {e x t}} \mid w \left(S _ {u}\right) \subset \hat {\Delta} _ {u} ^ {\vee} \right\}, \tag {3.6}
$$

$$
\Omega_ {u} = \{w \in W _ {e x t} \mid w (S _ {u}) = S _ {u} \},
$$

then there is a bijection

$$
W _ {u} / \Omega_ {u} \stackrel {\sim} {\rightarrow} \operatorname {A d m} _ {\kappa}. \tag {3.7}
$$

The number of admissible weights at level  $\kappa = -h^{\vee} + h^{\vee} / u$  is  $u^{r}$ . An admissible module  $L(\Lambda)$  is just the simple highest weight module of  $\hat{\mathfrak{g}}$  with the highest weight  $\Lambda \in \mathrm{Adm}_{\kappa}$ . The conformal weight  $h_{\Lambda}$  of the highest weight state of  $L(\Lambda)$  is

$$
h _ {\Lambda} = \frac {(\Lambda , \Lambda + 2 \hat {\rho})}{2 (\kappa + h ^ {\vee})}. \tag {3.8}
$$

Since  $W_{ext}$  is a semi-direct product of the coweight lattice  $P^{\vee}$  and the Weyl group of  $\mathfrak{g}$ , we can also write each  $w \in W_{ext}$  uniquely as a composition of a translation in  $\beta \in P^{\vee}$  and a Weyl transformation  $y \in W$

$$
w = t _ {\beta} y, \tag {3.9}
$$

with

$$
t _ {\beta} (\lambda) = \lambda + \lambda (K) \beta - \left((\lambda , \beta) + \frac {1}{2} \lambda (K) (\beta , \beta)\right) \delta . \tag {3.10}
$$

Here  $K$  is the central element in  $\hat{\mathfrak{g}}$ . We will also denote  $w = t_{\beta}y$  by  $(\beta, y)$ . Each  $\Lambda \in \mathrm{Adm}_{\kappa}$  can also be written as  $(t_{\beta}w)(\kappa \Lambda_0)$  for some  $(\beta, w)$ .

Given  $\Lambda \in \mathrm{Adm}_{\kappa}$ , let  $\mathrm{ch}_{\Lambda}(z;\tau,t)$  be the character of the admissible module  $L(\Lambda)$ . The space spanned by characters of admissible modules carries modular transformations generated by

$$
T: (z, \tau , t) \mapsto (z, \tau + 1, t),
$$

$$
S: (z, \tau , t) \mapsto \left(\frac {z}{\tau}, - \frac {1}{\tau}, t - \frac {(z , z)}{2 \tau}\right). \tag {3.11}
$$

Explicitly, we have

$$
\operatorname {c h} _ {\Lambda} (z; \tau + 1, t) = \sum_ {\Lambda^ {\prime} \in \operatorname {A d m} _ {\kappa}} \mathbb {T} _ {\Lambda , \Lambda^ {\prime}} \operatorname {c h} _ {\Lambda^ {\prime}} (z; \tau , t),
$$

$$
\operatorname {c h} _ {\Lambda} \left(\frac {z}{\tau}, - \frac {1}{\tau}, t - \frac {(z , z)}{2 \tau}\right) = \sum_ {\Lambda^ {\prime} \in \operatorname {A d m} _ {\kappa}} \mathbb {S} _ {\Lambda , \Lambda^ {\prime}} \operatorname {c h} _ {\Lambda^ {\prime}} (z; \tau , t). \tag {3.12}
$$

Given  $\Lambda = (t_{\beta}y).(\kappa \Lambda_0)$  and  $\Lambda^{\prime} = (t_{\beta^{\prime}}y^{\prime}).(\kappa \Lambda_{0})$  , entries of matrices  $\mathbb{T}$  and  $\mathbb{S}$  are

$$
\mathbb {T} _ {\Lambda , \Lambda^ {\prime}} = e ^ {2 \pi i \left(h _ {\Lambda} - \frac {c}{2 4}\right)} \delta_ {\Lambda , \Lambda^ {\prime}},
$$

$$
\mathbb {S} _ {\Lambda , \Lambda^ {\prime}} = \left| \frac {P ^ {\vee}}{u h ^ {\vee} Q ^ {\vee}} \right| ^ {- \frac {1}{2}} \epsilon \left(y y ^ {\prime}\right) \prod_ {\alpha \in \Delta_ {+}} 2 \sin \frac {\pi i u (\rho , \alpha)}{h ^ {\vee}} e ^ {- 2 \pi i \left(\left(\rho , \beta + \beta^ {\prime}\right) + \frac {h ^ {\vee} \left(\beta , \beta^ {\prime}\right)}{u}\right)}. \tag {3.13}
$$

Here  $c = c(V_{\kappa}(\mathfrak{g})) = \frac{\kappa\dim\mathfrak{g}}{\kappa + h^{\vee}}$  is the central charge of  $V_{\kappa}(\mathfrak{g})$ ,  $\left|\frac{P^{\vee}}{uh^{\vee}Q^{\vee}}\right|$  in the index of the sublattice  $uh^{\vee}Q^{\vee}$  in  $P^{\vee}$ ,  $\epsilon (yy')$  is the sign of the Weyl group element  $yy'$ .

Example 3.1. Let  $\mathfrak{g} = \mathfrak{sl}_2$  with boundary admissible level  $\kappa = -2 + \frac{2}{u}$ . Let  $\alpha$  be the unique positive coroot. The set  $S_{u}$  is

$$
S _ {u} = \{- \theta + u \delta , \alpha \} = \{- \alpha + u \delta , \alpha \}. \tag {3.14}
$$

The set  $\hat{\Delta}_{+}^{\vee}$  is

$$
\hat {\Delta} _ {+} ^ {\vee} = \left\{\alpha + n \delta \mid n \in \mathbb {Z} _ {\geq 0} \right\} \cup \left\{- \alpha + n \delta \mid n \in \mathbb {Z} _ {> 0} \right\}. \tag {3.15}
$$

The finite Weyl group is generated by  $s_{\alpha}$ , and the co-weight lattice is spanned by  $\frac{\alpha}{2}$ , so  $W_{ext}$  is

$$
W _ {e x t} = \left\{t _ {- m \alpha / 2}, t _ {- n \alpha / 2} s _ {\alpha} \mid m, n \in \mathbb {Z} \right\}. \tag {3.16}
$$

And  $\Omega_u \simeq \mathbb{Z}_2$  is generated by  $t_{u\alpha / 2} s_\alpha$ . Because  $t_{u\alpha / 2} s_\alpha$  sends  $t_{-m\alpha / 2}$  to  $t_{-n\alpha / 2} s_\alpha$  for some  $n$  and vice versa. We only need to consider  $w = t_{-\frac{m}{2}\alpha}$  satisfying  $w(S_u) \subset \hat{\Delta}_+^\vee$ . The action of  $w = t_{-\frac{m}{2}\alpha}$  on elements in  $S_u$  is

$$
t _ {- \frac {m}{2} \alpha} (- \alpha + u \delta) = - \alpha + (- m + u) \delta ,
$$

$$
t _ {- \frac {m}{2} \alpha} (\alpha) = \alpha + m \delta . \tag {3.17}
$$

The condition  $w(S_{u}) \subset \hat{\Delta}_{+}^{\vee}$  constraints the allowed values of  $m$  to be  $0 \leq m < u$ , and the total number admissible weights is indeed  $u$ . Using (3.4), the set  $\mathrm{Adm}_{\kappa}$  is

$$
\operatorname {A d m} _ {\kappa} = \left\{\Lambda_ {m} \equiv \left(\kappa + \frac {2 m}{u}\right) \Lambda_ {0} - \frac {2 m}{u} \Lambda_ {1}, 0 \leq m <   u \right\}. \tag {3.18}
$$

Example 3.2. Let  $\mathfrak{g} = \mathfrak{sl}_3$  with boundary admissible level  $\kappa = -3 + \frac{3}{u}$  such that  $\gcd(u, 3) = 1$ . The representatives of  $W_u / \Omega_u$  are

$$
\left\{t _ {- \left(k _ {1} \omega_ {1} + k _ {2} \omega_ {2}\right)} \mid k _ {1} \geq 0, k _ {2} \geq 0, k _ {1} + k _ {2} \leq u - 1 \right\} \cup \left\{t _ {\left(k _ {1} \omega_ {1} + k _ {2} \omega_ {2}\right)} s _ {\theta} \mid k _ {1} \geq 1, k _ {2} \geq 1, k _ {1} + k _ {2} \leq u \right\}. \tag {3.19}
$$

Here  $\omega_{1}$  and  $\omega_{2}$  are fundamental weights of  $\mathfrak{sl}_3$ , and  $s_\theta$  is the reflection with repsect to the highest root  $\theta = \alpha_1 + \alpha_2$ . The total number of admissible weights are  $u^2$ . For  $u = 4$ , there are a total of 16 admissible weights listed in table 7.

<table><tr><td>[tβy]</td><td>Λ</td><td>[tβy]</td><td>Λ</td><td>[tβy]</td><td>Λ</td></tr><tr><td>1</td><td>-9/4 Λ0</td><td>t-ω2</td><td>-6/4 Λ0 - 3/4 Λ2</td><td>t-2ω2</td><td>-3/4 Λ0 - 6/4 Λ2</td></tr><tr><td>t-3ω2</td><td>-9/4 Λ2</td><td>t-ω1</td><td>-6/4 Λ0 - 3/4 Λ1</td><td>t-ω1-ω2</td><td>-3/4 Λ0 - 3/4 Λ1 - 3/4 Λ2</td></tr><tr><td>t-ω1-2ω2</td><td>-3/4 Λ1 - 6/4 Λ2</td><td>t-2ω1</td><td>-3/4 Λ0 - 6/4 Λ1</td><td>t-2ω1-ω2</td><td>-6/4 Λ1 - 3/4 Λ2</td></tr><tr><td>t-3ω1</td><td>-9/4 Λ1</td><td>tω1+ω2sθ</td><td>1/4 Λ0 - 5/4 Λ1 - 5/4 Λ2</td><td>tω1+2ω2sθ</td><td>-2/4 Λ0 - 5/4 Λ1 - 2/4 Λ2</td></tr><tr><td>tω1+3ω2sθ</td><td>-5/4 Λ0 - 5/4 Λ1 + 1/4 Λ2</td><td>t2ω1+ω2sθ</td><td>-2/4 Λ0 - 2/4 Λ1 - 5/4 Λ2</td><td>t2ω1+2ω2sθ</td><td>-5/4 Λ0 - 2/4 Λ1 - 2/4 Λ2</td></tr><tr><td>t3ω1+ω2sθ</td><td>-5/4 Λ0 + 1/4 Λ1 - 5/4 Λ2</td><td></td><td></td><td></td><td></td></tr></table>

Table 7: The list of admissible weights of  $V_{-3 + 3/4}(\mathfrak{sl}_3)$ . The first column summarizes the representatives of classes in  $W_u / \Omega_u$ . The second column gives the admissible weight corresponding to the elements of the first column.

# 3.2 Representation theory of boundary admissible W-algebras

Let  $f$  be a nilpotent element of  $\mathfrak{g}$ , and include  $f$  in an  $\mathfrak{sl}_2$ -triple  $(e, f, x)$ , so that  $[x, e] = e$ ,  $[x, f] = -f$  and  $[e, f] = x$ . Then  $\mathfrak{g}$  admits an eigenvalue decomposition with the respect to the adjoint action of  $x$

$$
\mathfrak {g} = \oplus_ {j \in \mathbb {Z}} \mathfrak {g} _ {j}. \tag {3.20}
$$

By definition  $f \in \mathfrak{g}_{-1}$ . One can define an affine W-algebra  $W_{\kappa}(\mathfrak{g},f)$  associated with  $\mathfrak{g}$ ,  $f$  at level  $\kappa$  by the quantum Drinfeld-Sokolov (qDS) reduction [75, 76]. The central charge of  $W_{\kappa}(\mathfrak{g},f)$  is [76]

$$
c \left(W _ {\kappa} (\mathfrak {g}, f)\right) = \dim \mathfrak {g} _ {0} - \frac {1}{2} \dim \mathfrak {g} _ {\frac {1}{2}} - \frac {1 2}{\kappa + h ^ {\vee}} | \rho - (k + h ^ {\vee}) x | ^ {2}, \tag {3.21}
$$

where  $\rho$  is the Weyl vector of  $\mathfrak{g}$ . Although the vertex algebra structure of  $W_{\kappa}(\mathfrak{g},f)$  does not depend on the choices of  $(e,f,x)$ , the conformal structure does [1]. To match the central charge of the corresponding 4d theory,  $(e,f,x)$  is chosen to be the  $(X,Y,H/2)$  with  $(X,Y,H)$  being the standard  $\mathfrak{sl}_2$ -triple defined in [77].

Simple modules of  $W_{\kappa}(\mathfrak{g},f)$  can be obtained from admissible modules of  $V_{\kappa}(\mathfrak{g})$  by qDS-reduction. Firstly conjugate  $(e,f,x)$  to a new  $\mathfrak{sl}_2$ -triple  $(e',f',h')$  such that  $f'$  a regular nilpotent element in a standard Lévy subalgebra  $\mathfrak{l}$  of  $\mathfrak{g}$ . Here  $\mathfrak{l}$  is the centralizer of

$$
\mathfrak {h} ^ {f} = \{h \in \mathfrak {h} \mid f (h) = 0 \}. \tag {3.22}
$$

$Z_{\mathfrak{g}}(\mathfrak{h}^f)$ . The root system of  $\mathfrak{l}$  is given by

$$
\Delta_ {\mathfrak {l}} \equiv \left\{\alpha \in \Delta \mid \alpha | _ {\mathfrak {h} ^ {f}} = 0 \right\}. \tag {3.23}
$$

The simple roots of  $\Delta_{\mathfrak{l}}$  is required to be a subset of simple roots of  $\mathfrak{g}$  because  $\mathfrak{l}$  is standard. Kac and Wakimoto [43] (Generalizing [78]) defined a functor

$$
H _ {f} (-): V _ {\kappa} (\mathfrak {g}) - \operatorname {m o d} \rightarrow W _ {\kappa} (\mathfrak {g}, f) - \operatorname {m o d}, \tag {3.24}
$$

and they conjectured that this functor sends admissible module  $L(\Lambda)$  of  $V_{\kappa}(\mathfrak{g})$  to either 0 or simple modules of  $W_{\kappa}(\mathfrak{g},f)$ , and all simple modules of  $W_{\kappa}(\mathfrak{g},f)$  are obtained in this way. They further conjectured that  $H_{f}(L(\Lambda)) \neq 0$  if and only if

$$
t _ {\beta} y \left(S _ {u}\right) \subset \hat {\Delta} _ {+} ^ {\vee} \backslash \Delta_ {1} ^ {\vee}, \quad \Lambda = \left(t _ {\beta} y\right). (\kappa \Lambda_ {0}), \tag {3.25}
$$

and  $H_{f}(L(\Lambda))$  is isomorphic to  $H_{f}(L(\Lambda^{\prime}))$  if and only if

$$
\Lambda^ {\prime} \in W _ {f}. \Lambda , \tag {3.26}
$$

where  $W_{f}$  is the Weyl group generated by roots of  $\Delta_{\mathfrak{l}}$ . These conjectures are partially proved in [79-82]. The conformal weight of  $H_{f}(L(\Lambda))$  is [43, 81]

$$
h _ {H _ {f} (L (\Lambda))} = \frac {u}{2 h ^ {\vee}} \left(| \lambda + \rho | ^ {2} - | \rho | ^ {2}\right) - \frac {h ^ {\vee}}{2 u} | x | ^ {2} + (x, \rho), \tag {3.27}
$$

with  $\lambda$  being the finite part of  $\Lambda$ . Note that the first term of (3.27) is invariant under the action of  $W_{f}$ , and the choice of  $x$  only changes the conformal dimension by a constant shift.

The characters  $\mathrm{ch}_{H_f(L(\Lambda))}$  of  $W_{\kappa}(\mathfrak{g},f)$  also enjoy similar modular properties as characters of  $V_{\kappa}(\mathfrak{g})$  modules. If  $L(\Lambda)$  and  $L(\Lambda^{\prime})$  are two admissible modules which reduce to different W-algebra modules, the elements of modular matrices are

$$
\begin{array}{l} \mathbb {T} _ {H _ {f} (L (\Lambda)), H _ {f} (L (\Lambda^ {\prime}))} = e ^ {2 \pi i \left(h _ {H _ {f} (L (\Lambda))} - \frac {c}{2 4}\right)} \delta_ {H _ {f} (L (\Lambda)), H _ {f} (L (\Lambda^ {\prime}))}, \\ \mathbb {S} _ {H _ {f} (L (\Lambda)), H _ {f} (L \left(\Lambda^ {\prime}\right))} = (- i) ^ {\frac {1}{2} (\dim \mathfrak {g} - \dim \mathfrak {g} ^ {f})} \sum_ {y \in W ^ {f}} \mathbb {S} _ {\Lambda , y. \Lambda^ {\prime}}, \tag {3.28} \\ \end{array}
$$

where  $\mathbb{S}_{\Lambda, y, \Lambda'}$  is the modular  $S$  matrix of the parent affine vertex algebra, and  $\mathfrak{g}^f = \dim \mathfrak{g}_0 + \dim \mathfrak{g}_{1/2}$ .

Example 3.3. Let  $\mathfrak{g} = \mathfrak{sl}_2$ ,  $\kappa = -2 + 2/u$  and  $f \in \mathcal{O}_{[2]}$  an element in the principal nilpotent orbit. Choose  $(e, f, h) = (e_{\alpha}, f_{\alpha}, x)$ , then  $\Delta_{\mathfrak{l}} = \{\alpha\}$ , and  $W_f$  is just the Weyl group of  $\mathfrak{sl}_2$ . The condition when the admissible weight  $\Lambda = (t_{\beta}y) (\kappa \Lambda_0)$  does not reduce to zero becomes

$$
t _ {\beta} y \left(S _ {u}\right) \subset \hat {\Delta} _ {+} \backslash \Delta_ {1} = \{\pm \alpha + m \delta \mid m \in \mathbb {Z} _ {> 0} \}. \tag {3.29}
$$

Using admissible modules of  $V_{2 + \frac{2}{u}}(\mathfrak{sl}_2)$  worked out in example 3.1, one can see that the module  $L(\kappa \Lambda_0)$  reduces to 0, while  $L(\Lambda_m)$  and  $L(\Lambda_{u - m})$  reduces to the same  $W_{-2 + 2 / u}(\mathfrak{sl}_2,[2])$  module, so the total number of simple modules are  $(u - 1) / 2$ . The algebra  $W_{-2 + 2 / u}(\mathfrak{sl}_2,[2])$  is isomorphic to the  $(2,u)$  minimal model (the minimal series representation of the Virasoro algebra with central charge  $c = 1 - \frac{3(u - 2)^2}{u}$ ). The conformal dimension of  $H_{f}(L(\Lambda_{m}))$  is

$$
h _ {H _ {f} \left(L \left(\Lambda_ {m}\right)\right)} = - \frac {1}{2 u} (m - 1) (u - m - 1), \tag {3.30}
$$

which is symmetric under the exchange  $m \leftrightarrow u - m$  and matches with the  $(m,1)$  module of the  $(2,u)$  minimal model.

Example 3.4. Let  $\mathfrak{g} = \mathfrak{sl}_3$ ,  $\kappa = -3 + 3 / u$  and  $f \in \mathcal{O}_{[2,1]}$  an element of the minimal nilpotent orbit. To match the 2d central charge with the 4d central charge, one should choose  $f$  to be  $f_{\theta}$  and  $x = \frac{1}{2} (\omega_1 + \omega_2)$ , with the price that  $f$  is not regular in a standard Lévi. However, we can choose  $(f', x') = (f_{\alpha_1}, \omega_1)$  which are conjugate to  $(f, x)$ , such that  $\Delta_{\mathrm{f}} = \{\pm \alpha_1\}$  defines a standard Lévi. Now  $W_f$  is generated by  $s_1$ . The condition for the admissible module  $L(\Lambda)$  with  $\Lambda = (t_{\beta}y) \cdot (\kappa \Lambda_0)$  not reducing to 0 becomes

$$
t _ {\beta} y \left(S _ {u}\right) \subset \hat {\Delta} _ {+} \backslash \Delta_ {l} = \hat {\Delta} _ {+} \backslash \left\{\alpha_ {1} \right\}. \tag {3.31}
$$

When  $u = 4$ , one can use results in table 7 to work out the simple modules of  $W_{-3 + 3 / 4}(\mathfrak{sl}_2, [2,1])$  explicitly. There are three modules with conformal weight 0, one modules with conformal weight  $-1 / 4$ , and two modules with conformal weight  $-1 / 2$  (Computed using  $x'$ ). Results are summarized in table 8. One can then map the modules obtained above to modules defined by  $x$  using the method in [43].

# 4 Coulomb branch and its  $\mathbb{C}^*$ -fixed points

In the last section, we reviewed the representation theory of W-algebras which gives the information on the Higgs (Schur) sector of the 4d theory. When classifying simple modules, the computation reduces to the counting of extended affine Weyl group elements satisfying certain conditions. In this section, we go back to the Hitchin moduli space which describes the Coulomb branch of the 4d theory on a circle. Our Hitchin moduli space has a  $\mathbb{C}^*$  action which is the  $U(1)_r$  symmetry in the superconformal group. It was found previously in several class of theories that  $\mathbb{C}^*$ -fixed points are in one to one correspondence to the simple modules of the corresponding W-algebra [9, 10]. In those work, fixed points do not

<table><tr><td>[tβy], Λ</td><td>h</td><td>[tβy], Λ</td><td>h</td></tr><tr><td>[t-ω1], -6/4 Λ0 - 3/4 Λ1
[tω1+3ω2sθ], -5/4 Λ0 - 5/4 Λ1 + 1/4 Λ2</td><td>0</td><td>[t-3ω1], -9/4 Λ1
[t3ω1+ω2sθ], -5/4 Λ0 + 1/4 Λ1 - 5/4 Λ2</td><td>0</td></tr><tr><td>[t-2ω1], -3/4 Λ0 - 6/4 Λ1
[t2ω1+2ω2sθ], -5/4 Λ0 - 2/4 Λ1 - 2/4 Λ2</td><td>-1/4</td><td>[t-ω1-ω2], -3/4 Λ0 - 3/4 Λ1 - 3/4 Λ2
[tω1+2ω2sθ], -2/4 Λ0 - 5/4 Λ1 - 2/4 Λ2</td><td>-1/2</td></tr><tr><td>[t-2ω1-ω2], -6/4 Λ1 - 3/4 Λ2
[t2ω1+ω2sθ], -2/4 Λ0 - 2/4 Λ1 - 5/4 Λ2</td><td>-1/2</td><td>[t-ω1-2ω2], -3/4 Λ1 - 6/4 Λ2
[tω1+ω2sθ], 1/4 Λ0 - 5/4 Λ1 - 5/4 Λ2</td><td>-1/2</td></tr></table>

Table 8: The list of simple modules of  $W_{-3 + 3/4}(\mathfrak{sl}_2, [2,1])$ . The first column is the weight of the admissible module  $L(\Lambda)$  which does not reduce to 0, and the second column is the conformal weight of  $H_f(L(\Lambda))$ . Two weights which reduces to the same W-algebra module are related by the dot action of  $s_1$ . The  $L(\Lambda)$ 's which reduce to 0 are not listed. The conformal dimensions are computed using  $x'$ .

have an obvious representation theory meaning, hence it is difficult to generalize them to more complicated cases. We will show that affine Springer fibers provide an alternative description of this fixed varieties which makes the classification and matching (with the modules) more straightforward.

# 4.1 More on Higgs bundles and Higgs fields

As mentioned in section 2, the Coulomb branch is given by the Hitchin system defined on  $\mathbb{P}^1$  with one regular and one irregular singularity. We now review some details on the Higgs bundle and the Higgs field in this setting.  $\mathcal{M}_{Hit}$  is the space of solutions to Hitchin equation defined on a Riemann surface  $\Sigma$  [83]. It has a hyper-Kähler structure with three complex structures  $I,J,K$ . In complex structure  $I$ , each point of  $\mathcal{M}_{Hit}$  describes a Higgs bundle  $(E,\Phi)$ , where  $E$  is a holomorphic  $G^{\vee}$ -vector bundle on  $\Sigma$ , and  $\Phi$  is a Higgs field which is a holomorphic section of  $\operatorname{End}(E) \otimes K_{\Sigma}$ . Here  $G^{\vee}$  be a connected and simply connected Lie group whose Lie algebra is  $\mathfrak{g}^{\vee}$ , and we have  $\mathfrak{g} = \mathfrak{g}^{\vee} = \mathfrak{j}$  for the untwisted case labelled by ADE Lie algebra  $\mathfrak{j}$ , while  $\mathfrak{g}$  and  $\mathfrak{g}^{\vee}$  defined in table 3 in the twisted case labelled by  $(\mathfrak{j},o)$ . At each singularity,  $E$  is equipped with a level structure (which determines the correct gauge transformation at the singularity) and  $\Phi$  satisfies certain boundary condition.

First consider the irregular singularity at  $z = \infty$ . Choose a  $\mathbb{Z} / b\mathbb{Z}$  grading on  $\mathfrak{j}$  [60]

$$
j = \oplus_ {i \in \mathbb {Z} / b \mathbb {Z}} j _ {i / b}. \tag {4.1}
$$

At  $\infty$ ,  $E$  is equipped with a level structure determined by the grading (4.1) [64]. The Higgs field behaves as

$$
\Phi (z) \sim \left(T _ {k} z ^ {\frac {k}{b}} + \dots\right) d z, \tag {4.2}
$$

when  $z \to \infty$ . The leading coefficient  $T_{k}$  is regular semi-simple in  $\mathbf{j}_{k / b}$  and invariant under the action of  $o$ . Details on the choices of subsequent coefficients can be found in [17, 68]. For the later purpose, we redefine the Higgs field as

$$
\Phi (z) = \frac {\Phi^ {\prime} (z)}{z} \tag {4.3}
$$

and the asymptotical behavior for  $\Phi'(z)$  at  $z = \infty$  is then

$$
\Phi^ {\prime} \sim \left(T _ {k} z ^ {\nu} + \dots\right) d z, \tag {4.4}
$$

where  $\nu = \frac{k}{b} + 1$  and  $\nu > 0$  because  $k > -b$ . So the irregular singularity is specified by a rational number  $\nu$ .

The regular singularity at  $z = 0$  is labeled by a nilpotent element  $f$  of  $\mathfrak{g}$ . Recall that we assume that  $f$  is a regular nilpotent element in a Lévi l with l defined in section 3.2. Then on the Hitchin side, we should consider the Langlands dual  $\mathfrak{l}^{\vee}$ . Let  $\mathfrak{p}^{\vee} = \mathfrak{l}^{\vee} + \mathfrak{n}^{\vee} \subset \mathfrak{g}^{\vee}$  be the parabolic subalgebra with Lévi factor  $\mathfrak{l}^{\vee}$ , and  $\mathfrak{n}^{\vee}$  be its nilradical part. Let  $P^{\vee} \subset G^{\vee}$  be the parabolic subgroup whose Lie algebra is  $\mathfrak{p}^{\vee}$ . Then at  $z = 0$ , the Higgs bundle  $E$  is equipped with a  $P^{\vee}$ -level structure, which means the allowed gauge transformation around  $z = 0$  is of the form [84]

$$
g = g _ {0} + g _ {1} z + g _ {2} z ^ {2} + \dots , \quad g _ {0} \in P ^ {\vee}, g _ {i > 0} \in G ^ {\vee}. \tag {4.5}
$$

The boundary condition of  $\Phi^{\prime}$  at  $z = 0$  is

$$
\Phi^ {\prime} \sim ((m + \beta) + \dots) d z, \tag {4.6}
$$

where the mass deformation  $m$  is in the center of  $\mathfrak{l}^{\vee}$  and  $\beta \in \mathfrak{n}^{\vee}$ . In the massless limit  $m\to 0$ , the boundary condition becomes

$$
\lim  _ {z \rightarrow 0} \Phi^ {\prime} \in \mathfrak {n} ^ {\vee}. \tag {4.7}
$$

This boundary condition is related to the boundary condition (2.4) because

$$
\mathcal {O} _ {f ^ {\vee}} = d \left(\mathcal {O} _ {f}\right) = \operatorname {I n d} _ {\mathrm {l} ^ {\vee}} ^ {\mathfrak {g} ^ {\vee}} d \left(\mathcal {O} _ {f} ^ {\mathrm {l}}\right) = \operatorname {I n d} _ {\mathrm {l} ^ {\vee}} ^ {\mathfrak {g} ^ {\vee}} \mathcal {O} _ {0} ^ {\mathrm {l} ^ {\vee}}, \tag {4.8}
$$

and  $\mathrm{Ind}_{\mathfrak{l}^{\vee}}^{\mathfrak{g}^{\vee}}\mathcal{O}_0^{\mathfrak{l}^{\vee}} = G^{\vee}\cdot \mathfrak{n}^{\vee}$  [77]. Here Ind means the induction of orbit and  $d(\mathcal{O}_f^\mathfrak{l})$  is the dual orbit of  $\mathcal{O}_f^\mathfrak{l}$  in  $\mathfrak{g}^{\vee}$ . Since  $f$  is in regular in  $\mathfrak{l}$ ,  $d(\mathcal{O}_f^\mathfrak{l}) = \mathcal{O}_0^{\mathfrak{l}^{\vee}}$ . To further specify the Coulomb branch operators on Hitchin base  $B$ , one also needs an element  $c$  in the so-called component group  $A(f^{\vee})$  of  $f^{\vee}$  introduced in [41], then Coulomb branch operators are gauge invariant functions of  $\Phi$  which are also invariant under the action of  $c$  [62]. In summary, the Hitchin moduli space is specified by a Lie algebra  $\mathfrak{j}$  (resp.  $(\mathfrak{j},o)$ ), a rational number  $\nu = k / b + 1$  and a pair  $(f^{\vee},c)$  together with suitable level structure on the Higgs bundle, and the corresponding moduli space might be labeled as

$$
\mathcal {M} _ {H i t} (\mathrm {j}, \nu , (f ^ {\vee}, c)) \left(\text {r e s p .} \mathcal {M} _ {H i t} ((\mathrm {j}, o), \nu , (f ^ {\vee}, c))\right). \tag {4.9}
$$

# 4.2 Zero fibre of the Hitchin moduli space and the affine Springer fibre

The Hitchin system considered in this paper has a positive  $\mathbb{C}^*$  action on  $(x,z)$  coordinates

$$
x \rightarrow \lambda^ {\alpha} x, \quad z \rightarrow \lambda^ {\beta} z, \tag {4.10}
$$

which makes the spectral curve  $\operatorname{det}(x - \Phi(z)) = 0$  invariant. This implies that the  $\mathbb{C}^*$  weight of  $x$  should be the same as  $\Phi(z)$ , inducing an action on the AKM algebra where

$\Phi(z)$  lives in. The invariance of the spectral curve fixes the weight of the leading order coefficient  $T$  of Higgs field is 0, and the weights of  $x$  and  $z$  are related by  $\alpha = \beta \frac{k}{b}$ . Because of this weight assignment, the  $\mathbb{C}^*$ -fixed points of  $\mathcal{M}_{Hit}$  belong to the fibre over the  $\mathbb{C}^*$ -fixed point on the Hitchin base, which corresponds to the curve at the SCFT point listed in table 2 and 4. We call this fibre the zero fibre<sup>13</sup>.

Below, we consider a local situation in which we may assume that the holomorphic bundle  $E$  of the Higgs pair  $(E,\Phi)$  is trivial. Now the Hitchin moduli space can be described using the language of affine Lie algebra.

Untwisted cases: First consider the untwisted theories  $\mathcal{T}_{\mathrm{j},b,k,f}$  with  $\mathfrak{j} = ADE$ . Let  $\hat{\mathfrak{j}} = \mathfrak{j}[z,z^{-1}] \oplus \mathbb{C}K \oplus \mathbb{C}d$  be the AKM algebra associated with  $\mathfrak{j}$ . Here  $\mathfrak{j}[z,z^{-1}]$  is the polynomials in  $z$  and  $z^{-1}$  with coefficient valued in  $\mathfrak{j}$ . The modified Higgs field  $\Phi'(z)$  is now an element in  $\hat{\mathfrak{j}}$  satisfying the boundary condition (4.4) and (4.7) in last subsection.

Twisted cases: Now consider the twisted case  $\mathcal{T}_{j,o,b_t,k_t,f}$ . The space  $j$  has a decomposition

$$
j = j _ {0} \oplus j _ {\omega} \oplus \dots \oplus j _ {\omega^ {n - 1}}, \tag {4.11}
$$

under the action of  $o$ . Here the subscripts denote the eigenvalues under the action of  $o$  and  $n$  the order of  $o$ . By definition  $\mathfrak{j}_0 = \mathfrak{g}^\vee$  listed in table 3. The twisted affine Lie algebra  ${}^{n}\hat{\mathbf{j}}$  corresponding to  $(\mathfrak{j}, o)$  is then

$$
{ } ^ { n } \hat { \mathbf { j } } = \oplus _ { k \in \mathbb { Z } } \left( \mathrm { j } _ { 0 } z ^ { k } \oplus \mathrm { j } _ { \omega } z ^ { k + \frac { 1 } { n } } \oplus \cdots \oplus \mathrm { j } _ { \omega ^ { n - 1 } } z ^ { k + \frac { n - 1 } { n } } \right) \oplus \mathbb { C } K \oplus \mathbb { C } d .  ( 4 . 1 2 )
$$

Below we will set formally  $^1\hat{\mathbf{j}}$  as  $\hat{\mathbf{j}}$  so we can treat untwisted and twisted case uniformly.

By construction the modified Higgs field  $\Phi'(z)$  is an element in  $n\hat{\mathbf{j}}$  satisfying the following boundary conditions

$$
\Phi^ {\prime} (z) \sim \left(T z ^ {\nu} + \dots\right) d z, \quad z \rightarrow \infty , \tag {4.13}
$$

$$
\Phi^ {\prime} (z) \sim (\beta^ {\vee} + \dots) d z, \quad z \rightarrow 0.
$$

Here  $\nu = k_{t} / b_{t} + 1$ , and  $\beta^{\vee}$  is an element in  $\mathfrak{n}^{\vee} \subset \mathfrak{g}^{\vee}$ .

For the purpose of counting the fixed varieties, we only need to consider the zero fibre of the Hitchin moduli space and it is easier to describe it using the affine Springer fibre which we will review in the following. Choose an elliptic element  $\gamma \in {}^n\hat{\mathbf{j}}$  whose spectral curve is the  $\mathbb{C}^*$ -fixed point in  $B$ . Let  $\mathbf{G}^{\vee}$  be a connected and simply-connected affine Lie group whose Lie algebra is  ${}^n\hat{\mathbf{j}}^{14}$ . Let  $\tilde{\mathfrak{n}}^{\vee}$  be the Lie algebra with the root system  $\Delta_{\tilde{\mathfrak{n}}^{\vee}} \equiv \hat{\Delta}_{+}^{\vee} \backslash \Delta_{\mathfrak{l}}^{\vee}$ . Here  $\hat{\Delta}^{\vee}$  is the set of positive real roots of affine Lie algebra  ${}^n\hat{\mathbf{j}}$ . Let  $\mathbf{P}^{\vee} \subset \mathbf{G}^{\vee}$  be the parahori subgroup whose root system is  $\hat{\Delta}_{+}^{\vee} \cup \Delta_{\mathfrak{l}}^{\vee}$ . Then the affine Svalenstein variety is [45, 46]

$$
S p _ {\gamma , \mathbf {P} ^ {\vee}} = \left\{g \in \mathbf {P} ^ {\vee} \backslash \mathbf {G} ^ {\vee} \mid g \gamma g ^ {- 1} \subset \tilde {\mathfrak {n}} ^ {\vee} \right\}. \tag {4.14}
$$

In [64] the authors proved that the zero fibre of the Hitchin moduli space  $\mathcal{M}_{Hit}((\mathrm{j},o),\nu ,(f^{\vee},c))$  is homeomorphic to  $Sp_{\gamma ,\mathbf{P}^{\vee}}$ , with the relation

$$
\Phi (z) ^ {\prime} = g \gamma g ^ {- 1} d z. \tag {4.15}
$$

The choice of  $\gamma$  ensures that  $\Phi'$  satisfies the boundary condition from the irregular singularity at  $\infty$  while  $g\gamma g^{-1} \subset \tilde{\mathfrak{n}}^\vee$  ensures that  $\Phi'$  satisfies the boundary condition from the regular singularity at 0.

Example 4.1. Consider  $\nu = \frac{u}{h^{\vee}}$ , the elliptic element of  $n\hat{\mathbf{j}}$  is

$$
\gamma = e _ {- \theta} z ^ {u} + \sum_ {i = 1} ^ {r} e _ {\alpha_ {i}}. \tag {4.16}
$$

Here  $\theta$  is the longest root,  $\alpha_{i}$ 's are simple roots, and  $e_{\alpha}$  is an element in the Chevalley basis corresponding to the root  $\alpha$ . In particular when  $\mathbf{j} = A_{N - 1}$  and  $\nu = \frac{u}{N}$ , the spectral curve of  $\gamma$  is

$$
x ^ {N} + z ^ {u - N} = 0, \tag {4.17}
$$

so  $\gamma$  lies in the central fibre. It is useful to redefine the coordinate  $x' = xz$ , and so the spectral curve takes the form

$$
x ^ {\prime N} + z ^ {u} = 0, \tag {4.18}
$$

and the SW differential in the new variable is  $x' \frac{dz}{z}$ .

Example 4.2. Take the Lie algebra  $\mathfrak{g} = A_{N - 1}$ , and let  $e_1,\ldots ,e_N$  be the standard basis of  $\mathbb{R}^N$ . We give the explicit description of  $\mathfrak{n}^\vee$ . The set of positive roots are  $\Delta_{+} = \{e_{i} - e_{j}|1 < i < j\leq N\}$ , and the set of simple roots are  $\Pi = \{e_1 - e_2,\dots e_{N - 1} - e_N\}$ . Given a partition  $d = [d_{1},\dots ,d_{s}]$  of  $N$ , one pick the following set of simple roots corresponding to  $d$

$$
\Pi_ {d} = \Pi_ {1} \cup \Pi_ {2} \cup \dots \cup \Pi_ {s}, \tag {4.19}
$$

where

$$
\Pi_ {i} = \left\{e _ {\sum_ {l = 1} ^ {i - 1} d _ {l}} - e _ {\sum_ {l = 1} ^ {i - 1} d _ {l} + 1}, \dots , e _ {\sum_ {l = 1} ^ {i} d _ {l} - 1} - e _ {\sum_ {l = 1} ^ {i} d _ {l}} \right\}. \tag {4.20}
$$

Now let  $\Delta_d \subset \Delta$  be the sub-root system generated by  $\Pi_d$ . The standard Lévi subalgebra corresponding to  $d$  is

$$
\mathfrak {l} _ {d} ^ {\vee} = \mathfrak {h} ^ {\vee} \oplus_ {\alpha \in \Delta_ {d}} \mathfrak {g} _ {\alpha} ^ {\vee}, \tag {4.21}
$$

while the standard parabolic algebra  $\mathfrak{p}_d^\vee$  containing  $\mathfrak{l}_d^\vee$  is

$$
\mathfrak {p} _ {d} ^ {\vee} = \mathfrak {l} _ {d} ^ {\vee} \oplus_ {\alpha \in \Delta_ {+} \backslash \Delta_ {d}} \mathfrak {g} _ {\alpha} ^ {\vee}. \tag {4.22}
$$

$\mathfrak{p}_d^\vee$  has a Lévi decomposition  $\mathfrak{p}_d^\vee = \mathfrak{l}_d^\vee \oplus \mathfrak{n}_d^\vee$  with

$$
\mathfrak {n} _ {d} ^ {\vee} = \oplus_ {\alpha \in \Delta_ {+} \backslash \Delta_ {d}} \mathfrak {g} _ {\alpha} ^ {\vee}. \tag {4.23}
$$

The set of roots of  $\tilde{\mathfrak{n}}^{\vee}$  is then

$$
\Delta_ {\tilde {\mathfrak {n}} ^ {\vee}} = \{\alpha + n \delta | \alpha \in \Delta , n \in \mathbb {Z} _ {> 0} \} \cup \left(\Delta_ {+} ^ {\vee} \backslash \Delta_ {\mathrm {I} ^ {\vee}}\right). \tag {4.24}
$$

In particular, if  $d = [N]$  (so-called trivial puncture in physics literature),  $\mathfrak{n}^{\vee}$  is zero, then  $\tilde{\mathfrak{n}}^{\vee}$  is the Lie algebra generated by the root system  $\hat{\Delta}_{+}^{\vee} \backslash \Delta_{+}^{\vee}$ . If  $d = [1^{N}]$  (so-called full puncture in physics literature),  $\tilde{\mathfrak{n}}^{\vee}$  is generated by the root system  $\hat{\Delta}_{+}^{\vee}$ .

The requirement of elliptic element: In this work we focus on cases when there are no mass parameters in irregular singularity, which puts the constraint on choices of the rational number  $\nu$  which is called slope. Recall the constraints on  $(b,k)$  (resp.  $(b_{t},k_{t})$ ) for irregular singularities without mass deformation listed in table 5 (resp. table 6), and  $\nu = \frac{k}{b} +1$  (resp.  $\nu = \frac{k_t}{b_t} +1$ ). The requirement of no mass deformation imposes constraints on the denominator  $m$  of  $\nu = u / m$  which are listed in 9. Interestingly, such choices of  $m$  coincides with the so-called elliptic numbers [45, 46]. Similarly, the allowed elliptic numbers for the twisted case is also given in table 9. An elliptic number is called regular if it is the same as the dual Coxeter number  $h^{\vee}$ . The dimension for the elliptic affine Springer fiber is computed by [46, 69, 70], which is the same as our result in section 2.2.

<table><tr><td>j</td><td>Elliptic number m</td></tr><tr><td>An</td><td>n+1</td></tr><tr><td>Dn</td><td>m even, 2n-2/m odd</td></tr><tr><td></td><td>m even, 2n/m even</td></tr><tr><td>E6</td><td>12,9,6,3</td></tr><tr><td>E7</td><td>18,14,6,2</td></tr><tr><td>E8</td><td>2,3,5,6,10,15,30</td></tr><tr><td></td><td>4,8,12,24</td></tr><tr><td></td><td>20</td></tr></table>

<table><tr><td>j,o</td><td>Elliptic number m</td></tr><tr><td>A2n, Z2</td><td>m = 2r, r odd, 2n+1/r odd</td></tr><tr><td></td><td>m = 2r, r odd, 2n/r even</td></tr><tr><td>A2n-1, Z2</td><td>m = 2r, r odd, 2n-1/r odd</td></tr><tr><td></td><td>m = 2r, r odd, 2n/r even</td></tr><tr><td>Dn, Z2</td><td>m even, 2n/m odd</td></tr><tr><td></td><td>m even, 2n-2/m even</td></tr><tr><td>D4, Z3</td><td>12,6,3</td></tr><tr><td>E6, Z2</td><td>18,12,6,4,2</td></tr></table>

Table 9: List of elliptic number  $m$  .

# 4.3 Counting fixed varieties

In previous sections we argued that the affine Springer fibre can be used to replace the Hitchin moduli space when considering the  $\mathbb{C}^*$ -fixed points. For the elliptic case, there is a nice combinatorial counting algorithm [45, 46] which we will explain here. Given an elliptic slope  $\nu = u / m$  for an (twisted) affine Lie algebra  $\hat{\mathbf{j}}^{(n}\hat{\mathbf{j}}^{)}$ , define the set  $L_{\nu}$  as

$$
L _ {\nu} = \left\{\alpha + l \delta \in \hat {\Delta} ^ {\vee} \mid \nu \alpha (\rho) + l = 0 \right\}, \tag {4.25}
$$

and the set  $S_{\nu}$  as

$$
S _ {\nu} = \left\{\alpha + l \delta \in \hat {\Delta} ^ {\vee} \mid \nu \alpha (\rho)) + l = \nu \right\}. \tag {4.26}
$$

Here  $\hat{\Delta}^{\vee}$  is the set of real roots of  $\hat{\mathbf{j}}^{(n\hat{\mathbf{j}})}$ ,  $\rho$  the co-Weyl vector of the finite part of  $\hat{\mathbf{j}}^{(n\hat{\mathbf{j}})}$ . Denoted by  $W_{\nu}$  the Weyl group generated by roots in  $S_{\nu}$ .

With  $L_{\nu}$  and  $S_{\nu}$ , the set of fixed varieties  $Sp_{\gamma,\mathbf{P}^{\vee}}^{T}$  of the affine Springer fiber  $Sp_{\gamma,\mathbf{P}^{\vee}}$  is labelled by the affine Weyl group element up to the action of  $W_{\mathbf{P}^{\vee}}$  and  $W_{\nu}$  [15],

$$
S p _ {\gamma , \mathbf {P} ^ {\vee}} ^ {T} = \sqcup H _ {\tilde {w}}, \quad \left\{\tilde {w} \in W _ {\mathbf {P} ^ {\vee}} \backslash W _ {a f f} / W _ {\nu} \mid \operatorname {A d} (\tilde {w}) \gamma \in \tilde {\mathfrak {n}} ^ {\vee} \right\}. \tag {4.27}
$$

Here  $W_{\mathbf{P}^{\vee}}$  is the Weyl group for the parahori subgroup  $\mathbf{P}^{\vee}$ . The dimension of each fixed variety is [46]

$$
\boxed {\dim H _ {\tilde {w}} = | \tilde {w} L _ {\nu} \backslash \Delta_ {\tilde {\mathfrak {n}} ^ {\vee}} | - | \tilde {w} S _ {\nu} \backslash \Delta_ {\tilde {\mathfrak {n}} ^ {\vee}} |.} \tag {4.28}
$$

In the following, we will apply above formula to several interesting cases.

Regular elliptic case: Let  $\hat{\mathbf{j}}$  be a simply laced AKM algebra, then there is no difference between roots and coroots and  $\hat{\Delta}_{+} = \hat{\Delta}_{+}^{\vee}$ ,  $\nu = \frac{u}{h^{\vee}}$ ,  $f^{\vee}$  is the principal nilpotent orbit, so  $W_{\mathbf{P}^{\vee}}$  is trivial. The group  $\mathbf{P}^{\vee}$  in this case is an Iwahori subgroup and is denoted as  $\mathbf{I}^{\vee}$ , and  $\tilde{\mathfrak{n}}^{\vee}$  is the same as the set of positive affine roots  $\hat{\Delta}_{+}^{\vee}$ .  $L_{\nu}$  is empty because the maximal height of a finite root  $\alpha$  is  $h^{\vee} - 1$ , so the equation

$$
\frac {u}{h ^ {\vee}} \alpha (\rho) + l = 0, \tag {4.29}
$$

has no solution. Elements of  $S_{\nu}$  satisfying the following

$$
\frac {u}{h ^ {\vee}} \bar {\alpha} (\rho) + l = \frac {u}{h ^ {\vee}}, \tag {4.30}
$$

and the set of solutions is

$$
S _ {\nu} = \{- \theta + u \delta , \alpha_ {1}, \dots , \alpha_ {r} \}, \tag {4.31}
$$

which is the same as  $S_{u}$  defined previously in equation (3.3). The elliptic element  $\gamma$  can be chosen as

$$
\gamma = e _ {- \theta} z ^ {u} + \sum_ {i} e _ {\alpha_ {i}}. \tag {4.32}
$$

The fixed varieties are labelled by the following elements in the affine Weyl group

$$
\{\tilde {w} \in W _ {a f f} \mid \tilde {w} S _ {\nu} \subset \hat {\Delta} _ {+} \}. \tag {4.33}
$$

Because  $L_{\nu}$  is empty, we have

$$
| \tilde {w} L _ {\nu} \backslash \hat {\Delta} _ {+} | = 0. \tag {4.34}
$$

Also because  $\tilde{w} S_{\nu}\subset \hat{\Delta}_{+}$

$$
\tilde {w} S _ {\nu} \backslash \hat {\Delta} _ {+} = \emptyset . \tag {4.35}
$$

The dimension formula (4.28) then tells us that each fixed variety  $H_{\tilde{w}}$  has dimension 0. The number of fixed points  $|Sp_{\frac{u}{h^{\vee}},\mathbf{I}^{\vee}}^{T}|$  is then  $u^{r}$  [45].

Sub-regular case: Again consider  $\hat{\mathbf{j}}$  simply laced, but now take  $\nu = \frac{u}{m}$  with  $m$  being the next to maximum value in table 9, and  $f^{\vee}$  is still the principal nilpotent one. Notice that now there is only one finite root  $\mu$  of  $\hat{\mathbf{j}}$  with height  $m$ , so  $L_{\nu}$  consists two roots

$$
L _ {\nu} = \{\pm (\mu - u \delta) \}. \tag {4.36}
$$

The set  $S_{\nu}$  is

$$
S _ {\nu} = \left\{\alpha + l \delta \in \hat {\Delta} \mid \frac {u}{m} \alpha \left(\rho^ {\vee}\right)\right) + l = \frac {u}{m} \}. \tag {4.37}
$$

Now  $S_{\nu}$  contains both positive and negative affine roots. One choice of the elliptic element can be

$$
\gamma = \sum_ {\alpha + l \delta \in S _ {\nu}, l \geq 0} e _ {\alpha} z ^ {l}. \tag {4.38}
$$

Since  $L_{\nu} = \{\pm \tilde{\alpha}\}$ , and given  $\tilde{w} \in W_{aff}$ , the cardinality of  $\tilde{w} L_{\nu} \backslash \hat{\Delta}_{+}$  is always 1, the first term in the dimension formula (4.28) is always 1. The fixed varieties are separated into two groups by their dimensions.

1.  $\dim H_{\tilde{w}} = 1$  : so  $|\tilde{w} S_{\nu}\backslash \hat{\Delta}_{+}| = 0$  , i.e.  $\tilde{w} (S_{\nu})\subset \hat{\Delta}_{+}$  
2.  $\dim H_{\tilde{w}} = 0$ : so  $|\tilde{w} S_{\nu} \backslash \hat{\Delta}_{+}| = 1$ , i.e.  $\tilde{w} S_{\nu} \cap \hat{\Delta}_{-}$  has exactly 1 element.

In next section we will provide explicit examples.

Twisted case: consider a twisted affine Lie algebra  $^2\hat{A}_3$  with the slope  $\nu = \frac{1}{2}$ . The set of real roots is

$$
\hat {\Delta} ^ {\vee} = \left\{\alpha^ {\vee} + \frac {n}{2} \delta \mid \alpha^ {\vee} \in \Phi_ {s} ^ {0}, n \in \mathbb {Z} \right\} \cup \left\{\alpha^ {\vee} + n \delta \mid \alpha^ {\vee} \in \Phi_ {l} ^ {0}, n \in \mathbb {Z} \right\}, \tag {4.39}
$$

where  $\Phi_s^0$  and  $\Phi_l^0$  are respectively the set of short and long roots of  $C_2$  Lie algebra which is the finite part of  ${}^2\hat{A}_3$ . In orthogonal basis spanned by  $\{\beta_i\}$

$$
\Phi_ {l} ^ {0} = \left\{\pm 2 \beta_ {i} \right\}, \quad \Phi_ {s} ^ {0} = \left\{\pm \beta_ {i} \pm \beta_ {j}, i, j = 1, 2, i \neq j \right\}. \tag {4.40}
$$

The set of simple roots is

$$
\left\{\alpha_ {1} ^ {\vee} = \beta_ {1} - \beta_ {2}, \alpha_ {2} ^ {\vee} = 2 \beta_ {2} \right\}. \tag {4.41}
$$

The set  $L_{\nu}$  and  $S_{\nu}$  when  $\nu = 1 / 2$  are

$$
L _ {\nu} = \left\{\pm \left(\alpha_ {1} + \alpha_ {2} - \delta\right) \right\} \cup \left\{\pm \left(\alpha_ {1} - \frac {1}{2} \delta\right) \right\} \tag {4.42}
$$

and

$$
S _ {\nu} = \left\{\alpha_ {1}, \alpha_ {2}, - \alpha_ {1} + \delta , - \alpha_ {2} + \delta , 2 \alpha_ {1} + \alpha_ {2} - \delta , - 2 \alpha_ {1} - \alpha_ {2} + 2 \delta , \alpha_ {1} + \alpha_ {2} - \frac {\delta}{2}, - \alpha_ {1} - \alpha_ {2} + \frac {3 \delta}{2} \right\}. \tag {4.43}
$$

The fixed variety can be found by using the definition (4.27) and the dimension formula (4.28). On the other hand, there is also a bijection between fixed varieties and alcoves in the Cartan  $\mathfrak{h}$ , with algorithm listed below [45, 46]:

1. For each element  $\alpha + l\delta$  in  $S_{\nu}$ , one draws a wall which is a hyperplane  $H_{\alpha + l\delta} \subset \mathfrak{h}$  defined by  $\{x | (x, \alpha) + l = 0\}$  (red lines in figure 3). For each element  $\alpha + l\delta$  in  $L_{\nu}$ , one draws a mirror which is the hyperplane  $H_{\alpha + l\delta}$  (blue lines in figure 3). The fundamental alcove  $\Delta_0$  is the region defined by  $(x, \alpha) > 0$ ,  $i = 1, \dots, r$  and  $(x, -\alpha_\theta) + 1 > 0$  (the shaded area of 3).  
2. For an element  $\tilde{w} \in W_{aff}$ ,  $H_{\tilde{w}}$  is a fixed variety if  $\tilde{w}^{-1}\Delta_0$  lies in a bounded region closed by walls. If any points  $x \in \tilde{w}^{-1}\Delta_0$  satisfy  $(x, \alpha) > 0$  (or  $(x, \alpha) < 0$ ), we call  $\tilde{w}^{-1}\Delta_0$  is on the positive (or negative) side of the wall  $H_{\alpha}$ .  $|\tilde{w}S_{\nu} \backslash \hat{\Delta}_{+}|$  is the number of walls of which  $\tilde{w}^{-1}\Delta_0$  lies on the negative side. Finally, if  $\tilde{w}_1^{-1}\Delta_0$  is the same as  $\tilde{w}_2^{-1}\Delta_0$  reflected by some mirrors, they correspond to the same fixed variety.

Alcoves corresponding to fixed varieties in our example are shown in figure 3 with dimensions labelled. The alcoves marked by red dimension numbers are not reflected by the mirrors so they correspond to different fixed varieties. There are total of 4 fixed varieties.

![](images/90e81cdaa3b5b23be6fd75216ae9d819636d1d1c9a89dfb41d377f1abdaa758a.jpg)  
Figure 3: Alcoves correspond to fixed varieties of  $^2\hat{A}_3$  with  $\nu = 1/2$  are marked with dimensions, and the fundamental alcove is the shaded region. Alcoves with dimension marked in red below to different  $W_{\nu}$  orbit. There are one 2d fixed variety, one 1d fixed variety and two fixed points. Redlines are walls from roots in  $S_{\nu}$ , blue lines are mirrors from roots in  $L_{\nu}$ . Here  $\alpha_{\theta} = 2\alpha_{1} + \alpha_{2}$ ,  $\alpha_{s} = \alpha_{1} + \alpha_{2}$  is the highest short root, and  $\alpha_{0} = -\alpha_{s} + \delta / 2$ .

# 5 Mirror symmetry for circle compactified 4d  $\mathcal{N} = 2$  theory

With necessary knowledge reviewed in previous sections, we can finally make precise statements on the mirror symmetry and provide various checks. For a circle compactified 4d  $\mathcal{N} = 2$  SCFT, we now have two objects: the first one is the W-algebra  $W_{-h^{\vee} + \frac{1}{n\nu}}(\mathfrak{g},f)^{17}$  which describes Schur sector. The second one is the Hitchin moduli space  $\mathcal{M}_{hit}((\mathfrak{j},o),\nu ,(f^{\vee},c))$  for the Coulomb branch. Notice that the defining data involves Langlands dual on algebras:

1. The W-algebra  $W_{-h^{\vee} + \frac{1}{n\nu}}(\mathfrak{g},f)$  on the Schur sector is related to the affine Lie algebra  $\hat{\mathfrak{g}}$ , while the Hitchin moduli space involves the twisted affine Lie algebra based  ${}^{n}\hat{\mathbf{j}}$  which is the Langlands dual of  $\hat{\mathfrak{g}}$ .  
2. The  $(f^{\vee},c)\in \mathfrak{g}^{\vee}$  used in the Hitchin moduli space is the dual of the nilpotent element  $f\in \mathfrak{g}$  in  $W_{-h^{\vee} + \frac{1}{n\nu}}(\mathfrak{g},f)$ , and  $\mathfrak{g}^{\vee}$  is the Langlands dual of  $\mathfrak{g}$ .

# 5.1 Simple modules of W-algebra and fixed points

Our first statement is that there is a natural bijection between simple modules of  $W_{-h^{\vee} + \frac{1}{n\nu}}(\mathfrak{g},f)$  and irreducible components of  $\mathbb{C}^*$ -fixed varieties of  $\mathcal{M}_{hit}((\mathfrak{j},o),\nu ,(f^{\vee},c))$ . The case when  $\mathfrak{g} = A_{N - 1}$  and  $f$  principal was first noticed in [9]. Cases when  $\mathfrak{g} = A_1$ ,  $f$  trivial or cases when the W-algebra being  $W_{N}$  and  $B_{N}$  algebras are discussed in [10]. Our results vastly generalize previous understanding of the bijection between modules and fixed varieties.

Recall that irreducible components of fixed varieties of  $\mathcal{M}_{Hit}((\mathfrak{j},o),\nu ,(f^{\vee},c))$  are the same as fixed varieties of corresponding affine Springer fibre  $Sp_{\gamma ,\mathbf{P}^{\vee}}$  which are parameterized by the affine Weyl elements  $\tilde{w}$  satisfying condition in (4.27) up to a double coset. The bijection between fixed varieties of Hitchin moduli space and weights of simple modules of  $W_{-h^{\vee} + \frac{1}{n\nu}}(\mathfrak{g},f)$  is

$$
\text {F i x e d v a r i e t i e s o f} \mathcal {M} _ {h i t} ((j, o), \nu , (f ^ {\vee}, C)) \stackrel {\cong} {\rightarrow} \operatorname {I r r e p} \left(W _ {- h ^ {\vee} + \frac {1}{n \nu}} (\mathfrak {g}, f)\right), \tag {5.1}
$$

$$
H _ {\tilde {w}} \mapsto H _ {f} (L (\Lambda_ {\tilde {w}})), \quad \mathrm {w i t h} \Lambda_ {\tilde {w}} = \tilde {w} \cdot (\kappa \Lambda_ {0}),
$$

Here  $H_{\tilde{w}}$  denotes the irreducible component of the fixed varieties, and  $\Lambda_{\tilde{w}}$  denotes the affine weight.

Remark: In above proposal, we assume that the module of W-algebra is defined by choosing  $f$  regular in a standard Lévi (which naturally matches the definition of fixed varieties on the Hitchin side. To get the data for the W-algebra corresponding to the 4d theory (namely the grading has to be given by the standard  $\mathfrak{sl}_2$  triple), one need to do a further transformation resulting a shift in the conformal dimension.

# 5.1.1 W-algebras at boundary admissible level

Given a Lie algebra  $\mathfrak{g}$ , if the level  $\kappa$  is at the boundary admissible level  $\kappa = -h^{\vee} + \frac{h^{\vee}}{u}$  with  $\gcd(u, h^{\vee}) = 1$ , then the slope  $\nu$  of the corresponding fibre is  $\frac{u}{h^{\vee}}$ , and the denominator  $h^{\vee}$  is a regular elliptic number. In this situation,  $L_{\nu}$  is always an empty set. By the dimension formula (4.28) all fixed varieties have dimension 0 (fixed points). For boundary admissible case, the bijection can be proved rigorously and is given in our accompanying paper [42].

AKM cases: Let  $f$  being the trivial nilpotent orbit. One gets the associated vertex algebra  $L_{-h^{\vee} + \frac{h^{\vee}}{u}}(\mathfrak{g})$  on the VOA side. Following the notation in section 3.1, the set of admissible weights are given by

$$
\{\tilde {w}. (\kappa \Lambda_ {0}) \mid \tilde {w} \in W _ {e x t} / \Omega_ {u}, \tilde {w} (S _ {u}) \subset \hat {\Delta} _ {+} ^ {\vee} \}. \tag {5.2}
$$

On the Hitchin side, both  $W_{\nu}$  and  $W_{\mathbf{P}^{\vee}}$  are trivial, and the set of fixed varieties is labelled by (in this case,  $\tilde{\mathfrak{n}}^{\vee}$  is equal to the set of positive affine roots  $\hat{\Delta}_{+}^{\vee}$ )

$$
\{\tilde {w} \in W _ {a f f} \mid \tilde {w} \left(S _ {\nu}\right) \subset \hat {\Delta} _ {+} ^ {\vee} \}. \tag {5.3}
$$

The dimension of each fixed variety is 0 (fixed points). Notice that here  $S_{u} = S_{\nu}$ . One can show that for each element of the coset  $W_{ext} / \Omega_{u}$ , there is one and only one element in  $W_{aff}$  [18], hence the bijection. Both the number of admissible modules and fixed points are  $u^{r}$ .

Example 5.1.  $L_{-2 + 2 / u}(\mathfrak{sl}_2) \leftrightarrow \mathcal{M}_{Hit}(\mathfrak{sl}_2, \frac{u}{2}, [2])$ . Here  $u$  should be an odd integer. We have  $\mathfrak{g} = \mathfrak{g}^{\vee} = \mathfrak{sl}_2$ ,  $S_u = S_\nu = \{\alpha, -\alpha + u\delta\}$ . An element in the affine Weyl group can always be written as an element of the finite Weyl group followed by a translation in the

root lattice  $t_{m\alpha} s$  with  $s$  being 1 or  $s_{\alpha}$ . The fixed points are labelled by the following subset of  $W_{aff}$

$$
\left\{t _ {- m \alpha} \mid 0 \leq 2 m <   u \right\} \cup \left\{t _ {m \alpha} s _ {\alpha} \mid 0 <   2 m \leq u \right\}. \tag {5.4}
$$

The first set has  $(u + 1) / 2$  elements and the second one has  $(u - 1) / 2$  elements, so the total number of fixed points are  $u$ . Using the formula (5.1), we found that weights from the first set are

$$
\left\{\left(- 2 + \frac {2}{u} + \frac {4 m}{u}\right) \Lambda_ {0} - \frac {4 m}{u} \Lambda_ {1} \mid 0 \leq 2 m <   u \right\} \tag {5.5}
$$

and weights from the second set are

$$
\left\{\left(- 2 + \frac {2}{u} + \frac {2 u - 4 m}{u}\right) \Lambda_ {0} - \frac {2 u - 4 m}{u} \Lambda_ {1} \mid 0 <   2 m <   u \right\}. \tag {5.6}
$$

They give exactly the same weights as (3.18) in example 3.1.

Example 5.2.  $L_{-3 + 3 / u}(\mathfrak{sl}_3) \leftrightarrow \mathcal{M}_{Hit}(\mathfrak{sl}_3, u / 3, [3])$ . Here  $u$  is coprime with 3.  $S_\nu$  is the same as  $S_u$

$$
S _ {u} = S _ {\nu} = \{- \theta + u \delta , \alpha_ {1}, \alpha_ {2} \} \tag {5.7}
$$

with  $\theta = \alpha_{1} + \alpha_{2}$ . The condition for  $\tilde{w} = t_{\beta}y$  to give rise to a fixed point is

$$
t _ {\beta} y \left(S _ {u}\right) \subset \hat {\Delta} _ {+}, \quad \beta \in Q, \tag {5.8}
$$

with  $Q$  being the root lattice of  $\mathfrak{sl}_3$ . For  $u = 4$ , the list of fixed points and the corresponding affine weights (5.1) are listed in table 10, and we get exactly the same weights in table 7 in example 3.2. We also plot all alcoves corresponding to fixed points in figure 4.

<table><tr><td>tβy</td><td>Λ</td><td>tβy</td><td>Λ</td><td>tβy</td><td>Λ</td></tr><tr><td>1</td><td>-9/4 Λ0</td><td>t-α1-α2</td><td>-3/4 Λ0 - 3/4 Λ1 - 3/4 Λ2</td><td>t-α1-2α2</td><td>-9/4 Λ2</td></tr><tr><td>t-2α1-α2</td><td>-9/4 Λ1</td><td>t-α2s1</td><td>-2/4 Λ0 - 5/4 Λ1 - 2/4 Λ2</td><td>tα1-α2s1</td><td>-5/4 Λ0 + 1/4 Λ1 - 5/4 Λ2</td></tr><tr><td>t-α1s2</td><td>-2/4 Λ0 - 2/4 Λ1 - 5/4 Λ2</td><td>t-α1+α2s2</td><td>-5/4 Λ0 - 5/4 Λ1 + 1/4 Λ2</td><td>tα2s2s1</td><td>-3/4 Λ1 - 6/4 Λ2</td></tr><tr><td>t2α2s2s1</td><td>-3/4 Λ0 - 6/4 Λ1</td><td>tα1+2α2s2s1</td><td>-6/4 Λ0 - 3/4 Λ2</td><td>tα1s1s2</td><td>-6/4 Λ1 - 3/4 Λ2</td></tr><tr><td>t2α1s1s2</td><td>-3/4 Λ0 - 6/4 Λ2</td><td>t2α1+α2s1s2</td><td>-6/4 Λ0 - 3/4 Λ1</td><td>tα1+α2s1s2s1</td><td>1/4 Λ0 - 5/4 Λ1 - 5/4 Λ2</td></tr><tr><td>t2α1+2α2s1s2s1</td><td>-5/4 Λ0 - 2/4 Λ1 - 2/4 Λ2</td><td></td><td></td><td></td><td></td></tr></table>

Table 10: Fixed points of  $\mathcal{M}_{Hit}(\mathfrak{sl}_3,3 / u,[3])$  and their images under the bijection (5.1).

W-algebras case: Now we consider cases when  $f$  is a regular nilpotent element in a Lévi. As discussed in section 3.2, simple modules of  $W_{-h^{\vee} + \frac{h^{\vee}}{u}}(\mathfrak{g},f)$  are reduced from modules of  $L_{-h^{\vee} + \frac{h^{\vee}}{u}}(\mathfrak{g})$  satisfying the condition (3.25). In particular, some modules are projected out, and multiple modules of AKM is mapped to the same simple module of the W-algebra. On the Hitchin side, one can easily see the similar pattern: firstly the set  $L_{\nu}$  and  $S_{\nu}$  is not changed, secondly the set of affine roots of  $\tilde{\mathfrak{n}}^{\vee}$  is now smaller than  $\hat{\Delta}_{+}^{\vee}$  and so some of the previous fixed points will be projected out, thirdly one should quotient by a Weyl group  $W_{\mathbf{P}^{\vee}}$  action to get the final results. So the pattern on Hitchin side matches precisely with that on the VOA side.

![](images/14576f6efe58e9dd87fbd6e8b6edc87bd3c646f84480f8b81b90ecf7f6d74a99.jpg)  
Figure 4: Alcoves corresponding fixed points for  $A_{2}$ ,  $\nu = 4 / 3$ . Each alcove gives rise to a affine Weyl group element whose inverse gives rise to a fixed point: here  $s_0 = s_\theta t_{-\theta}$ , and  $s_i$  is the Weyl reflection generated by the simple roots of the Lie algebra. For example, the element  $s_0$  in the region gives rise to an element  $s_0^{-1} = t_\theta s_\theta = t_{\alpha_1 + \alpha_2}s_1s_2s_1$ .

Example 5.3.  $W_{-3 + 3 / u}(\mathfrak{sl}_3,[2,1]) \leftrightarrow \mathcal{M}_{Hit}(\mathfrak{sl}_3,u / 3,[2,1])$ .  $L_{\nu}$  is again empty and  $S_{\nu}$  is the same as equation (5.7) but

$$
\Delta_ {\tilde {n} ^ {\vee}} = \hat {\Delta} _ {+} \backslash \left\{\alpha_ {1} \right\}, \tag {5.9}
$$

and so  $W_{\mathbf{P}^{\vee}}$  is generated by  $s_1$ . The condition for fixed points are

$$
\tilde {w} \left(S _ {u}\right) \subset \Delta_ {\tilde {\mathfrak {n}} ^ {\vee}} = \hat {\Delta} _ {+} ^ {\vee} \backslash \left\{\alpha_ {1} \right\}, \quad \tilde {w} \in W _ {\mathbf {P} ^ {\vee}} \backslash W _ {a f f}. \tag {5.10}
$$

The total 6 fixed points when  $u = 4$  are listed in table 11 which are matched to the modules in table 8 through the bijection (5.1). Alcoves of fixed points are drawn in figure 5. In general there are  $u(u - 1) / 2$  fixed points.

<table><tr><td>tβy, Λ</td><td>tβy, Λ</td></tr><tr><td>t2α1+α2s1s2, -6/4Λ0 - 3/4Λ1</td><td>t-2α1-α2, -9/4Λ1</td></tr><tr><td>t-α1+α2s2, -5/4Λ0 - 5/4Λ1 + 1/4Λ2</td><td>tα1-α2s1, -5/4Λ0 + 1/4Λ1 - 5/4Λ2</td></tr><tr><td>t2α2s2s1, -3/4Λ0 - 6/4Λ1</td><td>t-α1-α2, -3/4Λ0 - 3/4Λ1 - 3/4Λ2</td></tr><tr><td>t2α1+2α2s1s2s1, -5/4Λ0 - 2/4Λ1 - 2/4Λ2</td><td>t-α2s1, -2/4Λ0 - 5/4Λ1 - 2/4Λ2</td></tr><tr><td>tα1s1s2, -6/4Λ1 - 3/4Λ2</td><td>tα2s2s1, -3/4Λ1 - 6/4Λ2</td></tr><tr><td>t-α1s2, -2/4Λ0 - 2/4Λ1 - 5/4Λ2</td><td>tα1+α2s1s2s1, 1/4Λ0 - 5/4Λ1 - 5/4Λ2</td></tr></table>

Table 11: Fixed points of  $\mathcal{M}_{Hit}(\mathfrak{sl}_3,3/4,[2,1])$  and their images under the bijection (5.1). The affine Weyl elements in the same box are related by the left action of  $s_1$ , so they reduces to the same fixed points.

![](images/26b80b54510f4b54933dadda2e9744e801133b9d4b0cfe794b83136b9250b127.jpg)  
Figure 5: Alcoves corresponding fixed points for  $A_{2}$ ,  $\nu = 4/3$ ,  $f^{\vee} = [2,1]$ . Alcoves with a blue edge (corresponding to reflection  $s_{1}$ ) on the walls does not reduce to a fixed point (under  $s_{1}$  they are reflected out of the area bounded by walls). Alcoves separated by a blue edge (two alcoves encircled by red edges and black edges) reduce to the same fixed point. Note that the label in each alcove is  $w^{-1}$  in terms of simple reflections.

Example 5.4.  $W_{-3 + 3 / u}(\mathfrak{sl}_3,[3]) \leftrightarrow \mathcal{M}_{Hit}(\mathfrak{sl}_3,u / 3,[1,1,1])$ . Here  $\Delta_{\tilde{\mathfrak{n}}^{\vee}} = \hat{\Delta}_{+}^{\vee} \backslash \{\alpha_{1},\alpha_{2}\}$  and  $W_{\mathbf{P}^{\vee}}$  is the full Weyl group of  $\mathfrak{sl}_3$ , so one only has to consider the affine Weyl group elements of the form  $t_{-k_1\alpha_1 - k_2\alpha_2}$ . Constraints on fixed points are

$$
t _ {- k _ {1} \alpha_ {1} - k _ {2} \alpha_ {2}} (- \alpha_ {1} - \alpha_ {2} + u \delta) = - \alpha_ {1} - \alpha_ {2} + (- k _ {1} - k _ {2} + u) \delta ,
$$

$$
t _ {- k _ {1} \alpha_ {1} - k _ {2} \alpha_ {2}} (\alpha_ {1}) = \alpha_ {1} + (2 k _ {1} - k _ {2}) \delta , \tag {5.11}
$$

$$
t _ {- k _ {1} \alpha_ {1} - k _ {2} \alpha_ {2}} (\alpha_ {2}) = \alpha_ {2} + (2 k _ {2} - k _ {1}) \delta .
$$

The set of allowed  $(k_{1},k_{2})$  is

$$
\left\{\left(k _ {1}, k _ {2}\right) \in \mathbb {Z} ^ {2} \mid u - k _ {1} - k _ {2} > 0, 2 k _ {1} - k _ {2} > 0, 2 k _ {2} - k _ {1} > 0 \right\} \tag {5.12}
$$

and the number of fixed points are  $\frac{(u - 2)(u - 1)}{6}$ . The corresponding W-algebra  $W_{-3 + 3 / u}(\mathfrak{sl}_3, [3])$  is isomorphic to  $W_{3}(3, 3 + u)$  minimal model and this is the bijection discussed in [9]. Alcoves corresponding to fixed points when  $u = 4$  are shown in figure 6.

# 5.1.2 Non-admissible W-algebras

In general it is not easy to study the representation theory of non-admissible W-algebras. On the other hand, computing fixed manifolds of corresponding affine Springer fibers is straightforward. Although we will not be able to provide a proof of the bijection like in boundary admissible cases, we can show that the bijection still holds for the few cases when the simple modules of non-admissible W-algebras are known [86, 87], and it is also interesting to use this bijection to predict information on other non-admissible W-algebras.

![](images/b9d4f244f0d2821b36f85998369d3cb614c2ae3b7cf0537aff392c442aea6b31.jpg)  
Figure 6: Alcoves corresponding fixed points for  $A_{2}$ ,  $\nu = 4/3$ ,  $f^{\vee} = [1,1,1]$ . Alcoves encircled by a hexagon of black edges are in the same  $W_{\mathbf{P}^{\vee}}$  orbit so reduces to the same fixed point. Since only one such hexagon in the area bounded by walls, so there is only one fixed point. Note that the label in each alcove is  $w^{-1}$  in terms of simple reflections.

For example, consider the affine vertex algebra  $L_{-2}(D_4)$ . Since  $h^{\vee} = 6$ , the level  $\kappa = -6 + 4/1$  is non-admissible. One of the fibre side we have  $\mathfrak{g} = D_4, \nu = \frac{1}{4}, \mathbf{P}^{\vee} = \mathbf{I}^{\vee}$ . To compute fixed varieties, we first find  $L_{\nu}$  and  $S_{\nu}$ . The set  $L_{\nu} = \{\alpha + l\delta \mid \frac{1}{4} (\alpha, \rho^{\vee}) + l = 0\}$  in this case is non-empty

$$
L _ {\nu} = \left\{\pm (- \mu + \delta) \right\}, \tag {5.13}
$$

where  $\mu = \alpha_{1} + \alpha_{2} + \alpha_{3} + \alpha_{4}$ , so  $W_{\nu}$  is the Weyl group generated by  $s_{-\mu +\delta}$ . The set  $S_{\nu} = \{\alpha +l\delta \mid \frac{1}{4} (\alpha ,\rho^{\vee}) + l = \frac{1}{4}\}$  is also larger than the admissible case:

$$
S _ {\nu} = \left\{\alpha_ {1}, \alpha_ {2}, \alpha_ {3}, \alpha_ {4}, - \mu + \alpha_ {1} + \delta , - \mu + \alpha_ {3} + \delta , - \mu + \alpha_ {4} + \delta , \theta - \delta \right\}, \tag {5.14}
$$

with  $\theta = \mu +\alpha_{2} = \alpha_{1} + 2\alpha_{2} + \alpha_{3} + \alpha_{4}$  being the highest root. We adopt the Bourbaki numbering for simple roots [85, 88].

By the discussion in section 4.3, the dimension one fixed variety is given by the affine Weyl element  $\tilde{w}$  such that  $\tilde{w}(S_{\nu}) \subset \hat{\Delta}_{+}$  up to the right action of  $W_{\nu}$ . There are only two such elements in  $W_{aff}$ , and they are indeed in the same  $W_{\nu}$  orbit

$$
\tilde {w} _ {0} = s _ {0} = t _ {\theta} s _ {2} s _ {3} s _ {1} s _ {2} s _ {4} s _ {2} s _ {3} s _ {1} s _ {2}, \tag {5.15}
$$

$$
\tilde {w} _ {0} ^ {\prime} = s _ {0} s _ {- \mu + \delta} = t _ {\mu} s _ {3} s _ {1} s _ {2} s _ {4} s _ {2} s _ {3} s _ {1} s _ {2},
$$

where  $s_i$  is the simple reflection corresponding to the simple root  $\alpha_i$ . Therefore there is only one fixed variety with dimension 1.

<table><tr><td>Dim</td><td>\( \tilde{w} = t_{\beta}w \)</td><td>\( \tilde{w}\cdot (k\Lambda_0) \)</td></tr><tr><td>0</td><td>1</td><td>-2\( \Lambda_0 \)</td></tr><tr><td>0</td><td>\( s_4s_0 = t_\theta s_4r_1r_2 \)</td><td>-2\( \Lambda_4 \)</td></tr><tr><td>0</td><td>\( s_1s_0 = t_\theta r_1r_2s_1 \)</td><td>-2\( \Lambda_1 \)</td></tr><tr><td>0</td><td>\( s_3s_0 = t_\theta r_1s_1r_2 \)</td><td>-2\( \Lambda_3 \)</td></tr><tr><td>1</td><td>\( s_0 = t_\theta r_1r_2 \)</td><td>- \( \Lambda_2 \)</td></tr></table>

Table 12: Fixed points of  $D_4, \nu = \frac{1}{4}$  and their images under the bijection (5.1). Here  $r_1 = s_2s_3s_1s_2s_4$ ,  $r_2 = s_2s_3s_1s_2$  and  $\theta = \alpha_1 + 2\alpha_2 + \alpha_3 + \alpha_4$ .

The dimension 0 fixed points corresponds to affine Weyl group elements  $\tilde{w}$  satisfying  $|\tilde{w}(S_{\nu}) \cap \hat{\Delta}_{-}| = 1$  up to the right action by  $W_{\nu}$ , and there are four fixed points

$$
\tilde {w} _ {1} = 1
$$

$$
\tilde {w} _ {2} = s _ {1} s _ {0} = t _ {\theta} s _ {2} s _ {3} s _ {1} s _ {2} s _ {4} s _ {2} s _ {3} s _ {1} s _ {2} s _ {1}, \tag {5.16}
$$

$$
\tilde {w} _ {3} = s _ {3} s _ {0} = t _ {\theta} s _ {2} s _ {3} s _ {1} s _ {2} s _ {4} s _ {1} s _ {2} s _ {3} s _ {1} s _ {2},
$$

$$
\tilde {w} _ {4} = s _ {4} s _ {0} = t _ {\theta} s _ {4} s _ {2} s _ {3} s _ {1} s _ {2} s _ {4} s _ {2} s _ {3} s _ {1} s _ {2}.
$$

The weights under the bijection (5.1) are given by  $t_{\beta}w$ .  $(-2\Lambda_0)$  and results are summarized in table 12  $(-2\Lambda_0$  is invariant under the dot action of  $W_{\nu}$  so  $\tilde{w}$  and  $\tilde{w} s_{-\mu +\delta}$  give the same weight). Indeed they agree with results in VOA literature [86, 87]. If one changes  $f$  to be an element in the minimal nilpotent orbit, there will be only one fixed point on the fibre side, and this is also consistent with the fact that  $W_{-2}(D_4,\min)$  is isomorphic to  $\mathbb{C}$  [87]. More examples on the bijection between fixed varieties and simple modules of non-admissible W-algebras are discussed in appendix A.

# 5.1.3 Formula for the number of fixed varieties

Here we give a formula on the number of fixed varieties of a fibre which will also give the number of simple modules of the corresponding W-algebras under the bijection (5.1).

1. For the Hitchin system defined by  ${}^n\hat{\mathbf{j}}$ ,  $\nu = u / m$  and  $\mathbf{I}^\vee$ , the corresponding VOA is  $L_{-h^\vee + \frac{1}{n\nu}}(\mathfrak{g})$  where  $\hat{\mathfrak{g}}$  is the Langlands dual of  $^o\mathbf{j}$  whose finite part is  $\mathfrak{g}^\vee$ . Let  $a$  be the dimension of the cohomology of fixed varieties when  $u = 1$ , then that of the general  $u$  is [45, 46]

$$
a u ^ {r} \tag {5.17}
$$

with  $r$  being the rank of  $\mathfrak{g}$ . In particular, when  $m$  is a regular elliptic number,  $a = 1$ , and there are only fixed points and so the number is  $u^r$ . The value of  $a$  for the other cases can be found in [46].

2. For the Hitchin system defined by non-twisted affine Lie algebra  $\hat{\mathbf{j}}$ ,  $\nu = u / h^{\vee}$ , and general  $\mathbf{P}^{\vee}$  which is given by the standard parabolic subalgebra, the corresponding VOA is a W-algebra at boundary admissible number, we show in [42] the number of

fixed points is

$$
\frac {(u - m _ {1}) (u - m _ {2}) \cdots (u - m _ {j})}{(m _ {1} + 1) (m _ {2} + 1) \cdots (m _ {i} + 1)}, \tag {5.18}
$$

where the set  $\{m_1, m_2, \dots, m_i\}$  is the set of exponents of the Weyl group of  $\mathfrak{l}$  of  $\mathfrak{p}$ .

# 5.2 Conformal weights and momentum map

The bijection (5.1) also maps geometric data on the Hitchin side to algebra data on the VOA side. On the Hitchin side, one can define a moment map of the  $\mathbb{C}^*$  action, and it was shown in several cases that the value of moment map on each fixed points is equal to the conformal weights of the corresponding module up to shift by a constant [9, 10]. We discuss a generalization of this correspondence in this section.

For simplicity, let us focus on the regular elliptic slope  $\nu$ , so the W-algebra is  $W_{-h^{\vee} + \frac{h\vee}{n u}}(\mathfrak{g},f)$ . Given a fixed point  $\tilde{w} = t_b w$ , the corresponding Higgs field is (up to gauge transformation)

$$
\Phi_ {\tilde {w}} (z) d z = \frac {d z}{z} \sum_ {\alpha + l \delta \in S _ {\nu}, l > 0} z ^ {l - \left(w ^ {- 1} b, \alpha\right)} e _ {w \alpha}. \tag {5.19}
$$

Following [9], one can define the moment map on the Hitchin moduli space  $^{19}$

$$
\mu \equiv \frac {i}{2 \pi} \int \mathrm {T r} \left(\Phi \wedge \Phi^ {\dagger_ {h}} - \mathrm {I d} | z | ^ {2 (u - h ^ {\vee}) / h ^ {\vee}} d z d \bar {z}\right), \tag {5.20}
$$

where  $\Phi^{\dagger h} = h^{-1}\Phi^{\dagger}h$  is the Hermitian adjoint of  $\Phi$ , and  $h$  is the Hermitian metric of the Higgs bundle. And we propose the following relation between the moment map of  $\Phi_{\tilde{w}}$  and the conformal dimension of  $H_{f}(L(\Lambda_{\tilde{w}}))$

$$
\boxed {h _ {H _ {f} (L (\Lambda_ {\tilde {w}}))} = \mu (\Phi_ {\tilde {w}} (z)) - \left[ \frac {u}{h ^ {\vee}} | \rho | ^ {2} - \frac {h ^ {\vee}}{u} | x | ^ {2} - 2 (x, \rho) \right].} \tag {5.21}
$$

Here  $x$  should be chosen to be  $H / 2$  of the standard triple  $(X, Y, H)$  to match with the VOA corresponding to 4d theory. It is straightforward to check that when  $\mathfrak{g} = A_{N-1}$  and  $f = [N]$ , equation (5.21) reproduces the result in [9] and when  $\mathfrak{g} = A_1$  and  $f = [1,1]$ , equation (5.21) also gives the result in [10].

We provide a derivation of (5.21) for  $\mathfrak{g} = A_{N - 1}$ , which essentially follows from [9]. Fixed point then has the following matrix form

$$
\Phi_ {\tilde {w}} (z) = M \left( \begin{array}{c c c c} 0 & z ^ {b _ {1}} & & \\ & & \ddots & \\ & & & z ^ {b _ {N - 1}} \\ z ^ {b _ {N}} & & & \end{array} \right) M ^ {- 1} d z, \tag {5.22}
$$

where  $M$  is a permutation matrix and

$$
b _ {i} = - \left(w ^ {- 1} b, \alpha_ {i}\right) - 1, 1 \leq i \leq N - 1, b _ {N} = u - 1 + \left(w ^ {- 1} b, \theta\right). \tag {5.23}
$$

The moment map at this fixed point can be computed explicitly using the definition (5.20)

$$
\mu \left(\Phi_ {(w, b)}\right) = \frac {h ^ {\vee}}{2 u} | \mathbf {a} | ^ {2}, \tag {5.24}
$$

where coordinates of the  $N$  dimensional vector  $\mathbf{a}$  is related with the coordinates of the vector  $\mathbf{b}$  by

$$
b _ {i} - \frac {u - h ^ {\vee}}{h ^ {\vee}} = a _ {i} - a _ {i + 1}, \quad \sum_ {i = 1} ^ {N} a _ {i} = 0. \tag {5.25}
$$

Here  $a_{N+1}$  is identified with  $a_1$ . Using the definition (5.23) of  $b_i$  and  $\alpha_i = e_i - e_{i+1}$  in orthogonal basis, one gets

$$
a _ {i} = \left(- w ^ {- 1} b - \frac {u}{h ^ {\vee}} \rho , e _ {i}\right). \tag {5.26}
$$

Here  $\rho$  is the Weyl vector, and  $(\rho, \alpha_i) = 1$ . Therefore the value of moment map at the fixed point is

$$
\begin{array}{l} \mu (\Phi_ {\tilde {w}} (z)) = \frac {h ^ {\vee}}{2 u} | \mathbf {a} | ^ {2} = \frac {h ^ {\vee}}{2 u} \sum_ {i} (- w ^ {- 1} b - \frac {u}{h ^ {\vee}} \rho , e _ {i}) ^ {2} \\ = \frac {h ^ {\vee}}{2 u} | - w ^ {- 1} b - \frac {u}{h ^ {\vee}} \rho | ^ {2} = \frac {h ^ {\vee}}{2 u} | b + \frac {u}{h ^ {\vee}} w \rho | ^ {2}, \tag {5.27} \\ \end{array}
$$

Using the formula of the admissible weight  $\Lambda_{\tilde{w}}$

$$
\Lambda_ {\tilde {w}} = t _ {b} w. \left(- h ^ {\vee} + \frac {h ^ {\vee}}{u}\right) \Lambda_ {0}, \tag {5.28}
$$

the finite part  $\lambda_{\tilde{w}}$  of  $\Lambda_{\tilde{w}}$  is

$$
\lambda_ {\tilde {w}} = w \rho + \frac {h ^ {\vee}}{u} b - \rho . \tag {5.29}
$$

Clearly we have

$$
\left| b + \frac {u}{h ^ {\vee}} w \rho \right| ^ {2} = \frac {u ^ {2}}{\left(h ^ {\vee}\right) ^ {2}} \left| \lambda_ {\tilde {w}} + \rho \right| ^ {2}, \tag {5.30}
$$

and the moment map can then be expressed in terms of  $\lambda_{\tilde{w}}$

$$
\mu \left(\Phi_ {\tilde {w}} (z)\right) = \frac {u}{2 h ^ {\vee}} \left| \lambda_ {\tilde {w}} + \rho \right| ^ {2}. \tag {5.31}
$$

Comparing (5.31) with the formula (3.27) of the conformal dimension of  $H_{f}(L(\Lambda_{\tilde{w}}))$

$$
h _ {H _ {f} \left(L \left(\Lambda_ {\tilde {w}}\right)\right)} = \frac {u}{2 h ^ {\vee}} \left(| \lambda_ {\tilde {w}} + \rho | ^ {2} - | \rho | ^ {2}\right) - \frac {h ^ {\vee}}{2 u} | x | ^ {2} + (x, \rho), \tag {5.32}
$$

we get the relation (5.21) between moment maps and conformal dimension.

# 5.3 Modular properties

Modular transformation and DAHA: One important aspect of VOA is the modular property on the characters of the modules [43]. It is definitely interesting to see whether one can find similar modular transformation on the Hitchin side, which actually indeed exists. The cohomology of the Hitchin moduli space (which is related to the data of fixed varieties

by using Morse theory) is realized as a finite dimensional representation of double affine Hecke algebra [45, 89], and the  $PSL^c (2,\mathbb{Z})$  action on DAHA [47] will induce a  $PSL^c (2,\mathbb{Z})$  action on the cohomology of fixed varieties. It is then natural to compare above two sets of modular transformation. This relation will be proved in [42]. The relation between modular matrices of minimal W-algebras of  $A$  type and spherical DAHA of  $A$  type was studied in [48].

Modular property for non-admissible W-algebras: The cohomology group  $H^{*}(\mathcal{M}_{Hit})$  considered in this paper carries a DAHA action. In good cases there is also a natural  $PSL^c (2,\mathbb{Z})$ -action on  $H^{*}(\mathcal{M}_{Hit})$ . Given the correspondence between the fixed varieties of Hitchin system and the modules of VOA, one would find interesting implication for the modular property of non-admissible W-algebra. A crucial fact is that in general the fixed varieties of  $\mathcal{M}_{Hit}$  corresponding to non-admissible W-algebra has higher dimensional components. This is in contrast with the admissible case where the fixed varieties are all of dimension zero.

Now in our correspondence, each irreducible component of fixed varieties gives a simple module (in the category  $\mathcal{O}$ ) of the corresponding VOA. However, in the Morse theory each higher dimensional fixed variety would contribute more than one basis vector to the cohomology. So the above mismatch suggests that if one want to have the modular property for the VOA, one has to enlarge the set of VOA modules. For instance, one might need to add the logarithmic modules to have the modular property which is also observed in some non-admissible VOAs [90, 91]. In fact, our correspondence suggests the number of added module should be the same as the dimension for the cohomology from the fixed varieties.

Modular data and Coulomb branch index: One can define a Coulomb branch index  $\mathcal{I}_T^m (t)$  (Hitchin character) of the 4d theory  $\mathcal{T}$  on  $L(m,1)\times S^{1}$  where  $L(m,1)$  is the Lens space [10, 49]. The Coulomb branch index has an expansion in terms of the fixed varieties, and the geometric data such as momentum map plays a crucial role in computing it. On the other hand, the Lens space Coulomb index  $\mathcal{I}^m (t)$  is deeply connected to the modular matrices (3.13) and (3.28) of the corresponding VOA [10, 11, 49], namely

$$
\lim  _ {t \rightarrow e ^ {2 \pi i}} \mathcal {I} _ {\mathcal {T}} ^ {m} (t) = a (\mathbb {S} \mathbb {T} ^ {m} \mathbb {S}) _ {v a c, v a c}, \tag {5.33}
$$

where  $a$  is a constant determined by  $\mathfrak{g}$ ,  $\mathbb{S}$  and  $\mathbb{T}$  are the modular matrices of characters of the VOA corresponding to theory  $\mathcal{T}$ , and  $(\mathbb{ST}^m\mathbb{S})_{vac,vac}$  means the vacuum-vacuum component of the matrix  $\mathbb{ST}^m\mathbb{S}$ . In general,  $\mathcal{I}_{\mathcal{T}}^{m}$  is difficult to compute for the theories considered in this paper as most of them lack a Lagrangian description. However, when  $n = 1$ , the Lens space is just the 3-sphere  $S^3$ , the Coulomb branch index on  $S^3\times S^1$  is completely determined by the Coulomb branch spectrum of the 4d theory which can be obtained using the method in [17, 19, 20], allowing us to check the relation (5.33) for  $m = 1$ .

Example: Consider 4d theory  $\mathcal{T}_{A_{N - 1},\frac{u}{N},f = \mathrm{trivial}}$  with  $\gcd (N,u) = 1$  (section 2.1), the corresponding VOA is  $L_{-N + \frac{N}{u}}(A_{N - 1})$ . The Coulomb branch spectrum  $\mathrm{CB}_{\mathcal{T}}$  can be found using the method in [19] and is the following set of rational numbers

$$
\mathrm {C B} _ {\mathcal {T}} = \left\{i - j \frac {N}{u} \mid i, j \in \mathbb {Z}, 2 \leq i \leq N, 1 \leq j \leq \left\lfloor (i - 1) \frac {u}{n} \right\rfloor \right\}. \tag {5.34}
$$

Here  $\lfloor x\rfloor$  is the maximal integer less or equal to  $x$ . The Coulomb branch  $\mathcal{I}_{\mathcal{T}}(t)$  on  $S^3\times S^1$  is then

$$
\mathcal {I} _ {\mathcal {T}} (t) = \prod_ {d \in \mathrm {C B} _ {\mathcal {T}}} \frac {1}{1 - t ^ {d}}. \tag {5.35}
$$

Because all elements in  $\mathrm{CB}_{\mathcal{T}}$  are not integer, the limit  $t \to e^{2\pi i}$  of  $\mathcal{I}_{\mathcal{T}}$  is not singular, comparing with the modular matrices of  $L_{-N + \frac{N}{u}}(A_{N - 1})$  (3.13) we find that for the theory  $\mathcal{T}_{A_{N - 1},\frac{u}{N},\mathrm{trivial}}$ ,

$$
\lim  _ {t \rightarrow e ^ {2 \pi i}} \mathcal {I} _ {\mathcal {T}} = e ^ {2 i \pi \left(h _ {\min } - \frac {c}{2 4}\right)} (\mathbb {S T S}) _ {v a c, v a c}, \tag {5.36}
$$

where  $h_{\mathrm{min}} = -\frac{\dim \mathfrak{g}}{24} \left( u - \frac{1}{u} \right)$  is the smallest conformal weights of all admissible modules of  $L_{-N + \frac{N}{u}}(A_{N - 1})$ . It would be nice to generalize this relation for lens space index  $L(m,1)$  in the future.

# 5.4 Zhu's  $C_2$  algebra and the cohomology ring

For each VOA  $V$  there is a commutative algebra  $C_2(V)$  associated to  $V$  called Zhu's  $C_2$  algebra. In the following, we will present examples when  $C_2(V)$  is isomorphic to the cohomology ring of the corresponding Hitchin system.

Consider  $\mathfrak{g} = A_{N - 1}$ ,  $\nu = \frac{u}{N}$  and  $f$  principal. The VOA is then the principal W-algebra  $W_{-N + N / u}(A_{N - 1},\mathrm{prin})$  (i.e.  $W_{N}(N,u)$  minimal model). Motivated from the character of its vacuum module,  $C_2(W_{-N + N / u}(A_{N - 1},\mathrm{prin}))$  is conjectured to be the same as the Jacobi algebra of an isolated hypersurface singularity [92]

$$
\mathbb {C} [ T _ {2}, T _ {3}, \dots , T _ {N} ] / \left\langle \frac {\partial f}{\partial T _ {2}}, \dots , \frac {\partial f}{\partial T _ {N}} \right\rangle . \tag {5.37}
$$

Here  $T_2, \dots, T_N$  are generators with degrees  $2, \dots, N$ , and  $f[T_2, \dots, T_n]$  is an isolated singularity with degree  $u + 1$ . The generators  $\left\{ \frac{\partial f}{\partial T_2}, \dots, \frac{\partial f}{\partial T_N} \right\}$  of the ideal then have degree  $u + 1 - n, \dots, u - 2$ . This construction ensures that the above algebra has the dimension  $\frac{(u - 1)!}{n!(u - n)!}$ , which is just the dimension for the Milnor algebra.

On the other hand, the cohomology ring for the corresponding Hitchin system is given by the following ring [89, 93]

$$
\mathbb {C} \left[ e _ {2}, e _ {3}, \dots , e _ {N} \right] / \langle g _ {u + 1 - N}, \dots , g _ {u - 1} \rangle . \tag {5.38}
$$

Here generators  $e_2, \dots, e_N$  also have degree  $2, \dots, N$ , and the generator  $g_{u - n + i}$  of the ideal is the coefficient of  $w^{u - n + i}$  in the Taylor expansion of

$$
\left(1 + e _ {2} w ^ {2} + \dots + e _ {n} w ^ {n}\right) ^ {u / n} \tag {5.39}
$$

at  $w = 0$ . From the descriptions above, one can deduce that the ring (5.37) and the ring (5.38) are isomorphic. This relations has a similar flavor to the Hikita conjecture which relates the coordinate ring of some scheme coming from a conical symplectic singularity to the cohomology ring of a symplectic resolution of the dual conical symplectic singularity [94]. In our context, the coordinate ring is coming from Zhu's  $C_2$  algebra, which would indeed give the coordinate ring of the Higgs branch [95]. It would be interesting to further study this correspondence in more general setups.

# 5.5 Generalization to arbitrary  $f$

So far we assume the nilpotent element  $f$  which labels the regular singularity to be a regular (principal) nilpotent element in a Lévi subalgebra of  $\mathfrak{g}$ , however, there are many nilpotent elements which is distinguished but not regular in any minimal Lévi subalgebra containing it (distinguished but not regular for short). For example, when  $\mathfrak{g}$  is of type CDEFG, any element  $f$  in the subregular nilpotent orbit is distinguished but not regular as the minimal Lévi subalgebra containing  $f$  is  $\mathfrak{g}$  itself.

Given a 4d theory  $\mathcal{T}_{j,b,k,f}$  or  $\mathcal{T}_{j,o,b_t,kt,f}$  with  $f$  distinguished but not regular, we should modify the definition of its corresponding  $\mathcal{M}_{Hit}$  in the following way. Adopting the same notation as in section 4.1 with the modification that  $\mathfrak{l}$  is the minimal standard Lévi subalgebra containing  $f$ , we still consider the Higgs bundle  $(E,\Phi)$  with a  $P^{\vee}$ -level structure at the regular singularity. However,  $\Phi$  should have a new boundary condition around the regular singularity (recall  $\Phi' = z\Phi$ )

$$
\lim  _ {z \rightarrow 0} \Phi^ {\prime} \in \overline {{d \left(\mathcal {O} _ {f} ^ {\mathrm {I}}\right)}} \oplus \mathfrak {n} ^ {\vee}, \tag {5.40}
$$

which is equivalent to  $\lim_{z\to 0}\Phi^{\prime}\in \overline{\mathcal{O}}_{f^{\vee}}$  because  $\overline{\mathcal{O}}_f\vee = G^\vee \cdot (\overline{d(\mathcal{O}_f^\intercal)}\oplus \mathfrak{n}^\vee)$ . When  $f$  in regular in  $\mathfrak{l}$ ,  $d(\mathcal{O}_f^\mathfrak{l})$  is the trivial nilpotent orbit in  $\mathfrak{l}$ , therefore (5.40) reduces to (4.7).

We propose that the corresponding affine Spaltenstein variety should be replaced by the following space

$$
S p _ {\gamma , \mathbf {P} ^ {\vee}, f} = \left\{g \in \mathbf {P} ^ {\vee} \backslash \mathbf {G} ^ {\vee} \mid g \gamma g ^ {- 1} \in \overline {{d \left(\mathcal {O} _ {f} ^ {\mathrm {I}}\right)}} \oplus \tilde {\mathfrak {n}} ^ {\vee} \right\}. \tag {5.41}
$$

The space  $Sp_{\gamma, \mathbf{P}^{\vee}, f}$  is well-defined because  $\overline{d(\mathcal{O}_f^{\mathfrak{l}})} \oplus \tilde{\mathfrak{n}}^{\vee}$  is stable under the action of  $P^{\vee}$  [96]. The fixed varieties of  $Sp_{\gamma, \mathbf{P}^{\vee}, f}$  are

$$
S p _ {\gamma , \mathbf {P} ^ {\vee}, f} ^ {T} = \sqcup H _ {\tilde {w}}, \quad \left\{\tilde {w} \in W _ {\mathbf {P} ^ {\vee}} \backslash W _ {a f f} / W _ {\nu} \mid \operatorname {A d} (\tilde {w}) \gamma \in \overline {{d \left(\mathcal {O} _ {f} ^ {\mathrm {l}}\right)}} \oplus \tilde {\mathfrak {n}} ^ {\vee} \right\}. \tag {5.42}
$$

We will provide examples to illustrate the matching between fixed varieties of  $\mathcal{M}_{Hit}$  with know results in W-algebras.

Example 5.5.  $W_{-(2n - 2) + \frac{2n - 2}{u}}(D_n, [2n - 3, 3]) \leftrightarrow \mathcal{M}_{Hit}(D_n, \frac{u}{2n - 2}, [2^2, 2n - 4])$ . Here  $\gcd(u, 2n - 2) = 1$  and the partition  $[2n - 3, 3]$  corresponds to the subregular nilpotent orbit of  $D_n$  which is distinguished in  $D_n$  itself. The boundary condition (5.40) in this case is

$$
\lim  _ {z \rightarrow 0} \Phi^ {\prime} \in \overline {{d (\mathcal {O} _ {s u b r e g})}} = \overline {{\mathcal {O} _ {m i n}}}, \tag {5.43}
$$

and  $P^{\vee} = G^{\vee} = SO(8)$ . There are only fixed points in  $\mathcal{M}_{Hit}(D_n, \frac{u}{2n-2}, [2^2, 2n-4])$ . Extra fixed points comparing to the principal case are labelled by the following elements of the affine Weyl group of  $\hat{D}_n$

$$
\{\tilde {w} \in W _ {G ^ {\vee}} \backslash W _ {a f f} \mid | \tilde {w} (S _ {\nu}) \cap \Delta^ {\vee} | = 1 \}, \tag {5.44}
$$

where  $\Delta^{\vee}$  is the set of all roots of  $D_{n}$ . The number of these extra fixed points is

$$
\frac {(u - h _ {1}) (u - h _ {2}) \cdots (u - h _ {n})}{2 ^ {n - 2} (n - 2) !}, \tag {5.45}
$$

where  $\{h_1, h_2, \dots, h_n\}$  is the following set of integers

$$
\{1, 3, \dots , 2 n - 5, 2 n - 4, n - 1 \}. \tag {5.46}
$$

This is just the set of exponents of  $D_{n}$  with the maximal exponent  $2n - 3$  subtracted by 1. The denominator  $2^{n - 2}(n - 2)!$  is also the order of the Weyl group of the centralizer of an element in  $\mathcal{O}_{\text{min}}$ . Formula (5.45) and (5.18) together predict the number of simple modules of subregular W-algebra  $W_{-(2n - 2) + \frac{2n - 2}{u}}(D_n, [2n - 3, 3])$ . When  $u = 2n - 3$ , the number of fixed points is  $n - 2$  which is the same as the number of simple modules of  $W_{-(2n - 2) + \frac{2n - 2}{2n - 3}}(D_n, [2n - 3, 3])$  given in [81].

Example 5.6.  $W_{-h^{\vee} + \frac{h^{\vee}}{u}}(E_n, f_{subreg}) \leftrightarrow \mathcal{M}_{Hit}(E_n, \frac{u}{h^{\vee}}, f_{min})$ . Here  $n = 6, 7, 8$  and  $\gcd(u, h^{\vee}) = 1$ . The minimal Lévi subalgebra containing  $f_{subreg}$  is again  $E_n$  itself. Numbers of extra fixed points comparing to the principal case are

$$
E _ {6}: \frac {1}{6 !} (u - 1) (u - 4) (u - 5) (u - 7) (u - 8) (u - 1 0),
$$

$$
E _ {7}: \frac {1}{2 ^ {5} 6 !} (u - 1) (u - 5) (u - 7) (u - 9) (u - 1 1) (u - 1 3) (u - 1 6), \tag {5.47}
$$

$$
E _ {8}: \frac {1}{2 9 0 3 0 4 0} (u - 1) (u - 7) (u - 1 1) (u - 1 3) (u - 1 7) (u - 1 9) (u - 2 3) (u - 2 8).
$$

Again  $h_i$ 's appear in the formula are exponents of  $E_n$  with the maximal one subtracted by 1, and the denominator is the order of the Weyl group of the centralizer of an element in  $\mathcal{O}_{min}$ . For example, 2903040 is the order of Weyl group of  $E_7$  which is the centralizer of an element of the  $A_1$  orbit of  $E_8$ . Formulae (5.47) and (5.18) together predict the number of simple modules of the subregular W-algebra  $W_{-h^{\vee} + \frac{h^{\vee}}{u}}(E_n, f_{subreg})$ . When  $u = h^{\vee} - 1$ , the number of fixed points matches the number of simple modules of  $W_{-h^{\vee} + \frac{h^{\vee}}{h^{\vee} - 1}}(E_n, f_{subreg})$  computed in [81].

It was also proved in [81] that W-algebras  $W_{-h^{\vee} + \frac{h^{\vee}}{h^{\vee} - 1}}(\mathfrak{g},f_{subreg})$  with  $\mathfrak{g}$  being type  $D$  or  $E$  are rational with modular matrices of simple modules worked out explicitly. It would also be nice to match these data from the VOA side with geometric data from the Hitchin side. In general, W-algebras with distinguished  $f$  (distinguished W-algebras) play fundamental role among W-algebras. However, the representation theory of distinguished W-algebras that are not of regular type are largely unexplored. Our correspondence provides motivations to study the space  $Sp_{\gamma ,\mathbf{P}^{\vee},f}$  and use the geometry to predict representation theories of distinguished W-algebras.

# 5.6 Relation with 3d symplectic duality

When taking the limit that the radius of the circle to be 0, one can get a 3d  $\mathcal{N} = 4$  SCFT  $\mathcal{T}^{3d}$ . As mentioned in the introduction, the Higgs branch  $X$  of  $\mathcal{T}^{3d}$  is the same as the Higgs branch of 4d theory, which is identified as the associated variety of the corresponding VOA  $V(\mathcal{T})$ . The Coulomb branch  $Y$  of  $\mathcal{T}^{3d}$  is also related to the Coulomb branch of the 4d on  $S^1$ . In the massless limit both  $X$  and  $Y$  are hyper-Kähler cones.

In many cases,  $Y$  (resp.  $X$ ) can also be realized as the Higgs (resp. Coulomb) branch of another 3d  $\mathcal{N} = 4$  quiver gauge theory  $\mathcal{T}^{3d,mirror}$  which is called the mirror of  $\mathcal{T}^{3d}$  in physics literature [53]. Properties of  $Y$  can be quite different from its 4d counter part:

1. Usually there is no flavor symmetries acting on the 4d Coulomb branch. However, there are sometimes emergent global symmetries on  $Y$ .  
2.  $Y$  is not irreducible, i.e., it typically has a component described by free hypermultiplets in the mirror theory.

Since  $X$  and  $Y$  are Higgs or Coulomb branches of the same 3d theory, they form a symplectic pair. Actually, many familiar symplectic pairs arises this way:

Example 5.7. Consider the 4d theory  $\mathcal{T}_{A_{N-1},\frac{u}{N},f=[1^N]}$  with  $\gcd(u,N)=1$  and  $u>N$ . After reducing to 3d, the Higgs branch  $X$  is the associated variety of  $L_{-N+N/u}(A_{N-1})$  which is the nilpotent cone  $\mathcal{N}$  of  $A_{N-1}$  [97] [20], while the Coulomb brach  $Y$  is given by the Higgs branch of the so-called  $T[SU(n)]$  theory [98] plus  $h_{u,N}=\frac{(N-1)(u-N-1)}{2}$  free hypermultiplets, which is  $\mathcal{N}$  plus the flat space  $\mathbb{C}^{h_{u,n}}$ . The interacting part 3d theory is self-mirror meaning both its Higgs and Coulomb branch are the same  $(\mathcal{N})$ . Notice that when  $u>N$ , 4d theories  $\mathcal{T}_{A_{N-1},\frac{u}{N},f=[1^N]}$  with different  $u$  give the same symplectic pairs.

Example 5.8. Next change  $f$  in the above example to be an element in arbitrary nilpotent orbit. Then  $X$  becomes  $S_f \cap \mathcal{N}$ , and  $Y$  is the Higgs branch of  $T_f[SU(N)]$  theory plus  $h_{u,N}$  free hypermultiplets. So  $Y$  is  $\overline{\mathcal{O}}_{f^{\vee}}$  plus  $\mathbb{C}^{h_{u,n}}$ . It is known that  $S_f \cap \mathcal{N}$  and  $\overline{\mathcal{O}}_{f^{\vee}}$  form a symplectic pair.

Example 5.9. Now take  $N = 2l + 1$  to be an odd integer,  $u = 2$  and  $f = [1^{2l + 1}]$ . The 3d mirror for this theory is given in [53], and  $X$  is now  $\overline{\mathcal{O}}_{[2^l,1]}$  and  $Y$  is  $S_{[l + 1,l]} \cap \mathcal{N}$ .

In above examples, we see that different 4d theories (VOAs) can have the same Higgs branch (associated variety). Their 4d Coulomb branches are different, however, after reducing to 3d, their 3d Coulomb branch differ only by a  $\mathbb{C}^h$  factor. It seems that the 4d perspective is a more "refined" version of 3d symplectic pair. It would also be interesting to see if it can provide new in-sight on symplectic dualities.

Moreover, one can get a finite W-algebra from the twisted Zhu's algebra of the associated VOA [54]. The finite W-algebra is precisely those found by doing quantization on the Higgs branch of 3d theory, so from the reduction of 4d theory, one not only gets a pair of symplectic singularities, but also an algebra/geometry pair.

# 6 Conclusion and outlook

In this paper, we study the mirror symmetry for circle compactified 4d  $\mathcal{N} = 2$  SCFTs. This symmetry involves an algebra object which is a VOA capturing the data on the Schur sector, and a geometric object which is the Coulomb branch of the effective 3d theory. We show that the representation theory of the VOA such as simple modules, modular

transformation, Zhu's algebra can be translated into geometric properties of the Coulomb branch. Various checks have been made in this paper when one can compute things on both sides, and one would get many interesting predictions on each side by using the mirror symmetry map.

Our mirror pair involves W-algebra and the Hitchin's moduli space, which all play important roles in various branches of physics and mathematics, and we hope that the mirror proposal in this paper would help understand them further. While there are many interesting matches in our mirror proposal, a further physical understanding of this mirror symmetry is definitely desirable. Hopefully the physical understanding would help us to construct VOA modules and their character. We mainly focus on regular elliptic slope and special nilpotent orbit in this paper (with a few studies on sub-regular elliptic slope), and detailed studies of other cases will be presented elsewhere.

The mirror symmetry involves an algebra defined using Higgs branch or its generalization and the effective Coulomb branch. Physically, it suggests that one can study following generalizations:

1. Twisted W-algebras: In this paper we encounter non-twisted affine Lie algebra on the VOA side. It is actually possible to find the mirror pair involving twisted affine Lie algebras and non-twisted Hitchin systems. Recall that one finds the Coulomb branch as Hitchin's moduli space as follows: one gets 3d theory by compactify 6d theory on  $\Sigma \times S^1$ ; if we first compactify 6d theory on  $\Sigma$ , one gets a 4d theory on  $S^1$ , and if we first compactify it on  $S^1$ , one gets a 5d theory on  $\Sigma$  whose Higgs branch is just the Hitchin's moduli space defined on  $\Sigma$ . The twisted theory is defined by turning on outer automorphism twist on  $\Sigma$ . Now to get 5d theory with non-simply laced gauge group, one needs to turn on outer automorphism twist around the circle  $S^1$ , and then one gets a non-twisted Hitchin system on  $\Sigma$ . On the left hand side of figure 1, one first compactifies the theory on  $\Sigma$  and then on  $S^1$  with outer-automorphism twist, and it is naturally to expect that one should get a twisted W-algebra by doing outer automorphism twist. [42] establishes the correspondence for twisted AKM at boundary admissible level.

2. Non-elliptic affine Springer fiber: We mainly focus on the so-called elliptic affine Springer fiber in this paper. The correspondence can certainly be generalized to the non-elliptic case. The Hitchin system is well defined and the corresponding VOA can be found using coset construction [18]. On the other, isomorphisms between W-algebras may predict isomorphisms between Hitchin systems. In certain cases, the non-elliptic Hitchin system is predicted to be isomorphic to elliptic Hitchin system using the isomorphism between W-algebras.

Example 6.1. Consider a 4d theory  $\mathcal{T}_{A_1,1,u - 1,f = [1^2]}$  which is also called the  $(A_{1},D_{2u})$  AD theory. Hitchin system describing its Coulomb branch is given by the data  $(A_{1},\nu = u,f^{\vee} = [2])$ , and the corresponding affine Springer fibre is not elliptic because the denominator of  $\nu$  is 1. However, the same 4d theory can also be realized as  $\mathcal{T}_{A_u,u + 1, - 1,[u - 1,1^2]}$  by using an irregular singularity which is indeed elliptic and a

special nilpotent orbit [13]. The Hitchin data corresponding to  $\mathcal{T}_{A_u,u + 1, - 1,[u - 1,1^2 ]}$  is  $(A_{u},\nu = \frac{u}{u + 1},f^{\vee} = [3,1^{u - 2}])$  . The duality of the 4d theory implies the isomorphism between Hitchin moduli space

$$
\mathcal {M} _ {H i t} \left(A _ {1}, u, [ 2 ]\right) \simeq \mathcal {M} _ {H i t} \left(A _ {u}, \frac {u}{u + 1}, [ 3, 1 ^ {u - 2} ]\right). \tag {6.1}
$$

Example 6.2. Consider a 4d theory whose spectral curve at SCFT point is  $^{21}$

$$
x ^ {n + n _ {1}} + x ^ {n _ {1}} y ^ {k} = 0, \tag {6.2}
$$

where  $n_1, n$  and  $k$  are positive integers such that  $\gcd(n, k) = 1$ . It was proposed that dual descriptions of this theory lead to the following isomorphisms of W-algebras [18]

$$
\begin{array}{l} W _ {- (n _ {1} (n + k) + n) + \frac {n _ {1} (n + k) + n}{n + k}} \left(\mathfrak {s l} _ {n _ {1} (n + k) + n}, [ (n + k - 1) ^ {n _ {1}}, n + n _ {1} ]\right) \tag {6.3} \\ \simeq W _ {- k + \frac {k}{n + k}} \left(\mathfrak {s l} _ {k}, \left[ k - n _ {1}, 1 ^ {n _ {1}} \right]\right) \\ \end{array}
$$

and isomorphisms of Hitchin moduli spaces

$$
\mathcal {M} _ {H i t} \left(\mathfrak {s l} _ {n _ {1} (n + k) + n}, \frac {n + k}{n _ {1} (n + k) + n}, [ (n + k - 1) ^ {n _ {1}}, n + n _ {1} ]\right) \simeq \mathcal {M} _ {H i t} \left(\mathfrak {s l} _ {k}, \frac {n + k}{k}, [ k - n _ {1}, 1 ^ {n _ {1}} ]\right). \tag {6.4}
$$

More isomorphisms involving other Lie algebras are also proposed in [18, 72], it would be nice if one can prove these isomorphisms rigorously.

3. Class S theory: VOAs for general class  $S$  theory has been found in [15, 71, 99], but little is known about their representation theory. On the other hand, the Coulomb branch for circle compactified theory is given by Hitchin system with regular singularities only. There are a lot of studies on the cohomology of the moduli space [100], and we might learn the representation theory of VOA by using results on Hitchin side.  
4. General  $\mathcal{N} = 2$  theories: We hope to push our mirror symmetry to more general  $\mathcal{N} = 2$  SCFTs and use it to study physical properties of those theories. It was found recently that one can attach interesting configuration of curves on the central fiber [101], and their fixed points and cohomology could be interesting objects to study. One can also consider more general  $\mathcal{N} = 2$  theories such as pure  $SU(N)$  gauge theory compactified on the circle, and study their related mirror symmetry.  
5. 3d  $\mathcal{N} = 4$  gauge theory with finite gauge coupling: The typical feature of 3d  $\mathcal{N} = 4$  SCFT is that its Coulomb branch can be given by the Higgs branch of the mirror quiver gauge theory. However, if one studies the gauge theory with finite gauge coupling, locally its Coulomb branch has the structure of  $\mathbb{R}^3\times T$  (ALF space) [8] which can no longer be given by the Higgs branch of a quiver gauge theory.

<table><tr><td>Physical theory</td><td>Coulomb branch</td><td>Mirror</td><td>Algebra</td></tr><tr><td>3d N = 4 SCFT</td><td>ALE</td><td>Certain quiver variety</td><td>Finite W-algebra</td></tr><tr><td>3d gauge theory</td><td>ALF</td><td>Bow diagram</td><td>?</td></tr><tr><td>4d N = 2 on S1</td><td>ALG</td><td>Hitchin system</td><td>VOA</td></tr><tr><td>5d N = 2 on T2</td><td>ALH</td><td>Periodic monopole on T3</td><td>?</td></tr><tr><td>6d (1,0) on T3</td><td>compact</td><td>K3</td><td>?</td></tr></table>

Table 13: Mirror symmetry for theories with eight supercharges.

Instead, it can be given by the so-called bow diagram [102], which can be viewed as a four dimensional theory on a one-dimensional space. To retain the mirror symmetry, the algebra side might also be changed.

6. Generalization to five and six dimensional SCFTs: One might also consider the  $T^2$  compactification of 5d  $\mathcal{N} = 1$  SCFT or  $T^3$  compactification of 6d  $(1,0)$  little string theory, and one would expect to have the similar mirror symmetric between an algebra and the Coulomb branch  $\mathcal{M}_C$  of the effective 3d theory. For the  $T^2$  compactification of rank one 5d theory, locally the effective 3d Coulomb branch would take the form of  $T^3 \times \mathbb{R}$  (ALH space) [103]. For the  $T^3$  compactification of 6d little string theory, the total space of the effective 3d Coulomb branch would be compact [104]. See table 13 for a summary. We do not know what kind of algebra would be involved for the Higgs branch side yet, and we believe that there are lots of interesting mathematics and physics involved in these mirror symmetries.

# Acknowledgments

PS is supported by NSCF Grant No. 12225108. WY is supported by Yau Mathematical Science Center at Tsinghua University. DX and WY are supported by national key research and development program of China (NO. 2020YFA0713000), and NNSF of China with Grant NO: 11847301 and 12047502.

# A Rank one SCFT

In this section we discuss fixed varieties of the Coulomb branch of rank one SCFTs. The corresponding VOAs are all non-admissible.

$E_6$  theory:  $L_{-3}(E_6)\leftrightarrow \mathcal{M}_{Hit}(E_6,\frac{1}{9},f^\vee = principal)$ . The two sets are

$$
L _ {\nu} = \left\{\pm \left(\alpha_ {1} + \alpha_ {2} + 2 \alpha_ {3} + 2 \alpha_ {4} + 2 \alpha_ {5} + \alpha_ {6} - \delta\right) \right\}, \tag {A.1}
$$

and

$$
S _ {\nu} = \left\{\alpha_ {1}, \alpha_ {2}, \alpha_ {3}, \alpha_ {4}, \alpha_ {5}, \alpha_ {6} \right\} \cup \left\{\beta_ {1}, \beta_ {2}, \gamma \right\}, \tag {A.2}
$$

where  $\beta_{1} = -\alpha_{1} - \alpha_{2} - 2\alpha_{3} - 2\alpha_{4} - \alpha_{5} - \alpha_{6} + \delta$ ,  $\beta_{2} = -\alpha_{1} - \alpha_{2} - \alpha_{3} - 2\alpha_{4} - 2\alpha_{5} - \alpha_{6} + \delta$  and  $\gamma = \alpha_{1} + \alpha_{2} + 2\alpha_{3} + 3\alpha_{4} + 2\alpha_{5} + \alpha_{6} - \delta$ . The set of fixed varieties are listed in table 14 which

matches simple modules of  $L_{-3}(E_6)$  classified in [87]. The fixed variety with dimension 1 corresponds to the only module with dominant weight  $-\Lambda_4$ .

<table><tr><td>Dim</td><td>\(\tilde{w}\simeq(w,\beta)\)</td><td>\(t_{\beta}w.(k\Lambda_0)\)</td></tr><tr><td>0</td><td>1\simeq(1,0)</td><td>-3\(\Lambda_0\)</td></tr><tr><td>0</td><td>\(s_1s_3s_0\simeq(r_1r_2s_1s_3s_2,\alpha_1+\alpha_2+2\alpha_3+3\alpha_4+2\alpha_5+\alpha_6)\)</td><td>-3\(\Lambda_1\)</td></tr><tr><td>0</td><td>\(s_6s_5s_0\simeq(s_6r_1s_1r_2s_2,\alpha_1+\alpha_2+2\alpha_3+3\alpha_4+2\alpha_5+\alpha_6)\)</td><td>-3\(\Lambda_6\)</td></tr><tr><td>0</td><td>\(s_5s_0\simeq(r_1s_1r_2s_2,\alpha_1+\alpha_2+2\alpha_3+3\alpha_4+2\alpha_5+\alpha_6)\)</td><td>-2\(\Lambda_5+\Lambda_6\)</td></tr><tr><td>0</td><td>\(s_0\simeq(s_2r_1r_2s_2,\alpha_1+2\alpha_2+2\alpha_3+3\alpha_4+2\alpha_5+\alpha_6)\)</td><td>-2\(\Lambda_2+\Lambda_0\)</td></tr><tr><td>0</td><td>\(s_3s_0\simeq(r_1r_2s_3s_2,\alpha_1+\alpha_2+2\alpha_3+3\alpha_4+2\alpha_5+\alpha_6)\)</td><td>\(\Lambda_1-2\Lambda_3\)</td></tr><tr><td>1</td><td>\(s_2s_0\simeq(r_1r_2s_2,\alpha_1+\alpha_2+2\alpha_3+3\alpha_4+2\alpha_5+\alpha_6)\)</td><td>- \(\Lambda_4\)</td></tr></table>

Table 14: Fixed varieties of  ${\mathcal{M}}_{Hit}\left( {{E}_{6},\frac{1}{9},principal}\right)$  . Here  ${r}_{1} = {s}_{4}{s}_{5}{s}_{3}{s}_{4}{s}_{1}{s}_{3}{s}_{2}{s}_{4}{s}_{5}{s}_{6}{s}_{5}{s}_{4}$  ,  ${r}_{2} = {s}_{3}{s}_{2}{s}_{4}{s}_{5}{s}_{1}{s}_{3}{s}_{4}$  and  ${\lambda }_{0} = {\bar{w}}_{1} + {\bar{w}}_{2} + {\bar{w}}_{3} + {\bar{w}}_{5} + {\bar{w}}_{6}$  .

$E_7$  theory:  $L_{-4}(E_7) \leftrightarrow \mathcal{M}_{Hit}(E_7, \frac{1}{14}, f^\vee = principal)$ . Two sets are:

$$
L _ {\nu} = \{\pm (\alpha_ {1} + 2 \alpha_ {2} + 2 \alpha_ {3} + 3 \alpha_ {4} + 3 \alpha_ {5} + 2 \alpha_ {6} + \alpha_ {7} - \delta) \}, \tag {A.3}
$$

and

$$
S _ {\nu} = \left\{\alpha_ {i}, i = 1, 2, \dots , 7 \right\} \cup \left\{\beta_ {1}, \beta_ {2}, \gamma \right\}, \tag {A.4}
$$

where  $\beta_{1} = -\alpha_{1} - \alpha_{2} - 2\alpha_{3} - 3\alpha_{4} - 3\alpha_{5} - 2\alpha_{6} - \alpha_{7} + \delta$ ,  $\beta_{2} = -\alpha_{1} - 2\alpha_{2} - 2\alpha_{3} - 3\alpha_{4} - 2\alpha_{5} - 2\alpha_{6} - \alpha_{7} + \delta$  and  $\gamma = \alpha_{1} + 2\alpha_{2} + 2\alpha_{3} + 4\alpha_{4} + 3\alpha_{5} + 2\alpha_{6} + \alpha_{7} - \delta$ .

There are one fixed variety of dimension 1 and seven fixed points of dimension 0 as summarized in 15. Again the fixed variety with dimension 1 corresponds to the simple module with dominant weight of  $V_{-4}(E_7)$ , while fixed points correspond to other simple modules [87].

$E_{8}$  theory:  $L_{-6}(E_8)\leftrightarrow \mathcal{M}_{Hit}(E_8,\frac{1}{24},f^{\vee} = principal)$ . Two sets of affine roots are

$$
L _ {\nu} = \{\pm (2 \alpha_ {1} + 3 \alpha_ {2} + 4 \alpha_ {3} + 5 \alpha_ {4} + 4 \alpha_ {5} + 3 \alpha_ {6} + 2 \alpha_ {7} + \alpha_ {8} - \delta) \}, \tag {A.5}
$$

<table><tr><td>Dim</td><td>\( \widetilde{w} \)</td><td>\( t_{\beta}w.(k\Lambda_0) \)</td></tr><tr><td>0</td><td>1</td><td>-4\( \Lambda_0 \)</td></tr><tr><td>0</td><td>\( s_0 \)</td><td>-3\( \Lambda_1 + 2\Lambda_0 \)</td></tr><tr><td>0</td><td>\( s_1s_0 \)</td><td>\( \Lambda_1 - 2\Lambda_3 \)</td></tr><tr><td>0</td><td>\( s_2s_3s_1s_0 \)</td><td>-2\( \Lambda_2 \)</td></tr><tr><td>0</td><td>\( s_5s_3s_1s_0 \)</td><td>-2\( \Lambda_5 + \Lambda_6 \)</td></tr><tr><td>0</td><td>\( s_6s_5s_3s_1s_0 \)</td><td>-3\( \Lambda_6 + 2\Lambda_7 \)</td></tr><tr><td>0</td><td>\( s_7s_6s_5s_3s_1s_0 \)</td><td>-4\( \Lambda_7 \)</td></tr><tr><td>1</td><td>\( s_3s_1s_0 \)</td><td>\( -\Lambda_4 \)</td></tr></table>

<table><tr><td>Dim</td><td>\(\tilde{w}\)</td><td>\(t_{\beta}w.(k\Lambda_{0})\)</td></tr><tr><td>0</td><td>1</td><td>-6\(\Lambda_{0}\)</td></tr><tr><td>0</td><td>\(s_{0}\)</td><td>-5\(\Lambda_{8}\)+4\(\Lambda_{0}\)</td></tr><tr><td>0</td><td>\(s_{8}s_{0}\)</td><td>-4\(\Lambda_{7}\)+3\(\Lambda_{8}\)</td></tr><tr><td>0</td><td>\(s_{7}s_{8}s_{0}\)</td><td>-3\(\Lambda_{6}\)+2\(\Lambda_{7}\)</td></tr><tr><td>0</td><td>\(s_{6}s_{7}s_{8}s_{0}\)</td><td>-2\(\Lambda_{5}\)+\(\Lambda_{6}\)</td></tr><tr><td>0</td><td>\(s_{2}s_{5}s_{6}s_{7}s_{8}s_{0}\)</td><td>-2\(\Lambda_{2}\)</td></tr><tr><td>0</td><td>\(s_{3}s_{5}s_{6}s_{7}s_{8}s_{0}\)</td><td>\(\Lambda_{1}-2\)\(\Lambda_{3}\)</td></tr><tr><td>0</td><td>\(s_{1}s_{3}s_{5}s_{6}s_{7}s_{8}s_{0}\)</td><td>-3\(\Lambda_{1}\)</td></tr><tr><td>1</td><td>\(s_{5}s_{6}s_{7}s_{8}s_{0}\)</td><td>-\(\Lambda_{4}\)</td></tr></table>

Table 15: Left: Fixed varieties of  $E_7$ ,  $\frac{1}{14}$ . Right: Fixed varieties of  $E_8$ ,  $\frac{1}{24}$ .

and

$$
S _ {\nu} = \left\{\alpha_ {i}, i = 1, 2, \dots , 8 \right\} \cup \left\{\beta_ {1}, \beta_ {2}, \gamma \right\}, \tag {A.6}
$$

where  $\beta_{1} = -2\alpha_{1} - 3\alpha_{2} - 3\alpha_{3} - 5\alpha_{4} - 4\alpha_{5} - 3\alpha_{6} - 2\alpha_{7} - \alpha_{8} + \delta$ ,  $\beta_{2} = -2\alpha_{1} - 2\alpha_{2} - 4\alpha_{3} - 5\alpha_{4} - 4\alpha_{5} - 3\alpha_{6} - 2\alpha_{7} - \alpha_{8} + \delta$  and  $\gamma = 2\alpha_{1} + 3\alpha_{2} + 4\alpha_{3} + 6\alpha_{4} + 4\alpha_{5} + 3\alpha_{6} + 2\alpha_{7} + \alpha_{8} - \delta$ .

There are one fixed manifold of dimension 1 and eight fixed points of dimension 0 as show in table 15. Again the fixed manifold corresponds to the simple module with dominant weight of  $V_{-6}(E_8)$ , while fixed points correspond to other simple modules [87].

$G_{2}$  theory:  $L_{-2}(G_2)\leftrightarrow \mathcal{M}_{Hit}((\hat{D}_4,\mathbb{Z}_3),\frac{1}{6},f^{\vee} = princaipal)$ . The set of real affine roots of the twisted affine Lie algebra  $^3 D_4$  is  $\hat{\Delta}^{\vee} = \Phi_{s}^{re}\cup \Phi_{l}^{re}$  with

$$
\Phi_ {s} ^ {r e} = \left\{\alpha + \frac {r}{3} \delta \mid r \in \mathbb {Z}, \alpha \in \Phi_ {s} ^ {0} \right\},
$$

$$
\Phi_ {l} ^ {r e} = \left\{\alpha + r \delta \mid r \in \mathbb {Z}, \alpha \in \Phi_ {l} ^ {0} \right\}. \tag {A.7}
$$

Here  $\Phi_0$  denotes the root system of  $G_{2}$  which is also the finite part of  $^3 D_4$

$$
\Phi_ {s} ^ {0} = \left\{\pm \left(\beta_ {1} - \beta_ {2}\right), \pm \left(\beta_ {2} - \beta_ {3}\right), \pm \left(\beta_ {1} - \beta_ {3}\right) \right\} = \left\{\pm \alpha_ {2}, \pm \left(\alpha_ {1} + 2 \alpha_ {2}\right), \pm \left(\alpha_ {1} + \alpha_ {2}\right) \right\},
$$

$$
\begin{array}{l} \Phi_ {l} ^ {0} = \{\pm (- 2 \beta_ {1} + \beta_ {2} + \beta_ {3}), \pm (\beta_ {1} - 2 \beta_ {2} + \beta_ {3}), \pm (\beta_ {1} + \beta_ {2} - 2 \beta_ {3}) \} = \\ = \left\{\pm \alpha_ {1}, \pm \left(\alpha_ {1} + 3 \alpha_ {2}\right), \pm \left(2 \alpha_ {1} + 3 \alpha_ {2}\right) \right\}. \tag {A.8} \\ \end{array}
$$

Here  $\beta_{1},\beta_{2},\beta_{3}$  are orthogonal basis, and the simple roots are  $\alpha_{1} = -2\beta_{1} + \beta_{2} + \beta_{3}$  and  $\alpha_{2} = \beta_{1} - \beta_{2}$ . The highest root is  $\theta_l = 2\alpha_1 + 3\alpha_2$ , and the highest short root is  $\theta_s = \alpha_1 + 2\alpha_2$ . The set

$$
L _ {\nu} = \left\{\alpha + l \delta \in \hat {\Delta} ^ {\vee} \mid \frac {1}{6} \alpha \left(\rho^ {\vee}\right) + l = 0 \right\}\rightarrow L _ {\nu} = \left\{\pm \left(\alpha_ {1} + \alpha_ {2} - \frac {1}{3} \delta\right)\right\} \tag {A.9}
$$

and the set  $S_{\nu}$  are

$$
S _ {\nu} = \left\{\alpha + l \delta \in \hat {\Delta} ^ {\vee} \mid \frac {1}{6} \alpha \left(\rho^ {\vee}\right) + l = \frac {1}{6} \right\}\rightarrow S _ {\nu} = \left\{\alpha_ {1}, \alpha_ {2}, - \theta_ {s} + \frac {2}{3} \delta , \theta_ {s} - \frac {1}{3} \delta , - \theta_ {l} + \delta , - \alpha_ {2} + \frac {1}{3} \delta \right\} \tag {A.10}
$$

One can then use the graphic method to find the affine Weyl group elements corresponding to fixed varieties. This fibre has one fixed variety of dimension 1 labelled by  $s_0$ , and two fixed varieties labelled by 1 and  $s_1s_0$  [46], and here  $s_0$  is given by the simple reflection of the affine root  $-\theta_s + \frac{1}{3}\delta$ . Assuming the bijection is still true in the non-admissible case, we conjecture that there are three simple modules of  $L_{-2}(G_2)$  with weights

$$
- 2 \Lambda_ {0}, \quad s _ {0}. (- 2 \Lambda_ {0}) = - \Lambda_ {2}, \quad \left(s _ {1} s _ {0}\right). (- 2 \Lambda_ {0}) = - 2 \Lambda_ {1}. \tag {A.11}
$$

It would be nice to check if this statement is true from VOA side.

SO(7) theory:  $L_{-2}(SO(7)) \leftrightarrow \mathcal{M}_{Hit}((A_5,\mathbb{Z}_2),\frac{1}{6},f^\vee = principal)$ . The set of real affine roots of the twisted Lie algebra  $^2\hat{A}_5$  is  $\hat{\Delta}^{\vee} = \Phi_s^{re} \cup \Phi_l^{re}$  with

$$
\Phi_ {s} ^ {r e} = \left\{\alpha + \frac {n}{2} \delta \mid n \in \mathbb {Z}, \alpha \in \Phi_ {s} ^ {0} \right\},
$$

$$
\Phi_ {l} ^ {r e} = \left\{\alpha + n \delta \mid n \in \mathbb {Z}, \alpha \in \Phi_ {l} ^ {0} \right\}. \tag {A.12}
$$

Here the set of finite roots  $\Phi_s^0\cup \Phi_l^0$  is that of  $C_3$  Lie algebra:

$$
\begin{array}{l} \Phi_ {s} ^ {0} = \{\pm \beta_ {i} \pm \beta_ {j}, i, j = 1, 2, 3 i \neq j \} \\ = \left\{\pm a _ {1} ^ {\vee}, \pm a _ {2} ^ {\vee}, \pm \left(a _ {2} ^ {\vee} + a _ {3} ^ {\vee}\right), \pm \left(a _ {1} ^ {\vee} + a _ {2} ^ {\vee} + a _ {3} ^ {\vee}\right), \pm \left(a _ {1} ^ {\vee} + a _ {2} ^ {\vee}\right), \pm \left(a _ {1} ^ {\vee} + 2 a _ {2} ^ {\vee} + a _ {3} ^ {\vee}\right) \right\}, \\ \end{array}
$$

$$
\begin{array}{l} \Phi_ {l} ^ {0} = \{\pm 2 \beta_ {i}, \quad i = 1, 2, 3 \} \\ = \left\{\pm \alpha_ {3} ^ {\vee}, \pm \left(2 \alpha_ {2} ^ {\vee} + \alpha_ {3} ^ {\vee}\right), \pm \left(2 \alpha_ {1} ^ {\vee} + 2 \alpha_ {2} ^ {\vee} + \alpha_ {3} ^ {\vee}\right) \right\}. \tag {A.13} \\ \end{array}
$$

Here  $\beta_{i}$  are the orthogonal basis. The set of simple roots are

$$
\alpha_ {1} ^ {\vee} = \beta_ {1} - \beta_ {2}, \quad \alpha_ {2} ^ {\vee} = \beta_ {2} - \beta_ {3}, \quad \alpha_ {3} ^ {\vee} = 2 \beta_ {3}, \tag {A.14}
$$

which are simple coroots of  $B_{3}$ . The highest root is  $\theta_{l}^{\vee} = 2\alpha_{1}^{\vee} + 2\alpha_{2}^{\vee} + \alpha_{3}^{\vee}$ , and the highest short root is  $\theta_{s}^{\vee} = \alpha_{1}^{\vee} + 2\alpha_{2}^{\vee} + \alpha_{3}^{\vee}$ .

The set  $L_{\nu}$  is

$$
L _ {\nu} = \left\{\alpha + l \delta \in \hat {\Delta} \mid \frac {1}{6} \alpha (\rho) + l = 0 \right\}\rightarrow L _ {\nu} = \left\{\pm \left(\alpha_ {1} ^ {\vee} + \alpha_ {2} ^ {\vee} + \alpha_ {3} ^ {\vee} - \frac {1}{2} \delta\right)\right\} \tag {A.15}
$$

and the set  $S_{\nu}$  is

$$
S _ {\nu} = \{\alpha + l \delta \in \hat {\Delta} \mid \frac {1}{6} \alpha (\rho) + l = \frac {1}{6} \} \rightarrow
$$

$$
S _ {\nu} = \left\{\alpha_ {1} ^ {\vee}, \alpha_ {2} ^ {\vee}, \alpha_ {3} ^ {\vee}, \theta_ {s} ^ {\vee} - \frac {1}{2} \delta , - \theta_ {l} ^ {\vee} + \delta , - \left(\alpha_ {1} ^ {\vee} + \alpha_ {2} ^ {\vee}\right) + \frac {1}{2} \delta , - \left(\alpha_ {2} ^ {\vee} + \alpha_ {3} ^ {\vee}\right) + \frac {1}{2} \delta \right\} \tag {A.16}
$$

There is one dimension 1 fixed variety labelled by  $s_0$ , and three dimensional 0 fixed points labelled by 1,  $s_1s_0$  and  $s_3s_0$ . We predict that the corresponding simple modules have weights

$$
- 2 \Lambda_ {0}, s _ {0}. (- 2 \Lambda_ {0}) = - \Lambda_ {2}, (s _ {1} s _ {0}). (- 2 \Lambda_ {0}) = - 2 \Lambda_ {1}, (s _ {3} s _ {0}). (- 2 \Lambda_ {0}) = - 2 \Lambda_ {3}. \tag {A.17}
$$

$F_{4}$  theory:  $L_{-3}(F_4)\leftrightarrow \mathcal{M}_{Hit}((E_6,\mathbb{Z}_2),\frac{1}{12},f^{\vee} = principal)$ . The set of real affine roots of the twisted Lie algebra  ${}^{2}\hat{E}_{6}$  is  $\hat{\Delta}^{\vee} = \Phi_{s}^{re}\cup \Phi_{l}^{re}$  with

$$
\Phi_ {s} ^ {r e} = \left\{\alpha + \frac {n}{2} \delta \mid n \in \mathbb {Z}, \alpha \in \Phi_ {s} ^ {0} \right\},
$$

$$
\Phi_ {l} ^ {r e} = \left\{\alpha + n \delta \mid n \in \mathbb {Z}, \alpha \in \Phi_ {l} ^ {0} \right\}. \tag {A.18}
$$

Here the set of finite roots  $\Phi_s^0\cup \Phi_l^0$  is that of  $F_{4}$  Lie algebra. The simple roots are:

$$
\alpha_ {1} = \beta_ {1} - \beta_ {2}, \alpha_ {2} = \beta_ {2} - \beta_ {3}, \alpha_ {3} = \beta_ {3}, \alpha_ {4} = \frac {1}{2} (- \beta_ {1} - \beta_ {2} - \beta_ {3} + \beta_ {4}). \tag {A.19}
$$

Here  $\beta_{i}$  are orthogonal basis. The set of roots are

$$
\Phi_ {s} = \left\{\pm \alpha_ {3}, \pm \left(\alpha_ {2} + \alpha_ {3}\right), \pm \left(\alpha_ {1} + \alpha_ {2} + \alpha_ {3}\right), \pm \left(\alpha_ {1} + 2 \alpha_ {2} + 3 \alpha_ {3} + 2 \alpha_ {4}\right) \right\}
$$

$$
\cup \left\{\pm \left(\alpha_ {2} + 2 \alpha_ {3} + \alpha_ {4}\right), \pm \left(\alpha_ {1} + \alpha_ {2} + \alpha_ {3} + \alpha_ {4}\right), \pm \left(\alpha_ {1} + \alpha_ {2} + 2 \alpha_ {3} + \alpha_ {4}\right), \pm \left(\alpha_ {2} + \alpha_ {3} + \alpha_ {4}\right) \right\}
$$

$$
\cup \left\{\pm \left(\alpha_ {3} + \alpha_ {4}\right), \pm \left(\alpha_ {1} + 2 \alpha_ {2} + 2 \alpha_ {3} + \alpha_ {4}\right), \pm \left(\alpha_ {4}\right), \pm \left(\alpha_ {1} + 2 \alpha_ {2} + 3 \alpha_ {3} + \alpha_ {4}\right) \right\},
$$

$$
\Phi_ {l} = \left\{\pm \alpha_ {1}, \pm \left(\alpha_ {1} + 2 \alpha_ {2} + 2 \alpha_ {3}\right), \pm \left(\alpha_ {1} + \alpha_ {2}\right), \pm \left(\alpha_ {1} + \alpha_ {2} + 2 \alpha_ {3}\right), \pm \left(\alpha_ {1} + 2 \alpha_ {2} + 2 \alpha_ {3}\right) \right.
$$

$$
\cup \left\{\pm \left(2 \alpha_ {1} + 3 \alpha_ {2} + 4 \alpha_ {3} + 2 \alpha_ {4}\right), \pm \alpha_ {2}, \pm \left(\alpha_ {2} + 2 \alpha_ {3}\right), \pm \left(\alpha_ {1} + \alpha_ {2} + 2 \alpha_ {3} + 2 \alpha_ {4}\right) \right\}
$$

$$
\cup \left\{\pm \left(\alpha_ {1} + 3 \alpha_ {2} + 4 \alpha_ {3} + 2 \alpha_ {4}\right), \pm \left(\alpha_ {1} + 2 \alpha_ {2} + 2 \alpha_ {3} + 2 \alpha_ {4}\right), \pm \left(\alpha_ {1} + 2 \alpha_ {2} + 4 \alpha_ {3} + 2 \alpha_ {4}\right) \right\}. \tag {A.20}
$$

The highest root root is  $\theta_{l} = 2\alpha_{1} + 3\alpha_{2} + 4\alpha_{3} + 2\alpha_{4}$ , and the highest short root is  $\theta_{s} = \alpha_{1} + 2\alpha_{2} + 3\alpha_{3} + 2\alpha_{4}$ . The set  $L_{\nu}$  is

$$
L _ {\nu} = \{\alpha + l \delta \in \hat {\Delta} ^ {\vee} \mid \frac {1}{1 2} \alpha (\rho^ {\vee}) + l = 0 \} \to L _ {\nu} = \{\pm (\alpha_ {1} + 2 \alpha_ {2} + 2 \alpha_ {3} + \alpha_ {4} - \frac {1}{2} \delta) \}, (A. 2 1)
$$

and the set  $S_{\nu}$  is

$$
\begin{array}{l} S _ {\nu} = \{\alpha + l \delta \in \hat {\Delta} ^ {\vee} \mid \frac {1}{1 2} \alpha (\rho^ {\vee}) + l = \frac {1}{1 2} \} \to \\ S _ {\nu} = \{\alpha_ {1}, \alpha_ {2}, \alpha_ {3}, \alpha_ {4}, (\alpha_ {1} + 2 \alpha_ {2} + 3 \alpha_ {3} + \alpha_ {4}) - \frac {1}{2} \delta , - \theta_ {l} + \delta , \\ - \left(\alpha_ {1} + \alpha_ {2} + 2 \alpha_ {3} + \alpha_ {4}\right) + \frac {1}{2} \delta \}. \tag {A.22} \\ \end{array}
$$

The fixed variety of dimension 1 is labelled by  $s_4 \vee s_0 \vee$ , while fixed points are labelled by 1,  $s_0 \vee$ ,  $s_2 \vee s_4 \vee s_0 \vee$ ,  $s_1 \vee s_2 \vee s_4 \vee s_0 \vee$  with  $s_i \vee$  being the reflection of the simple root  $\alpha_i^\vee$  of  $^2 E_6$ . Assuming the correspondence between fixed varieties and simple modules still holds, we predict that the simple modules are

$$
1. (- 3 \Lambda_ {0}) = - 3 \Lambda_ {0}, s _ {0}. (- 3 \Lambda_ {0}) = - 2 \Lambda_ {1} - \Lambda_ {0}, (s _ {1} s _ {0}). (- 3 \Lambda_ {0}) = - 3 \Lambda_ {2}, \tag {A.23}
$$

$$
(s _ {3} s _ {1} s _ {0}). (- 3 \Lambda_ {0}) = - 2 \Lambda_ {3} + \Lambda_ {4}, (s _ {4} s _ {3} s _ {1} s _ {0}). (- 3 \Lambda_ {0}) = - 3 \Lambda_ {4}.
$$

There is a flip from 1,2,3,4 to 4,3,2,1 because our labelling of roots in  $^{2}\hat{E}_{6}$  is such that short roots are still  $\alpha_{3}$  and  $\alpha_{4}$  so that the node of  $\alpha_{0}$  is connected to the node of  $\alpha_{4}$  in the Dynkin diagram of  $^{2}\hat{E}_{6}$ .

# B Twisted theory

In this section we give an example when the VOA side is the affine vertex algebra of a non-simply laced AKM. On the fibre side we need to consider the twisted affine Lie algebra.

Example B.1.  $L_{-(2l - 1) + \frac{2l - 1}{u}}(B_l)\leftrightarrow \mathcal{M}_{Hit}((A_{2l - 1},\mathbb{Z}_2),\frac{u}{2(2l - 1)},f^\vee = principal)$ . On the VOA side, the simple roots of  $B_{l}$  in orthogonal basis are

$$
\Delta_ {+} = \left\{\alpha_ {1} = \beta_ {1} - \beta_ {2}, \dots , \alpha_ {l - 1} = \beta_ {l - 1} - \beta_ {l}, \alpha_ {l} = \beta_ {l} \right\}, \tag {B.1}
$$

and the highest long root  $\theta = \beta_{1} + \beta_{2}$ . Therefore, following the definition of  $S_{u}$ , we have

$$
\begin{array}{l} S _ {u} = \left\{\alpha_ {1} ^ {\vee}, \dots , \alpha_ {l} ^ {\vee}, - \theta_ {l} ^ {\vee} + u \delta \right\} \tag {B.2} \\ = \left\{\beta_ {1} - \beta_ {2}, \dots , \beta_ {l - 1} - \beta_ {l}, 2 \beta_ {l}, - \beta_ {1} - \beta_ {2} + u \delta \right\}. \\ \end{array}
$$

The set of real roots of  $\hat{B}_l$  is

$$
\hat {\Delta} = \left\{\alpha + n \delta \mid \alpha \in \Delta , n \in \mathbb {Z} \right\}. \tag {B.3}
$$

Here  $\Delta$  is the set of roots of  $B_{l}$ .

One the fibre side, we need to consider the twisted affine Lie algebra  $^2\hat{A}_{2l - 1}$  which is the Langlands dual of  $\hat{B}_l$ . The set of real roots of  $^2\hat{A}_{2l - 1}$  is  $\hat{\Delta}^C = \Phi_s^{re}\cup \Phi_l^{re}$  with

$$
\Phi_ {s} ^ {r e} = \left\{\alpha + \frac {n}{2} \delta \mid \alpha \in \Phi_ {s} ^ {0}, n \in \mathbb {Z} \right\},
$$

$$
\Phi_ {l} ^ {r e} = \left\{\alpha + n \delta \mid \alpha \in \Phi_ {l} ^ {0}, n \in \mathbb {Z} \right\}. \tag {B.4}
$$

Here  $\Phi^0$  is the set of roots of  $C_l$  which is the finite part of  ${}^2\hat{A}_{2l - 1}$ . In orthogonal basis

$$
\Phi_ {l} ^ {0} = \left\{\pm 2 \beta_ {i} \right\}, \quad \Phi_ {s} ^ {0} = \left\{\pm \beta_ {i} \pm \beta_ {j}, i, j = 1, \dots , l, i \neq j \right\}. \tag {B.5}
$$

The set of simple roots of  $C_l$  are

$$
\left\{\alpha_ {1} ^ {\vee} = \beta_ {1} - \beta_ {2}, \alpha_ {2} ^ {\vee} = \beta_ {2} - \beta_ {3}, \dots , \alpha_ {l - 1} ^ {\vee} = \beta_ {l - 1} - \beta_ {l}, \alpha_ {l} ^ {\vee} = 2 \beta_ {l} \right\}. \tag {B.6}
$$

By definition there is a natural bijection between  $\hat{\Delta}^{\vee}$  and  $\hat{\Delta}^{C}$  which simply sends  $\alpha + n\delta \in \hat{\Delta}^{\vee}$  into  $\alpha + \frac{n}{2}\delta \in \hat{\Delta}^{C22}$ .

To find the fixed points, we compute the following two sets

$$
L _ {\nu} = \left\{\alpha + l \delta \in \hat {\Delta} ^ {C} \mid \frac {u}{2 (2 l - 1)} \alpha \left(\rho^ {\vee}\right) + l = 0 \right\}\rightarrow L _ {\nu} = \emptyset . \tag {B.7}
$$

and

$$
S _ {\nu} = \left\{ \right.\alpha + l \delta \in \hat {\Delta} \mid \frac {u}{2 (2 l - 1)} \alpha \left(\rho^ {\vee}\right)\left. \right) + l = \frac {u}{2 (2 l - 1)} \} \rightarrow S _ {\nu} = \left\{\alpha_ {1} ^ {\vee}, \alpha_ {2} ^ {\vee}, \dots , \alpha_ {l} ^ {\vee}, - \theta^ {\vee} + \frac {u}{2} \delta \right\}. \tag {B.8}
$$

Here  $\theta^{\vee} = \beta_{1} + \beta_{2}$  is the highest short root of  $C_l$  which is Langlands dual to the highest long root of  $B_{l}$  and has height  $2l - 2$ .

We see that the bijection between  $\hat{\Delta}$  and  $\hat{\Delta}^C$  also sends  $S_u^\vee$  into  $S_{\nu}$ . Also using the fact that both the affine Weyl group and extended Weyl group of  $\hat{B}_l$  and  ${}^2\hat{A}_{2l - 1}$  are the same. One can see the natural isomorphisms between admissible modules and fixed points.

# References

[1] B.R. Greene and M.R. Plesser, Duality in Calabi-Yau Moduli Space, Nucl. Phys. B 338 (1990) 15.  
[2] P. Candelas, X.C. De La Ossa, P.S. Green and L. Parkes, A Pair of Calabi-Yau manifolds as an exactly soluble superconformal theory, Nucl. Phys. B 359 (1991) 21.  
[3] K.A. Intriligator and N. Seiberg, Mirror symmetry in three-dimensional gauge theories, Phys. Lett. B 387 (1996) 513 [hep-th/9607207].  
[4] T. Braden, A. Licata, N. Proudfoot and B. Webster, Gale duality and Koszul duality, Advances in Mathematics 225 (2010) 2002.  
[5] T. Braden, N. Proudfoot and B. Webster, Quantizations of conical symplectic resolutions I: local and global structure, 1208.3863.

[6] T. Braden, A. Licata, N. Proudfoot and B. Webster, Quantizations of conical symplectic resolutions II: category  $\mathcal{O}$  and symplectic duality, 1407.0964.  
[7] M. Bullimore, T. Dimofte, D. Gaiotto and J. Hilburn, Boundaries, Mirror Symmetry, and Symplectic Duality in 3d  $\mathcal{N} = 4$  Gauge Theory, JHEP 10 (2016) 108 [1603.08382].  
[8] N. Seiberg and E. Witten, Gauge dynamics and compactification to three-dimensions, in Conference on the Mathematical Beauty of Physics (In Memory of C. Itzykson), pp. 333-366, 6, 1996 [hep-th/9607163].  
[9] L. Fredrickson and A. Neitzke, From  $S^1$ -fixed points to  $\mathcal{W}$ -algebra representations, 1709.06142.  
[10] L. Fredrickson, D. Pei, W. Yan and K. Ye, *Argyres-Douglas Theories*, Chiral Algebras and Wild Hitchin Characters, JHEP 01 (2018) 150 [1701.08782].  
[11] M. Dedushenko, S. Gukov, H. Nakajima, D. Pei and K. Ye, 3d TQFTs from Argyres-Douglas theories, J. Phys. A 53 (2020) 43LT01 [1809.04638].  
[12] C. Beem, M. Lemos, P. Liendo, W. Peelaers, L. Rastelli and B.C. van Rees, Infinite Chiral Symmetry in Four Dimensions, Commun. Math. Phys. 336 (2015) 1359 [1312.5344].  
[13] J. Song, D. Xie and W. Yan, Vertex operator algebras of Argyres-Douglas theories from M5-branes, JHEP 12 (2017) 123 [1706.01607].  
[14] C. Beem and L. Rastelli, Vertex operator algebras, Higgs branches, and modular differential equations, JHEP 08 (2018) 114 [1707.07679].  
[15] T. Arakawa, Chiral algebras of class  $\mathcal{S}$  and Moore-Tachikawa symplectic varieties, 1811.01577.  
[16] D. Xie, W. Yan and S.-T. Yau, Chiral algebra of the Argyres-Douglas theory from M5 branes, Phys. Rev. D 103 (2021) 065003 [1604.02155].  
[17] Y. Wang and D. Xie, Codimension-two defects and Argyres-Douglas theories from outer-automorphism twist in 6d (2,0) theories, Phys. Rev. D 100 (2019) 025001 [1805.08839].  
[18] D. Xie and W. Yan,  $W$  algebras, cosets and VOAs for 4d  $\mathcal{N} = 2$  SCFTs from M5 branes, JHEP 04 (2021) 076 [1902.02838].  
[19] D. Xie, General Argyres-Douglas Theory, JHEP 01 (2013) 100 [1204.2270].  
[20] Y. Wang and D. Xie, Classification of Argyres-Douglas theories from M5 branes, Phys. Rev. D 94 (2016) 065012 [1509.00847].  
[21] M. Buican and T. Nishinaka, On the superconformal index of Argyres-Douglas theories, J. Phys. A49 (2016) 015401 [1505.05884].  
[22] M. Buican and T. Nishinaka, *Argyres-Douglas theories*,  $S^1$  reductions, and topological symmetries, J. Phys. A49 (2016) 045401 [1505.06205].  
[23] C. Cordova and S.-H. Shao, Schur Indices, BPS Particles, and Argyres-Douglas Theories, JHEP 01 (2016) 040 [1506.00265].  
[24] M. Buican and T. Nishinaka, *Argyres-Douglas Theories*, the Macdonald Index, and an RG Inequality, JHEP 02 (2016) 159 [1509.05402].  
[25] J. Song, Superconformal indices of generalized Argyres-Douglas theories from 2d TQFT, JHEP 02 (2016) 045 [1509.06730].

[26] S. Cecotti, J. Song, C. Vafa and W. Yan, Superconformal Index, BPS Monodromy and Chiral Algebras, JHEP 11 (2017) 013 [1511.01516].  
[27] T. Nishinaka and Y. Tachikawa, On 4d rank-one  $\mathcal{N} = 3$  superconformal field theories, JHEP 09 (2016) 116 [1602.01503].  
[28] M. Buican and T. Nishinaka, Conformal Manifolds in Four Dimensions and Chiral Algebras, J. Phys. A49 (2016) 465401 [1603.00887].  
[29] C. Cordova, D. Gaiotto and S.-H. Shao, Infrared Computations of Defect Schur Indices, JHEP 11 (2016) 106 [1606.08429].  
[30] J. Song, Macdonald Index and Chiral Algebra, JHEP 08 (2017) 044 [1612.08956].  
[31] T. Creutzig, W-algebras for Argyres-Douglas theories, European Journal of Mathematics 3 (2017) 659 [1701.05926].  
[32] C. Cordova, D. Gaiotto and S.-H. Shao, Surface Defect Indices and 2d-4d BPS States, JHEP 12 (2017) 078 [1703.02525].  
[33] C. Cordova, D. Gaiotto and S.-H. Shao, Surface Defects and Chiral Algebras, JHEP 05 (2017) 140 [1704.01955].  
[34] M. Buican and T. Nishinaka, On Irregular Singularity Wave Functions and Superconformal Indices, JHEP 09 (2017) 066 [1705.07173].  
[35] M. Buican, Z. Laczko and T. Nishinaka,  $\mathcal{N} = 2$  S-duality revisited, JHEP 09 (2017) 087 [1706.03797].  
[36] M. Buican and Z. Laczko, Nonunitary Lagrangians and unitary non-Lagrangian conformal field theories, Phys. Rev. Lett. 120 (2018) 081601 [1711.09949].  
[37] J. Choi and T. Nishinaka, On the chiral algebra of Argyres-Douglas theories and  $S$ -duality, JHEP 04 (2018) 004 [1711.07941].  
[38] T. Creutzig, Logarithmic W-algebras and Argyres-Douglas theories at higher rank, JHEP 11 (2018) 188 [1809.01725].  
[39] T. Nishinaka, S. Sasa and R.-D. Zhu, On the Correspondence between Surface Operators in Argyres-Douglas Theories and Modules of Chiral Algebra, JHEP 03 (2019) 091 [1811.11772].  
[40] C. Beem, C. Meneghelli, W. Peelaers and L. Rastelli, VOAs and rank-two instanton SCFTs, Commun. Math. Phys. 377 (2020) 2553 [1907.08629].  
[41] P.N. Achar, An order-reversing duality map for conjugacy classes in Lusztig's canonical quotient, Transformation groups 8 (2003) 107.  
[42] P. Shan, D. Xie and W. Yan, Verlinde algebras for  $W$ -algebras and DAHA, in preparation.  
[43] V.G. Kac and M. Wakimoto, On rationality of  $W$ -algebras, Transformation Groups 13 (2008) 671.  
[44] V.G. Kac and M. Wakimoto, Modular invariant representations of infinite-dimensional Lie algebras and superalgebras, Proceedings of the National Academy of Sciences 85 (1988) 4956.  
[45] M. Varagnolo and E. Vasserot, Finite-dimensional representations of DAHA and affine Springer fibers: The spherical case, Duke Math. J. 146 (2009) 439.  
[46] A. Oblomkov and Z. Yun, Geometric representations of graded and rational Cherednik algebras, Advances in Mathematics 292 (2016) 601.

[47] I. Cherednik, Double Affine Hecke Algebras, Lecture note series, Cambridge University Press (2005).  
[48] S. Gukov, P. Koroteev, S. Nawata, D. Pei and I. Saberi, Branes and DAHA Representations, 2206.03565.  
[49] C. Kozcaz, S. Shakirov and W. Yan, *Argyres-Douglas theories*, modularity of minimal models and refined Chern-Simons, Adv. Theor. Math. Phys. **26** (2022) 643 [1801.08316].  
[50] Y. Zhu, Modular invariance of characters of vertex operator algebras, Journal of the American Mathematical Society 9 (1996) 237.  
[51] P. Boalch, Irregular connections and Kac-Moody root systems, 0806.1050.  
[52] F. Benini, Y. Tachikawa and D. Xie, Mirrors of 3d Sicilian theories, JHEP 09 (2010) 063 [1007.0992].  
[53] D. Xie, 3d mirror for Argyres-Douglas theories, 2107.05258.  
[54] A. De Sole and V.G. Kac, Finite vs affine  $W$ -algebras, Japanese Journal of Mathematics 1 (2006) 137.  
[55] S. Cecotti, A. Neitzke and C. Vafa, R-twisting and  $4d/2d$  correspondences, 1006.3435.  
[56] N. Seiberg and E. Witten, Electric-magnetic duality, monopole condensation, and confinement in  $N = 2$  supersymmetric Yang-Mills theory, Nucl. Phys. B426 (1994) 19 [hep-th/9407087].  
[57] N. Seiberg and E. Witten, Monopoles, duality and chiral symmetry breaking in  $N = 2$  supersymmetric QCD, Nucl. Phys. B431 (1994) 484 [hep-th/9408099].  
[58] D. Gaiotto,  $N = 2$  dualities, JHEP 08 (2012) 034 [0904.2715].  
[59] D. Gaiotto, G.W. Moore and A. Neitzke, Wall-crossing, Hitchin systems, and the WKB approximation, Adv. Math. 234 (2013) 239 [0907.3987].  
[60] M. Reeder, P. Levy, J.-K. Yu and B.H. Gross, Gradings of positive rank on simple Lie algebras, Transformation Groups 17 (2012) 1123.  
[61] D. Xie and S.-T. Yau, 4d  $N = 2$  SCFT and singularity theory Part I: Classification, 1510.01324.  
[62] O. Chacaltana, J. Distler and Y. Tachikawa, Nilpotent orbits and codimension-two defects of 6d  $N = (2,0)$  theories, Int. J. Mod. Phys. A 28 (2013) 1340006 [1203.2930].  
[63] B. Li, D. Xie and W. Yan, On low rank 4d  $\mathcal{N} = 2$  SCFTs, JHEP 05 (2023) 132 [2212.03089].  
[64] R. Bezrukavnikov, P.B. Alvarez, M. McBreen and Z. Yun, Non-abelian Hodge moduli spaces and homogeneous affine Springer fibers, 2209.14695.  
[65] B. Chen, D. Xie, S.-T. Yau, S.S.T. Yau and H. Zuo,  $4D\mathcal{N} = 2$  SCFT and singularity theory. Part II: complete intersection, Adv. Theor. Math. Phys. 21 (2017) 121 [1604.07843].  
[66] Y. Wang, D. Xie, S.S.T. Yau and S.-T. Yau, 4d  $\mathcal{N} = 2$  SCFT from complete intersection singularity, Adv. Theor. Math. Phys. 21 (2017) 801 [1606.06306].  
[67] B. Chen, D. Xie, S.S.T. Yau, S.-T. Yau and H. Zuo,  $4d\mathcal{N} = 2$  SCFT and singularity theory Part III: Rigid singularity, Adv. Theor. Math. Phys. 22 (2018) 1885 [1712.00464].

[68] D. Xie and K. Ye, *Argyres-Douglas matter and S-duality: Part II*, JHEP 03 (2018) 186 [1711.06684].  
[69] D. Kazhdan and G. Lusztig, Fixed point varieties on affine flag manifolds, *Israel Journal of Mathematics* 62 (1988) 129.  
[70] R. Bezrukavnikov, The dimension of the fixed point set on affine flag manifolds, Mathematical Research Letters 3 (1996) 185.  
[71] C. Beem, W. Peelaers, L. Rastelli and B.C. van Rees, Chiral algebras of class  $S$ , JHEP 1505 (2015) 020 [1408.6522].  
[72] D. Xie and W. Yan,  $4d\mathcal{N} = 2$  SCFTs and lisse W-algebras, JHEP 04 (2021) 271 [1910.02281].  
[73] V.G. Kac and M. Wakimoto, Modular and conformal invariance constraints in representation theory of affine algebras, Adv. Math. 70 (1988) 156.  
[74] T. Arakawa, Rationality of admissible affine vertex algebras in the category  $O$ , Duke Mathematical Journal 165 (2016).  
[75] J. de Boer and T. Tjin, The Relation between quantum  $W$  algebras and Lie algebras, Commun. Math. Phys. 160 (1994) 317 [hep-th/9302006].  
[76] V. Kac, S.-S. Roan and M. Wakimoto, Quantum reduction for affine superalgebras, Commun. Math. Phys. 241 (2003) 307.  
[77] D.H. Collingwood and W.M. McGovern, Nilpotent orbits in semisimple Lie algebra: an introduction, CRC Press (1993).  
[78] E. Frenkel, V. Kac and M. Wakimoto, Characters and fusion rules for  $W$  algebras via quantized Drinfeld-Sokolov reductions, Commun. Math. Phys. 147 (1992) 295.  
[79] T. Arakawa, Representation theory of  $W$ -algebras, II: Ramond twisted representations, 0802.1564.  
[80] T. Arakawa, Rationality of  $W$ -algebras: principal nilpotent cases, Annals of Mathematics 182 (2012).  
[81] T. Arakawa and J. van Ekeren, Rationality and Fusion Rules of Exceptional W-Algebras, 1905.11473.  
[82] J. Fasquel, Rationality of the exceptional  $W$ -algebras  $W_{k}(\mathfrak{sp}_{4},f_{\text{subreg}})$  associated with subregular nilpotent elements of  $\mathfrak{sp}_4$ , Commun. Math. Phys. 390 (2022) 33.  
[83] N.J. Hitchin, The self-duality equations on a Riemann surface, Proceedings of the London Mathematical Society 3 (1987) 59.  
[84] S. Gukov and E. Witten, Gauge Theory, Ramification, And The Geometric Langlands Program, hep-th/0612073.  
[85] R. Carter and R.W. Carter, Lie algebras of finite and affine type, no. 96, Cambridge University Press (2005).  
[86] O. Perse, A note on representations of some affine vertex algebras of type  $D$ , Glasnik matematicki 48 (2013) 81 [1205.3003].  
[87] T. Arakawa and A. Moreau, Joseph Ideals and Lisse Minimal  $W$ -algebras, J. Inst. Math. Jussieu 17 (2018) 397 [1506.00710].  
[88] N. Bourbaki, Groupes de Lie, Springer (2006).

[89] A. Oblomkov and Z. Yun, The cohomology ring of certain compactified Jacobians, 1710.05391.  
[90] T. Arakawa and K. Kawasetsu, Quasi-lisse vertex algebras and modular linear differential equations, in Lie Groups, Geometry, and Representation Theory, pp. 41-57, Springer (2018).  
[91] H. Zheng, Y. Pan and Y. Wang, Surface defects, flavored modular differential equations, and modularity, Phys. Rev. D 106 (2022) 105020 [2207.10463].  
[92] D. Xie and W. Yan, Schur sector of Argyres-Douglas theory and  $W$ -algebra, SciPost Phys. 10 (2021) 080 [1904.09094].  
[93] E. Gorsky, Arc spaces and DAHA representations, Selecta Mathematica 19 (2013) 125.  
[94] T. Hikita, An algebro-geometric realization of the cohomology ring of Hilbert scheme of points in the affine plane, International Mathematics Research Notices 2017 (2017) 2538.  
[95] T. Arakawa, Representation theory of  $W$ -algebras and Higgs branch conjecture, in International Congress of Mathematicians, pp. 1261-1278, 2018 [1712.07331].  
[96] I. Losev, L. Mason-Brown and D. Matvieievsky, Unipotent Ideals and Harish-Chandra Bimodules, 2108.03453.  
[97] T. Arakawa, Associated varieties of modules over Kac-Moody algebras and  $C_2$ -cofiniteness of  $W$ -algebras, Int. Math. Res. Not. IMRN (2015) 11605.  
[98] D. Gaiotto and E. Witten, S-Duality of Boundary Conditions In  $N = 4$  Super Yang-Mills Theory, Adv. Theor. Math. Phys. 13 (2009) 721 [0807.3720].  
[99] M. Lemos and W. Peelaers, Chiral Algebras for Trinion Theories, JHEP 02 (2015) 113 [1411.3252].  
[100] T. Hausel and F. Rodriguez-Villegas, Mixed Hodge polynomials of character varieties: with an appendix by Nicholas M. Katz, Inventiones mathematicae 174 (2008) 555.  
[101] D. Xie, Pseudo-periodic map and classification of theories with eight supercharges, 2304.13663.  
[102] S.A. Cherkis, Instantons on Gravitons, Commun. Math. Phys. 306 (2011) 449 [1007.0044].  
[103] S.A. Cherkis and R.S. Ward, Moduli of Monopole Walls and Amoebas, JHEP 05 (2012) 090 [1202.1294].  
[104] K.A. Intriligator, Compactified little string theories and compact moduli spaces of vacua, Phys. Rev. D 61 (2000) 106005 [hep-th/9909219].
# 1 Non-vacuum module of W algebra at boundary admissible level

# 1.1 Argyres–Douglas theories and associated VOAs

In this paper, we focus on Argyres–Douglas (AD) theories corresponding to $\mathcal { W }$ -algebras at boundary admissible level

$$
k _ {F} = - h ^ {\vee} + \frac {h ^ {\vee}}{q}, \quad (p, q) = 1, \tag {1}
$$

These AD theories admit a class $\boldsymbol { S }$ realization in terms of an irregular puncture characterized by the Higgs field

$$
\Phi (z) = \left(\frac {T _ {k}}{z ^ {2 + \frac {k}{b}}} + \sum_ {- b \leq l <   k} \frac {T _ {l}}{z ^ {2 + \frac {l}{b}}} + \dots\right) d z, q = b + k. \tag {2}
$$

The type of irregular puncture is labeled by the rational number $\textstyle \nu = 1 + { \frac { k } { b } } = { \frac { u } { m } }$ , where the allowed values of $m$ for a simple Lie algebra $\mathfrak { g }$ are listed in Table 1 [].

Table 1: Regular number $m$ for simple Lie algebra   

<table><tr><td>g</td><td>m</td></tr><tr><td>An</td><td>n+1</td></tr><tr><td>Dn</td><td>m even, 2n-2m odd
m even, 2n/m even</td></tr><tr><td>E6</td><td>12, 9, 6, 3</td></tr><tr><td>E7</td><td>18, 14, 6, 2</td></tr><tr><td>E8</td><td>2, 3, 5, 6, 10, 15, 30
4, 8, 12, 24
20</td></tr></table>

In addition to the irregular data, one may also introduce a regular puncture labeled by a nilpotent orbit $f$ . The resulting AD theory is therefore specified by

$$
(J ^ {b} [ k ], f). \tag {3}
$$

We first consider the AD theory with only an irregular puncture $J ^ { b } [ k ]$ . This theory corresponds to the affine Kac–Moody (AKM) algebra $L _ { - k _ { F } } ( { \mathfrak { g } } )$ at boundary admissible level. The boundary admissible weights are given by []

$$
\Lambda = \left(t _ {\beta} y\right). \left(k _ {F} \Lambda_ {0}\right), \tag {4}
$$

where $\beta \in Q ^ { * }$ and $y \in W$ satisfy $( t _ { \beta } y ) \hat { \Pi } _ { u } \subset \hat { \Delta } _ { + }$ for

$$
\hat {\Pi} _ {u} = \left\{u \delta - \theta , \hat {\alpha} _ {1}, \dots , \hat {\alpha} _ {r} \right\}. \tag {5}
$$

The character of the vacuum module is []

$$
\left(\frac {\eta (u \tau)}{\eta (\tau)}\right) ^ {\frac {1}{2} (3 r - \dim \mathfrak {g})} \prod_ {\alpha \in \Delta_ {+}} \frac {\vartheta_ {1} (\alpha (z) , u \tau)}{\vartheta_ {1} (\alpha (z) , \tau)} \tag {6}
$$

while the character of a non-vacuum module is []

$$
e ^ {2 \pi i \left(\frac {h ^ {\vee}}{u} (z | \beta)\right)} q ^ {\frac {h ^ {\vee}}{2 u} | \beta | ^ {2}} \left(\frac {\eta (u \tau)}{\eta (\tau)}\right) ^ {\frac {1}{2} (3 r - \dim \mathfrak {g})} \prod_ {\alpha \in \Delta_ {+}} \frac {\vartheta_ {1} (y (\alpha) (z + \tau \beta) , u \tau)}{\vartheta_ {1} (\alpha (z) , \tau)}. \tag {7}
$$

The conformal dimension of $L ( \Lambda )$ is

$$
h _ {\Lambda} = \frac {(\Lambda , \Lambda + 2 \hat {\rho})}{2 (\kappa + h ^ {\vee})}. \tag {8}
$$

Closing the regular puncture corresponds to performing the quantum Drinfeld–Sokolov reduction, which produces a $W$ -algebra $W ^ { k _ { F } } ( { \mathfrak { g } } , f ) \ [ ]$ . This construction requires choosing an ${ \mathfrak { s l } } _ { 2 }$ -triple $( x , e , f )$ in $\mathfrak { g }$ , guaranteed by the Jacobson–Morozov theorem [], satisfying

$$
[ x, e ] = e, [ x, f ] = - f, [ e, f ] = 2 x \tag {9}
$$

The Lie algebra then decomposes into eigenspaces of ad $x$ ,

$$
\mathfrak {g} = \oplus \mathfrak {g} _ {j} \quad \mathfrak {g} _ {j} = \{[ x, g _ {j} ] = j g _ {j} \}. \tag {10}
$$

Under the quantum Drinfeld–Sokolov reduction, an admissible AKM module is mapped either to zero or to an admissible $\mathcal { W }$ -algebra module []

$$
H _ {f} (-): V _ {\kappa} (\mathfrak {g}) - \mathrm {m o d} \rightarrow W _ {\kappa} (\mathfrak {g}, f) - \mathrm {m o d}. \tag {11}
$$

The vacuum character of the W-algebra is given by

$$
(- i) ^ {| \Delta_ {+} |} q ^ {\frac {h ^ {\vee}}{2 u} | x | ^ {2}} \frac {\eta (u \tau) ^ {\frac {3}{2} r} - \frac {1}{2} \dim \mathfrak {g}}{\eta (\tau) ^ {\frac {3}{2} l - \frac {1}{2} \dim \left(\mathfrak {g} _ {0} + \mathfrak {g} _ {\frac {1}{2}}\right)}} \frac {\prod_ {\alpha \in \Delta_ {+}} - \vartheta_ {1} (\alpha (z - \tau x) , u \tau)}{\prod_ {\alpha \in \Delta_ {+} ^ {0}} - \vartheta_ {1} (\alpha (z) , \tau) \left(\prod_ {\alpha \in \Delta_ {\frac {1}{2}}} \vartheta_ {4} (\alpha (z) , \tau)\right) ^ {\frac {1}{2}}} \tag {12}
$$

where $\Delta _ { + } ^ { 0 } = \Delta _ { + } \cap \Delta _ { 0 }$ . The character of a non-vacuum $\mathcal { W }$ -algebra module takes the form

$$
\begin{array}{l} \operatorname {c h} _ {H (\Lambda)} (\tau , z) = (- i) ^ {| \Delta_ {+} |} q ^ {\frac {h ^ {\vee}}{2 u} | \beta - x | ^ {2}} e ^ {\frac {2 \pi i h ^ {\vee}}{u} (\beta | z)} \\ \times \frac {\eta (u \tau) ^ {\frac {3}{2} r - \frac {1}{2} \dim (\mathfrak {g} _ {0} + \mathfrak {g} _ {\frac {1}{2}})}}{\eta (\tau) ^ {\frac {3}{2} r - \frac {1}{2} \dim (\mathfrak {g} _ {0} + \mathfrak {g} _ {\frac {1}{2}})}} \frac {\prod_ {\alpha \in \Delta_ {+}} - \vartheta_ {1} (y (\alpha) (z + \tau \beta - \tau x) , u \tau)}{\prod_ {\alpha \in \Delta_ {+} ^ {0}} - \vartheta_ {1} (\alpha (z) , \tau) \left(\prod_ {\alpha \in \Delta_ {\frac {1}{2}}} \vartheta_ {4} (\alpha (z) , \tau)\right) ^ {\frac {1}{2}}}. \tag {13} \\ \end{array}
$$

Finally, the characters of the AKM algebra and the associated $W$ -algebra are related by

$$
(R _ {W} \mathrm {c h} _ {H (\Lambda)}) (\tau , z) = (\hat {R} \mathrm {c h} _ {L (\Lambda)}) (\tau , - \tau x + z, \frac {\tau}{2} (x | x)), \tag {14}
$$

where $H ( \Lambda )$ and $L ( \Lambda )$ denote $\mathcal { W }$ -algebra and AKM modules, respectively. The prefactors are

$$
\begin{array}{l} R _ {W} (\tau , z) = \eta (\tau) ^ {\frac {3}{2} l - \frac {1}{2} \dim \left(\mathfrak {g} _ {0} + \mathfrak {g} _ {1 / 2}\right)} \prod_ {\alpha \in \Delta_ {+} ^ {0}} - \vartheta_ {1} (\tau , \alpha (z)) \left(\prod_ {\alpha \in \Delta_ {1 / 2}} \vartheta_ {2} (\tau , \alpha (z))\right) ^ {1 / 2}, \tag {15} \\ \hat {R} (\tau , z) = (- i) ^ {| \Delta_ {+} |} \eta (\tau) ^ {\frac {1}{2} (3 \ell - \dim \mathfrak {g})} \prod_ {\alpha \in \Delta_ {+}} - \vartheta_ {1} (\tau , \alpha (z)). \\ \end{array}
$$

# 1.2 Modularity of W algebra

In this subsection, we review the modular properties of the $\mathcal { W }$ algebra at boundary admissible level. The general form of the character of a module associated with a W algebra or an AKM algebra is

$$
\mathcal {I} = \operatorname {T r} _ {\Lambda} q ^ {L _ {0} + c _ {4 d} / 2} \mathbf {y} ^ {\alpha}. \tag {16}
$$

Here the lowest eigenvalue of $L _ { 0 }$ defines the conformal dimension $h _ { \Lambda }$ , and $c _ { 4 d }$ denotes the central charge of the corresponding four-dimensional theory. For a W algebra at boundary admissible level, the associated four-dimensional central charge is given by

$$
\frac {- 1}{1 2} \left(\dim \mathfrak {g} _ {0} - \frac {1}{2} \dim \mathfrak {g} _ {\frac {1}{2}} - \frac {1 2}{\kappa + h ^ {\vee}} | \rho - (k + h ^ {\vee}) x | ^ {2}\right), \quad \kappa = - h ^ {\vee} + \frac {h ^ {\vee}}{h ^ {\vee} + k}. \tag {17}
$$

Let us first consider the AKM case. For a boundary admissible weight $\Lambda$ , the conformal dimension is

$$
h _ {\Lambda} = \frac {(\Lambda , \Lambda + 2 \hat {\rho})}{2 (\kappa + h ^ {\vee})}. \tag {18}
$$

Consequently, the leading power in the $q$ -expansion of the Schur index is

$$
h _ {\Lambda} + \frac {c _ {4 d}}{2}. \tag {19}
$$

The modular $\mathbb { T }$ and $\mathbb { S }$ matrices for two VOA weights $\Lambda = ( t _ { \beta } y ) \cdot ( \kappa \Lambda _ { 0 } )$ and $\Lambda ^ { \prime } = ( t _ { \beta ^ { \prime } } y ^ { \prime } ) \cdot ( \kappa \Lambda _ { 0 } )$ are given by

$$
\mathbb {T} _ {\Lambda , \Lambda^ {\prime}} = e ^ {2 \pi i \left(h _ {\Lambda} - \frac {c}{2 4}\right)} \delta_ {\Lambda , \Lambda^ {\prime}},
$$

$$
\mathbb {S} _ {\Lambda , \Lambda^ {\prime}} = \left| \frac {P ^ {\vee}}{u h ^ {\vee} Q ^ {\vee}} \right| ^ {- \frac {1}{2}} \epsilon \left(y y ^ {\prime}\right) \prod_ {\alpha \in \Delta_ {+}} \left(2 \sin \frac {\pi u (\rho , \alpha)}{h ^ {\vee}}\right) e ^ {- 2 \pi i \left(\left(\rho , \beta + \beta^ {\prime}\right) + \frac {h ^ {\vee} \left(\beta , \beta^ {\prime}\right)}{u}\right)}. \tag {20}
$$

As an explicit example, we consider ${ \mathfrak { s l } } _ { 3 }$ at level $\textstyle k = - 3 + { \frac { 3 } { 4 } }$ . The corresponding boundary admissible weights are summarized in Table 2 [].

Table 2: Admissible weight for $L _ { - 3 + \frac { 3 } { 4 } } ( \mathfrak { s l } _ { 3 } )$   

<table><tr><td>[tβy]</td><td>Λ</td><td>[tβy]</td><td>Λ</td></tr><tr><td>1</td><td>-9/4 Λ0</td><td>t-ω2</td><td>-3/2 Λ0 - 3/4 Λ2</td></tr><tr><td>t-2ω2</td><td>-3/4 Λ0 - 3/2 Λ2</td><td>t-3ω2</td><td>-9/4 Λ2</td></tr><tr><td>t-ω1</td><td>-3/2 Λ0 - 3/4 Λ1</td><td>t-ω1-ω2</td><td>-3/4 Λ0 - 3/4 Λ1 - 3/4 Λ2</td></tr><tr><td>t-ω1-2ω2</td><td>-3/4 Λ1 - 3/2 Λ2</td><td>t-2ω1</td><td>-3/4 Λ0 - 3/2 Λ1</td></tr><tr><td>t-2ω1-ω2</td><td>-3/2 Λ1 - 3/4 Λ2</td><td>t-3ω1</td><td>-9/4 Λ1</td></tr><tr><td>tω1+ω2sθ</td><td>1/4 Λ0 - 5/4 Λ1 - 5/4 Λ2</td><td>tω1+2ω2sθ</td><td>-1/2 Λ0 - 5/4 Λ1 - 1/2 Λ2</td></tr><tr><td>tω1+3ω2sθ</td><td>-5/4 Λ0 - 5/4 Λ1 + 1/4 Λ2</td><td>t2ω1+ω2sθ</td><td>-1/2 Λ0 - 1/2 Λ1 - 5/4 Λ2</td></tr><tr><td>t2ω1+2ω2sθ</td><td>-5/4 Λ0 - 1/2 Λ1 - 1/2 Λ2</td><td>t3ω1+ω2sθ</td><td>-5/4 Λ0 + 1/4 Λ1 - 5/4 Λ2</td></tr></table>

Using these data, the lowest powers appearing in the $q$ -expansion are

$$
h _ {\Lambda} + \frac {2}{2} = \left\{1, \frac {1}{4}, 0, \frac {1}{4}, \frac {1}{4}, - \frac {1}{4}, - \frac {1}{4}, 0, - \frac {1}{4}, \frac {1}{4}, - \frac {1}{4}, - \frac {1}{4}, \frac {1}{4}, - \frac {1}{4}, 0, \frac {1}{4} \right\}, \tag {21}
$$

which precisely matches the lowest dimensions appearing in the expansion of the corresponding Schur index. For this case, we can explicitly determine the modular $T$ and $S$ matrices, which are given by

$$
T = \left( \begin{array}{c c c c c c c c c c c c c c c} 1 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 \\ 0 & i & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 \\ 0 & 0 & 1 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 \\ 0 & 0 & 0 & i & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 \\ 0 & 0 & 0 & 0 & i & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 \\ 0 & 0 & 0 & 0 & 0 & - i & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 \\ 0 & 0 & 0 & 0 & 0 & 0 & - i & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 \\ 0 & 0 & 0 & 0 & 0 & 0 & 0 & 1 & 0 & 0 & 0 & 0 & 0 & 0 & 0 \\ 0 & 0 & 0 & 0 & 0 & 0 & 0 & - i & 0 & 0 & 0 & 0 & 0 & 0 & 0 \\ 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & i & 0 & 0 & 0 & 0 & 0 & 0 \\ 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & - i & 0 & 0 & 0 & 0 & 0 \\ 0 & 0 & 0 & 0 & 0 & - i \end{array} \right) \tag {22}
$$

and

$$
S = \left( \right.\begin{array}{c c c c c c c c c c c c c c c}\frac {1}{4}&\frac {1}{4}&\frac {1}{4}&\frac {1}{4}&\frac {1}{4}&\frac {1}{4}&\frac {1}{4}&\frac {1}{4}&\frac {1}{4}&- \frac {1}{4}&- \frac {1}{4}&- \frac {1}{4}&- \frac {1}{4}&- \frac {1}{4}&- \frac {1}{4}\\\frac {1}{4}&- \frac {1}{4}&\frac {1}{4}&- \frac {1}{4}&- \frac {i}{4}&\frac {i}{4}&- \frac {i}{4}&- \frac {1}{4}&\frac {1}{4}&\frac {i}{4}&- \frac {i}{4}&\frac {i}{4}&- \frac {1}{4}&\frac {1}{4}\\\frac {1}{4}&\frac {1}{4}&\frac {1}{4}&\frac {1}{4}&- \frac {1}{4}&- \frac {1}{4}&- \frac {1}{4}&\frac {1}{4}&\frac {1}{4}&- \frac {1}{4}&\frac {1}{4}&\frac {1}{4}&- \frac {1}{4}&- \frac {1}{4}\\\frac {1}{4}&- \frac {1}{4}&\frac {1}{4}&- \frac {1}{4}&\frac {i}{4}&- \frac {i}{4}&\frac {i}{4}&- \frac {1}{4}&\frac {1}{4}&- \frac {i}{4}&- \frac {i}{4}&- \frac {i}{4}&- \frac {1}{4}&\frac {i}{4}\\\frac {1}{4}&- \frac {i}{4}&- \frac {1}{4}&\frac {i}{4}&- \frac {1}{4}&\frac {i}{4}&\frac {1}{4}&\frac {1}{4}&- \frac {i}{4}&- \frac {1}{4}&\frac {i}{4}&- 1\\\frac {1}{4}&i\\2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 6.\\\frac {1}{4}&i\\- \frac {i}{4}&- \frac {1}{4}\\- \frac {1}{4}&- \frac {i}{4}\\- \frac {1}{4}&- \frac {i}{4}\\- \frac {1}{4}&- \frac {i}{4}\\- \frac {1}{4}&- \frac {i}{4}\\- \frac {1}{4}&- \frac {i}{4}\\- \frac {i}{4}&- \frac {i}{4}\\- \frac {i}{4}&- \frac {i}{4}\\- \frac {i}{4}&- \frac {i}{4}\\- \frac {i}{4}&- \frac {i}{4}\\- \frac {i}{4}&- \frac {i}{4}\\- \frac {i}{4}&- \frac {i}\text {(}\\- \frac {\text {(}}{2}) ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime } ^ {\prime }\end{array}, (2) _ {\mathrm {{S}}}
$$

which is exactly the one given by the formula (20), as expected.

# 1.3 Example: sl3 at level $\textstyle k = - 3 + { \frac { 3 } { 4 } }$

We now illustrate the example of ${ \mathfrak { g } } = { \mathfrak { s l } } _ { 3 }$ at level $\begin{array} { r } { k = - 3 + \frac { 3 } { 4 } } \end{array}$ . In this case, the vacuum character of the affine Kac–Moody algebra $L _ { - 3 + \frac { 3 } { 4 } } ( \mathfrak { s l } _ { 3 } )$ is given by

$$
\left(\frac {\eta (u \tau)}{\eta (\tau)}\right) ^ {- 1} \prod_ {\alpha \in \Delta_ {+}} \frac {\vartheta_ {1} (\alpha (z) , u \tau)}{\vartheta_ {1} (\alpha (z) , \tau)} \tag {24}
$$

The total number of simple modules is $u ^ { r } = 1 6$ .

We next introduce a regular puncture corresponding to the nilpotent orbit $f = \lfloor 2 , 1 \rfloor$ . After performing the quantum Drinfeld–Sokolov reduction, the admissible weights of the resulting $W$ -algebra are listed in Table 3.

Table 3: Admissible weights for $W ^ { - 3 + \frac { 3 } { 4 } } ( \mathfrak { s l } _ { 3 } , [ 2 , 1 ] )$   

<table><tr><td>[tβy]</td><td>Λ</td><td>[tβy]</td><td>Λ</td></tr><tr><td>1</td><td>-9/4 Λ0</td><td>t-ω2</td><td>-3/2 Λ0 - 3/4 Λ2</td></tr><tr><td>t-2ω2</td><td>-3/4 Λ0 - 3/2 Λ2</td><td>t-ω1</td><td>-3/2 Λ0 - 3/4 Λ1</td></tr><tr><td>t-ω1-ω2</td><td>-3/4 Λ0 - 3/4 Λ1 - 3/4 Λ2</td><td>t-2ω1</td><td>-3/4 Λ0 - 3/2 Λ1</td></tr><tr><td>tω1+ω2sθ</td><td>1/4 Λ0 - 5/4 Λ1 - 5/4 Λ2</td><td>tω1+2ω2sθ</td><td>-1/2 Λ0 - 5/4 Λ1 - 1/2 Λ2</td></tr><tr><td>tω1+3ω2sθ</td><td>-5/4 Λ0 - 5/4 Λ1 + 1/4 Λ2</td><td>t2ω1+ω2sθ</td><td>-1/2 Λ0 - 1/2 Λ1 - 5/4 Λ2</td></tr><tr><td>t2ω1+2ω2sθ</td><td>-5/4 Λ0 - 1/2 Λ1 - 1/2 Λ2</td><td>t3ω1+ω2sθ</td><td>-5/4 Λ0 + 1/4 Λ1 - 5/4 Λ2</td></tr></table>

# References
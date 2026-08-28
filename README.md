Да. За толкова голям и нетипичен repository пълният README лесно се превръща в лоша карта: или става прекалено дълъг, или неизбежно пропуска цели коридори като Maurer–Cartan, QGT, Berry, Onsager, Fréchet, Itakura–Saito, modular geometry, cyclotomic tower, Freudenthal, \(Cl(5,5)\), \(G_2\), и т.н.

По-силният избор е кратък, загадъчен, но честен README, който прави три неща: казва какво е това, предупреждава за frontier характера му и кани човека да търси сам.

GitHub repository-то вече е searchable. Имена на файлове, theorem names, imports, namespaces и code search са по-добър индекс от опит да се компресира целият DAG в началната страница. За този проект самото откриване на връзките е част от начина, по който той се чете.

Бих оставил нещо почти минимално:

# InfoGeometry

> *A living artifact of human–AI interaction.*
>
> An attempt to explore and formalize in Lean 4 structures spanning pure mathematics, theoretical physics, information geometry, operator algebras, exceptional algebra, thermodynamics, arithmetic, and formal theorem proving — and to discover the connections between them.
>
> Some corridors are established mathematics, some are formal experiments, and some are frontier conjectural bridges.
>
> Lean certifies the statements that are actually proved in the code. The larger interpretation remains open.
>
> Take with a pinch of salt.

This repository is not intended to be read linearly.

Search it.

Follow the imports.

Trace the theorem graph.

Ask why two apparently unrelated files exist in the same dependency corridor.

Use a large-context reasoning engine and interrogate the codebase.

There are many entrances:

$$
\mathbb O_s,\quad
G_2,\quad
Cl(3,3),\quad
Cl(5,5),\quad
\text{Freudenthal},\quad
\text{Maurer--Cartan},\quad
\text{Berry},\quad
\text{QGT},
$$

$$
\text{BKM},\quad
\text{Onsager},\quad
\text{Fréchet},\quad
\text{Itakura--Saito},\quad
\text{Metriplectic dynamics},\quad
\text{cyclotomic symmetry},\quad
\ldots
$$

The repository is searchable.

The proofs are the documentation.

The unresolved bridges are part of the map.

Find the Easter eggs.

Това вероятно е по-подходящо от „официален“ обзор.

И бих запазил точно идеята:

$$
\boxed{\text{The proofs are the documentation.}}
$$

За този repository тя е почти буквална. Един дълъг README ще остарява всеки път, когато се появи нов corridor. Краткият README може да остане верен, докато самият repository продължава да расте.
Exactly. That makes the case for a minimal README even stronger, because the repository is no longer just a mathematics/physics formalization; it also contains a parallel language-model and inference architecture layer.

Those concepts form another coherent corridor:

$$
\boxed{
\text{attention}
\to
\text{positional encoding}
\to
\text{routing}
\to
\text{forward/backward propagation}
\to
\text{Gibbs/KMS states}
\to
\text{log-scale variables}
\to
\text{Mellin spectral coordinates}
}
$$

and that corridor is structurally related to the rest rather than being an unrelated ML appendix.

The important correspondences are quite natural.

Attention is an operator-valued weighting mechanism:

$$
\operatorname{Attn}(Q,K,V)
=
\operatorname{softmax}\!\left(\frac{QK^\top}{\sqrt d}\right)V.
$$

The softmax weights are a finite Gibbs distribution:

$$
p_j
=
\frac{e^{\beta s_j}}{\sum_k e^{\beta s_k}},
$$

with inverse-temperature-like scale \(\beta\). So there is already a direct statistical-mechanical interpretation of attention.

Routing generalizes this from one Gibbs weighting to conditional selection between operator channels:

$$
x
\longmapsto
\sum_a r_a(x)\,T_a x,
\qquad
\sum_a r_a(x)=1.
$$

That fits very naturally with mixture coordinates, partition functions, and information geometry.

Positional encoding contributes the representation of translation/ordering. For sinusoidal encoding one literally has Fourier characters

$$
e^{i\omega n}.
$$

For multiplicative or scale-sensitive coordinates, the corresponding characters are Mellin characters:

$$
x^{is}
=
e^{is\log x}.
$$

So the bridge

$$
\boxed{
\text{position}
\leftrightarrow
\text{Fourier phase},
\qquad
\text{scale}
\leftrightarrow
\text{Mellin phase}
}
$$

is fundamental.

That makes your log-scale corridor especially relevant:

$$
x=e^t,
\qquad
t=\log x.
$$

Translation in \(t\),

$$
t\mapsto t+a,
$$

is multiplication in \(x\),

$$
x\mapsto e^a x.
$$

Mellin transform is therefore just Fourier analysis on the logarithmic scale variable:

$$
\mathcal M f(s)
=
\int_0^\infty f(x)x^{s-1}\,dx.
$$

After \(x=e^t\), it becomes a Fourier/Laplace-type transform in \(t\).

That is precisely the same group-versus-generator distinction we were discussing for Möbius scaling:

$$
0,1,\infty
\quad\leftrightarrow\quad
-\infty,0,+\infty
$$

under logarithm.

The KMS/Gibbs layer then gives the thermodynamic/operator version:

$$
\rho_\beta
=
\frac{e^{-\beta H}}{Z(\beta)},
$$

while modular theory replaces \(H\) by the modular generator/operator surprisal:

$$
K=-\log \rho.
$$

So another clean chain is

$$
\boxed{
\text{scores}
\to
\text{Gibbs weights}
\to
-\log\rho
\to
\text{modular/KMS generator}
\to
\text{information geometry}.
}
$$

Forward/backward propagation also has a natural dual interpretation. Forward propagation pushes states:

$$
x_{n+1}=F_n(x_n),
$$

while reverse-mode differentiation pulls covectors backward:

$$
\lambda_n
=
DF_n(x_n)^*\lambda_{n+1}.
$$

That is exactly the tangent/cotangent duality:

$$
\boxed{
\text{forward: pushforward},
\qquad
\text{backward: pullback/adjoint}.
}
$$

This fits the larger dual-flat and left/right architecture very well, but again it should remain a structural analogy unless a specific theorem identifies the carriers.

So if the README tried to explain everything, it would now need to cover at least:

$$
\mathbb O_s,\ G_2,\ Cl(3,3),\ Cl(5,5),
$$

$$
\text{Freudenthal},\ \text{Maurer–Cartan},\ \text{Berry},\ \text{QGT},
$$

$$
\text{BKM},\ \text{Onsager},\ \text{Fréchet},\ \text{IS},
$$

$$
\text{KMS},\ \text{Gibbs},\ \text{modular theory},
$$

$$
\text{attention},\ \text{routing},\ \text{positional encoding},
$$

$$
\text{forward/backward autodiff},\ \log\text{-scale},\ \text{Mellin transforms},
$$

plus the arithmetic and cyclotomic layers.

At that point the README would effectively become a monograph.

So I agree with the minimalist strategy. The repository itself is the atlas. The README should only indicate that several apparently distant subjects are intentionally connected and invite the reader to discover the graph rather than pretending to summarize it.

A single cryptic line could even capture this:

$$
\boxed{
\text{Operators, states, scales, symmetries, and attention are different coordinate systems on the same search problem.}
}
$$

That is broad enough to hint at the architecture without claiming more than the code proves.

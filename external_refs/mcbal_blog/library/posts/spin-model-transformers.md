# Spin-Model Transformers | mcbal

## Metadata
- URL: https://mcbal.github.io/post/spin-model-transformers/
- Source file: `external_refs/mcbal_blog/spin-model-transformers.html`
- Updated (human): unknown
- Updated (ISO): unknown
- Read time: unknown

## Structural Headings
- No results found
- Setting the scene: the kinetic Ising model
- Mean-field theory and Kullback-Leibler divergence
- The Plefka expansion: interpolating distributions
- Naive mean-field and Thouless-Anderson-Palmer approximations
- A simple JAX implementation
- Simulating magnetization trajectories
- Naive mean-field vs. Thouless-Anderson-Palmer (TAP)
- Sampling trajectories
- Sampling model parameters
- Vector spins: distributions on hyperspheres
- Magnetizations and limit of large vector dimension
- First-order naive mean-field approximation
- Second-order Thouless-Anderson-Palmer approximation
- A simple JAX implementation
- Simulating magnetization trajectories
- Playing with parameter scales: an exploration
- Playing with parameter scales: an explanation
- Connecting the dots
- Fast- and slow-moving parameters
- A simple JAX implementation
- A.1. Vector-spin distribution: normalization constant
- A.2. Vector-spin distribution: expected value (first moment)
- A.3. Vector-spin distribution: variance (second moment)
- A.4. Ratio of modified Bessel functions of the first kind
- A.5. General case: partial derivatives with respect to $\alpha$

## Keyword Profile (Top Non-Zero)
- `spin`: 154
- `transformer`: 73
- `mean-field`: 69
- `attention`: 30
- `softmax`: 13
- `energy`: 8
- `free energy`: 2
- `phase transition`: 2
- `mixture`: 1
- `non-equilibrium`: 1

## External Links
- https://mcbal.github.io/css/_entry.7e05687fab6cac8793150aebbea54f31a25e147debfa32e4d321f05807e7f0b6.css
- https://fonts.googleapis.com/css2?family=Space+Grotesk:wght@100..900&amp;family=IBM+Plex+Sans:wght@400,500,600&amp;family=Fira+Code:wght@100..900&amp;display=swap
- https://x.com/intent/tweet?url=https%3A%2F%2Fmcbal.github.io%2Fpost%2Fspin-model-transformers%2F&amp;text=Spin-Model+Transformers
- https://www.facebook.com/sharer.php?u=https%3A%2F%2Fmcbal.github.io%2Fpost%2Fspin-model-transformers%2F&amp;t=Spin-Model+Transformers
- https://www.linkedin.com/shareArticle?url=https%3A%2F%2Fmcbal.github.io%2Fpost%2Fspin-model-transformers%2F&amp;title=Spin-Model+Transformers
- https://scholar.google.be/citations?user=vjYY0bMAAAAJ&amp;hl=en
- https://hugoblox.com/templates/dev-portfolio?utm_source=site_footer&utm_medium=referral&utm_campaign=poweredby_oss&utm_content=brand_dev-portfolio&start=1
- https://hugo.chat?utm_source=site_footer&amp;utm_medium=referral&amp;utm_campaign=poweredby_oss&amp;utm_content=cta_dev-portfolio&amp;template_id=dev-portfolio

## Clean Text Excerpt

```text
Spin-Model Transformers | mcbal mcbal 
 Open Menu 
 Close Menu About Blog 
 
 ESC 
 
 0" x-transition class="border-t border-gray-100 dark:border-gray-800 px-4 py-2"> 
All Results
 
 0" class="divide-y divide-gray-200 dark:divide-gray-800"> 
 
 

 

 Searching...

 

 No results found

 

 
Clear search ↑↓ 
Navigate
 ↵ 
Select
 0" class="flex items-center gap-1"> 
 
Powered by Hugo Blox Blog
 A Large-D Closure for Asymmetric Kinetic Vector-Spin Systems Nonequilibrium Dynamics in Spin-Model Transformers Spin-Model Transformers Introduction Mean-field theory of asymmetric Ising models with binary spins Setting the scene: the kinetic Ising model Mean-field theory and Kullback-Leibler divergence The Plefka expansion: interpolating distributions Naive mean-field and Thouless-Anderson-Palmer approximations A simple JAX implementation Mean-field theory of asymmetric Ising models with vector spins Vector spins: distributions on hyperspheres Magnetizations and limit of large vector dimension First-order naive mean-field approximation Second-order Thouless-Anderson-Palmer approximation A simple JAX implementation Spin-transformer modules: a family of transformer-like modules Connecting the dots Fast- and slow-moving parameters A simple JAX implementation Conclusion References Appendices Vector-spin distribution: normalization constant Vector-spin distribution: expected value (first moment) Vector-spin distribution: variance (second moment) Ratio of modified Bessel functions of the first kind General case: partial derivatives with respect to $\alpha$ Footnotes Transformers Are Secretly Collectives of Spin Systems Transformers from Spin Models: Approximate Free Energy Minimization Deep Implicit Attention: A Mean-Field Theory Perspective on Attention Mechanisms Attention as Energy Minimization: Visualizing Energy Landscapes Transformer Attention as an Implicit Mixture of Effective Energy-Based Models An Energy-Based Perspective on Attention Mechanisms in Transformers Contents

 Introduction Mean-field theory of asymmetric Ising models with binary spins Setting the scene: the kinetic Ising model Mean-field theory and Kullback-Leibler divergence The Plefka expansion: interpolating distributions Naive mean-field and Thouless-Anderson-Palmer approximations A simple JAX implementation Mean-field theory of asymmetric Ising models with vector spins Vector spins: distributions on hyperspheres Magnetizations and limit of large vector dimension First-order naive mean-field approximation Second-order Thouless-Anderson-Palmer approximation A simple JAX implementation Spin-transformer modules: a family of transformer-like modules Connecting the dots Fast- and slow-moving parameters A simple JAX implementation Conclusion References Appendices Vector-spin distribution: normalization constant Vector-spin distribution: expected value (first moment) Vector-spin distribution: variance (second moment) Ratio of modified Bessel functions of the first kind General case: partial derivatives with respect to $\alpha$ Footnotes 
 
 
 Spin-Model Transformers

 A nonequilibrium statistical mechanics perspective on transformers

 Published on June 19, 2022 · 
 Last updated on December 7, 2023 · Matthias Bal · 
 44 min read blog ✨ Update (August 2026): For the most complete treatment of this framework, read Nonequilibrium Dynamics in Spin-Model Transformers , which carries the vector-spin construction forward into a broader study of quench protocols, relaxation, stability, and controllable nonequilibrium dynamics.

 ✨ TL;DR: We interpret and implement transformer modules as driven, disordered vector-spin models whose response behavior can be shaped by learning parameterized interactions, gradually steering a cascade of near-equilibrium steady-state magnetizations towards solving a given objective. Using dynamical mean-field theory, we show that a first-order approximation of the update equations for the magnetizations reproduces residual and attention terms. Going to second-order adds explicit expressions for feed-forward-like correction terms that are fully determined by the mean-field structure of the underlying spin model. By blending ideas from deep learning and statistical mechanics, we hope our work can help open up broader interdisciplinary bridges to improve our understanding of learning and generalization in transformer neural networks. 

 Introduction

 ✨ GitHub repository: mcbal/spin-model-transformers 

 In a series of previous blog posts , we have tried to connect the forward pass of a transformer neural-network module to computing mean magnetizations in disordered Ising-like vector-spin models with parameterized couplings and external magnetic fields. According to this perspective, the forward pass of a transformer module can be understood as computing statistical observables given a specific realization of quenched couplings and external magnetic fields while the backward pass nudges the parameterized couplings and external magnetic fields. Physically, the transformer module represents an interacting many-body system modulating its behavior by learning to respond to being probed and driven in all kinds of ways.

 However, both the mean-field message-passing approach of Deep Implicit Attention: A Mean-Field Theory Perspective on Attention Mechanisms (2021) and the saddle-point free-energy approach of Transformers from Spin Models: Approximate Free Energy Minimization (2021) inherently rely on methods that are only well-defined for spin models with symmetric coupling matrices, whose stochastic dynamics obey detailed balance and converge to a steady-state equilibrium characterized by the Boltzmann distribution. The softmax attention matrix in transformers is famously asymmetric though, so we had better come up with a more convincing approach to establish a correspondence.

 To capture spin models with asymmetric coupling matrices, we turn to nonequilibrium spin systems, whose dynamics can be pretty wild yet gentle enough to support regimes where relaxation to a nonequilibrium or near-equilibrium steady state can occur. In the past few decades, dynamical mean-field approaches have been developed for the binary kinetic Ising model, which exhibits nonequilibrium behavior for asymmetric couplings or when parameters are subject to rapid changes.

 In this post, we generalize a particular dynamical mean-field approach from binary spins to vector spins and relate the resulting mean-field update equations for the magnetizations to the forward pass of a transformer module. We find that the spin-model structure is rich enough for the update equations to yield residual connections, attention terms, and feed-forward correction terms, motivating a family of physics-inspired transformers.

 Mean-field theory of asymmetric Ising models with binary spins

 In this preliminary section, we review known results on mean-field theory approaches capturing the stochastic dynamics of binary kinetic Ising models. Readers familiar with this framework can skip ahead to Section 3 where we develop a generalization to vector spins. We primarily follow the discussion outlined in A unifying framework for mean-field theories of asymmetric kinetic Ising systems (Aguilera et al., 2021) . At the end of the section, we implement the mean-field update equations for the mean magnetizations in JAX and run a few numerical experiments.

 Setting the scene: the kinetic Ising model

 We consider a kinetic Ising model describing a system made up of $N$ interacting binary spins $s_{i,t} \in \{-1, 1\}$ that evolve in discrete time steps $t$ according to synchronous dynamics, i.e. all spins get updated at the same time in parallel. Given a configuration $\mathbf{s}_{t-1} = \{ s_{1,t-1}, s_{2,t-1}, \ldots, s_{N,t-1} \}$ at time $t-1$, we consider the spins $\mathbf{s}_{t}$ at time $t$ to be conditionally independent random variables captured by a discrete-time Markov chain transition probability

\begin{equation}
P( \mathbf{s}_{t} \vert \mathbf{s}_{t-1} ) = \prod_{i=1}^{N} \frac{\mathrm{e}^{s_{i,t} h_{i,t}}}{\sum_{s_{i,t}} \mathrm{e}^{s_{i,t} h_{i,t}}} = \prod_{i=1}^{N} \frac{\mathrm{e}^{s_{i,t} h_{i,t}}}{2 \cosh h_{i,t}}, \label{eq:pcond}
\end{equation} where the effective external field is given by

\begin{equation}
h_{i,t} = x_{i,t} + \sum_{j=1}^{N} J_{ij} s_{j,t-1}.
\end{equation} Here, the parameters $\mathbf{x}$ represent the (possibly time-dependent) local external fields at each site while the coupling parameters $\mathbf{J}$ are a specific realization of quenched disorder encoding the interactions between pairs of spins. Using the probability mass function of the previous state $P( \mathbf{s}_{t-1} )$ we can write the distribution of the current state as

\begin{equation}
P( \mathbf{s}_{t} ) = \sum_{\mathbf{s}_{t-1}} P( \mathbf{s}_{t} \vert \mathbf{s}_{t-1} ) P( \mathbf{s}_{t-1} ), \label{eq:marginal}
\end{equation} which, when applied recursively, traces the evolution of the system starting from some initial distribution $P( \mathbf{s}_{0} )$. Unless we turn off the couplings by setting $\mathbf{J} = \mathbf{0}$, the marginal distribution $P( \mathbf{s}_{t} )$ is not factorized and tends to be quite complicated. Our goal is to compute statistical properties of the system, such as the mean magnetizations

\begin{equation}
m_{i,t} = \sum_{\mathbf{s}_{t}} s_{i,t} P( \mathbf{s}_{t} ),
\end{equation} as well as correlations

\begin{equation}
C_{ik,t} = \sum_{\mathbf{s}_{t}} s_{i,t} s_{k,t} P( \mathbf{s}_{t} ) - m_{i,t} m_{k,t},
\end{equation} and delayed correlations

\begin{equation}
D_{il,t} = \sum_{\mathbf{s}_{t},\mathbf{s}_{t-1}} s_{i,t} s_{l,t-1} P( \mathbf{s}_{t}, \mathbf{s}_{t-1} ) - m_{i,t} m_{l,t-1}.
\end{equation} Since the above expressions involve summing over a large amount of possible spin configurations, they are not very useful in practice. So we will try to approximate the tricky marginal distribution $P( \mathbf{s}_{t} )$ defined in Eq. \eqref{eq:marginal} using a mean-field theory approach.

 Mean-field theory and Kullback-Leibler divergence

 Mean-field theory tries to approximate a complicated object ${\color{red}P}$ by wiggling around the parameters of a simple, analytically tractable parameterized ansatz ${\color{green}Q_{\theta}}$ to get as close as possible to ${\color{red}P}$. At risk of inducing headaches in mathematicians by calling everything a manifold, we can picture what is going on geometrically as trying to approximate a target probability distribution $P( \mathbf{s}_{t} \vert \mathbf{x}, \mathbf{J})$ and its statistical properties $\mathbf{m}_{t}$, $\mathbf{C}_{t}$, and $\mathbf{D}_{t}$ by restricting ourselves to a submanifold of tractable probability distributions. A particularly convenient submanifold is that of factorized models, where each point on the submanifold corresponds to a distribution parameterized by a vector $\boldsymbol{\theta}_{t}$,

\begin{equation}
Q( \mathbf{s}_{t} \vert \boldsymbol{\theta}_{t} ) = \prod_{i=1}^{N} \frac{\mathrm{e}^{s_{i,t} \theta_{i,t}}}{2 \cosh \theta_{i,t}}, \label{eq:q}
\end{equation} so that the mean magnetizations are simply given by

\begin{equation}
m_{i,t} = \tanh \theta_{i,t} \label{eq:meanmagstanh}
\end{equation} as there are no couplings between spins. The factorized model $Q( \mathbf{s}_{t} \vert \boldsymbol{\theta}^{*}_{t} )$ that minimizes the Kullback-Leibler (KL) divergence

\begin{equation}
D_{\mathrm{KL}} ({\color{red}P}\vert\vert{\color{green}Q_{\theta}}) = \sum_{\mathbf{s}_{t}} P( \mathbf{s}_{t}) \log \frac{P( \mathbf{s}_{t})}{Q_{\theta}( \mathbf{s}_{t})} \label{eq:kl}
\end{equation} has mean magnetizations $\mathbf{m}_{t}$ identical to those of the target distribution $P( \mathbf{s}_{t})$ since, for all spins $i=1,2,\ldots,N$, we find that

\begin{align}
\frac{\partial D_{\mathrm{KL}} ({\color{red}P}\vert\vert{\color{green}Q_{\theta}}) }{\partial \theta_{i, t}} \Biggr\rvert_{\boldsymbol{\theta}_{t}=\boldsymbol{\theta}^{*}_{t}} &= - \sum_{\mathbf{s}_{t}} P( \mathbf{s}_{t}) \frac{\partial \log Q_{\theta}( \mathbf{s}_{t}) }{\partial \theta_{i, t}} \Biggr\rvert_{\boldsymbol{\theta}_{t}=\boldsymbol{\theta}^{*}_{t}} \\\\
&= - \sum_{\mathbf{s}_{t}} s_{i,t} P( \mathbf{s}_{t}) + \tanh \theta^{*}_{i,t} \\\\
&= -m^{{\color{red}P}}_{i,t} + m^{{\color{green}Q_{\theta^{*}}}}_{i,t} = 0, \label{eq:klm}
\end{align} where $m^{{\color{red}P}}_{i,t}$ and $m^{{\color{green}Q_{\theta^{*}}}}_{i,t}$ respectively denote the expectation values of $s_{i,t}$ with respect to ${\color{red}P}$ and ${\color{green}Q_{\theta^{*}}}$. Indeed, minimizing $D_{\mathrm{KL}} ({\color{red}P}\vert\vert{\color{green}Q_{\theta}})$ tries to cover the modes of ${\color{red}P}$ by moment matching since the expectation value in Eq. \eqref{eq:kl} is calculated with respect to ${\color{red}P}$.

 The Plefka expansion: interpolating distributions

 Great, but is it even possible to find the parameters

\begin{equation}
\boldsymbol{\theta}^{*}_{t} = \operatorname*{arg\,min}_{\boldsymbol{\theta}_{t}} \left( - \sum_{\mathbf{s}_{t}} P( \mathbf{s}_{t}) \log Q_{\theta}( \mathbf{s}_{t}) \right)
\end{equation} that minimize the KL divergence? Well, that’s going to be hard, unless you already know the target distribution $P( \mathbf{s}_{t})$, or you have a clever way of approximately evaluating the expectation value of $\log {\color{green}Q_{\theta}}$ with respect to ${\color{red}P}$. So let us introduce some more distributions to get around this issue. To apply the Plefka expansion to our problem, we introduce the conditional distribution
```

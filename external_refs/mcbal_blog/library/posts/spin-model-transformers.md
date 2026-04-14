# Spin-Model Transformers | mcbal

## Metadata
- URL: https://mcbal.github.io/post/spin-model-transformers/
- Source file: `external_refs/mcbal_blog/spin-model-transformers.html`
- Updated (human): Dec 7, 2023
- Updated (ISO): 2023-12-07
- Read time: 51 min read

## Structural Headings
- 2.1. Setting the scene: the kinetic Ising model
- 2.2. Mean-field theory and Kullback-Leibler divergence
- 2.3. The Plefka expansion: interpolating distributions
- 2.4. Naive mean-field and Thouless-Anderson-Palmer approximations
- 2.5. A simple JAX implementation
- Simulating magnetization trajectories
- Naive mean-field vs. Thouless-Anderson-Palmer (TAP)
- Sampling trajectories
- Sampling model parameters
- 3.1. Vector spins: distributions on hyperspheres
- 3.2. Magnetizations and limit of large vector dimension
- 3.3. First-order naive mean-field approximation
- 3.4. Second-order Thouless-Anderson-Palmer approximation
- 3.5. A simple JAX implementation
- Simulating magnetization trajectories
- Playing with parameter scales: an exploration
- Playing with parameter scales: an explanation
- 4.1. Connecting the dots
- 4.2. Fast- and slow-moving parameters
- 4.3. A simple JAX implementation
- A.1. Vector-spin distribution: normalization constant
- A.2. Vector-spin distribution: expected value (first moment)
- A.3. Vector-spin distribution: variance (second moment)
- A.4. Ratio of modified Bessel functions of the first kind
- A.5. General case: partial derivatives with respect to $\alpha$
- Related

## Keyword Profile (Top Non-Zero)
- `spin`: 141
- `transformer`: 66
- `mean-field`: 64
- `attention`: 28
- `softmax`: 13
- `non-equilibrium`: 12
- `energy`: 5
- `entropy`: 2
- `free energy`: 2
- `phase transition`: 2
- `mixture`: 1

## External Links
- https://mcbal.github.io/post/spin-model-transformers/
- https://fonts.gstatic.com
- https://cdnjs.cloudflare.com/ajax/libs/academicons/1.9.0/css/academicons.min.css
- https://cdnjs.cloudflare.com/ajax/libs/font-awesome/5.14.0/css/all.min.css
- https://cdnjs.cloudflare.com/ajax/libs/fancybox/3.5.7/jquery.fancybox.min.css
- https://cdnjs.cloudflare.com/ajax/libs/highlight.js/10.2.0/styles/github.min.css
- https://cdnjs.cloudflare.com/ajax/libs/highlight.js/10.2.0/styles/dracula.min.css
- https://cdnjs.cloudflare.com/ajax/libs/leaflet/1.7.1/leaflet.min.css
- https://fonts.googleapis.com/css?family=IBM+Plex+Serif:ital,wght@0,300;0,400;1,300;1,400%7CIBM+Plex+Sans:ital,wght@0,300;0,400;0,700;1,400%7CFira+Code&display=swap
- https://mcbal.github.io/css/wowchemy.css
- https://mcbal.github.io/index.webmanifest
- https://mcbal.github.io/images/icon_hu0b7a4cb9992c9ac0e91bd28ffd38dd00_9727_32x32_fill_lanczos_center_3.png
- https://mcbal.github.io/images/icon_hu0b7a4cb9992c9ac0e91bd28ffd38dd00_9727_192x192_fill_lanczos_center_3.png
- https://mcbal.github.io/
- https://mcbal.github.io/#posts
- https://mcbal.github.io/#about
- https://github.com/mcbal/spin-model-transformers
- https://mcbal.github.io/post/transformers-are-secretly-collectives-of-spin-systems/
- https://mcbal.github.io/post/deep-implicit-attention-a-mean-field-theory-perspective-on-attention-mechanisms/
- https://mcbal.github.io/post/transformers-from-spin-models-approximate-free-energy-minimization/
- https://arxiv.org/abs/2002.04309
- https://arxiv.org/abs/1103.1044
- https://en.wikipedia.org/wiki/Spin_glass#Sherrington%E2%80%93Kirkpatrick_model
- https://en.wikipedia.org/wiki/Von_Mises%E2%80%93Fisher_distribution
- https://en.wikipedia.org/wiki/Concentration_parameter
- https://www.jstor.org/stable/2005830
- https://link.springer.com/article/10.1007/BF02764812
- https://en.wikipedia.org/wiki/Sherman%E2%80%93Morrison_formula
- https://en.wikipedia.org/wiki/Bilevel_optimization
- https://arxiv.org/abs/1003.5599
- https://arxiv.org/abs/1509.01229
- https://mcbal.github.io/post/transformers-are-secretly-collectives-of-spin-systems/#5-why-dont-we-just-probe-a-vector-spin-system-with-data
- https://github.com/lucidrains/x-transformers#root-mean-square-layer-normalization
- https://github.com/patrick-kidger/equinox
- https://docs.kidger.site/equinox/tricks/#improve-compilation-speed-with-scan-over-layers
- https://twitter.com/YiTayML/status/1714315484357857766
- https://arxiv.org/abs/2306.09228
- https://dlmf.nist.gov/10.32#i
- https://dlmf.nist.gov/10.29
- https://github.com/mcbal/spin-model-transformers/blob/main/spin_model_transformers/bessel.py
- https://isas.iar.kit.edu/pdf/ACC13_Kurz.pdf
- https://docs.scipy.org/doc/scipy/reference/generated/scipy.special.ive.html#scipy.special.ive
- https://mcbal.github.io/tag/artificial-intelligence/
- https://mcbal.github.io/tag/associative-memories/
- https://mcbal.github.io/tag/attention/
- https://mcbal.github.io/tag/deep-learning/
- https://mcbal.github.io/tag/ising-models/
- https://mcbal.github.io/tag/many-body-systems/
- https://mcbal.github.io/tag/mean-field-theory/
- https://mcbal.github.io/tag/neural-networks/
- https://mcbal.github.io/tag/near-equilibrium-dynamics/
- https://mcbal.github.io/tag/non-equilibrium-dynamics/
- https://mcbal.github.io/tag/spin-glasses/
- https://mcbal.github.io/tag/spin-models/
- https://mcbal.github.io/tag/statistical-physics/
- https://mcbal.github.io/tag/transformers/
- https://mcbal.github.io/tag/vector-spin-models/
- https://twitter.com/intent/tweet?url=https://mcbal.github.io/post/spin-model-transformers/&amp;text=Spin-Model%20Transformers
- https://www.facebook.com/sharer.php?u=https://mcbal.github.io/post/spin-model-transformers/&amp;t=Spin-Model%20Transformers
- https://www.linkedin.com/shareArticle?url=https://mcbal.github.io/post/spin-model-transformers/&amp;title=Spin-Model%20Transformers
- https://service.weibo.com/share/share.php?url=https://mcbal.github.io/post/spin-model-transformers/&amp;title=Spin-Model%20Transformers
- https://twitter.com/MatthiasBal
- https://www.linkedin.com/in/matthiasbal/
- https://scholar.google.be/citations?user=vjYY0bMAAAAJ&amp;hl=en
- https://github.com/mcbal
- https://mcbal.github.io/post/entropy-production-in-non-equilibrium-neural-networks/
- https://mcbal.github.io/post/transformer-attention-as-an-implicit-mixture-of-effective-energy-based-models/
- https://wowchemy.com
- https://github.com/wowchemy/wowchemy-hugo-modules

## Clean Text Excerpt

```text
Spin-Model Transformers | mcbal 

 

 

 
 
 
 
 
 
 
 

 
 
 

 
 
 Search

 
 
 
 
 

 
 
 
 
 

 
 

 
 
 

 
 
 

 

 
 

 
 
 mcbal 
 
 

 
 
 
 
 

 
 
 mcbal 
 
 

 
 
 

 
 
 

 

 
 
 
 
 

 

 
 
 
 

 
 
 
 
 
 
 
 
 
 
 
 
 
 

 
 Blog
```

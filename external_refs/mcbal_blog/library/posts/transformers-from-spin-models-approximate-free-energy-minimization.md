# Transformers from Spin Models: Approximate Free Energy Minimization | mcbal

## Metadata
- URL: https://mcbal.github.io/post/transformers-from-spin-models-approximate-free-energy-minimization/
- Source file: `external_refs/mcbal_blog/transformers-from-spin-models-approximate-free-energy-minimization.html`
- Updated (human): Oct 12, 2021
- Updated (ISO): 2021-10-12
- Read time: 25 min read

## Structural Headings
- 2.1. A vector-spin model and its partition function
- 2.2. Peeking into a physicist’s bag of tricks
- 2.3. Steepest descent: hunting for the saddle
- 2.4. Taking stock of what we have done
- 2.4.1. Questioning steepest descent and the large-$D$ limit
- 2.4.2. Energy-based models and effective energy functions
- 2.4.3. Spin glasses and mean-field approximation
- 3.1. The algorithm: bold moves on a tricky landscape
- 3.1.1. Initialization and normalization
- 3.1.2. Implicit layers for steepest-descent root-finding
- 3.1.3. Fun with free energies
- 3.2. The attention module: probing spins with data
- 3.2.1. Spin expectation values
- 3.2.2. Wrapping around the spin model
- 3.2.3. Comparison with vanilla transformers
- Related

## Keyword Profile (Top Non-Zero)
- `spin`: 105
- `transformer`: 45
- `energy`: 37
- `attention`: 34
- `mean-field`: 20
- `free energy`: 15
- `entropy`: 2
- `hopfield`: 2
- `non-equilibrium`: 1
- `softmax`: 1

## External Links
- https://mcbal.github.io/post/transformers-from-spin-models-approximate-free-energy-minimization/
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
- https://mcbal.github.io/post/transformers-are-secretly-collectives-of-spin-systems/
- https://github.com/mcbal/afem
- https://mcbal.github.io/post/deep-implicit-attention-a-mean-field-theory-perspective-on-attention-mechanisms/
- https://doi.org/10.1103/PhysRev.176.718
- https://physics.anu.edu.au/theophys/baxter_book.php
- https://en.wikipedia.org/wiki/N-vector_model
- https://en.wikipedia.org/wiki/Ising_model
- https://en.wikipedia.org/wiki/Classical_XY_model
- https://en.wikipedia.org/wiki/Classical_Heisenberg_model
- https://en.wikipedia.org/wiki/Spherical_model
- https://en.wikipedia.org/wiki/Boltzmann_machine
- https://en.wikipedia.org/wiki/Hopfield_network
- https://en.wikipedia.org/wiki/Spin_glass#The_model_of_Sherrington_and_Kirkpatrick
- https://doi.org/10.1103/PhysRev.160.437
- https://en.wikipedia.org/wiki/Method_of_steepest_descent
- https://en.wikipedia.org/wiki/Stirling%27s_approximation#Stirling%27s_formula_for_the_gamma_function
- https://www.nobelprize.org/prizes/physics/2021/summary/
- https://arxiv.org/abs/1506.07128
- http://implicit-layers-tutorial.org/implicit_functions/
- https://en.wikipedia.org/wiki/Newton%27s_method
- https://www.math.uwaterloo.ca/~hwolkowi/matrixcookbook.pdf
- https://arxiv.org/abs/1706.03762
- https://arxiv.org/abs/1909.01377
- http://blog.math.toronto.edu/GraduateBlog/files/2020/07/ut-thesis-Ko-updated.pdf
- https://arxiv.org/abs/1512.04441
- https://en.wikipedia.org/wiki/Woodbury_matrix_identity#Inverse_of_a_sum
- https://mcbal.github.io/tag/artificial-intelligence/
- https://mcbal.github.io/tag/associative-memories/
- https://mcbal.github.io/tag/attention/
- https://mcbal.github.io/tag/boltzmann-machine/
- https://mcbal.github.io/tag/deep-learning/
- https://mcbal.github.io/tag/emergent-collective-computational-capabilities/
- https://mcbal.github.io/tag/free-energy/
- https://mcbal.github.io/tag/hopfield-networks/
- https://mcbal.github.io/tag/ising-models/
- https://mcbal.github.io/tag/many-body-systems/
- https://mcbal.github.io/tag/neural-networks/
- https://mcbal.github.io/tag/partition-function/
- https://mcbal.github.io/tag/saddle-point/
- https://mcbal.github.io/tag/statistical-physics/
- https://mcbal.github.io/tag/steepest-descent/
- https://mcbal.github.io/tag/transformers/
- https://mcbal.github.io/tag/vector-spin-models/
- https://twitter.com/intent/tweet?url=https://mcbal.github.io/post/transformers-from-spin-models-approximate-free-energy-minimization/&amp;text=Transformers%20from%20Spin%20Models:%20Approximate%20Free%20Energy%20Minimization
- https://www.facebook.com/sharer.php?u=https://mcbal.github.io/post/transformers-from-spin-models-approximate-free-energy-minimization/&amp;t=Transformers%20from%20Spin%20Models:%20Approximate%20Free%20Energy%20Minimization
- https://www.linkedin.com/shareArticle?url=https://mcbal.github.io/post/transformers-from-spin-models-approximate-free-energy-minimization/&amp;title=Transformers%20from%20Spin%20Models:%20Approximate%20Free%20Energy%20Minimization
- https://service.weibo.com/share/share.php?url=https://mcbal.github.io/post/transformers-from-spin-models-approximate-free-energy-minimization/&amp;title=Transformers%20from%20Spin%20Models:%20Approximate%20Free%20Energy%20Minimization
- https://twitter.com/MatthiasBal
- https://www.linkedin.com/in/matthiasbal/
- https://scholar.google.be/citations?user=vjYY0bMAAAAJ&amp;hl=en
- https://github.com/mcbal
- https://mcbal.github.io/post/entropy-production-in-non-equilibrium-neural-networks/
- https://mcbal.github.io/post/spin-model-transformers/
- https://mcbal.github.io/post/an-energy-based-perspective-on-attention-mechanisms-in-transformers/
- https://wowchemy.com
- https://github.com/wowchemy/wowchemy-hugo-modules

## Clean Text Excerpt

```text
Transformers from Spin Models: Approximate Free Energy Minimization | mcbal 

 

 

 
 
 
 
 
 
 
 

 
 
 

 
 
 Search

 
 
 
 
 

 
 
 
 
 

 
 

 
 
 

 
 
 

 

 
 

 
 
 mcbal 
 
 

 
 
 
 
 

 
 
 mcbal 
 
 

 
 
 

 
 
 

 

 
 
 
 
 

 

 
 
 
 

 
 
 
 
 
 
 
 
 
 
 
 
 
 

 
 Blog
```

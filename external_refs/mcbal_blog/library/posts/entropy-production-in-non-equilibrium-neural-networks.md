# Entropy Production in Non-Equilibrium Neural Networks | mcbal

## Metadata
- URL: https://mcbal.github.io/post/entropy-production-in-non-equilibrium-neural-networks/
- Source file: `external_refs/mcbal_blog/entropy-production-in-non-equilibrium-neural-networks.html`
- Updated (human): Feb 18, 2026
- Updated (ISO): 2026-02-18
- Read time: 8 min read

## Structural Headings
- 1. Introduction
- 2. Background and intuitions
- 3. Non-equilibrium neural networks
- 3.1. Example model
- 3.2. Entropy production
- Vibe check
- 4. Experiments
- Model behavior in a noisy environment
- Global coherence from local backpropagation
- Growing network topologies
- 5. Discussion and related work
- References
- Related

## Keyword Profile (Top Non-Zero)
- `spin`: 27
- `transformer`: 21
- `entropy`: 17
- `non-equilibrium`: 12
- `mean-field`: 11
- `attention`: 9
- `softmax`: 5
- `energy`: 2
- `free energy`: 1
- `mixture`: 1

## External Links
- https://mcbal.github.io/post/entropy-production-in-non-equilibrium-neural-networks/
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
- https://commons.wikimedia.org/wiki/File:Starling_murmuration.jpg
- https://github.com/mcbal/neqnn
- https://mcbal.github.io/post/spin-model-transformers/
- https://en.wikipedia.org/wiki/Entropy_production#Entropy_production_in_stochastic_processes
- https://byorgey.wordpress.com/2009/01/12/abstraction-intuition-and-the-monad-tutorial-fallacy/
- https://mcbal.github.io/post/deep-implicit-attention-a-mean-field-theory-perspective-on-attention-mechanisms/
- https://arxiv.org/abs/2002.04309
- https://en.wikipedia.org/wiki/Synchronization_%28alternating_current%29
- https://dspace.mit.edu/handle/1721.1/130835?show=full
- https://arxiv.org/abs/2602.08079
- https://mcbal.github.io/tag/artificial-intelligence/
- https://mcbal.github.io/tag/associative-memories/
- https://mcbal.github.io/tag/attention/
- https://mcbal.github.io/tag/controllable-non-equilibrium-behavior/
- https://mcbal.github.io/tag/cybernetics/
- https://mcbal.github.io/tag/deep-learning/
- https://mcbal.github.io/tag/entropy-production/
- https://mcbal.github.io/tag/ising-models/
- https://mcbal.github.io/tag/many-body-systems/
- https://mcbal.github.io/tag/mean-field-theory/
- https://mcbal.github.io/tag/neural-networks/
- https://mcbal.github.io/tag/near-equilibrium-dynamics/
- https://mcbal.github.io/tag/non-equilibrium-dynamics/
- https://mcbal.github.io/tag/self-organizing-computational-stability/
- https://mcbal.github.io/tag/spin-glasses/
- https://mcbal.github.io/tag/spin-models/
- https://mcbal.github.io/tag/statistical-physics/
- https://mcbal.github.io/tag/transformers/
- https://mcbal.github.io/tag/vector-spin-models/
- https://twitter.com/intent/tweet?url=https://mcbal.github.io/post/entropy-production-in-non-equilibrium-neural-networks/&amp;text=Entropy%20Production%20in%20Non-Equilibrium%20Neural%20Networks
- https://www.facebook.com/sharer.php?u=https://mcbal.github.io/post/entropy-production-in-non-equilibrium-neural-networks/&amp;t=Entropy%20Production%20in%20Non-Equilibrium%20Neural%20Networks
- https://www.linkedin.com/shareArticle?url=https://mcbal.github.io/post/entropy-production-in-non-equilibrium-neural-networks/&amp;title=Entropy%20Production%20in%20Non-Equilibrium%20Neural%20Networks
- https://service.weibo.com/share/share.php?url=https://mcbal.github.io/post/entropy-production-in-non-equilibrium-neural-networks/&amp;title=Entropy%20Production%20in%20Non-Equilibrium%20Neural%20Networks
- https://twitter.com/MatthiasBal
- https://www.linkedin.com/in/matthiasbal/
- https://scholar.google.be/citations?user=vjYY0bMAAAAJ&amp;hl=en
- https://github.com/mcbal
- https://mcbal.github.io/post/transformers-are-secretly-collectives-of-spin-systems/
- https://mcbal.github.io/post/transformers-from-spin-models-approximate-free-energy-minimization/
- https://mcbal.github.io/post/transformer-attention-as-an-implicit-mixture-of-effective-energy-based-models/
- https://wowchemy.com
- https://github.com/wowchemy/wowchemy-hugo-modules

## Clean Text Excerpt

```text
Entropy Production in Non-Equilibrium Neural Networks | mcbal 

 

 

 
 
 
 
 
 
 
 

 
 
 

 
 
 Search

 
 
 
 
 

 
 
 
 
 

 
 

 
 
 

 
 
 

 

 
 

 
 
 mcbal 
 
 

 
 
 
 
 

 
 
 mcbal 
 
 

 
 
 

 
 
 

 

 
 
 
 
 

 

 
 
 
 

 
 
 
 
 
 
 
 
 
 
 
 
 
 

 
 Blog
```

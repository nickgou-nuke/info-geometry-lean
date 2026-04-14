# Transformers Are Secretly Collectives of Spin Systems | mcbal

## Metadata
- URL: https://mcbal.github.io/post/transformers-are-secretly-collectives-of-spin-systems/
- Source file: `external_refs/mcbal_blog/transformers-are-secretly-collectives-of-spin-systems.html`
- Updated (human): Nov 29, 2021
- Updated (ISO): 2021-11-29
- Read time: 15 min read

## Structural Headings
- 1. Introduction
- 2. Where does the transformer module architecture come from?
- 3. Deriving attention from energy functions only gets you so far
- 4. Back to the roots: physical spin systems and vector-spin models
- 5. Why don’t we just probe a vector-spin system with data?
- 6. A slice of statistical mechanics: magnetizations and free energies
- 7. Turning a differentiable spin system into a neural network
- 8. An exercise in squinting: recognizing the transformer module
- 9. Training transformer modules shapes collective behavior
- 10. Training deep transformers orchestrates spin-system collectives
- 11. Conclusion
- Acknowledgements
- References & footnotes
- Related

## Keyword Profile (Top Non-Zero)
- `spin`: 77
- `transformer`: 50
- `energy`: 39
- `attention`: 21
- `free energy`: 17
- `hopfield`: 9
- `softmax`: 7
- `mean-field`: 5
- `non-equilibrium`: 4
- `logsumexp`: 3
- `entropy`: 2

## External Links
- https://mcbal.github.io/post/transformers-are-secretly-collectives-of-spin-systems/
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
- https://mcbal.github.io/post/spin-model-transformers/
- https://mcbal.github.io/post/deep-implicit-attention-a-mean-field-theory-perspective-on-attention-mechanisms/
- https://mcbal.github.io/post/transformers-from-spin-models-approximate-free-energy-minimization/
- https://arxiv.org/abs/1706.03762
- https://arxiv.org/abs/2111.11418
- https://arxiv.org/abs/2008.02217
- https://arxiv.org/abs/2008.06996
- https://mcbal.github.io/post/an-energy-based-perspective-on-attention-mechanisms-in-transformers/
- https://mcbal.github.io/post/an-energy-based-perspective-on-attention-mechanisms-in-transformers/#modern-continuous-hopfield-networks
- https://mcbal.github.io/post/attention-as-energy-minimization-visualizing-energy-landscapes/
- https://en.wikipedia.org/wiki/Ising_model
- https://en.wikipedia.org/wiki/Boltzmann_machine
- https://en.wikipedia.org/wiki/Hopfield_network
- https://en.wikipedia.org/wiki/N-vector_model
- https://github.com/mcbal
- http://implicit-layers-tutorial.org/
- https://mlcollective.org/
- https://www.physics.rutgers.edu/~pchandra/physics681/Sompolinsky_PhysicsToday.pdf
- http://blog.math.toronto.edu/GraduateBlog/files/2020/07/ut-thesis-Ko-updated.pdf
- https://arxiv.org/abs/1512.04441
- https://giamarchi.unige.ch/local/people/thierry.giamarchi/pdf/cours_sft.pdf
- https://youtu.be/vSgHuErXuqk?t=2188
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
- https://mcbal.github.io/tag/statistical-physics/
- https://mcbal.github.io/tag/transformers/
- https://mcbal.github.io/tag/vector-spin-models/
- https://twitter.com/intent/tweet?url=https://mcbal.github.io/post/transformers-are-secretly-collectives-of-spin-systems/&amp;text=Transformers%20Are%20Secretly%20Collectives%20of%20Spin%20Systems
- https://www.facebook.com/sharer.php?u=https://mcbal.github.io/post/transformers-are-secretly-collectives-of-spin-systems/&amp;t=Transformers%20Are%20Secretly%20Collectives%20of%20Spin%20Systems
- https://www.linkedin.com/shareArticle?url=https://mcbal.github.io/post/transformers-are-secretly-collectives-of-spin-systems/&amp;title=Transformers%20Are%20Secretly%20Collectives%20of%20Spin%20Systems
- https://service.weibo.com/share/share.php?url=https://mcbal.github.io/post/transformers-are-secretly-collectives-of-spin-systems/&amp;title=Transformers%20Are%20Secretly%20Collectives%20of%20Spin%20Systems
- https://twitter.com/MatthiasBal
- https://www.linkedin.com/in/matthiasbal/
- https://scholar.google.be/citations?user=vjYY0bMAAAAJ&amp;hl=en
- https://mcbal.github.io/post/entropy-production-in-non-equilibrium-neural-networks/
- https://wowchemy.com
- https://github.com/wowchemy/wowchemy-hugo-modules

## Clean Text Excerpt

```text
Transformers Are Secretly Collectives of Spin Systems | mcbal 

 

 

 
 
 
 
 
 
 
 

 
 
 

 
 
 Search

 
 
 
 
 

 
 
 
 
 

 
 

 
 
 

 
 
 

 

 
 

 
 
 mcbal 
 
 

 
 
 
 
 

 
 
 mcbal 
 
 

 
 
 

 
 
 

 

 
 
 
 
 

 

 
 
 
 

 
 
 
 
 
 
 
 
 
 
 
 
 
 

 
 Blog
```

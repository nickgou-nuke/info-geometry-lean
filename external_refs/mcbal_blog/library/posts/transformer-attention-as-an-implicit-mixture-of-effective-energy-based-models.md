# Transformer Attention as an Implicit Mixture of Effective Energy-Based Models | mcbal

## Metadata
- URL: https://mcbal.github.io/post/transformer-attention-as-an-implicit-mixture-of-effective-energy-based-models/
- Source file: `external_refs/mcbal_blog/transformer-attention-as-an-implicit-mixture-of-effective-energy-based-models.html`
- Updated (human): Dec 30, 2020
- Updated (ISO): 2020-12-30
- Read time: 14 min read

## Structural Headings
- Restricted Boltzmann Machines
- Why hidden units?
- Effective energies and correlations
- Modern Hopfield networks as mixtures of effective RBMs
- Bending the explicit architecture
- From explicit architectures to implicit energy minimization
- Deep implicit layers for attention dynamics
- Related

## Keyword Profile (Top Non-Zero)
- `attention`: 58
- `energy`: 56
- `transformer`: 21
- `hopfield`: 14
- `mixture`: 12
- `softmax`: 7
- `spin`: 3
- `logsumexp`: 2
- `entropy`: 1
- `mean-field`: 1
- `non-equilibrium`: 1

## External Links
- https://mcbal.github.io/post/transformer-attention-as-an-implicit-mixture-of-effective-energy-based-models/
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
- https://mcbal.github.io/post/an-energy-based-perspective-on-attention-mechanisms-in-transformers/
- https://implicit-layers-tutorial.org/
- https://en.wikipedia.org/wiki/Restricted_Boltzmann_machine
- https://arxiv.org/abs/1803.08823
- https://mcbal.github.io/post/an-energy-based-perspective-on-attention-mechanisms-in-transformers/#energy-based-models-a-gentle-introduction
- https://en.wikipedia.org/wiki/Common_integrals_in_quantum_field_theory
- https://en.wikipedia.org/wiki/Hubbard%E2%80%93Stratonovich_transformation
- https://en.wikipedia.org/wiki/Renormalization_group
- https://en.wikipedia.org/wiki/Kenneth_G._Wilson
- https://en.wikipedia.org/wiki/Cumulant
- https://en.wikipedia.org/wiki/Bernoulli_distribution#Higher_moments_and_cumulants
- https://en.wikipedia.org/wiki/Gaussian_integral#n-dimensional_with_linear_term
- https://arxiv.org/abs/2008.06996
- https://arxiv.org/abs/2009.14794
- https://arxiv.org/abs/2005.09561
- https://colab.research.google.com/drive/1OUVzeUh66wVOFI_Nc_rIAuO70gHimHH8?usp=sharing#scrollTo=vFlF3gTnzOpp
- https://arxiv.org/abs/1909.01377
- https://arxiv.org/abs/1706.03762
- http://www.stat.uchicago.edu/~pmcc/courses/stat306/2013/cumulants.pdf
- https://papers.nips.cc/paper/2008/hash/e820a45f1dfc7b95282d10b6087e11c0-Abstract.html
- https://en.wikipedia.org/wiki/Expectation%E2%80%93maximization_algorithm
- https://mcbal.github.io/tag/artificial-intelligence/
- https://mcbal.github.io/tag/associative-memories/
- https://mcbal.github.io/tag/attention/
- https://mcbal.github.io/tag/deep-learning/
- https://mcbal.github.io/tag/energy-based-models/
- https://mcbal.github.io/tag/neural-networks/
- https://mcbal.github.io/tag/renormalization-group/
- https://mcbal.github.io/tag/restricted-boltzmann-machine/
- https://mcbal.github.io/tag/statistical-physics/
- https://mcbal.github.io/tag/transformers/
- https://twitter.com/intent/tweet?url=https://mcbal.github.io/post/transformer-attention-as-an-implicit-mixture-of-effective-energy-based-models/&amp;text=Transformer%20Attention%20as%20an%20Implicit%20Mixture%20of%20Effective%20Energy-Based%20Models
- https://www.facebook.com/sharer.php?u=https://mcbal.github.io/post/transformer-attention-as-an-implicit-mixture-of-effective-energy-based-models/&amp;t=Transformer%20Attention%20as%20an%20Implicit%20Mixture%20of%20Effective%20Energy-Based%20Models
- https://www.linkedin.com/shareArticle?url=https://mcbal.github.io/post/transformer-attention-as-an-implicit-mixture-of-effective-energy-based-models/&amp;title=Transformer%20Attention%20as%20an%20Implicit%20Mixture%20of%20Effective%20Energy-Based%20Models
- https://service.weibo.com/share/share.php?url=https://mcbal.github.io/post/transformer-attention-as-an-implicit-mixture-of-effective-energy-based-models/&amp;title=Transformer%20Attention%20as%20an%20Implicit%20Mixture%20of%20Effective%20Energy-Based%20Models
- https://twitter.com/MatthiasBal
- https://www.linkedin.com/in/matthiasbal/
- https://scholar.google.be/citations?user=vjYY0bMAAAAJ&amp;hl=en
- https://github.com/mcbal
- https://mcbal.github.io/post/attention-as-energy-minimization-visualizing-energy-landscapes/
- https://mcbal.github.io/post/deep-implicit-attention-a-mean-field-theory-perspective-on-attention-mechanisms/
- https://mcbal.github.io/post/entropy-production-in-non-equilibrium-neural-networks/
- https://mcbal.github.io/post/spin-model-transformers/
- https://wowchemy.com
- https://github.com/wowchemy/wowchemy-hugo-modules

## Clean Text Excerpt

```text
Transformer Attention as an Implicit Mixture of Effective Energy-Based Models | mcbal 

 

 

 
 
 
 
 
 
 
 

 
 
 

 
 
 Search

 
 
 
 
 

 
 
 
 
 

 
 

 
 
 

 
 
 

 

 
 

 
 
 mcbal 
 
 

 
 
 
 
 

 
 
 mcbal 
 
 

 
 
 

 
 
 

 

 
 
 
 
 

 

 
 
 
 

 
 
 
 
 
 
 
 
 
 
 
 
 
 

 
 Blog
```

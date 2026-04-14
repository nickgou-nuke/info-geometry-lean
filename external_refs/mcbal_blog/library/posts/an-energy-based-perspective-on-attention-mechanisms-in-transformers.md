# An Energy-Based Perspective on Attention Mechanisms in Transformers | mcbal

## Metadata
- URL: https://mcbal.github.io/post/an-energy-based-perspective-on-attention-mechanisms-in-transformers/
- Source file: `external_refs/mcbal_blog/an-energy-based-perspective-on-attention-mechanisms-in-transformers.html`
- Updated (human): Dec 3, 2020
- Updated (ISO): 2020-12-03
- Read time: 25 min read

## Structural Headings
- Vanilla Transformers
- Beyond vanilla: confronting quadratic scaling
- Classical discrete Hopfield networks
- Physical intuition
- Modern discrete Hopfield networks
- Modern continuous Hopfield networks
- Physical intuition
- Deriving the update rule
- Modern continuous Hopfield Networks as energy-based models
- Energy-based models: a gentle introduction
- Exactly optimizing modern continuous Hopfield networks
- Transformers store and retrieve context-dependent patterns
- Where are patterns stored in a Transformer?
- Pretraining loss functions
- Stepping through the Transformer: implicit energy minimization
- Meta-learning and few-shot inference
- Attention dynamics: embracing collective phenomena
- Why very long sequences should not be needed
- Related

## Keyword Profile (Top Non-Zero)
- `attention`: 78
- `energy`: 71
- `transformer`: 59
- `hopfield`: 40
- `spin`: 18
- `softmax`: 13
- `logsumexp`: 8
- `entropy`: 2
- `mixture`: 2
- `free energy`: 1
- `mean-field`: 1
- `non-equilibrium`: 1

## External Links
- https://mcbal.github.io/post/an-energy-based-perspective-on-attention-mechanisms-in-transformers/
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
- https://xkcd.com/793/
- https://mcbal.github.io/post/transformers-are-secretly-collectives-of-spin-systems/
- https://arxiv.org/abs/1706.03762
- https://arxiv.org/abs/2001.08361
- https://arxiv.org/abs/2010.11929
- https://arxiv.org/abs/2008.02217
- https://arxiv.org/abs/2008.06996
- https://ml-jku.github.io/hopfield-layers/
- https://en.wikipedia.org/wiki/Hopfield_network
- https://www.pnas.org/content/pnas/79/8/2554.full.pdf
- https://en.wikipedia.org/wiki/Boltzmann_machine
- https://en.wikipedia.org/wiki/Ising_model#Application_to_neuroscience
- https://en.wikipedia.org/wiki/Spin_glass
- https://en.wikipedia.org/wiki/Neural_network
- https://en.wikipedia.org/wiki/Order_and_disorder#Quenched_disorder
- https://en.wikipedia.org/wiki/Philip_W._Anderson
- https://en.wikipedia.org/wiki/Spin_glass#cite_note-10
- https://arxiv.org/abs/1910.01592
- https://en.wikipedia.org/wiki/Restricted_Boltzmann_machine
- https://en.wikipedia.org/wiki/Boltzmann_distribution
- https://en.wikipedia.org/wiki/Gaussian_integral#n-dimensional_with_linear_term
- https://arxiv.org/abs/2005.14165
- https://ml-jku.github.io/blog-post-performer/
- https://www.youtube.com/watch?v=iDulhoQ2pro
- http://gabrielilharco.com/publications/EMNLP_2020_Tutorial__High_Performance_NLP.pdf
- https://2020.emnlp.org/tutorials
- https://github.com/lucidrains?tab=repositories
- https://arxiv.org/abs/1606.01164
- https://arxiv.org/abs/1702.01929
- https://en.wikipedia.org/wiki/Classical_XY_model
- https://en.wikipedia.org/wiki/Classical_Heisenberg_model
- http://yann.lecun.com/exdb/publis/pdf/lecun-06.pdf
- https://atcold.github.io/pytorch-Deep-Learning/en/week07/07-1/
- https://arxiv.org/abs/1803.08823
- https://mcbal.github.io/tag/artificial-intelligence/
- https://mcbal.github.io/tag/associative-memories/
- https://mcbal.github.io/tag/attention/
- https://mcbal.github.io/tag/deep-learning/
- https://mcbal.github.io/tag/energy-based-models/
- https://mcbal.github.io/tag/hopfield-networks/
- https://mcbal.github.io/tag/neural-networks/
- https://mcbal.github.io/tag/statistical-physics/
- https://mcbal.github.io/tag/transformers/
- https://twitter.com/intent/tweet?url=https://mcbal.github.io/post/an-energy-based-perspective-on-attention-mechanisms-in-transformers/&amp;text=An%20Energy-Based%20Perspective%20on%20Attention%20Mechanisms%20in%20Transformers
- https://www.facebook.com/sharer.php?u=https://mcbal.github.io/post/an-energy-based-perspective-on-attention-mechanisms-in-transformers/&amp;t=An%20Energy-Based%20Perspective%20on%20Attention%20Mechanisms%20in%20Transformers
- https://www.linkedin.com/shareArticle?url=https://mcbal.github.io/post/an-energy-based-perspective-on-attention-mechanisms-in-transformers/&amp;title=An%20Energy-Based%20Perspective%20on%20Attention%20Mechanisms%20in%20Transformers
- https://service.weibo.com/share/share.php?url=https://mcbal.github.io/post/an-energy-based-perspective-on-attention-mechanisms-in-transformers/&amp;title=An%20Energy-Based%20Perspective%20on%20Attention%20Mechanisms%20in%20Transformers
- https://twitter.com/MatthiasBal
- https://www.linkedin.com/in/matthiasbal/
- https://scholar.google.be/citations?user=vjYY0bMAAAAJ&amp;hl=en
- https://github.com/mcbal
- https://mcbal.github.io/post/transformer-attention-as-an-implicit-mixture-of-effective-energy-based-models/
- https://mcbal.github.io/post/deep-implicit-attention-a-mean-field-theory-perspective-on-attention-mechanisms/
- https://mcbal.github.io/post/transformers-from-spin-models-approximate-free-energy-minimization/
- https://mcbal.github.io/post/entropy-production-in-non-equilibrium-neural-networks/
- https://wowchemy.com
- https://github.com/wowchemy/wowchemy-hugo-modules

## Clean Text Excerpt

```text
An Energy-Based Perspective on Attention Mechanisms in Transformers | mcbal 

 

 

 
 
 
 
 
 
 
 

 
 
 

 
 
 Search

 
 
 
 
 

 
 
 
 
 

 
 

 
 
 

 
 
 

 

 
 

 
 
 mcbal 
 
 

 
 
 
 
 

 
 
 mcbal 
 
 

 
 
 

 
 
 

 

 
 
 
 
 

 

 
 
 
 

 
 
 
 
 
 
 
 
 
 
 
 
 
 

 
 Blog
```

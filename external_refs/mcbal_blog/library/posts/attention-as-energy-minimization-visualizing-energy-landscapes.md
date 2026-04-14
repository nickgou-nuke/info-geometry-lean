# Attention as Energy Minimization: Visualizing Energy Landscapes | mcbal

## Metadata
- URL: https://mcbal.github.io/post/attention-as-energy-minimization-visualizing-energy-landscapes/
- Source file: `external_refs/mcbal_blog/attention-as-energy-minimization-visualizing-energy-landscapes.html`
- Updated (human): Mar 18, 2021
- Updated (ISO): 2021-03-18
- Read time: 19 min read

## Structural Headings
- 3.1. Explicit vanilla softmax attention
- 3.2. Implicit energy-based attention
- 4.1. Energy function
- 4.2. Verifying the update rule
- Cross-attention
- Self-attention
- 4.3. Adding queries, keys, and values
- 4.4. Adding masking and multiple attention heads
- Masking
- Multi-head attention
- Bare cross-attention
- Small steps go nowhere
- Lots of (big) steps converge near (global) minimum or repeated softmax iterations make all token representations identical
- Decreasing the scale (increasing the temperature) makes the landscape smoother and encourages convergence to same (global) minimum
- Increasing the scale (lowering the temperature) creates “disconnected” valleys in the energy landscape inhabited by stored patterns which act as attractors for any query that happens to be in its basin of attraction
- Adding linear query-key-value transformations
- Bare self-attention: on the importance of scale and why multiple heads
- Related

## Keyword Profile (Top Non-Zero)
- `energy`: 125
- `attention`: 108
- `softmax`: 41
- `hopfield`: 24
- `transformer`: 15
- `logsumexp`: 4
- `mixture`: 3
- `mean-field`: 2
- `entropy`: 1
- `non-equilibrium`: 1
- `spin`: 1

## External Links
- https://mcbal.github.io/post/attention-as-energy-minimization-visualizing-energy-landscapes/
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
- https://colab.research.google.com/drive/1UsJ24rwCT9sVjh_v3bnr6Ld5NwLbJq54?usp=sharing
- https://mcbal.github.io/post/an-energy-based-perspective-on-attention-mechanisms-in-transformers/
- https://mcbal.github.io/post/transformer-attention-as-an-implicit-mixture-of-effective-energy-based-models/
- https://arxiv.org/abs/2103.03404
- https://arxiv.org/abs/2103.03206
- https://mcbal.github.io/post/an-energy-based-perspective-on-attention-mechanisms-in-transformers/#modern-continuous-hopfield-networks
- https://ml-jku.github.io/hopfield-layers/#update
- https://arxiv.org/abs/2008.02217
- https://arxiv.org/abs/2008.06996
- https://mcbal.github.io/tag/artificial-intelligence/
- https://mcbal.github.io/tag/associative-memories/
- https://mcbal.github.io/tag/attention/
- https://mcbal.github.io/tag/deep-learning/
- https://mcbal.github.io/tag/dynamical-systems/
- https://mcbal.github.io/tag/energy-based-models/
- https://mcbal.github.io/tag/neural-networks/
- https://mcbal.github.io/tag/transformers/
- https://twitter.com/intent/tweet?url=https://mcbal.github.io/post/attention-as-energy-minimization-visualizing-energy-landscapes/&amp;text=Attention%20as%20Energy%20Minimization:%20Visualizing%20Energy%20Landscapes
- https://www.facebook.com/sharer.php?u=https://mcbal.github.io/post/attention-as-energy-minimization-visualizing-energy-landscapes/&amp;t=Attention%20as%20Energy%20Minimization:%20Visualizing%20Energy%20Landscapes
- https://www.linkedin.com/shareArticle?url=https://mcbal.github.io/post/attention-as-energy-minimization-visualizing-energy-landscapes/&amp;title=Attention%20as%20Energy%20Minimization:%20Visualizing%20Energy%20Landscapes
- https://service.weibo.com/share/share.php?url=https://mcbal.github.io/post/attention-as-energy-minimization-visualizing-energy-landscapes/&amp;title=Attention%20as%20Energy%20Minimization:%20Visualizing%20Energy%20Landscapes
- https://twitter.com/MatthiasBal
- https://www.linkedin.com/in/matthiasbal/
- https://scholar.google.be/citations?user=vjYY0bMAAAAJ&amp;hl=en
- https://github.com/mcbal
- https://mcbal.github.io/post/deep-implicit-attention-a-mean-field-theory-perspective-on-attention-mechanisms/
- https://mcbal.github.io/post/entropy-production-in-non-equilibrium-neural-networks/
- https://mcbal.github.io/post/spin-model-transformers/
- https://wowchemy.com
- https://github.com/wowchemy/wowchemy-hugo-modules

## Clean Text Excerpt

```text
Attention as Energy Minimization: Visualizing Energy Landscapes | mcbal 

 

 

 
 
 
 
 
 
 
 

 
 
 

 
 
 Search

 
 
 
 
 

 
 
 
 
 

 
 

 
 
 

 
 
 

 

 
 

 
 
 mcbal 
 
 

 
 
 
 
 

 
 
 mcbal 
 
 

 
 
 

 
 
 

 

 
 
 
 
 

 

 
 
 
 

 
 
 
 
 
 
 
 
 
 
 
 
 
 

 
 Blog
```

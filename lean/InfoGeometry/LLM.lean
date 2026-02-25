import InfoGeometry.LLM.TransformerBlock
import InfoGeometry.LLM.MaskedTransformerBlock
import InfoGeometry.LLM.PositionalEncoding
import InfoGeometry.Research.Attention
import InfoGeometry.Research.AttentionEuclidean
import InfoGeometry.Research.AttentionSplit
import InfoGeometry.Research.FormalScaffold
import InfoGeometry.Research.GrandCanonicalExperts
import InfoGeometry.Research.LorentzianRouting
import InfoGeometry.Research.Triality

/-!
# InfoGeometry.LLM

Unified entrypoint for LLM-oriented formalization layers:
- thermodynamic attention and context windows
- Euclidean and Lorentzian/split attention variants
- geometric multi-head attention and output projection
- canonical transformer-block scaffold (attention + residual + normalization + MLP)
- causal-mask transformer interface
- positional encoding abstraction with run-composition lemmas
-/

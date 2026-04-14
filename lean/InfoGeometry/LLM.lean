import InfoGeometry.LLM.TransformerBlock
import InfoGeometry.LLM.MaskedTransformerBlock
import InfoGeometry.LLM.TransformerArchitecture
import InfoGeometry.LLM.ThermodynamicSwitching
import InfoGeometry.LLM.ScalarThermoBridge
import InfoGeometry.LLM.RouterFreeEnergyBridge
import InfoGeometry.LLM.TrialityMoE
import InfoGeometry.Canonical.Attention
import InfoGeometry.Canonical.AttentionEuclidean
import InfoGeometry.Canonical.AttentionSplit
import InfoGeometry.Canonical.FormalScaffold
import InfoGeometry.Canonical.GrandCanonicalExperts
import InfoGeometry.Canonical.LorentzianRouting
import InfoGeometry.Canonical.Triality

namespace InfoGeometry

/-!
# InfoGeometry.LLM

Unified entrypoint for LLM-oriented formalization layers:
- thermodynamic attention and context windows
- Euclidean and Lorentzian/split attention variants
- geometric multi-head attention and output projection
- canonical transformer-block scaffold (attention + residual + normalization + MLP)
- causal-mask transformer interface
-/

end InfoGeometry

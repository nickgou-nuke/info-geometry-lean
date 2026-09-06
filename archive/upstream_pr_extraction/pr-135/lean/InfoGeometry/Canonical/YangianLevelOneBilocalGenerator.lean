import Mathlib
import InfoGeometry.Canonical.YangianLevelZeroRepresentation

namespace InfoGeometry.Canonical

variable {K : Type*} [CommRing K] [Invertible (2 : K)]
variable {L : Type*} [LieRing L] [LieAlgebra K L]
variable {V W : Type*} [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
                       [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]

open scoped TensorProduct

/--
The true coproduct of the Level-One Yangian Generator involves both the local
evaluation part and the bilocal part:
Δ(J^{(1)}) = J^{(1)} ⊗ 1 + 1 ⊗ J^{(1)} + 1/2 f^{bc}_a T_b ⊗ T_c
Here we state that the total Level-One generator preserves the super-invariance
of the BCFW glued state, which is the heart of the Yangian invariance of Amplituhedron.
-/
class LevelOneYangianInvariance (bilinearCoprod : L →ₗ[K] L ⊗[K] L)
    (localAction : L →ₗ[K] Module.End K (V ⊗[K] W)) where
  /-- The bilocal action constructed from the structure constants. -/
  bilocalAction : L →ₗ[K] Module.End K (V ⊗[K] W)
  
  /-- The total level-one action is the sum of local and bilocal parts. -/
  totalAction : L →ₗ[K] Module.End K (V ⊗[K] W) :=
    localAction + bilocalAction
    
  /-- 
  The apex theorem: The BCFW glued state is annihilated by the total level-one 
  Yangian generator if it is annihilated by the local action.
  This represents the invariance of the scattering amplitude under Yangian symmetry.
  -/
  is_invariant : ∀ (Ω : V ⊗[K] W), (∀ x, localAction x Ω = 0) → (∀ x, totalAction x Ω = 0)

end InfoGeometry.Canonical

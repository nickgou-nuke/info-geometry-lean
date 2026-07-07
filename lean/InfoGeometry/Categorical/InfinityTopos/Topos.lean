import InfoGeometry.Categorical.InfinityTopos.Category
import InfoGeometry.Categorical.InfinityTopos.Axioms

namespace InfoGeometry.Categorical

universe v u

/-- 
  Giraud's ∞-Axioms for an ∞-Topos.
  An ∞-Topos is an (∞,1)-category satisfying:
    1. Colimits: All small colimits exist
    2. Descent: Effective epimorphisms
    3. Universes: Object classifiers
-/
structure InfinityTopos (C : Type u) [InfinityCategory C] where
  colim_complete : HasAllSmallColimits C
  descent : EffectiveEpis C
  universe : ObjectClassifier C

end InfoGeometry.Categorical

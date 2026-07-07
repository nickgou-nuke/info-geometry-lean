import InfoGeometry.Categorical.InfinityTopos.Category

namespace InfoGeometry.Categorical

universe v u

/-- Axiom 1: All small colimits exist in the ∞-category -/
class HasAllSmallColimits (C : Type u) [InfinityCategory C]

/-- Axiom 2: Effective epimorphisms (Descent datum) -/
class EffectiveEpis (C : Type u) [InfinityCategory C]

/-- Axiom 3: Object classifiers (Universes) -/
class ObjectClassifier (C : Type u) [InfinityCategory C]

end InfoGeometry.Categorical

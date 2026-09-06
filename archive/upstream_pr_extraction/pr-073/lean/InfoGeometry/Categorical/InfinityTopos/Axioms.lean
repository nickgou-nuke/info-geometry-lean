import InfoGeometry.Categorical.InfinityTopos.Category
import Mathlib.CategoryTheory.Limits.HasLimits

namespace InfoGeometry.Categorical

universe v u

/--
The ordinary Mathlib colimit part of the proposed infinity-topos interface.

This is deliberately tied to the native `HasColimits` class; it is not an
empty marker.  Higher-categorical descent and classifier data remain separate
interfaces below.
-/
class HasAllSmallColimits (C : Type u) [InfinityCategory C]
    extends CategoryTheory.Limits.HasColimits C

/--
Interface for the effective-epimorphism/descent component.  No native
Mathlib infinity-categorical implementation is asserted by this marker.
-/
class EffectiveEpis (C : Type u) [InfinityCategory C]

/--
Interface for the object-classifier component.  No native Mathlib
infinity-topos classifier is asserted by this marker.
-/
class ObjectClassifier (C : Type u) [InfinityCategory C]

end InfoGeometry.Categorical

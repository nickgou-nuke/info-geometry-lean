/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.CategoryTheory.Limits.HasLimits
import InfoGeometry.Categorical.InfinityTopos.Category
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Categorical

universe v u

/-- Axiom 1: All small colimits exist in the ∞-category -/
class HasAllSmallColimits (C : Type u) [InfinityCategory C]

/-- Axiom 2: Effective epimorphisms (Descent datum) -/
class EffectiveEpis (C : Type u) [InfinityCategory C]

/-- Axiom 3: Object classifiers (Universes) -/
class ObjectClassifier (C : Type u) [InfinityCategory C]

end InfoGeometry.Categorical

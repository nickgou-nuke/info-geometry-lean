/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.AnharmonicSixPermutations

open InfoGeometry.Geometry.AnharmonicPunctures

#print axioms InfoGeometry.Geometry.AnharmonicPunctures.anharmonicWord_mul
#print axioms InfoGeometry.Geometry.AnharmonicPunctures.anharmonicWord_inv
#print axioms InfoGeometry.Geometry.AnharmonicPunctures.sixPermutationSubgroup
#print axioms InfoGeometry.Geometry.AnharmonicPunctures.anharmonicGroup_eq_sixPermutationSubgroup
#print axioms InfoGeometry.Geometry.AnharmonicPunctures.mem_anharmonicGroup_iff
#print axioms InfoGeometry.Geometry.AnharmonicPunctures.anharmonicWord_injective
#print axioms InfoGeometry.Geometry.AnharmonicPunctures.anharmonicWord_separating_values
#print axioms InfoGeometry.Geometry.AnharmonicPunctures.anharmonicGroup_natCard
#print axioms InfoGeometry.Geometry.AnharmonicPunctures.translation_not_preserves_punctures

example : exchangeEquiv * inversionEquiv ≠ inversionEquiv * exchangeEquiv := by
  intro h
  have hi : (3 : Fin 6) = 4 := anharmonicWord_injective h
  norm_num at hi

/-- Faithfulness of the whole action does not require a free action at every point. -/
example : exchangeEquiv (⟨1 / 2, by norm_num⟩ : Punctured) =
    (⟨1 / 2, by norm_num⟩ : Punctured) := by
  apply Subtype.ext
  norm_num [exchangeEquiv, exchange]

example : Nat.card anharmonicGroup = 6 := anharmonicGroup_natCard

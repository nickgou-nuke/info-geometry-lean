/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CuntzComplexStarProductPositivity
import InfoGeometry.QuantumContext.MatrixProductWordReadout
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

/-! Exact word-pair values of the positive functional on the actual quotient. -/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge
open InfoGeometry.Algebra.CliffordBitWordEquivalence
open InfoGeometry.Algebra.CuntzComplexStarBinaryCoreProjection
open InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge
open InfoGeometry.OperatorAlgebra.CuntzComplexStarColimitEmbedding
open InfoGeometry.OperatorAlgebra.CuntzComplexStarFiniteStageHom
open InfoGeometry.QuantumContext.MatrixStageProductDensity
open InfoGeometry.Categorical.FiniteWordPathWeights
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

theorem quotientProductFunctional_bitWordPair (q : Fin 2 → ℝ)
    (hq : q 0 + q 1 = 1) (n : ℕ) (u v : BitWord n) :
    quotientProductFunctional q hq (complexStarWordPair (List.ofFn u) (List.ofFn v)) =
      if u = v then ((wordWeight q (fun i => finTwoEquivBool.symm (u i)) : ℝ) : ℂ) else 0 := by
  have he : stageStarAlgEquiv n (Matrix.single u v (1 : ℂ)) =
      Matrix.single (bitWordFinPowTwoEquiv n u) (bitWordFinPowTwoEquiv n v) 1 := by
    ext i j
    simp [stageStarAlgEquiv, InfoGeometry.Canonical.BitWordComplexStageReindex.equiv,
      Matrix.reindexAlgEquiv, Matrix.reindex_apply, Matrix.single, Equiv.eq_symm_apply]
  have hm : quotientHom (stageInjection n
      (stageStarAlgEquiv n (Matrix.single u v 1))) =
      complexStarWordPair (List.ofFn u) (List.ofFn v) := by
    rw [quotientHom_stage]
    change stageMap n ((stageStarAlgEquiv n).symm
      (stageStarAlgEquiv n (Matrix.single u v 1))) = _
    rw [StarAlgEquiv.symm_apply_apply, stageMap_single, one_smul]
  rw [← hm, quotientProductFunctional_embed, he, productFunctional_wordMatrixUnit]

theorem quotientProductFunctional_wordPair (q : Fin 2 → ℝ)
    (hq : q 0 + q 1 = 1) (u v : List Bool) :
    quotientProductFunctional q hq (complexStarWordPair u v) =
      if u = v then (((u.map (fun b => q (finTwoEquivBool.symm b))).prod : ℝ) : ℂ) else 0 := by
  by_cases hlen : u.length = v.length
  · obtain ⟨i, hi⟩ : ∃ i : BitWord u.length, List.ofFn i = u :=
      ⟨u.get, List.ofFn_get u⟩
    obtain ⟨j, hj⟩ : ∃ j : BitWord u.length, List.ofFn j = v := by
      rw [hlen]
      exact ⟨v.get, List.ofFn_get v⟩
    rw [← hi, ← hj, quotientProductFunctional_bitWordPair]
    simp [wordWeight, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
  · rw [← quotientProductFunctional_projection q hq, projection_wordPair]
    have hne : u ≠ v := fun h => hlen (congrArg List.length h)
    simp [hlen, hne]

theorem quotientProductFunctional_uniform_wordPair (u v : List Bool) :
    quotientProductFunctional (fun _ => (1 / 2 : ℝ)) (by norm_num)
      (complexStarWordPair u v) = canonicalGaugeState u v := by
  rw [quotientProductFunctional_wordPair]
  simp [canonicalGaugeState,
    InfoGeometry.OperatorAlgebra.CuntzCanonicalGaugeGNSState.gaugeStateWord]

/-- Linear functionals on the quotient are determined by their word-pair values. -/
theorem linearMap_ext_wordPairs
    (f g : InfoGeometry.Physics.ComplexStarCuntzRedesign.ComplexStarCuntzAlg Bool →ₗ[ℂ] ℂ)
    (h : ∀ u v, f (complexStarWordPair u v) = g (complexStarWordPair u v)) : f = g := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ InfoGeometry.Canonical.CuntzComplexStarBinaryWordPairSpanBridge.sourceWordPairSpan := by
    rw [InfoGeometry.Canonical.CuntzComplexStarBinaryWordPairSpanBridge.sourceWordPair_span_eq_top]
    trivial
  unfold InfoGeometry.Canonical.CuntzComplexStarBinaryWordPairSpanBridge.sourceWordPairSpan at hx
  refine Submodule.span_induction (p := fun y _ => f y = g y) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨⟨u, v⟩, rfl⟩
    exact h u v
  · simp
  · intro a b _ _ ha hb
    simp [ha, hb]
  · intro c y _ hy
    simp [hy]

end InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional
end

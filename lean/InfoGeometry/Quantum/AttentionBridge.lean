import InfoGeometry.Canonical.Triality
import InfoGeometry.Canonical.Unification

namespace InfoGeometry.Quantum.AttentionBridge

open InfoGeometry.Canonical.Triality
open InfoGeometry.Canonical.Unification

/--
Attention-side scalar source tension: weighted interaction energy for a query.
-/
noncomputable def attentionSourceTension
    {Q K V ι : Type*}
    (core : TriadicCore Q K V)
    [DecidableEq ι] [AddCommGroup V] [Module ℝ V]
    (attn : GeometricAttentionMap core ι)
    (q : Q) : ℝ :=
  ∑ i ∈ attn.I, (attn.weights q i) * core.interact q (attn.keys i)

/--
For the split `Cl(1,1)` triadic instance, softmax weights are exactly Gibbs factors.
-/
theorem split_softmax_weight_formula
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (hI : I.Nonempty)
    (keys : ι → (ℝ × ℝ))
    (q : ℝ × ℝ) (i : ι) :
    (softmaxAttention splitMetricTriadicInstance.toTriadicCore I hI keys).weights q i =
      Real.exp (InfoGeometry.Clifford.splitB11 q (keys i)) /
        (∑ j ∈ I, Real.exp (InfoGeometry.Clifford.splitB11 q (keys j))) := by
  simp [softmaxAttention, splitMetricTriadicInstance]

/--
In split `Cl(1,1)` with additive route, attention decomposes into query residual plus weighted keys.
-/
theorem split_attention_as_residual
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (hI : I.Nonempty)
    (keys : ι → (ℝ × ℝ))
    (q : ℝ × ℝ) :
    let attn := softmaxAttention splitMetricTriadicInstance.toTriadicCore I hI keys
    attn.attention q = q + ∑ i ∈ I, (attn.weights q i) • keys i := by
  dsimp
  simpa using
    (GeometricAttentionMap.attention_decomposition_residual
      (attn := softmaxAttention splitMetricTriadicInstance.toTriadicCore I hI keys)
      (toV := fun q' => q')
      (kToV := fun k => k)
      (h_route := by
        intro q' k'
        rfl)
      q)

/--
If Rosetta source tension is identified with attention source tension,
its modular image follows directly from the scalar Rosetta commuting map.
-/
theorem attention_source_transports_to_modular
    {E : Type 0} {Q K V ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : ScalarAnomalyRosettaStone (E := E))
    (core : TriadicCore Q K V)
    [DecidableEq ι] [AddCommGroup V] [Module ℝ V]
    (attn : GeometricAttentionMap core ι)
    (q : Q)
    (h_source : S.source = attentionSourceTension core attn q) :
    (ScalarAnomalyRosettaStone.scalarToMajorana (E := E) (S := S))
        (attentionSourceTension core attn q) = S.modularGenerator := by
  calc
    (ScalarAnomalyRosettaStone.scalarToMajorana (E := E) (S := S))
        (attentionSourceTension core attn q)
        = (ScalarAnomalyRosettaStone.scalarToMajorana (E := E) (S := S)) S.source := by
            simp [h_source]
    _ = S.modularGenerator := S.scalar_source_eq_modular

end InfoGeometry.Quantum.AttentionBridge

import InfoGeometry.Topology.DelaunayFlipMatrix
import InfoGeometry.LLM.KreinAttentionEnergy
import InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws
import InfoGeometry.Analysis.FiniteSpectralMellinTaylor

/-!
# Delaunay adjacent structures

This module is an owner-boundary bridge.  It records that the finite Delaunay
flip layer lives next to, but is not replaced by, the existing LLM/Krein,
Pin(5,5), and finite Mellin owner surfaces.

Closed content here is deliberately limited to readback/projection theorems:

* the rational Delaunay two-by-two inverse flip theorem is re-exported from
  `InfoGeometry.Topology.DelaunayFlipMatrix`;
* split/Krein attention normalization is re-exported from
  `InfoGeometry.LLM.KreinAttentionEnergy`;
* finite Pin(5,5) basis matrix laws are re-exported from
  `InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws`;
* finite Mellin/Taylor interchange is re-exported from
  `InfoGeometry.Analysis.FiniteSpectralMellinTaylor`.

No theorem in this file asserts that Delaunay flips are Pin(5,5) actions,
Krein isometries, attention heads, or Mellin transforms.  Such claims require
additional explicit embeddings.
-/

open scoped BigOperators

namespace InfoGeometry.Topology.DelaunayAdjacentStructures

/-- Boundary marker: the adjacent formal lanes are available as separate owners. -/
structure AdjacentOwnerSurface where
  hasDelaunayFlipMatrix : Prop := True
  hasKreinAttention : Prop := True
  hasPin55MatrixLaws : Prop := True
  hasFiniteMellinTaylor : Prop := True

/-- The default boundary marker carries no mathematical identification between lanes. -/
def ownerSurface : AdjacentOwnerSurface := {}

namespace Readback

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- Readback of the kernel-checked rational two-by-two Delaunay inverse theorem. -/
theorem delaunay_flip_inverse
    (labels : InfoGeometry.Topology.Delaunay.FlipLabels ι)
    (i k j l : ι) (hik : i ≠ k) (hjl : j ≠ l) :
    InfoGeometry.Topology.Delaunay.flipInverseStatement labels i k j l hik hjl :=
  InfoGeometry.Topology.Delaunay.flip_inverse_identity labels i k j l hik hjl

variable {V : Type*} [AddCommMonoid V] [Module ℝ V]
variable {n : ℕ} [Fact (0 < n)]

omit [AddCommMonoid V] [Module ℝ V] in
/-- Readback of the normalized split/Krein attention-weight theorem. -/
theorem krein_attention_weights_sum_one
    (q : ℝ × ℝ)
    (ctx : InfoGeometry.Canonical.Attention.ContextWindow n (ℝ × ℝ) V)
    (β : ℝ) :
    ∑ i, InfoGeometry.LLM.KreinAttentionEnergy.kreinAttentionWeights (V := V) q ctx β i = 1 :=
  InfoGeometry.LLM.KreinAttentionEnergy.kreinAttentionWeights_sum_one (V := V) q ctx β

/-- Readback of the finite basis-generator Pin(5,5) matrix-law packet. -/
theorem pin55_basis_packet :
    (∀ k : Fin 10,
      InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws.IsO55
        (InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws.pinReflect k)) ∧
      (∀ k : Fin 10,
        InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws.pinReflect k *
          InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws.pinReflect k = 1) ∧
      (∀ i j : Fin 10,
        InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws.IsO55
          (InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws.pinProduct i j)) ∧
      (∀ k j : Fin 10,
        (InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws.pinReflect k).mulVec
            (InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws.basisVec j) =
          if k = j then -InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws.basisVec j
          else InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws.basisVec j) ∧
      (∀ i : Fin 5,
        InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws.cliffordSquareSign ⟨i.val, by omega⟩ = 1) ∧
      (∀ i : Fin 5,
        InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws.cliffordSquareSign ⟨i.val + 5, by omega⟩ = -1) :=
  InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws.full_pin55_basis_packet

variable {α R : Type*} [Fintype α] [CommSemiring R]

/-- Readback of finite spectral Taylor/Mellin interchange. -/
theorem finite_mellin_taylor_interchange
    (D : InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData α R)
    (c : ℕ → R) (N : ℕ) :
    (∑ i : α, D.weight i * D.pointwiseTaylorPrefix c N i) =
      D.taylorMomentPrefix c N :=
  InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData.weighted_pointwiseTaylorPrefix_eq_taylorMomentPrefix
    D c N

end Readback

end InfoGeometry.Topology.DelaunayAdjacentStructures

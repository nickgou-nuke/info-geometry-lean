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

namespace DelaunayAdjacentStructures

/-- Boundary packet recording the adjacent formal lanes as real theorem readbacks. -/
structure AdjacentOwnerSurface where
  hasDelaunayFlipMatrix : ∀ {ι : Type*} [DecidableEq ι]
    (labels : InfoGeometry.Topology.Delaunay.FlipLabels ι)
    (i k j l : ι) (hik : i ≠ k) (hjl : j ≠ l),
      InfoGeometry.Topology.Delaunay.flipInverseStatement labels i k j l hik hjl
  hasKreinAttention : ∀ {V : Type*} [AddCommMonoid V] [Module ℝ V]
    {n : ℕ} [Fact (0 < n)]
    (q : ℝ × ℝ)
    (ctx : InfoGeometry.Canonical.Attention.ContextWindow n (ℝ × ℝ) V)
    (β : ℝ),
      ∑ i, InfoGeometry.LLM.KreinAttentionEnergy.kreinAttentionWeights (V := V) q ctx β i = 1
  hasPin55MatrixLaws :
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
        InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws.cliffordSquareSign ⟨i.val + 5, by omega⟩ = -1)
  hasFiniteMellinTaylor : ∀ {α R : Type*} [Fintype α] [CommSemiring R]
    (D : InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData α R)
    (c : ℕ → R) (N : ℕ),
      (∑ i : α, D.weight i * D.pointwiseTaylorPrefix c N i) = D.taylorMomentPrefix c N

/-- The default boundary packet is the already-proved readback bundle. -/
def ownerSurface : AdjacentOwnerSurface :=
  { hasDelaunayFlipMatrix := by
      intro ι inst labels i k j l hik hjl
      exact InfoGeometry.Topology.Delaunay.flip_inverse_identity labels i k j l hik hjl
    hasKreinAttention := by
      intro V instV n instn
      refine fun q ctx β => ?_
      simpa using (InfoGeometry.LLM.KreinAttentionEnergy.kreinAttentionWeights_sum_one
        (V := V) (q := q) (ctx := ctx) (β := β))
    hasPin55MatrixLaws := InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws.full_pin55_basis_packet
    hasFiniteMellinTaylor := by
      intro α R instα instR D c N
      exact InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData.weighted_pointwiseTaylorPrefix_eq_taylorMomentPrefix
        D c N }

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

end DelaunayAdjacentStructures

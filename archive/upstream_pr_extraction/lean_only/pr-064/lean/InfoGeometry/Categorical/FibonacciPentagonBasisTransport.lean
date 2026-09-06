import InfoGeometry.Categorical.FibonacciPentagonPathComposition

/-!
# Vertex-basis transport for finite Fibonacci pentagon paths

The five path matrices currently share `Basis6`, while the five parenthesized
fusion objects have distinct formal vertices.  This file exposes the missing
basis-transport interface without choosing a noncanonical basis and without
asserting the pentagon equation.
-/

namespace InfoGeometry.Categorical.FibonacciPentagonBasisTransport

open InfoGeometry.Categorical.FibonacciPentagonPathCarrier
open InfoGeometry.Categorical.FibonacciPentagonPathComposition
open InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices

abbrev PathCarrier :=
  InfoGeometry.Categorical.FibonacciPentagonPathCarrier.PathCarrier

structure VertexBasisData where
  basis : PentagonVertex → PathCarrier ≃ₗ[ℂ] PathCarrier

noncomputable def transportedEdge
    (C : VertexBasisData) (e : PentagonEdge)
    (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    PathCarrier →ₗ[ℂ] PathCarrier :=
  (C.basis (edgeTarget e)).toLinearMap.comp
    ((edgeLinearMap e qNeg4 q3 B).comp
      (C.basis (edgeSource e)).symm.toLinearMap)

noncomputable def transportedInverseEdge
    (C : VertexBasisData) (e : PentagonEdge)
    (qNeg4 q3 : ℂ) (B Binv : BBlockEntries) :
    PathCarrier →ₗ[ℂ] PathCarrier :=
  (C.basis (edgeSource e)).toLinearMap.comp
    ((edgeInverseLinearMap e qNeg4 q3 B Binv).comp
      (C.basis (edgeTarget e)).symm.toLinearMap)

theorem transportedEdge_comp_inverse
    (C : VertexBasisData) (e : PentagonEdge)
    (qNeg4 q3 : ℂ) (B Binv : BBlockEntries)
    (hB : BBlockEntries.matrix B * BBlockEntries.matrix Binv = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    (transportedEdge C e qNeg4 q3 B).comp
        (transportedInverseEdge C e qNeg4 q3 B Binv) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp only [transportedEdge, transportedInverseEdge,
    LinearMap.comp_apply, LinearMap.id_apply]
  have h := congrArg
    (fun T : PathCarrier →ₗ[ℂ] PathCarrier =>
      T ((C.basis (edgeTarget e)).symm x))
    (edgeLinearMap_comp_inverse e qNeg4 q3 B Binv hB hqNeg4 hq3)
  simpa [LinearMap.comp_apply] using
    congrArg (C.basis (edgeTarget e)) h

theorem transportedInverse_comp_edge
    (C : VertexBasisData) (e : PentagonEdge)
    (qNeg4 q3 : ℂ) (B Binv : BBlockEntries)
    (hBinv : BBlockEntries.matrix Binv * BBlockEntries.matrix B = 1)
    (hqNeg4 : qNeg4 ≠ 0) (hq3 : q3 ≠ 0) :
    (transportedInverseEdge C e qNeg4 q3 B Binv).comp
        (transportedEdge C e qNeg4 q3 B) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp only [transportedEdge, transportedInverseEdge,
    LinearMap.comp_apply, LinearMap.id_apply]
  have h := congrArg
    (fun T : PathCarrier →ₗ[ℂ] PathCarrier =>
      T ((C.basis (edgeSource e)).symm x))
    (edgeInverse_comp_linearMap e qNeg4 q3 B Binv hBinv hqNeg4 hq3)
  simpa [LinearMap.comp_apply] using
    congrArg (C.basis (edgeSource e)) h

/-- Consecutive transported edges compose by cancelling the intermediate
vertex basis.  This is the reusable transport identity needed before a
concrete five-edge pentagon equality can be stated. -/
theorem transportedEdge_comp_transportedEdge
    (C : VertexBasisData) (e₁ e₂ : PentagonEdge)
    (hvertex : edgeTarget e₂ = edgeSource e₁)
    (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    (transportedEdge C e₁ qNeg4 q3 B).comp
        (transportedEdge C e₂ qNeg4 q3 B) =
      (C.basis (edgeTarget e₁)).toLinearMap.comp
        ((edgeLinearMap e₁ qNeg4 q3 B).comp
          ((edgeLinearMap e₂ qNeg4 q3 B).comp
            (C.basis (edgeSource e₂)).symm.toLinearMap)) := by
  apply LinearMap.ext
  intro x
  simp only [transportedEdge, LinearMap.comp_apply]
  rw [← hvertex]
  simp

/- The vertex-basis conjugation is faithful.  This is the cancellation
lemma needed to reduce a future pentagon equality to an equality of the
underlying finite path matrices, once the same basis data has been fixed. -/
theorem transportedEdge_eq_iff
    (C : VertexBasisData) (e : PentagonEdge)
    (qNeg4 q3 : ℂ) (B B' : BBlockEntries) :
    transportedEdge C e qNeg4 q3 B =
        transportedEdge C e qNeg4 q3 B' ↔
      edgeLinearMap e qNeg4 q3 B =
        edgeLinearMap e qNeg4 q3 B' := by
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    have h' := congrArg
      (fun L : PathCarrier →ₗ[ℂ] PathCarrier =>
        (C.basis (edgeTarget e)).symm
          (L ((C.basis (edgeSource e)) x))) h
    simpa [transportedEdge, LinearMap.comp_apply] using h'
  · intro h
    simp [transportedEdge, h]

noncomputable def transportedWord
    (C : VertexBasisData) (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    List PentagonEdge → PathCarrier →ₗ[ℂ] PathCarrier
  | [] => LinearMap.id
  | e :: es =>
      (transportedEdge C e qNeg4 q3 B).comp
        (transportedWord C qNeg4 q3 B es)

@[simp] theorem transportedWord_nil
    (C : VertexBasisData) (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    transportedWord C qNeg4 q3 B [] = LinearMap.id := by
  rfl

@[simp] theorem transportedWord_cons
    (C : VertexBasisData) (e : PentagonEdge) (es : List PentagonEdge)
    (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    transportedWord C qNeg4 q3 B (e :: es) =
      (transportedEdge C e qNeg4 q3 B).comp
        (transportedWord C qNeg4 q3 B es) := by
  rfl

theorem transportedWord_append
    (C : VertexBasisData) (xs ys : List PentagonEdge)
    (qNeg4 q3 : ℂ) (B : BBlockEntries) :
    transportedWord C qNeg4 q3 B (xs ++ ys) =
      (transportedWord C qNeg4 q3 B xs).comp
        (transportedWord C qNeg4 q3 B ys) := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
      simp only [List.cons_append, transportedWord_cons, ih]
      simp only [LinearMap.comp_assoc]

/-- Edgewise matrix equality is preserved by every fixed vertex-basis
transport.  This is the reusable reduction from a concrete finite matrix
word identity to its transported linear-map identity. -/
theorem transportedWord_eq_of_edgewise_eq
    (C : VertexBasisData) (xs : List PentagonEdge)
    (qNeg4 q3 : ℂ) (B B' : BBlockEntries)
    (h : ∀ e, e ∈ xs →
      edgeLinearMap e qNeg4 q3 B = edgeLinearMap e qNeg4 q3 B') :
    transportedWord C qNeg4 q3 B xs =
      transportedWord C qNeg4 q3 B' xs := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
      rw [transportedWord_cons, transportedWord_cons]
      rw [show transportedEdge C e qNeg4 q3 B =
          transportedEdge C e qNeg4 q3 B' by
        exact (transportedEdge_eq_iff C e qNeg4 q3 B B').2
          (h e (by simp))]
      congr 1
      apply ih
      intro e' he'
      exact h e' (by simp [he'])

end InfoGeometry.Categorical.FibonacciPentagonBasisTransport

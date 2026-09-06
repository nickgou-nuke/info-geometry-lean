import InfoGeometry.Clifford.Cl55WittOrthogonalBasis
import InfoGeometry.Clifford.Cl55WittOrthogonalNative
import InfoGeometry.Clifford.RealQuadraticReflectionCartanDieudonne

namespace InfoGeometry.Clifford.Clifford55

/-!
# Native reflection generation for `Q55`

The finite-basis Cartan--Dieudonné argument is already proved for the
repository's orthogonal subgroup.  This file exposes its exact native
`QuadraticMap.IsometryEquiv` consequence.  No second vector carrier or
alternative orthogonal group is introduced.
-/

noncomputable def nativeQuadraticReflectionSet :
    Set (Q55.IsometryEquiv Q55) :=
  {f | ∃ (v : V55) (hv : Q55 v ≠ 0),
      f = realQuadraticReflectionIsometry Q55 v hv}

noncomputable def nativeQuadraticReflectionSubgroup :
    Subgroup (Q55.IsometryEquiv Q55) :=
  Subgroup.closure nativeQuadraticReflectionSet

theorem nativeQuadraticReflectionSubgroup_eq_top :
    nativeQuadraticReflectionSubgroup = ⊤ := by
  change
    realQuadraticReflectionSubgroup Q55 =
      (⊤ : Subgroup (Q55.IsometryEquiv Q55))
  exact realQuadraticReflectionSubgroup_eq_top_of_orthogonal_spanning
    Q55 wittBasis wittBasis_span_eq_top
    wittBasis_Q_ne_zero wittBasis_pairwise_orthogonal

noncomputable def nativeQuadraticReflectionProduct
    (l : List (Q55.IsometryEquiv Q55)) : Q55.IsometryEquiv Q55 :=
  l.foldr (· * ·) 1

@[simp] theorem nativeQuadraticReflectionProduct_append
    (l₁ l₂ : List (Q55.IsometryEquiv Q55)) :
    nativeQuadraticReflectionProduct (l₁ ++ l₂) =
      nativeQuadraticReflectionProduct l₁ *
        nativeQuadraticReflectionProduct l₂ := by
  induction l₁ with
  | nil => simp [nativeQuadraticReflectionProduct]
  | cons r l ih =>
      change r * nativeQuadraticReflectionProduct (l ++ l₂) =
        (r * nativeQuadraticReflectionProduct l) *
          nativeQuadraticReflectionProduct l₂
      rw [ih]
      simp [mul_assoc]

theorem nativeQuadraticReflectionSet_inv_mem
    {r : Q55.IsometryEquiv Q55}
    (hr : r ∈ nativeQuadraticReflectionSet) :
    r⁻¹ ∈ nativeQuadraticReflectionSet := by
  rcases hr with ⟨v, hv, rfl⟩
  refine ⟨v, hv, ?_⟩
  exact inv_eq_of_mul_eq_one_right
    (realQuadraticReflectionIsometry_mul_self Q55 v hv)

theorem nativeQuadraticReflection_mem_factorization
    {f : Q55.IsometryEquiv Q55}
    (hf : f ∈ nativeQuadraticReflectionSubgroup) :
    ∃ l : List (Q55.IsometryEquiv Q55),
      (∀ r ∈ l, r ∈ nativeQuadraticReflectionSet) ∧
        nativeQuadraticReflectionProduct l = f := by
  induction hf using Subgroup.closure_induction'' with
  | mem r hr =>
      exact ⟨[r], by simp [hr], by simp [nativeQuadraticReflectionProduct]⟩
  | inv_mem r hr =>
      exact ⟨[r⁻¹], by simp [nativeQuadraticReflectionSet_inv_mem hr],
        by simp [nativeQuadraticReflectionProduct]⟩
  | one =>
      exact ⟨[], by simp, by simp [nativeQuadraticReflectionProduct]⟩
  | mul r s hr hs hrf hsf =>
      rcases hrf with ⟨lr, hrl, hpr⟩
      rcases hsf with ⟨ls, hsl, hps⟩
      refine ⟨lr ++ ls, ?_, ?_⟩
      · intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact hrl t ht
        · exact hsl t ht
      · rw [nativeQuadraticReflectionProduct_append, hpr, hps]

theorem nativeQuadraticReflection_factorization
    (f : Q55.IsometryEquiv Q55) :
    ∃ l : List (Q55.IsometryEquiv Q55),
      (∀ r ∈ l, r ∈ nativeQuadraticReflectionSet) ∧
        nativeQuadraticReflectionProduct l = f := by
  apply nativeQuadraticReflection_mem_factorization
  rw [nativeQuadraticReflectionSubgroup_eq_top]
  trivial

end InfoGeometry.Clifford.Clifford55

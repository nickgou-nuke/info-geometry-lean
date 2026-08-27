import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Exterior-power and exterior-form tower interface

This owner keeps multivectors `⋀[R]^n V` separate from forms, represented by
alternating maps on `V`.  It records the finite decomposable locus used by the
existing Plücker/Klein owners without asserting a duality `V ≃ V*`.
-/

noncomputable section

namespace InfoGeometry.Projective.ExteriorPluckerTower

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

abbrev Multivector (n : ℕ) := ⋀[R]^n V

abbrev ExteriorForm (n : ℕ) := AlternatingMap R V R (Fin n)

abbrev Frame (n : ℕ) := Fin n → V

def pluckerEmbedding (n : ℕ) : Frame V n → Multivector R V n :=
  exteriorPower.ιMulti R n

/-! A finite-stage tower datum.  The transition is deliberately supplied as
data: exterior powers of different degree do not carry a canonical map. -/
structure TowerDatum where
  k : ℕ
  kleinBoundary : Set (Multivector R V k)
  frameTransition : ∀ n, Frame V n → Frame V (n + 1)
  transition : ∀ n, Multivector R V n →ₗ[R] Multivector R V (n + 1)
  transition_compatible :
    ∀ n (v : Frame V n),
      transition n (pluckerEmbedding R V n v) =
        pluckerEmbedding R V (n + 1) (frameTransition n v)

def IsDecomposable {n : ℕ} (x : Multivector R V n) : Prop :=
  ∃ v : Fin n → V, exteriorPower.ιMulti R n v = x

theorem isDecomposable_ιMulti {n : ℕ} (v : Fin n → V) :
    IsDecomposable R V (exteriorPower.ιMulti R n v) :=
  ⟨v, rfl⟩

theorem pluckerEmbedding_image_is_decomposable {n : ℕ} (v : Frame V n) :
    IsDecomposable R V (pluckerEmbedding R V n v) := by
  exact isDecomposable_ιMulti R V v

theorem pluckerEmbedding_eq_ιMulti (n : ℕ) (v : Frame V n) :
    pluckerEmbedding R V n v = exteriorPower.ιMulti R n v := rfl

theorem transition_compatible_on_plucker
    (T : TowerDatum R V) (n : ℕ) (v : Frame V n) :
    T.transition n (pluckerEmbedding R V n v) =
      pluckerEmbedding R V (n + 1) (T.frameTransition n v) :=
  T.transition_compatible n v

theorem exteriorPower_ιMulti_mem_span {n : ℕ} (v : Fin n → V) :
    exteriorPower.ιMulti R n v ∈
      (Submodule.span R (Set.range (exteriorPower.ιMulti R n)) :
        Submodule R (Multivector R V n)) := by
  exact Submodule.subset_span ⟨v, rfl⟩

theorem exteriorPower_ιMulti_span_eq_top (n : ℕ) :
    Submodule.span R (Set.range (exteriorPower.ιMulti R n)) =
      (⊤ : Submodule R (Multivector R V n)) := by
  exact exteriorPower.ιMulti_span R n V

end InfoGeometry.Projective.ExteriorPluckerTower

import InfoGeometry.Clifford.Cl55ExteriorBivectorDerivation
import InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge

/-!
# Degree preservation for the lifted `Cl(5,5)` bivector action

The exterior-algebra derivation induced by a linear map on the generators
preserves each finite exterior degree.  This file proves the claim for the
repository's span-based homogeneous-degree predicate.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55ExteriorBivectorDegreeAction

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
open InfoGeometry.Clifford.Cl55ExteriorBivectorDerivation
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.BivectorVectorRepresentation

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

private def wordSpan (n : ℕ) : Submodule R (ExteriorAlgebra R V) :=
  Submodule.span R (Set.range fun v : Fin n → V =>
    List.prod (List.ofFn fun i => ExteriorAlgebra.ι R (v i)))

private theorem liftExteriorDerivation_one_eq_zero (f : V →ₗ[R] V) :
    liftExteriorDerivation f (1 : ExteriorAlgebra R V) = 0 := by
  have h := liftExteriorDerivation_leibniz f (1 : ExteriorAlgebra R V) 1
  have h' : liftExteriorDerivation f 1 + 0 =
      liftExteriorDerivation f 1 + liftExteriorDerivation f 1 := by
    simpa using h
  exact (add_left_cancel h').symm

private theorem generator_mul_wordSpan {n : ℕ} (v : V)
    (x : ExteriorAlgebra R V) (hx : x ∈ wordSpan (R := R) (V := V) n) :
    ExteriorAlgebra.ι R v * x ∈ wordSpan (R := R) (V := V) (n + 1) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨w, rfl⟩
    apply Submodule.subset_span
    refine ⟨Fin.cons v w, ?_⟩
    simp [wordSpan, List.ofFn_succ, List.prod_cons]
  · simpa using (wordSpan (R := R) (V := V) (n + 1)).zero_mem
  · intro x y hx hy h₁ h₂
    simpa [mul_add] using (wordSpan (R := R) (V := V) (n + 1)).add_mem h₁ h₂
  · intro r x hx h₁
    rw [mul_smul_comm]
    exact (wordSpan (R := R) (V := V) (n + 1)).smul_mem r h₁

private theorem liftExteriorDerivation_ιMulti_mem (f : V →ₗ[R] V) :
    ∀ n (v : Fin n → V),
      liftExteriorDerivation f (ExteriorAlgebra.ιMulti R n v) ∈
        wordSpan (R := R) (V := V) n := by
  intro n
  induction n with
  | zero =>
      intro v
      rw [ExteriorAlgebra.ιMulti_zero_apply, liftExteriorDerivation_one_eq_zero]
      exact (wordSpan (R := R) (V := V) 0).zero_mem
  | succ n ih =>
      intro v
      rw [ExteriorAlgebra.ιMulti_succ_apply,
        liftExteriorDerivation_leibniz]
      apply (wordSpan (R := R) (V := V) (n + 1)).add_mem
      · rw [liftExteriorDerivation_ι]
        apply Submodule.subset_span
        refine ⟨Fin.cons (f (v 0)) (Matrix.vecTail v), ?_⟩
        simp [List.ofFn_succ, List.prod_cons,
          ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_succ_apply]
      · exact generator_mul_wordSpan (R := R) (V := V) (v 0)
          (liftExteriorDerivation f (ExteriorAlgebra.ιMulti R n (Matrix.vecTail v)))
          (ih (Matrix.vecTail v))

/-- The lift of a linear map on generators preserves every homogeneous
exterior degree. -/
theorem liftExteriorDerivation_preserves_homogeneous_degree
    (f : V →ₗ[R] V) (n : ℕ) (x : ExteriorAlgebra R V)
    (hx : IsHomogeneousExteriorDegree (R := R) (V := V) n x) :
    IsHomogeneousExteriorDegree (R := R) (V := V) n
      (liftExteriorDerivation f x) := by
  change x ∈ wordSpan (R := R) (V := V) n at hx
  change liftExteriorDerivation f x ∈ wordSpan (R := R) (V := V) n
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨v, rfl⟩
    exact liftExteriorDerivation_ιMulti_mem f n v
  · simpa using (wordSpan (R := R) (V := V) n).zero_mem
  · intro x y hx hy h₁ h₂
    simpa using (wordSpan (R := R) (V := V) n).add_mem h₁ h₂
  · intro r x hx h₁
    rw [map_smul]
    exact (wordSpan (R := R) (V := V) n).smul_mem r h₁

local notation "Exterior55" => ExteriorAlgebra ℝ V55

/-- The `Cl(5,5)` bivector-induced derivation preserves exterior degree. -/
theorem bivectorExteriorDerivation_preserves_homogeneous_degree
    (u v : V55) (n : ℕ) (x : Exterior55)
    (hx : IsHomogeneousExteriorDegree (R := ℝ) (V := V55) n x) :
    IsHomogeneousExteriorDegree (R := ℝ) (V := V55) n
      (bivectorExteriorDerivation u v x) := by
  exact liftExteriorDerivation_preserves_homogeneous_degree
    (bivectorVectorTransformLinear u v) n x hx

end InfoGeometry.Clifford.Cl55ExteriorBivectorDegreeAction

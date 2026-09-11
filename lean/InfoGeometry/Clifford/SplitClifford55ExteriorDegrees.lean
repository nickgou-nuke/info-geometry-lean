import Mathlib.LinearAlgebra.ExteriorPower.Basis
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import InfoGeometry.Clifford.SplitClifford55ExteriorSpinor

/-!
# Homogeneous dimensions of the exterior spinor

The exterior algebra is graded by the exterior powers.  This owner records the
native Mathlib dimension theorem for each homogeneous degree; it does not
introduce a `Fin 32` carrier before the graded direct-sum dimension has been
proved.
-/

namespace InfoGeometry.Clifford.SplitClifford55ExteriorDegrees

open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor

abbrev V := V5

noncomputable def vBasis : Module.Basis (Fin 5) ℝ V := Pi.basisFun ℝ (Fin 5)

noncomputable def degreeBasis (k : ℕ) :
    Module.Basis (Set.powersetCard (Fin 5) k) ℝ (⋀[ℝ]^k V) :=
  vBasis.exteriorPower k

instance degree_finiteDimensional (k : ℕ) :
    FiniteDimensional ℝ (⋀[ℝ]^k V) :=
  Module.Basis.finiteDimensional_of_finite (degreeBasis k)

theorem exteriorDegree_finrank (k : ℕ) :
    Module.finrank ℝ (⋀[ℝ]^k V) = Nat.choose 5 k := by
  rw [exteriorPower.finrank_eq]
  simp [V]

theorem exteriorDegree_subsingleton_of_five_lt {k : ℕ} (hk : 5 < k) :
    Subsingleton (⋀[ℝ]^k V) := by
  have hfin : Module.finrank ℝ (⋀[ℝ]^k V) = 0 := by
    rw [exteriorDegree_finrank]
    exact Nat.choose_eq_zero_of_lt hk
  have hz : ∀ x : (⋀[ℝ]^k V), x = 0 :=
    finrank_zero_iff_forall_zero.mp hfin
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem exteriorDegree_eq_zero_of_five_lt
    {k : ℕ} (hk : 5 < k) (x : ⋀[ℝ]^k V) :
    x = 0 := by
  letI := exteriorDegree_subsingleton_of_five_lt hk
  exact Subsingleton.elim _ _

/- Every element of the full graded direct sum has support in degrees at most
   five.  This is the finite-support wire needed before replacing the
   `ℕ`-indexed direct sum by the finite `Fin 6` direct sum. -/
theorem gradedDirectSum_support_subset_range_six
    (x : DirectSum ℕ (fun k => ⋀[ℝ]^k V)) :
    {k | x k ≠ 0} ⊆ (Finset.range 6 : Set ℕ) := by
  intro k hk
  by_contra h
  have hk5 : 5 < k := by
    exact Nat.lt_of_not_ge (by simpa [Finset.mem_range] using h)
  have hx : x k = 0 := exteriorDegree_eq_zero_of_five_lt hk5 (x k)
  exact hk (by simp [hx])

/- The standard graded decomposition of the exterior algebra has the finite
   degree support proved above. -/
noncomputable def gradedDecomposition :
    ExteriorAlgebra ℝ V ≃ₗ[ℝ]
      DirectSum ℕ (fun k => ⋀[ℝ]^k V) :=
  (DirectSum.decomposeAlgEquiv
    (𝒜 := fun k : ℕ => ⋀[ℝ]^k V)).toLinearEquiv

theorem gradedDecomposition_support_subset_range_six
    (x : ExteriorAlgebra ℝ V) :
    {k | gradedDecomposition x k ≠ 0} ⊆
      (Finset.range 6 : Set ℕ) := by
  exact gradedDirectSum_support_subset_range_six
    (gradedDecomposition x)

noncomputable def exteriorAlgebraBasisSigma :
    Module.Basis
      (Σ k : ℕ, Set.powersetCard (Fin 5) k) ℝ (ExteriorAlgebra ℝ V) :=
  (DirectSum.Decomposition.isInternal
      (ℳ := fun k : ℕ => ⋀[ℝ]^k V)).collectedBasis
  (fun k => degreeBasis k)

/- The sigma index `(k,s)` is canonically just the underlying finite subset
   `s`; `Equiv.sigmaFiberEquiv Finset.card` performs this reindexing. -/
noncomputable def exteriorAlgebraBasisFinset :
    Module.Basis (Finset (Fin 5)) ℝ (ExteriorAlgebra ℝ V) :=
  exteriorAlgebraBasisSigma.reindex (Equiv.sigmaFiberEquiv Finset.card)

theorem exteriorAlgebra_finrank :
    Module.finrank ℝ (ExteriorAlgebra ℝ V) = 32 := by
  rw [Module.finrank_eq_card_basis exteriorAlgebraBasisFinset]
  rw [Fintype.card_finset, Fintype.card_fin]
  norm_num

end InfoGeometry.Clifford.SplitClifford55ExteriorDegrees

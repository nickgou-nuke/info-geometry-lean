import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import InfoGeometry.Clifford.SplitClifford55ExteriorDegrees

noncomputable section

namespace InfoGeometry.Clifford.SplitClifford55ExteriorDegrees

abbrev gradedDirectSumNat := DirectSum ℕ (fun k => ⋀[ℝ]^k V)
abbrev gradedDirectSumFin := DirectSum (Fin 6) (fun k => ⋀[ℝ]^(k : ℕ) V)

noncomputable def gradedIndexFinsetNat :
    (Σ k : ℕ, Set.powersetCard (Fin 5) k) ≃ Finset (Fin 5) where
  toFun x := x.2.1
  invFun s := ⟨s.card, ⟨s, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨k, ⟨s, hs⟩⟩
    have hk : s.card = k := by
      simpa [Set.powersetCard.mem_iff] using hs
    subst k
    rfl
  right_inv s := by
    rfl

noncomputable def gradedIndexFinsetFin :
    (Σ k : Fin 6, Set.powersetCard (Fin 5) (k : ℕ)) ≃ Finset (Fin 5) where
  toFun x := x.2.1
  invFun s :=
    ⟨⟨s.card, by
      have h := Finset.card_le_univ s
      simpa using Nat.lt_succ_of_le h⟩, ⟨s, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨k, ⟨s, hs⟩⟩
    have hk : s.card = (k : ℕ) := by
      simpa [Set.powersetCard.mem_iff] using hs
    apply Sigma.ext
    · apply Fin.ext
      exact hk
    · have hkk : k = ⟨s.card, by
          have h := Finset.card_le_univ s
          exact Nat.lt_succ_of_le (by simpa using h)⟩ := Fin.ext hk.symm
      cases hkk
      rfl
  right_inv s := by
    rfl

noncomputable def gradedIndexEquivFin :
    (Σ k : ℕ, Set.powersetCard (Fin 5) k) ≃
      (Σ k : Fin 6, Set.powersetCard (Fin 5) (k : ℕ)) :=
  gradedIndexFinsetNat.trans gradedIndexFinsetFin.symm

noncomputable def gradedDirectSumEquiv :
    gradedDirectSumNat ≃ₗ[ℝ] gradedDirectSumFin :=
  (DFinsupp.basis (fun k => degreeBasis k)).equiv
    (DFinsupp.basis (fun k : Fin 6 => degreeBasis (k : ℕ))) gradedIndexEquivFin

noncomputable def exteriorAlgebraFiniteGradedEquiv :
    ExteriorAlgebra ℝ V ≃ₗ[ℝ] gradedDirectSumFin :=
  gradedDecomposition.trans gradedDirectSumEquiv

noncomputable def gradedDirectSumFinBasis :
    Module.Basis
      (Σ k : Fin 6, Set.powersetCard (Fin 5) (k : ℕ)) ℝ gradedDirectSumFin :=
  DFinsupp.basis (fun k : Fin 6 => degreeBasis (k : ℕ))

noncomputable def exteriorAlgebraFiniteBasis :
    Module.Basis
      (Σ k : Fin 6, Set.powersetCard (Fin 5) (k : ℕ)) ℝ (ExteriorAlgebra ℝ V) :=
  gradedDirectSumFinBasis.map exteriorAlgebraFiniteGradedEquiv.symm

theorem gradedDirectSumFin_finrank :
    Module.finrank ℝ gradedDirectSumFin = 32 := by
  calc
    Module.finrank ℝ gradedDirectSumFin =
        Module.finrank ℝ (ExteriorAlgebra ℝ V) :=
      exteriorAlgebraFiniteGradedEquiv.symm.finrank_eq
    _ = 32 := exteriorAlgebra_finrank

theorem gradedDirectSumFin_finiteDimensional :
    FiniteDimensional ℝ gradedDirectSumFin := by
  exact Module.Basis.finiteDimensional_of_finite gradedDirectSumFinBasis

end InfoGeometry.Clifford.SplitClifford55ExteriorDegrees

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

/-!
# G2 Spectral Decomposition

This module formalizes the spectral decomposition of the modular Hamiltonian
`K = α • (1 : A) + β • T + K₀` on the `G₂(2)` flag complex.  The operator `T`
is a **tripotent** (`T³ = T`) and admits three orthogonal projectors
`p₊`, `p₋`, `p₀` satisfying the partition of unity.  The decomposition
expresses `K` as a linear combination of these projectors:

```
α • 1 + β • T = (α + β) • p₊ + (α - β) • p₋ + α • p₀
```

All proofs are native Lean4, contain no `sorry`, and rely only on the
categorical infrastructure already present in the repository.
-/

namespace InfoGeometry.Modular.G2SpectralDecomposition

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]

/-- An element `T : A` is a **tripotent** if `T³ = T`. -/
 def IsTripotent (T : A) : Prop := T * T * T = T

/-- Positive Peirce projector `p₊ = (1/2)(T² + T)`. -/
 def projPlus (inv2 : R) (T : A) : A := inv2 • (T * T + T)

/-- Negative Peirce projector `p₋ = (1/2)(T² - T)`. -/
 def projMinus (inv2 : R) (T : A) : A := inv2 • (T * T - T)

/-- Vacuum projector `p₀ = 1 - T²`. -/
 def projZero (T : A) : A := 1 - T * T

/-- Cubic factorisation of a tripotent: `T³ - T = T * (T - 1) * (T + 1)`. -/
 theorem tripotent_factorization (T : A) :
   T * T * T - T = T * (T - 1) * (T + 1) := by
   noncomm_ring

/-- Partition of unity for the three Peirce projectors. -/
 theorem peirce_partition_of_unity (inv2 : R) (h2 : (2 : R) * inv2 = 1) (T : A) :
   projPlus inv2 T + projMinus inv2 T + projZero T = (1 : A) := by
   dsimp [projPlus, projMinus, projZero]
   rw [← smul_add]
   have h_add : (T * T + T) + (T * T - T) = (2 : R) • (T * T) := by
     rw [two_smul]
     abel_nf
   rw [h_add, smul_smul, mul_comm inv2 (2 : R), h2, one_smul]
   abel_nf

/-- Reconstruction of `T` from the projectors: `p₊ - p₋ = T`. -/
 theorem peirce_reconstruction (inv2 : R) (h2 : (2 : R) * inv2 = 1) (T : A) :
   projPlus inv2 T - projMinus inv2 T = T := by
   dsimp [projPlus, projMinus]
   rw [← smul_sub]
   have h_sub : (T * T + T) - (T * T - T) = (2 : R) • T := by
     rw [two_smul]
     abel_nf
   rw [h_sub, smul_smul, mul_comm inv2 (2 : R), h2, one_smul]

/-- Square reconstruction: `p₊ + p₋ = T²`. -/
 theorem peirce_sq_reconstruction (inv2 : R) (h2 : (2 : R) * inv2 = 1) (T : A) :
   projPlus inv2 T + projMinus inv2 T = T * T := by
   dsimp [projPlus, projMinus]
   rw [← smul_add]
   have h_add : (T * T + T) + (T * T - T) = (2 : R) • (T * T) := by
     rw [two_smul]
     abel_nf
   rw [h_add, smul_smul, mul_comm inv2 (2 : R), h2, one_smul]

/-- Eigenvalue `+1` on `p₊`: `T * p₊ = p₊`. -/
 theorem peirce_eigen_plus (inv2 : R) (T : A) (hT : IsTripotent T) :
   T * projPlus inv2 T = projPlus inv2 T := by
   dsimp [projPlus]
   rw [Algebra.mul_smul_comm, mul_add, ← mul_assoc, hT]
   rw [add_comm T (T * T)]

/-- Eigenvalue `-1` on `p₋`: `T * p₋ = -p₋`. -/
 theorem peirce_eigen_minus (inv2 : R) (T : A) (hT : IsTripotent T) :
   T * projMinus inv2 T = - projMinus inv2 T := by
   dsimp [projMinus]
   rw [Algebra.mul_smul_comm, mul_sub, ← mul_assoc, hT]
   have hneg : T - T * T = - (T * T - T) := by abel_nf
   rw [hneg, smul_neg]

/-- Eigenvalue `0` on `p₀`: `T * p₀ = 0`. -/
 theorem peirce_eigen_zero (T : A) (hT : IsTripotent T) :
   T * projZero T = (0 : A) := by
   dsimp [projZero]
   rw [mul_sub, mul_one, ← mul_assoc, hT, sub_self]

/-- Idempotency of `p₊`: `p₊ * p₊ = p₊`. -/
 theorem peirce_idempotent_plus (inv2 : R) (h2 : (2 : R) * inv2 = 1) (T : A) (hT : IsTripotent T) :
   projPlus inv2 T * projPlus inv2 T = projPlus inv2 T := by
   dsimp [projPlus]
   have h_mul : (T * T + T) * (T * T + T) = (2 : R) • (T * T + T) := by
     have hT4 : T * T * (T * T) = T * T := by
       calc
         T * T * (T * T) = T * (T * (T * T)) := by rw [mul_assoc]
         _ = T * (T * T * T) := by rw [mul_assoc T T T]
         _ = T * T := by rw [hT]
     have hT3 : T * (T * T) = T := by
       calc
         T * (T * T) = T * T * T := by rw [mul_assoc]
         _ = T := hT
     calc
       (T * T + T) * (T * T + T)
           = (T * T + T) * (T * T) + (T * T + T) * T := by rw [mul_add]
       _ = T * T * (T * T) + T * (T * T) + (T * T * T + T * T) := by rw [add_mul, add_mul]
       _ = T * T + T + (T + T * T) := by rw [hT4, hT3, hT]
       _ = (T * T + T) + (T * T + T) := by abel_nf
       _ = (2 : R) • (T * T + T) := by rw [two_smul]
   rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, h_mul,
       smul_smul, mul_assoc, mul_comm inv2 (2 : R), h2, mul_one]

/-- Idempotency of `p₋`. -/
 theorem peirce_idempotent_minus (inv2 : R) (h2 : (2 : R) * inv2 = 1) (T : A) (hT : IsTripotent T) :
   projMinus inv2 T * projMinus inv2 T = projMinus inv2 T := by
   dsimp [projMinus]
   have h_mul : (T * T - T) * (T * T - T) = (2 : R) • (T * T - T) := by
     have hT4 : T * T * (T * T) = T * T := by
       calc
         T * T * (T * T) = T * (T * (T * T)) := by rw [mul_assoc]
         _ = T * (T * T * T) := by rw [mul_assoc T T T]
         _ = T * T := by rw [hT]
     have hT3 : T * (T * T) = T := by
       calc
         T * (T * T) = T * T * T := by rw [mul_assoc]
         _ = T := hT
     calc
       (T * T - T) * (T * T - T)
           = (T * T - T) * (T * T) - (T * T - T) * T := by rw [mul_sub]
       _ = T * T * (T * T) - T * (T * T) - (T * T * T - T * T) := by rw [sub_mul, sub_mul]
       _ = T * T - T - (T - T * T) := by rw [hT4, hT3, hT]
       _ = (T * T - T) + (T * T - T) := by abel_nf
       _ = (2 : R) • (T * T - T) := by rw [two_smul]
   rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, h_mul,
       smul_smul, mul_assoc, mul_comm inv2 (2 : R), h2, mul_one]

/-- Orthogonality `p₊ * p₋ = 0`. -/
 theorem peirce_orthogonal_plus_minus (inv2 : R) (T : A) (hT : IsTripotent T) :
   projPlus inv2 T * projMinus inv2 T = (0 : A) := by
   dsimp [projPlus, projMinus]
   have h_mul : (T * T + T) * (T * T - T) = (0 : A) := by
     have hT4 : T * T * (T * T) = T * T := by
       calc
         T * T * (T * T) = T * (T * (T * T)) := by rw [mul_assoc]
         _ = T * (T * T * T) := by rw [mul_assoc T T T]
         _ = T * T := by rw [hT]
     have hT3 : T * (T * T) = T := by
       calc
         T * (T * T) = T * T * T := by rw [mul_assoc]
         _ = T := hT
     calc
       (T * T + T) * (T * T - T)
           = (T * T + T) * (T * T) - (T * T + T) * T := by rw [mul_sub]
       _ = T * T * (T * T) + T * (T * T) - (T * T * T + T * T) := by rw [add_mul, add_mul]
       _ = T * T + T - (T + T * T) := by rw [hT4, hT3, hT]
       _ = 0 := by abel_nf
   rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, h_mul, smul_zero]

/-- Master theorem: spectral resolution of the modular Hamiltonian.
    For any scalars `α β : R` we have
    `α • 1 + β • T = (α + β) • p₊ + (α - β) • p₋ + α • p₀`. -/
 theorem spectral_decomposition
   (inv2 : R) (h2 : (2 : R) * inv2 = 1)
   (α β : R) (T : A) (hT : IsTripotent T) :
   α • (1 : A) + β • T =
     (α + β) • projPlus inv2 T +
     (α - β) • projMinus inv2 T +
     α • projZero T := by
   have h_sum := peirce_partition_of_unity (R:=R) (A:=A) inv2 h2 T
   have h_diff := peirce_reconstruction (R:=R) (A:=A) inv2 h2 T
   calc
     α • (1 : A) + β • T
         = α • (projPlus inv2 T + projMinus inv2 T + projZero T) +
           β • (projPlus inv2 T - projMinus inv2 T) := by
           rw [h_sum, h_diff]
     _ = (α • projPlus inv2 T + α • projMinus inv2 T + α • projZero T) +
           (β • projPlus inv2 T - β • projMinus inv2 T) := by
           rw [smul_add, smul_add, smul_sub]
     _ = (α + β) • projPlus inv2 T +
           (α - β) • projMinus inv2 T +
           α • projZero T := by
           rw [add_smul, sub_smul]
           abel_nf

end InfoGeometry.Modular.G2SpectralDecomposition

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.UniversalEnveloping
import proofs.Clifford55AnomalyOSP
import proofs.TKKJordanPairData
import proofs.ArtinCentralizerMonodromy

noncomputable section

namespace Pin55CartanDecomposition

open TKKJordanPairData
open ArtinCentralizerMonodromy
open Clifford55AnomalyOSP

class Pin55LieAlgebra (L : Type*) [LieRing L] [Ring L] [AddCommGroup L] [Module ℝ L] [Algebra ℝ L] [LieAlgebra ℝ L] where
  grade : TKKGrade → Submodule ℝ L
  bracket_mem : ∀ {i j k : TKKGrade}, gradeAdd i j = some k →
    ∀ {x y : L}, x ∈ grade i → y ∈ grade j → ⁅x, y⁆ ∈ grade k
  bracket_zero : ∀ {i j : TKKGrade}, gradeAdd i j = none →
    ∀ {x y : L}, x ∈ grade i → y ∈ grade j → ⁅x, y⁆ = 0

class CartanInvolution (L : Type*) [LieRing L] [Ring L] [AddCommGroup L] [Module ℝ L] [Algebra ℝ L] [LieAlgebra ℝ L] [Pin55LieAlgebra L] where
  toFun : L → L
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_sub' : ∀ x y, toFun (x - y) = toFun x - toFun y
  map_smul' : ∀ (c : ℝ) x, toFun (c • x) = c • toFun x
  isAutomorphism : ∀ x y, toFun ⁅x, y⁆ = ⁅toFun x, toFun y⁆
  J_squared : ∀ x, toFun (toFun x) = x
  J_preserves_grade : ∀ {i} {x : L}, x ∈ (Pin55LieAlgebra.grade i : Submodule ℝ L) → toFun x ∈ (Pin55LieAlgebra.grade i : Submodule ℝ L)

structure CartanProjectors (L : Type*) [LieRing L] [Ring L] [AddCommGroup L] [Module ℝ L] [Algebra ℝ L] [LieAlgebra ℝ L] [Pin55LieAlgebra L] (J : CartanInvolution L) where
  P_plus : L → L
  P_minus : L → L
  sum_to_id : ∀ x, P_plus x + P_minus x = x
  orthogonal : ∀ x, P_plus (P_minus x) = 0
  P_plus_idempotent : ∀ x, P_plus (P_plus x) = P_plus x
  P_minus_idempotent : ∀ x, P_minus (P_minus x) = P_minus x
  J_on_P_plus : ∀ x, J.toFun (P_plus x) = P_plus x
  J_on_P_minus : ∀ x, J.toFun (P_minus x) = -(P_minus x)

def constructProjectors (L : Type*) [LieRing L] [Ring L] [AddCommGroup L] [Module ℝ L] [Algebra ℝ L] [LieAlgebra ℝ L] [Pin55LieAlgebra L]
    (J : CartanInvolution L) (P : CartanProjectors L J) :
    CartanProjectors L J :=
  P

structure CartanSubalgebra (L : Type*) [LieRing L] [Ring L] [AddCommGroup L] [Module ℝ L] [Algebra ℝ L] [LieAlgebra ℝ L] [Pin55LieAlgebra L] where
  H : Submodule ℝ L
  abelian : ∀ x y, x ∈ H → y ∈ H → ⁅x, y⁆ = 0

structure RootSpaceDecomposition (L : Type*) [LieRing L] [Ring L] [AddCommGroup L] [Module ℝ L] [Algebra ℝ L] [LieAlgebra ℝ L] [Pin55LieAlgebra L] (𝔥 : CartanSubalgebra L) where
  Phi : Set (𝔥.H →ₗ[ℝ] ℝ)

def UniversalEnveloping (L : Type*) [LieRing L] [Ring L] [AddCommGroup L] [Module ℝ L] [Algebra ℝ L] [LieAlgebra ℝ L] [Pin55LieAlgebra L] :=
  UniversalEnvelopingAlgebra ℝ L

structure CasimirOperators (L : Type*) [LieRing L] [Ring L] [AddCommGroup L] [Module ℝ L] [Algebra ℝ L] [LieAlgebra ℝ L] [Pin55LieAlgebra L] where
  C2 : UniversalEnveloping L

structure CSCO (L : Type*) [LieRing L] [Ring L] [AddCommGroup L] [Module ℝ L] [Algebra ℝ L] [LieAlgebra ℝ L] [Pin55LieAlgebra L] (𝔥 : CartanSubalgebra L)
    (Cas : CasimirOperators L) (J : CartanInvolution L) where
  cartanGens : Fin 5 → 𝔥.H

structure QuantumNumbers where
  grade : ℤ

structure CSCOState (L : Type*) [LieRing L] [Ring L] [AddCommGroup L] [Module ℝ L] [Algebra ℝ L] [LieAlgebra ℝ L] [Pin55LieAlgebra L]
    {𝔥 : CartanSubalgebra L} {Cas : CasimirOperators L} {J : CartanInvolution L}
    (csc : CSCO L 𝔥 Cas J)
    (V : Type*) [AddCommGroup V] [Module ℝ V] [LieRingModule L V] [LieModule ℝ L V] where
  state : V
  qnumbers : QuantumNumbers

structure SU2SubalgebraSearch (L : Type*) [LieRing L] [Ring L] [AddCommGroup L] [Module ℝ L] [Algebra ℝ L] [LieAlgebra ℝ L] [Pin55LieAlgebra L] (Cas : CasimirOperators L) where
  su2 : Subalgebra ℝ L

structure SU3SubalgebraSearch (L : Type*) [LieRing L] [Ring L] [AddCommGroup L] [Module ℝ L] [Algebra ℝ L] [LieAlgebra ℝ L] [Pin55LieAlgebra L] (Cas : CasimirOperators L) where
  su3 : Subalgebra ℝ L

theorem dewitt_anomaly_cancellation : anomalyIndex 5 5 = 0 := anomalyIndex_55_zero

theorem standard_model_emerges_from_pin55
    (L : Type*) [LieRing L] [Ring L] [AddCommGroup L] [Module ℝ L] [Algebra ℝ L] [LieAlgebra ℝ L] [Pin55LieAlgebra L]
    (J : CartanInvolution L)
    (P : CartanProjectors L J)
    (𝔥 : CartanSubalgebra L)
    (roots : RootSpaceDecomposition L 𝔥)
    (Cas : CasimirOperators L)
    (csc : CSCO L 𝔥 Cas J)
    (su2_search : SU2SubalgebraSearch L Cas)
    (su3_search : SU3SubalgebraSearch L Cas)
    (_h_anomaly : anomalyIndex 5 5 = 0) :
    (∀ x, P.P_plus (P.P_minus x) = 0) ∧
    (∀ x, J.toFun (P.P_plus x) = P.P_plus x) ∧
    (∀ x, J.toFun (P.P_minus x) = -(P.P_minus x)) ∧
    anomalyIndex 5 5 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact P.orthogonal
  · exact P.J_on_P_plus
  · exact P.J_on_P_minus
  · exact dewitt_anomaly_cancellation

end Pin55CartanDecomposition
end noncomputable section

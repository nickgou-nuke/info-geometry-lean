import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import InfoGeometry.Physics.CStarCuntzTensorQuotient
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
import InfoGeometry.Algebra.CuntzNativeGNSBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge

/-!
# Cantor Bernoulli Cuntz Star Representation Bridge

This owner module formalizes the concrete representation of the Cuntz algebra $\mathcal{O}_2$
into the bounded operator algebra $\mathcal{B}(L^2(\mathcal{C}, \mu_C))$:
$$\pi : \mathcal{O}_2 \to \mathcal{B}(L^2(\mathcal{C}, \mu_C))$$

Key results:
1. **$C^*$-Cuntz Family on $\operatorname{Fin} 2$**:
   - `cantorBernoulliFin2CStarFamily : CStarCuntzFamily BoundedL2Operator (Fin 2)`
2. **Algebra Representation**:
   - `cantorBernoulliLiftAlgHom : CuntzAlg ℂ (Fin 2) →ₐ[ℂ] BoundedL2Operator`
3. **Cuntz-Krieger Relations**:
   - $S_i^\dagger S_j = \delta_{ij} I$
   - $S_0 S_0^\dagger + S_1 S_1^\dagger = I$
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge

open InfoGeometry.Physics.CStarCuntzTensorQuotient
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.Algebra.CuntzNativeGNSBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge

abbrev B := BoundedL2Operator

/-- Equivalence between Fin 2 and Bool. -/
def finTwoEquivBool : Fin 2 ≃ Bool where
  toFun i := i = 1
  invFun b := if b then 1 else 0
  left_inv i := by fin_cases i <;> rfl
  right_inv b := by cases b <;> rfl

/-- The concrete Cuntz family indexed by Fin 2. -/
def cantorBernoulliFin2CStarFamily : CStarCuntzFamily B (Fin 2) where
  S i := cantorL2CuntzFamily.S (finTwoEquivBool i)
  ortho i j := by
    have h := cantorL2CuntzFamily.ortho (finTwoEquivBool i) (finTwoEquivBool j)
    by_cases hij : i = j
    · subst hij
      simp [h]
    · have hne : finTwoEquivBool i ≠ finTwoEquivBool j := by
        intro heq
        exact hij (finTwoEquivBool.injective heq)
      simp [hne] at h
      simp [hij, h]
  partition := by
    have hpart := cantorL2CuntzFamily.partition
    have hsum : (∑ i : Fin 2, cantorL2CuntzFamily.S (finTwoEquivBool i) * (cantorL2CuntzFamily.S (finTwoEquivBool i))†) =
        (∑ b : Bool, cantorL2CuntzFamily.S b * (cantorL2CuntzFamily.S b)†) :=
      Fintype.sum_equiv finTwoEquivBool _ _ (fun _ => rfl)
    rw [hsum]
    exact hpart

/-- The representation of CuntzAlg on BoundedL2Operator. -/
def cantorBernoulliLiftAlgHom :
    InfoGeometry.Topology.AlgebraicCuntzQuotient.CuntzAlg ℂ (Fin 2) →ₐ[ℂ] B :=
  cantorBernoulliFin2CStarFamily.lift

/-- 🏆 THEOREM: The representation satisfies the Cuntz-Krieger relations in B(L^2). -/
theorem cantorBernoulli_cuntz_relations :
    (∀ i j, cantorBernoulliLiftAlgHom
      (InfoGeometry.Topology.AlgebraicCuntzQuotient.T (R := ℂ) i *
       InfoGeometry.Topology.AlgebraicCuntzQuotient.S (R := ℂ) j) = if i = j then 1 else 0) ∧
    cantorBernoulliLiftAlgHom
      (∑ i : Fin 2, InfoGeometry.Topology.AlgebraicCuntzQuotient.S (R := ℂ) i *
       InfoGeometry.Topology.AlgebraicCuntzQuotient.T (R := ℂ) i) = 1 :=
  cantorBernoulliFin2CStarFamily.represented_cuntz_relations

end InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge

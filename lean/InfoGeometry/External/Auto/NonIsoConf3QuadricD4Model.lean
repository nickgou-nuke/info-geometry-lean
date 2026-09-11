import InfoGeometry.External.Auto.NonIsoConf3OrlikSolomon
import InfoGeometry.Algebra.FiniteSpinAlgebra
/-!
# D=4 formal quadric-generator algebra for three non-isotropic points

This file records a finite algebraic model with two generator types for each
of the three pairs:

* `alpha12, alpha23, alpha13` in degree `1`;
* `beta12, beta23, beta13` in degree `3`.

The formal rank calculation is the tensor product of the alpha quotient by the
Arnold triangle relation with the free exterior algebra on the beta generators.
No geometric comparison theorem for the actual configuration space is asserted
in this file.
-/

noncomputable section

namespace NonIsoConf3QuadricD4Model

/-- The six visible generators in the corrected D=4 candidate. -/
inductive QuadricGen where
  | alpha12
  | alpha23
  | alpha13
  | beta12
  | beta23
  | beta13
  deriving DecidableEq, Repr, Inhabited

open QuadricGen

/-- Formal degrees: `alpha` classes have degree 1, `beta` classes degree 3. -/
def genDegree : QuadricGen → ℕ
  | alpha12 | alpha23 | alpha13 => 1
  | beta12 | beta23 | beta13 => 3

theorem alpha_degrees :
    genDegree alpha12 = 1 ∧ genDegree alpha23 = 1 ∧ genDegree alpha13 = 1 := by
  simp [genDegree]

theorem beta_degrees :
    genDegree beta12 = 3 ∧ genDegree beta23 = 3 ∧ genDegree beta13 = 3 := by
  simp [genDegree]

/-- Degree-two alpha products. -/
inductive AlphaProduct where
  | a12a23
  | a12a13
  | a23a13
  deriving DecidableEq, Repr, Inhabited

open AlphaProduct

abbrev Rank2Vector := InfoGeometry.Algebra.FiniteSpin.Vec2Z

def vadd (u v : Rank2Vector) : Rank2Vector := fun i => u i + v i
def vsub (u v : Rank2Vector) : Rank2Vector := fun i => u i - v i

/-- Formal normal form for degree-two alpha products in the candidate
quotient after the standard Arnold-type triangle pattern. This is a finite
combinatorial normalization, not a claimed geometric identification with the
actual `dlog` classes. -/
def reduceAlphaProduct : AlphaProduct → Rank2Vector
  | a12a23 => fun i => if i = 0 then 1 else 0
  | a12a13 => fun i => if i = 1 then 1 else 0
  | a23a13 => fun i => if i = 0 then -1 else 1

/-- The formal triangle pattern reduces to zero in this candidate basis. -/
theorem alpha_arnold_relation :
    vadd (vsub (reduceAlphaProduct a12a23) (reduceAlphaProduct a12a13))
      (reduceAlphaProduct a23a13) = 0 := by
  funext i
  fin_cases i <;> simp [vadd, vsub, reduceAlphaProduct]

/-- Betti numbers for the alpha generators (degree 1) subject to the
Arnold relation `A12*A23 - A12*A13 + A23*A13 = 0`.
The relation drops the rank in degree 2 by 1, and kills degree 3 entirely. -/
def alphaRank : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 2
  | _ => 0

/-- Betti numbers for the beta generators (degree 3) forming a free exterior algebra. -/
def betaRank : ℕ → ℕ
  | 0 => 1
  | 3 => 3
  | 6 => 3
  | 9 => 1
  | _ => 0

/-- Hilbert ranks of the formal exterior quotient computed by the tensor product
of the alpha quotient algebra and the beta exterior algebra.

This tensor product imposes only the alpha Arnold relation. It does not claim
the final cohomology of the D=4 configuration space. -/
def candidateRank (n : ℕ) : ℕ :=
  (List.range (n + 1)).map (fun i => alphaRank i * betaRank (n - i)) |>.sum

theorem low_degree_candidate_ranks :
    candidateRank 0 = 1 ∧
    candidateRank 1 = 3 ∧
    candidateRank 2 = 2 ∧
    candidateRank 3 = 3 ∧
    candidateRank 4 = 9 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem top_candidate_rank_zero : candidateRank 12 = 0 := by
  rfl

/-- Summary of the finite algebraic data proved in this file. -/
theorem corrected_d4_candidate_synthesis :
    genDegree alpha12 = 1 ∧
    genDegree beta12 = 3 ∧
    vadd (vsub (reduceAlphaProduct a12a23) (reduceAlphaProduct a12a13))
      (reduceAlphaProduct a23a13) = 0 ∧
    candidateRank 0 = 1 ∧
    candidateRank 1 = 3 ∧
    candidateRank 2 = 2 ∧
    candidateRank 12 = 0 := by
  exact ⟨rfl, rfl, alpha_arnold_relation, rfl, rfl, rfl, rfl⟩

end NonIsoConf3QuadricD4Model

end noncomputable section

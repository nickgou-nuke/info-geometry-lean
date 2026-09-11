import InfoGeometry.Clifford.Clifford55
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55SpinBivectorImage
import InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge
import Mathlib.Tactic

/-!
# Native Clifford Bivector Vector Representation and `SO(5,5)` Realization

This module establishes the native vector representation of `SpinBivector55`:
1. `bivectorVectorTransform`: The explicit vector action $T_B(w) = B(v, w) u - B(u, w) v$.
2. `bivector_vector_action_eq`: Mechanically proves $[ \iota(u)\iota(v), \iota(w) ] = \iota(T_B(w))$.
3. `bivectorVectorTransform_skew`: Mechanically proves $B(T_B w_1, w_2) + B(w_1, T_B w_2) = 0$, establishing that $T_B \in \mathfrak{so}(Q_{5,5})$.
4. `bivector_bracket_vector_action`: Mechanically proves that the Clifford Lie bracket of bivectors matches the Lie bracket commutator of their vector transformations:
   $[ [B_1, B_2], \iota(w) ] = \iota( [T_1, T_2](w) )$.
-/

noncomputable section

namespace InfoGeometry.Clifford.BivectorVectorRepresentation

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinBivectorImage
open InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge
open CliffordAlgebra

/-- The canonical vector transformation induced on $V_{5,5}$ by an elementary bivector $u \wedge v$. -/
def bivectorVectorTransform (u v w : V55) : V55 :=
  (QuadraticMap.polar (⇑Q55) v w) • u - (QuadraticMap.polar (⇑Q55) u w) • v

/-- 🏆 THEOREM 1: Clifford Commutator Realizes the Vector Action:
    $[ \iota(u) \iota(v), \iota(w) ] = \iota(T_B(w))$. -/
theorem bivector_vector_action_eq (u v w : V55) :
    ⁅ι55 u * ι55 v, ι55 w⁆ = ι55 (bivectorVectorTransform u v w) := by
  have hcomm : ⁅ι55 u * ι55 v, ι55 w⁆ =
      ι55 u * (ι55 v * ι55 w + ι55 w * ι55 v) - (ι55 u * ι55 w + ι55 w * ι55 u) * ι55 v := by
    simp [Ring.lie_def]
    noncomm_ring
  rw [hcomm]
  rw [CliffordAlgebra.ι_mul_ι_add_swap (Q := Q55) v w]
  rw [CliffordAlgebra.ι_mul_ι_add_swap (Q := Q55) u w]
  have h1 : ι55 u * algebraMap ℝ Cl55 (QuadraticMap.polar (⇑Q55) v w) =
      (QuadraticMap.polar (⇑Q55) v w) • ι55 u := by
    rw [← Algebra.commutes, ← Algebra.smul_def]
  have h2 : algebraMap ℝ Cl55 (QuadraticMap.polar (⇑Q55) u w) * ι55 v =
      (QuadraticMap.polar (⇑Q55) u w) • ι55 v := by
    rw [← Algebra.smul_def]
  rw [h1, h2]
  dsimp [bivectorVectorTransform]
  rw [map_sub, map_smul, map_smul]

/-- 🏆 THEOREM 2: Exact Skew-Symmetry / $\mathfrak{so}(Q_{5,5})$ Preservation:
    $B(T_B(w_1), w_2) + B(w_1, T_B(w_2)) = 0$. -/
theorem bivectorVectorTransform_skew (u v w₁ w₂ : V55) :
    (QuadraticMap.polar (⇑Q55) (bivectorVectorTransform u v w₁) w₂) +
      (QuadraticMap.polar (⇑Q55) w₁ (bivectorVectorTransform u v w₂)) = 0 := by
  dsimp [bivectorVectorTransform]
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left]
  rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right]
  have hsymm1 : QuadraticMap.polar (⇑Q55) w₁ u = QuadraticMap.polar (⇑Q55) u w₁ :=
    QuadraticMap.polar_comm (⇑Q55) w₁ u
  have hsymm2 : QuadraticMap.polar (⇑Q55) w₁ v = QuadraticMap.polar (⇑Q55) v w₁ :=
    QuadraticMap.polar_comm (⇑Q55) w₁ v
  rw [hsymm1, hsymm2]
  simp only [smul_eq_mul]
  ring

/-- 🏆 THEOREM 3: Lie Homomorphism Property of Bivector Vector Action:
    $[ [B_1, B_2], \iota(w) ] = \iota( [T_1, T_2](w) )$. -/
theorem bivector_bracket_vector_action (u₁ v₁ u₂ v₂ w : V55) :
    ⁅⁅ι55 u₁ * ι55 v₁, ι55 u₂ * ι55 v₂⁆, ι55 w⁆ =
      ι55 (bivectorVectorTransform u₁ v₁ (bivectorVectorTransform u₂ v₂ w) -
           bivectorVectorTransform u₂ v₂ (bivectorVectorTransform u₁ v₁ w)) := by
  have hjacobi : ⁅⁅ι55 u₁ * ι55 v₁, ι55 u₂ * ι55 v₂⁆, ι55 w⁆ =
      ⁅ι55 u₁ * ι55 v₁, ⁅ι55 u₂ * ι55 v₂, ι55 w⁆⁆ - ⁅ι55 u₂ * ι55 v₂, ⁅ι55 u₁ * ι55 v₁, ι55 w⁆⁆ := by
    simp [Ring.lie_def]
    noncomm_ring
  rw [hjacobi]
  rw [bivector_vector_action_eq u₂ v₂ w]
  rw [bivector_vector_action_eq u₁ v₁ w]
  rw [bivector_vector_action_eq u₁ v₁ (bivectorVectorTransform u₂ v₂ w)]
  rw [bivector_vector_action_eq u₂ v₂ (bivectorVectorTransform u₁ v₁ w)]
  rw [map_sub]

end InfoGeometry.Clifford.BivectorVectorRepresentation

import InfoGeometry.OperatorAlgebra.KreinInnerDerivation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Supergraded metric-Cuntz tangent layer

Parity and the Krein involution are explicit parameters. This avoids conflating
Hilbert adjoint, Krein adjoint, and grading.
-/

namespace InfoGeometry.OperatorAlgebra

open InfoGeometry.Krein
open InfoGeometry.Krein.KreinSpace
open InfoGeometry.Algebra.Cuntz
open scoped InnerProductSpace BigOperators

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]
variable {N : ℕ}

structure SuperKreinCuntzFamily
    (Γ : H →L[ℝ] H)
    (sharp : (H →L[ℝ] H) → (H →L[ℝ] H))
    (η ηinv : Fin N → Fin N → ℝ) where
  S : Fin N → H →L[ℝ] H
  gamma_involutive : Γ * Γ = 1
  odd : ∀ i, Γ * S i * Γ = -(S i)
  metric_isometry : ∀ i j,
    sharp (S i) * S j = η i j • 1
  metric_complete :
    ∑ i : Fin N, ∑ j : Fin N,
      ηinv i j • (S i * sharp (S j)) = 1

structure SuperKreinCuntzTangent
    {Γ : H →L[ℝ] H}
    {sharp : (H →L[ℝ] H) → (H →L[ℝ] H)}
    {η ηinv : Fin N → Fin N → ℝ}
    (O : SuperKreinCuntzFamily (N := N) Γ sharp η ηinv) where
  X : Fin N → H →L[ℝ] H
  tangent_odd : ∀ i, Γ * X i * Γ = -(X i)
  tangent_isometry : ∀ i j,
    sharp (X i) * O.S j + sharp (O.S i) * X j = 0
  tangent_complete :
    ∑ i : Fin N, ∑ j : Fin N,
      ηinv i j •
        (X i * sharp (O.S j) + O.S i * sharp (X j)) = 0

theorem even_commutator_odd
    {A : Type*} [Ring A]
    (Γ K S : A)
    (hΓ : Γ * Γ = 1)
    (hK : K * Γ = Γ * K)
    (hS : Γ * S * Γ = -S) :
    Γ * (K * S - S * K) * Γ = -(K * S - S * K) := by
  calc
    Γ * (K * S - S * K) * Γ =
        Γ * K * S * Γ - Γ * S * K * Γ := by noncomm_ring
    _ = K * Γ * S * Γ - Γ * S * Γ * K := by
      simp only [mul_assoc]
      congr 1
      · rw [← mul_assoc, hK.symm]
        simp only [mul_assoc]
      · rw [hK]
    _ = -(K * S - S * K) := by
      calc
        K * Γ * S * Γ - Γ * S * Γ * K =
            K * (Γ * S * Γ) - (Γ * S * Γ) * K := by noncomm_ring
        _ = -(K * S - S * K) := by
          rw [hS]
          noncomm_ring
/-- An even Krein-skew generator produces a supergraded metric-Cuntz tangent. -/
noncomputable def evenKreinGenerator_superCuntzTangent
    (O : SuperKreinCuntzFamily (N := N) Γ sharp η ηinv)
    (K : H →L[ℝ] H)
    (hK : IsKreinSkewAdjoint K)
    (hKeven : K * Γ = Γ * K)
    (hsharpK : ∀ T, kreinCommutator K (sharp T) = sharp (kreinCommutator K T)) :
    SuperKreinCuntzTangent O := by
  let X : Fin N → H →L[ℝ] H := fun i => kreinCommutator K (O.S i)
  have hK1 : kreinCommutator K (1 : H →L[ℝ] H) = 0 := by
    change K * 1 - 1 * K = 0
    simp only [mul_one, one_mul, sub_self]
  have hisometry (i j : Fin N) :
      kreinCommutator K (sharp (O.S i) * O.S j) =
        sharp (X i) * O.S j + sharp (O.S i) * X j := by
    rw [kreinCommutator_leibniz, hsharpK]
  have hcomplete :
      kreinCommutator K
          (∑ i : Fin N, ∑ j : Fin N,
            ηinv i j • (O.S i * sharp (O.S j))) =
        ∑ i : Fin N, ∑ j : Fin N,
          ηinv i j •
            (X i * sharp (O.S j) + O.S i * sharp (X j)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [kreinCommutator_smul]
    change ηinv i j •
        (K * (O.S i * sharp (O.S j)) -
          (O.S i * sharp (O.S j)) * K) =
      ηinv i j •
        ((K * O.S i - O.S i * K) * sharp (O.S j) +
          O.S i * sharp (kreinCommutator K (O.S j)))
    rw [← hsharpK (O.S j)]
    change ηinv i j •
        (K * (O.S i * sharp (O.S j)) -
          (O.S i * sharp (O.S j)) * K) =
      ηinv i j •
        ((K * O.S i - O.S i * K) * sharp (O.S j) +
          O.S i * (K * sharp (O.S j) - sharp (O.S j) * K))
    exact congrArg (fun Z => ηinv i j • Z) (by noncomm_ring)
  refine { X := X, tangent_odd := ?_, tangent_isometry := ?_, tangent_complete := ?_ }
  · intro i
    exact even_commutator_odd Γ K (O.S i)
      O.gamma_involutive hKeven (O.odd i)
  · intro i j
    have hrel := congrArg (kreinCommutator K) (O.metric_isometry i j)
    rw [hisometry] at hrel
    simpa [kreinCommutator_smul, hK1] using hrel
  · have hrel := congrArg (kreinCommutator K) O.metric_complete
    rw [hcomplete] at hrel
    simpa [hK1] using hrel

end InfoGeometry.OperatorAlgebra

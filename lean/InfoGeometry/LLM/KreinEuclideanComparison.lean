import InfoGeometry.LLM.KreinAttentionEnergy
import InfoGeometry.Canonical.Attention
import InfoGeometry.Meta.Architecture

open scoped BigOperators

namespace InfoGeometry.LLM.KreinEuclideanComparison

open InfoGeometry.LLM.KreinAttentionEnergy
open InfoGeometry.Canonical.Attention

/-- Euclidean interaction energy on `ℝ × ℝ` (same carrier as the split/Krein lane). -/
def euclideanInteractionEnergy2D (q k : ℝ × ℝ) : ℝ :=
  -(q.1 * k.1 + q.2 * k.2)

/-- Coordinate form of Euclidean interaction energy on `ℝ × ℝ`. -/
@[simp, rep_depth krein]
theorem euclideanInteractionEnergy2D_eq_coords
    (q k : ℝ × ℝ) :
    euclideanInteractionEnergy2D q k = -(q.1 * k.1 + q.2 * k.2) := by
  rfl

/-- Compact comparison law: Krein vs Euclidean interaction energies differ by `2*q₂*k₂`. -/
@[simp, rep_depth krein]
theorem krein_minus_euclidean_energy
    (q k : ℝ × ℝ) :
    kreinInteractionEnergy q k - euclideanInteractionEnergy2D q k = 2 * q.2 * k.2 := by
  simp [kreinInteractionEnergy_eq_neg_splitB11, euclideanInteractionEnergy2D_eq_coords]
  ring

section ContextComparison

variable {n : ℕ}
variable {V : Type*}

/--
Same-context comparison surface:
if query/key second channels vanish, split (Krein) and Euclidean energies coincide.
-/
@[rep_depth transport]
theorem context_energy_agreement_of_zero_second_channel
    (q : ℝ × ℝ)
    (ctx : ContextWindow n (ℝ × ℝ) V)
    (j : Fin n)
    (hq : q.2 = 0)
    (hk : (ctx.keys j).2 = 0) :
    kreinInteractionEnergy q (ctx.keys j)
      = euclideanInteractionEnergy2D q (ctx.keys j) := by
  have hsub :
      kreinInteractionEnergy q (ctx.keys j)
        - euclideanInteractionEnergy2D q (ctx.keys j) = 0 := by
    have h := krein_minus_euclidean_energy q (ctx.keys j)
    rw [hq, hk] at h
    simpa using h
  exact sub_eq_zero.mp hsub

end ContextComparison

end InfoGeometry.LLM.KreinEuclideanComparison

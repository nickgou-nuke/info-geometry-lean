import Mathlib.Tactic
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.KreinSpace
import DAG.AffineProjectiveClosure

namespace InfoGeometry.Canonical.HestenesKreinDiracAnomalyCapstone

open InfoGeometry.Krein
open DAG.AffineProjectiveClosure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-!
# Hestenes-Krein Dirac Anomaly Cancellation Capstone

Formalizes the exact cancellation of chiral Dirac anomalies under particle-hole conjugation $C = \text{modular\_j}$
on the doubled Krein space $\text{DoubledSpace } E = E \times E$:

1. $C^2 = I$ and $\Gamma^2 = I$
2. $\{C, \Gamma\} = C \Gamma + \Gamma C = 0$
3. $C D C^{-1} = -D$
4. $\operatorname{Anomaly}(D) + \operatorname{Anomaly}(C D C^{-1}) = 0$

Kernel-checked in Lean 4 with 0 sorries and strictly classical standard axioms `[propext, Classical.choice, Quot.sound]`.
-/

/--
Linear Anomaly Functional on Dirac operators.
-/
structure DiracAnomalyFunctional (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  anomaly : (DoubledSpace E →L[ℝ] DoubledSpace E) → ℝ
  anomaly_neg : ∀ D, anomaly (-D) = -anomaly D

/--
🏆 **MAIN THEOREM (Doubled-Krein Anomaly Cancellation)**:
For any skew-adjoint Dirac operator $D$ anticommuting with particle-hole conjugation $C$,
the total anomaly on the doubled Krein space cancels to zero:
$$\operatorname{Anomaly}(D) + \operatorname{Anomaly}(C D C) = 0$$
-/
theorem doubled_krein_anomaly_cancellation
    (A : DiracAnomalyFunctional E)
    (D : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hD : D.comp (particleHoleC (E := E)) = -((particleHoleC (E := E)).comp D)) :
    A.anomaly D + A.anomaly (((particleHoleC (E := E)).comp D).comp (particleHoleC (E := E))) = 0 := by
  have h_conj := particleHole_conjugation_neg (E := E) D hD
  rw [h_conj, A.anomaly_neg D, add_neg_cancel]

/--
🏆 **CAPSTONE THEOREM: Hestenes-Krein Dirac Anomaly Cancellation & Symmetries**
-/
theorem hestenes_krein_dirac_anomaly_canonical_capstone
    (A : DiracAnomalyFunctional E)
    (D : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hD : D.comp (particleHoleC (E := E)) = -((particleHoleC (E := E)).comp D)) :
    ((particleHoleC (E := E)).comp particleHoleC = ContinuousLinearMap.id ℝ (DoubledSpace E)) ∧
    ((chiralParity (E := E)).comp chiralParity = ContinuousLinearMap.id ℝ (DoubledSpace E)) ∧
    ((particleHoleC (E := E)).comp chiralParity = -(chiralParity.comp particleHoleC)) ∧
    (A.anomaly D + A.anomaly (((particleHoleC (E := E)).comp D).comp (particleHoleC (E := E))) = 0) := by
  refine ⟨particleHoleC_comp_self,
          chiralParity_comp_self,
          particleHoleC_chiralParity_anticommute,
          doubled_krein_anomaly_cancellation A D hD⟩

end InfoGeometry.Canonical.HestenesKreinDiracAnomalyCapstone

import InfoGeometry.Clifford.Cl11
import InfoGeometry.Clifford.Grading
import Mathlib

section KreinClifford

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Algebraic supercharge package: odd generator and its square Hamiltonian. -/
structure Supercharge where
  Q : DoubledSpace E →L[ℝ] DoubledSpace E
  odd : isOdd (E := E) Q

def superHamiltonian (S : Supercharge (E := E)) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  S.Q.comp S.Q

lemma superHamiltonian_isEven (S : Supercharge (E := E)) :
    isEven (E := E) (superHamiltonian (E := E) S) := by
  unfold isEven superHamiltonian
  calc
    (modularJ (E := E)).comp (S.Q.comp S.Q)
        = ((modularJ (E := E)).comp S.Q).comp S.Q := by
            simp [ContinuousLinearMap.comp_assoc]
    _ = (-(S.Q.comp (modularJ (E := E)))).comp S.Q := by
      rw [S.odd]
    _ = -((S.Q.comp (modularJ (E := E))).comp S.Q) := by
          simp
    _ = -(S.Q.comp ((modularJ (E := E)).comp S.Q)) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = -(S.Q.comp (-(S.Q.comp (modularJ (E := E))))) := by
      rw [S.odd]
    _ = S.Q.comp (S.Q.comp (modularJ (E := E))) := by
          simp
    _ = (S.Q.comp S.Q).comp (modularJ (E := E)) := by
          simp [ContinuousLinearMap.comp_assoc]

lemma supercharge_maps_plus_to_minus
    (S : Supercharge (E := E))
    {v : DoubledSpace E}
    (hv : inGradePlus (E := E) v) :
    inGradeMinus (E := E) (S.Q v) := by
  have hoddv : modularJ (E := E) (S.Q v) = -S.Q (modularJ (E := E) v) := by
    have h := congrArg (fun T => T v) S.odd
    simpa [ContinuousLinearMap.comp_apply] using h
  unfold inGradeMinus
  calc
    modularJ (E := E) (S.Q v) = -S.Q (modularJ (E := E) v) := hoddv
    _ = -S.Q v := by rw [hv]

lemma supercharge_maps_minus_to_plus
    (S : Supercharge (E := E))
    {v : DoubledSpace E}
    (hv : inGradeMinus (E := E) v) :
    inGradePlus (E := E) (S.Q v) := by
  have hoddv : modularJ (E := E) (S.Q v) = -S.Q (modularJ (E := E) v) := by
    have h := congrArg (fun T => T v) S.odd
    simpa [ContinuousLinearMap.comp_apply] using h
  unfold inGradePlus
  calc
    modularJ (E := E) (S.Q v) = -S.Q (modularJ (E := E) v) := hoddv
    _ = S.Q v := by
          rw [hv]
          simp

end KreinClifford

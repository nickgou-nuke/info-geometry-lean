import InfoGeometry.Krein.Grading

namespace InfoGeometry.Krein

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure Supercharge where
  Q : DoubledSpace E →L[ℝ] DoubledSpace E
  odd : isOdd (E := E) Q

abbrev superSquare (S : Supercharge (E := E)) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  S.Q * S.Q

def superHamiltonian (S : Supercharge (E := E)) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  superSquare (E := E) S

lemma superHamiltonian_isEven (S : Supercharge (E := E)) :
    isEven (E := E) (superHamiltonian (E := E) S) := by
  unfold isEven superHamiltonian superSquare
  -- J(QQ) = (JQ)Q = (-(QJ))Q = -Q(JQ) = -Q(-(QJ)) = (QQ)J
  calc
    modularJ (E := E) * (S.Q * S.Q)
        = (modularJ (E := E) * S.Q) * S.Q := by simp [mul_assoc]
    _ = (-(S.Q * modularJ (E := E))) * S.Q := by simpa using S.odd
    _ = -(S.Q * (modularJ (E := E) * S.Q)) := by
          simp [mul_assoc, sub_eq_add_neg, add_assoc]
    _ = -(S.Q * (-(S.Q * modularJ (E := E)))) := by
          -- rewrite J*Q using odd again
          have : modularJ (E := E) * S.Q = -(S.Q * modularJ (E := E)) := S.odd
          -- solve for (J*Q) and substitute
          simpa [this, mul_assoc]
    _ = (S.Q * S.Q) * modularJ (E := E) := by
          simp [mul_assoc]

lemma supercharge_maps_plus_to_minus (S : Supercharge (E := E))
    {v : DoubledSpace E} (hv : inGradePlus (E := E) v) :
    inGradeMinus (E := E) (S.Q v) := by
  have hoddv : modularJ (E := E) (S.Q v) = -S.Q (modularJ (E := E) v) := by
    -- unfold odd condition at v
    -- (J*Q) v = -(Q*J) v
    simpa [isOdd, ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply] using
      congrArg (fun T => T v) S.odd
  unfold inGradeMinus
  calc
    modularJ (E := E) (S.Q v) = -S.Q (modularJ (E := E) v) := hoddv
    _ = -S.Q v := by simp [hv]

lemma superHamiltonian_maps_plus_to_plus (S : Supercharge (E := E))
    {v : DoubledSpace E} (hv : inGradePlus (E := E) v) :
    inGradePlus (E := E) ((superHamiltonian (E := E) S) v) := by
  have h_minus : inGradeMinus (E := E) (S.Q v) :=
    supercharge_maps_plus_to_minus (E := E) S hv
  unfold superHamiltonian superSquare inGradePlus inGradeMinus at *
  -- Apply oddness twice
  have hoddv : modularJ (E := E) (S.Q (S.Q v)) = -S.Q (modularJ (E := E) (S.Q v)) := by
    simpa [isOdd, ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply] using
      congrArg (fun T => T (S.Q v)) S.odd
  calc
    modularJ (E := E) (S.Q (S.Q v)) = -S.Q (modularJ (E := E) (S.Q v)) := hoddv
    _ = -S.Q (-S.Q v) := by simp [h_minus]
    _ = S.Q (S.Q v) := by simp

def epsilonSupercharge : Supercharge (E := E) where
  Q := spectralEpsilon (E := E)
  odd := spectralEpsilon_isOdd (E := E)

lemma epsilonSupercharge_hamiltonian :
    superHamiltonian (E := E) (epsilonSupercharge (E := E))
      = (1 : DoubledSpace E →L[ℝ] DoubledSpace E) := by
  unfold superHamiltonian superSquare epsilonSupercharge
  exact spectralEpsilon_involution (E := E)

lemma complexI_isOdd : isOdd (E := E) (complexI (E := E)) := by
  unfold isOdd complexI
  ext v <;> simp [modularJ, spectralEpsilon, mul_assoc]

def complexISupercharge : Supercharge (E := E) where
  Q := complexI (E := E)
  odd := complexI_isOdd (E := E)

lemma complexISupercharge_hamiltonian :
    superHamiltonian (E := E) (complexISupercharge (E := E))
      = -(1 : DoubledSpace E →L[ℝ] DoubledSpace E) := by
  unfold superHamiltonian superSquare complexISupercharge
  exact complexI_sq (E := E)

end InfoGeometry.Krein
